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

namespace PEqualNP.Outside.L_meta_44976_aux

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

def dom_31 : Nat := 0xffffffff
def goal_31 : Nat := 0xfeeaeaa8feeaeaa8feeaeaa8feeaeaa8feeaeaa8feeaeaa8feeaeaa8feeaeaa8
def roots_31 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xfeaafeaaeaa8eaa8feaafeaaeaa8eaa8feaafeaaeaa8eaa8feaafeaaeaa8eaa8
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfcfcfc00fcc0c000fcfcfc00fcc0c000fcfcfc00fcc0c000fcfcfc00fcc0c000
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_30 : Nat := 0x55555555
def goal_30 : Nat := 0xfcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000
def roots_30 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_15 : Nat := 0xffff
def goal_15 : Nat := 0xeaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8
def roots_15 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0]

def dom_47_16 : Nat := 0xffff0000ffff0000
def goal_47_16 : Nat := 0xfefefefefeeafeeafefefefefeeafeeafefefefefeeafeeafefefefefeeafeea
def roots_47_16 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_15_16 : Nat := 0xffff0000
def goal_15_16 : Nat := 0xfeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeea
def roots_15_16 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xfefeaaaaeaeaa8a8fefeaaaaeaeaa8a8fefeaaaaeaeaa8a8fefeaaaaeaeaa8a8
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xeeeeeeaaeeaaaa88eeeeeeaaeeaaaa88eeeeeeaaeeaaaa88eeeeeeaaeeaaaa88
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfafafaaafaaaaaa0fafafaaafaaaaaa0fafafaaafaaaaaa0fafafaaafaaaaaa0
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_23 : Nat := 0xff00ff
def goal_23 : Nat := 0xeaeaa8a8eaeaa8a8eaeaa8a8eaeaa8a8eaeaa8a8eaeaa8a8eaeaa8a8eaeaa8a8
def roots_23 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0]

def dom_27 : Nat := 0xf0f0f0f
def goal_27 : Nat := 0xeeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88
def roots_27 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_43 : Nat := 0xf0f00000f0f
def goal_43 : Nat := 0xeeaaeeaaaa88aa88eeaaeeaaaa88aa88eeaaeeaaaa88aa88eeaaeeaaaa88aa88
def roots_43 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_51 : Nat := 0xf000f000f000f
def goal_51 : Nat := 0xeeeeaaaaaaaa8888eeeeaaaaaaaa8888eeeeaaaaaaaa8888eeeeaaaaaaaa8888
def roots_51 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_29 : Nat := 0x33333333
def goal_29 : Nat := 0xfaaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0faaaaaa0
def roots_29 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_45 : Nat := 0x333300003333
def goal_45 : Nat := 0xfaaafaaaaaa0aaa0faaafaaaaaa0aaa0faaafaaaaaa0aaa0faaafaaaaaa0aaa0
def roots_45 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_53 : Nat := 0x33003300330033
def goal_53 : Nat := 0xfafaaaaaaaaaa0a0fafaaaaaaaaaa0a0fafaaaaaaaaaa0a0fafaaaaaaaaaa0a0
def roots_53 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_55_8 : Nat := 0xff00ff00ff00ff00
def goal_55_8 : Nat := 0xfefefefefefeeaeafefefefefefeeaeafefefefefefeeaeafefefefefefeeaea
def roots_55_8 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59_4 : Nat := 0xf0f0f0f0f0f0f0f0
def goal_59_4 : Nat := 0xffffffaaffeeeeaaffffffaaffeeeeaaffffffaaffeeeeaaffffffaaffeeeeaa
def roots_59_4 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61_2 : Nat := 0xcccccccccccccccc
def goal_61_2 : Nat := 0xffffffaafffafaaaffffffaafffafaaaffffffaafffafaaaffffffaafffafaaa
def roots_61_2 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_23_8 : Nat := 0xff00ff00
def goal_23_8 : Nat := 0xfefeeaeafefeeaeafefeeaeafefeeaeafefeeaeafefeeaeafefeeaeafefeeaea
def roots_23_8 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0]

def dom_39_16 : Nat := 0xff000000ff0000
def goal_39_16 : Nat := 0xfefefefeeaeaeaeafefefefeeaeaeaeafefefefeeaeaeaeafefefefeeaeaeaea
def roots_39_16 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0]

def dom_39_8 : Nat := 0xff000000ff00
def goal_39_8 : Nat := 0xfefefefeeaeaeaeafefefefeeaeaeaeafefefefeeaeaeaeafefefefeeaeaeaea
def roots_39_8 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0]

def dom_27_4 : Nat := 0xf0f0f0f0
def goal_27_4 : Nat := 0xffeeeeaaffeeeeaaffeeeeaaffeeeeaaffeeeeaaffeeeeaaffeeeeaaffeeeeaa
def roots_27_4 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfefefeaafeeaeaa8fefefeaafeeaeaa8fefefeaafeeaeaa8fefefeaafeeaeaa8
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

namespace S_31
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 9), (1, 17), (2, 3), (4, 5), (6, 7), (6, 14), (6, 22), (8, 9), (10, 11), (10, 14), (10, 26), (12, 13), (12, 14), (12, 28), (16, 17), (18, 19), (18, 22), (18, 26), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28)]
def r1sG : List Nat := [1, 1, 1, 1, 2, 4, 6, 6, 6, 8, 10, 10, 10, 12, 12, 12, 16, 18, 18, 18, 20, 20, 20, 24, 24, 24]
def r2sG : List Nat := [3, 5, 9, 17, 3, 5, 7, 14, 22, 9, 11, 14, 26, 13, 14, 28, 17, 19, 22, 26, 21, 22, 28, 25, 26, 28]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [2203520468227, 6601533424389, 4402510170373, 6601566979331, 2203520469251, 10999613490435, 19795841254659, 8800489571081, 6601566980355, 13198536082185, 13237106311950, 13220246722062, 13198603191045, 11021189781006, 2203419346179, 19834176866586, 22016020251414, 21994629628689, 4402644910853, 13237493701134]
def xsM : List Nat := roots_31.map (· &&& dom_31)
def goalM : Nat := goal_31 &&& dom_31
def NN : Nat → Nat
  | 4 => 6
  | 5 => 37
  | 6 => 61
  | 7 => 9
  | 8 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xadd70e10ac05225e3af66a742894ea921d44e6e417cfa2c2
  | 5, 0 => 0xac05225e6528b32b5e1d4aa85299e96d4fb17e0e4530cac13d8f140e3c7381e53a6b8d41358bf72434b216b632f633fb32bc99002d026e952ce412202720edd82637312d2561510121c32ccb1ac7d7cf1912da0d12f0140512161fe5105081110e1c9e840b3763f30b178bec0adaa4e009c35db909639ed508884c85085f815d07a7bc1a06937bbb0523c5ca04ed2e9904e179de
  | 6, 0 => 0xd051f507ac05225e76e6bc16700151036e5cf1046b778c425e1d4aa8554c825e5299e96d4d02a438407c58e93a6b8d41388fb024381fe78f32f633fb32bc990030706e422eb6f7e02db5e6222637312d2596f911206585ea1f1fe9ed1d978cb81b8a7ef11ac7d7cf18c41cbb18b8e630187c321d1863781a172f56661604e97e148cee9c147c6aa71386b0af12fe2d5b12e5db1310ccb8d00fd672800f91f1710e148d100de1e4bc0d360c660c1ef63c0a8209a909873cd908dabbe6074368e8067329db061a7d5105eeac45058c87c50569308c04b53d6b049ac070034963b102aadecf0241d3e100c1d07800b965fd004a583e
  | 7, 0 => 0xd051f507ac05225e554c825e5299e96d3a6b8d4130706e42206585ea1b8a7ef10241d3e1
  | 8, 0 => 0xac05225e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xcc00cc0000000000000000000000000000000000000000000000000000000000aa00aa00000000000000000000000000000000000000000000000000000000005500550000000000000000000000000000000000000000000000000000000000330033000000000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000555500000000000000000000000000000000000000000000000000000000000000ff
  | 0, 1 => 0x3f3f3f3f0000000000000000000000000000000000000000000000000000000033333333000000000000000000000000000000000000000000000000000000000f0ff0f0000000000000000000000000000000000000000000000000000000000f0f0f0f00000000000000000000000000000000000000000000000000000000050f050f0000000000000000000000000000000000000000000000000000000000ffffff0000000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000ff0000
  | 0, 2 => 0x8888888800000000000000000000000000000000000000000000000000000000666666660000000000000000000000000000000000000000000000000000000055ff55ff000000000000000000000000000000000000000000000000000000005555555500000000000000000000000000000000000000000000000000000000555500000000000000000000000000000000000000000000000000000000000050505050000000000000000000000000000000000000000000000000000000004444cccc0000000000000000000000000000000000000000000000000000000044444444
  | 0, 3 => 0xaaaaaaaa00000000000000000000000000000000000000000000000000000000aaaa888800000000000000000000000000000000000000000000000000000000aaaa555500000000000000000000000000000000000000000000000000000000aaaa000000000000000000000000000000000000000000000000000000000000aa00aa0000000000000000000000000000000000000000000000000000000000a8a8a8a800000000000000000000000000000000000000000000000000000000a0a0a0a000000000000000000000000000000000000000000000000000000000a0a00000
  | 0, 4 => 0xcccccccc00000000000000000000000000000000000000000000000000000000cc00cc0000000000000000000000000000000000000000000000000000000000cc00000000000000000000000000000000000000000000000000000000000000c0c0c0c000000000000000000000000000000000000000000000000000000000bb33bb3300000000000000000000000000000000000000000000000000000000afafafaf00000000000000000000000000000000000000000000000000000000aaffaaff00000000000000000000000000000000000000000000000000000000aaaaffff
  | 0, 5 => 0xf0f0000000000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000eeeeeeee00000000000000000000000000000000000000000000000000000000eeeecccc00000000000000000000000000000000000000000000000000000000eecceecc00000000000000000000000000000000000000000000000000000000eeaaaaaa00000000000000000000000000000000000000000000000000000000ee00ee0000000000000000000000000000000000000000000000000000000000dddddddd
  | 0, 6 => 0xf8f8f8f800000000000000000000000000000000000000000000000000000000f5f5f5f500000000000000000000000000000000000000000000000000000000f0fff0ff00000000000000000000000000000000000000000000000000000000f0f0ffff00000000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000f0f0c0c000000000000000000000000000000000000000000000000000000000f0f0a0a000000000000000000000000000000000000000000000000000000000f0f00f0f
  | 0, 7 => 0xff80ff8000000000000000000000000000000000000000000000000000000000ff0fff0f00000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000ff00fa0000000000000000000000000000000000000000000000000000000000fcfcfcfc00000000000000000000000000000000000000000000000000000000fafafafa00000000000000000000000000000000000000000000000000000000fafaf0f000000000000000000000000000000000000000000000000000000000fafaaaaa
  | 0, 8 => 0xfff0fff000000000000000000000000000000000000000000000000000000000ffccffcc00000000000000000000000000000000000000000000000000000000ffcccccc00000000000000000000000000000000000000000000000000000000ffc0ff0000000000000000000000000000000000000000000000000000000000ffaaffaa00000000000000000000000000000000000000000000000000000000ffaaff0000000000000000000000000000000000000000000000000000000000ffaaaaaa00000000000000000000000000000000000000000000000000000000ffa8ffa8
  | 0, 9 => 0xfffffcfc00000000000000000000000000000000000000000000000000000000fffff0f000000000000000000000000000000000000000000000000000000000ffffcccc00000000000000000000000000000000000000000000000000000000ffffaaaa00000000000000000000000000000000000000000000000000000000ffffaa0000000000000000000000000000000000000000000000000000000000ffff888800000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000fffafffa
  | 0, 10 => 0xffffff00
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x497accb2497acd39f500f59a73a801ea73e35004b86cd5a007ac139f4
  | 5, 0, 0 => 0x7acd39c02b31eb34e7964c66698a2c97accf91592cd31f08b25eb75a5d65c3669cfabd7690f83596f59ab3eb25fb34e7d64b34e8432cb7a9cf8c592e939912b260334e7d64c666a4fac97a9cf8b5
  | 5, 0, 1 => 0x927c70c12b25eb3549d64bd66a082c97acd394592f59a33eb259ab3e2564a73e304ac97ae539f592cca0e12af5a273e0964bc669cfac97ae9399593119a73eb261b34e5564b34e504ac984cd3945
  | 5, 0, 2 => 0x497acd39f5a1059a73eb263ae4e7d64bd4e7c62d0669cf8a5
  | 6, 0, 0 => 0x125ea7447c6300931d9ae4e7d804f92f59a73ec024bd669cf9860125eb34e7c034e9319eb34e7dc04966b939f12c028497acd39460125eb33e64730092f59a73e3d804990f59a73ec024bd669d21460125eb35e9cfb0092e99a73e2580497acd8a73ec024b34e7c4886
  | 6, 0, 1 => 0x125eb3649cfb0092f59a73e69804d92f59ad3ec024bd669cf9260125eb35e7c730092f59ac3e7180497acd6a72ec024bd669cf87601263334e7c4b0092f9eb34e7d80497accf8e18c024b5669cf8960125eb34e7cab0092f59a72839804a92f59a73ec024bd669d01f6
  | 6, 0, 2 => 0x125eb34e7c3300012539f1825400092f5ca73ea024c67acd39f60125eb34e5ca30092f59a7284d800092f5d2732a024bd70cd39f60125eba669cfb009315eb34e7d805092f539f18c024bd669cf83600024b34e504a8092f59a84e7d80497acd39f0ac024b34e7c4866
  | 6, 0, 3 => 0x24bd669cf94600024bd669cfa8092f539f283180497acd3a53ec01eb34e7ce03601261b34e7cdb0001263ae4e7d40497acd39f38c000497a9cf8c50125eb6669ca30098f59a73e0d800092f59a728a024c37acd3946
  | 7, 0, 0 => 0x24bd669cf9460125eb34e7d64bd669cf9c60125ea73e3140497acd39459319eb34e7da4bd74cd39f692f59a73e0da4bd66bd39f6
  | 8, 0, 0 => 0x497acd39f5
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 39
  | 5 => 39
  | 6 => 53
  | 7 => 46
  | 8 => 39
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 7 0) :: stateWires n (ids >>> 7)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xe01d0000000000000000000000000000000000000000000000000000000000000000f00000000000000000000000000000000000000000000000000000000007f01f0000000000000000000000000000000000000000000000000000000000071002f000000000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000e1e0000000000000000000000000000000000000000000000000000000000000fff000000000000000000000000000000000000000000000000000000000000001ff
  | 0, 1 => 0x3fffe3f0000000000000000000000000000000000000000000000000000000003f1e22f00000000000000000000000000000000000000000000000000000000038fe1e000000000000000000000000000000000000000000000000000000000038f1e1f00000000000000000000000000000000000000000000000000000000038f1e1f00000000000000000000000000000000000000000000000000000000007fffff00000000000000000000000000000000000000000000000000000000007f01ff00000000000000000000000000000000000000000000000000000000007f0000
  | 0, 2 => 0xe1ddf0000000000000000000000000000000000000000000000000000000003ffffff0000000000000000000000000000000000000000000000000000000003fffff00000000000000000000000000000000000000000000000000000000003ff0000000000000000000000000000000000000000000000000000000000000070e1e000000000000000000000000000000000000000000000000000000000000e1dd000000000000000000000000000000000000000000000000000000000000e1dd0
  | 0, 3 => 0xf0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 0, 4 => 0xe1dd00000000000000000000000000000000000000000000000000000000000001c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001c00000000000000000000000000000000000000000000000000000000003f1e22f00000000000000000000000000000000000000000000000000000000038f1e1f00000000000000000000000000000000000000000000000000000000007f01ff000000000000000000000000000000000000000000000000000000000000ffff
  | 0, 5 => 0x700000000000000000000000000000000000000000000000000000000000000000e00000000000000000000000000000000000000000000000000000000000000e1ddf00000000000000000000000000000000000000000000000000000000000e1dd000000000000000000000000000000000000000000000000000000000000e1dd0000000000000000000000000000000000000000000000000000000000000000f0000000000000000000000000000000000000000000000000000000000001c000000000000000000000000000000000000000000000000000000000003fffff0
  | 0, 6 => 0x70e1e00000000000000000000000000000000000000000000000000000000003fffff000000000000000000000000000000000000000000000000000000000007fe1ff000000000000000000000000000000000000000000000000000000000070ffff000000000000000000000000000000000000000000000000000000000070e1e000000000000000000000000000000000000000000000000000000000007001c000000000000000000000000000000000000000000000000000000000007000000000000000000000000000000000000000000000000000000000000000701e1f
  | 0, 7 => 0x380fe0000000000000000000000000000000000000000000000000000000000038ffe1f000000000000000000000000000000000000000000000000000000000380fe00000000000000000000000000000000000000000000000000000000000380e00000000000000000000000000000000000000000000000000000000000007efdf0000000000000000000000000000000000000000000000000000000000070e1ef000000000000000000000000000000000000000000000000000000000070e1e0000000000000000000000000000000000000000000000000000000000070000f
  | 0, 8 => 0x3f0ffe000000000000000000000000000000000000000000000000000000000038effd000000000000000000000000000000000000000000000000000000000038e1dd0000000000000000000000000000000000000000000000000000000000380fe00000000000000000000000000000000000000000000000000000000000380fe0f000000000000000000000000000000000000000000000000000000000380fe00000000000000000000000000000000000000000000000000000000000380000f000000000000000000000000000000000000000000000000000000000380fe00
  | 0, 9 => 0x3fffdf00000000000000000000000000000000000000000000000000000000003ffe1e00000000000000000000000000000000000000000000000000000000003ff1dd00000000000000000000000000000000000000000000000000000000003ff000f0000000000000000000000000000000000000000000000000000000003ff00000000000000000000000000000000000000000000000000000000000003ff00000000000000000000000000000000000000000000000000000000000003ff00000000000000000000000000000000000000000000000000000000000003f0ffef
  | 0, 10 => 0x3fffe00
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x260151000000000000000000000000000000000000000000000000000000000013007b0000000000000000000000000000000000000000000000000000000000240100000000000000000000000000000000000000000000000000000000000011002a0000000000000000000000000000000000000000000000000000000000006ef700000000000000000000000000000000000000000000000000000000000068e200000000000000000000000000000000000000000000000000000000000048800000000000000000000000000000000000000000000000000000000000000073
  | 0, 1 => 0x3dbb63f0000000000000000000000000000000000000000000000000000000002d1a22e00000000000000000000000000000000000000000000000000000000018b78ea00000000000000000000000000000000000000000000000000000000018b161d00000000000000000000000000000000000000000000000000000000010b10190000000000000000000000000000000000000000000000000000000000376fff000000000000000000000000000000000000000000000000000000000037017b0000000000000000000000000000000000000000000000000000000000370108
  | 0, 2 => 0x204510000000000000000000000000000000000000000000000000000000001bd7bae00000000000000000000000000000000000000000000000000000000037fd9fb00000000000000000000000000000000000000000000000000000000036cd98000000000000000000000000000000000000000000000000000000000036c9100000000000000000000000000000000000000000000000000000000000264c98000000000000000000000000000000000000000000000000000000000012c5dd100000000000000000000000000000000000000000000000000000000012c5980
  | 0, 3 => 0x93267f0000000000000000000000000000000000000000000000000000000000930459000000000000000000000000000000000000000000000000000000000093488800000000000000000000000000000000000000000000000000000000009300080000000000000000000000000000000000000000000000000000000000802604000000000000000000000000000000000000000000000000000000000012247300000000000000000000000000000000000000000000000000000000001020620000000000000000000000000000000000000000000000000000000000100000
  | 0, 4 => 0x12e5dd10000000000000000000000000000000000000000000000000000000001085c80000000000000000000000000000000000000000000000000000000000108100000000000000000000000000000000000000000000000000000000000002449c00000000000000000000000000000000000000000000000000000000002d1a62e00000000000000000000000000000000000000000000000000000000019b367f0000000000000000000000000000000000000000000000000000000000b7277f0000000000000000000000000000000000000000000000000000000000936eff
  | 0, 5 => 0x2748100000000000000000000000000000000000000000000000000000000000240e8800000000000000000000000000000000000000000000000000000000001bf7fff0000000000000000000000000000000000000000000000000000000001bf5dd90000000000000000000000000000000000000000000000000000000001ae7fd500000000000000000000000000000000000000000000000000000000019b367f0000000000000000000000000000000000000000000000000000000001887e8400000000000000000000000000000000000000000000000000000000036eddd1
  | 0, 6 => 0x276edf300000000000000000000000000000000000000000000000000000000037cf9e2000000000000000000000000000000000000000000000000000000000277e9fb000000000000000000000000000000000000000000000000000000000274eff7000000000000000000000000000000000000000000000000000000000274e9e2000000000000000000000000000000000000000000000000000000000274c9c0000000000000000000000000000000000000000000000000000000000274a1620000000000000000000000000000000000000000000000000000000002748715
  | 0, 7 => 0x3c8fec40000000000000000000000000000000000000000000000000000000003cbfe9d0000000000000000000000000000000000000000000000000000000003c8fe840000000000000000000000000000000000000000000000000000000003c8fe8400000000000000000000000000000000000000000000000000000000037efdf30000000000000000000000000000000000000000000000000000000002f7efff0000000000000000000000000000000000000000000000000000000002f7e9ea0000000000000000000000000000000000000000000000000000000002f7a77f
  | 0, 8 => 0x3fcffe60000000000000000000000000000000000000000000000000000000003eeffd50000000000000000000000000000000000000000000000000000000003eeddd10000000000000000000000000000000000000000000000000000000003ecff840000000000000000000000000000000000000000000000000000000003dbfeff0000000000000000000000000000000000000000000000000000000003dbfe8c0000000000000000000000000000000000000000000000000000000003dbb67f0000000000000000000000000000000000000000000000000000000003dafef7
  | 0, 9 => 0x3fffdfb0000000000000000000000000000000000000000000000000000000003fff9ea0000000000000000000000000000000000000000000000000000000003ffddd90000000000000000000000000000000000000000000000000000000003ffb77f0000000000000000000000000000000000000000000000000000000003ffb70c0000000000000000000000000000000000000000000000000000000003ff95590000000000000000000000000000000000000000000000000000000003ff91080000000000000000000000000000000000000000000000000000000003ffffff
  | 0, 10 => 0x3ffff8c
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 81 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 81 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 81 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 81 then wireAt i else 0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_31 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_31 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
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
private theorem z4_0 : ∀ i, 0 ≤ i → i < 6 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 6 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_16 : ∀ i, 16 ≤ i → i < 32 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_32 : ∀ i, 32 ≤ i → i < 37 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 5 32 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 37 → Z 5 i = true := (range_split (range_split z5_0 z5_16) z5_32)
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
private theorem z6_48 : ∀ i, 48 ≤ i → i < 61 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 13 48 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 61 → Z 6 i = true := (range_split (range_split z6_0 z6_16) (range_split z6_32 z6_48))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 9 0 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 9 → Z 7 i = true := z7_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_0 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := z8_0
theorem checked (s : Nat) (hs : s ≤ 8) : ∀ i < NN s, Z s i = true := by
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
def RootG (s : Nat) : Bool :=
  scr dom_31 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD dom_31 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_31 roots_31 goal_31 9 := by
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

theorem low_31 : Lower dom_31 roots_31 goal_31 9 := S_31.noCircuit

namespace S_47
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 9), (1, 33), (2, 3), (4, 5), (6, 7), (6, 14), (8, 9), (10, 11), (10, 14), (10, 42), (12, 13), (12, 14), (12, 44), (32, 33), (34, 35), (34, 42), (36, 37), (36, 44), (38, 39), (38, 46), (40, 41), (40, 42), (40, 44)]
def r1sG : List Nat := [1, 1, 1, 1, 2, 4, 6, 6, 8, 10, 10, 10, 12, 12, 12, 32, 34, 34, 36, 36, 38, 38, 40, 40, 40]
def r2sG : List Nat := [3, 5, 9, 33, 3, 5, 7, 14, 9, 11, 14, 42, 13, 14, 44, 33, 35, 42, 37, 44, 39, 46, 41, 42, 44]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [2203520468227, 6601533424389, 4402510170373, 6601566979331, 2203520469251, 10999613490435, 37388364155139, 8800489571081, 39587387541765, 6601533425923, 13198603191045, 13237106311950, 2203992072451, 13237763189262, 41807230601477, 2203419346179, 10999512826633, 11020903449870, 13219926704910, 44126511366954, 43985333256969, 13199041365257, 35188837581601, 8800961175817, 44135101302060, 44032023659820, 44023433724714, 43984930603809, 37387860837153]
def xsM : List Nat := roots_47.map (· &&& dom_47)
def goalM : Nat := goal_47 &&& dom_47
def NN : Nat → Nat
  | 4 => 20
  | 5 => 121
  | 6 => 144
  | 7 => 15
  | 8 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x987b90b88ce4fcb9814fbcef79bdac285d10716c5be8a5b44c3a26344af444df3cb0954f390a23dd335b89b9334691ea277152a91ea84e101c83c1f21c6c7945199307090f1fce070e5b99400a76c179
  | 5, 0 => 0x3da27f4b3615f46a35750a43312ceb8d2f051aa22c23c0eb2b9c38162b69386e2ac939b029157492290acf4c27b3f3112649714124e6a5912366326d2244a8d722084fc9214a53a520561c45203b9a0d1efc262f1d659a0a1d265e9b1c7a52a61b2929df19a1be7719732026188d164d188b6e561796f9df164310eb15d1737615bc7d7f13ba48f9135578761209bd7c11dd3ed2105b5265104151d3102c32d10f85ac1b0f72228e0f1fce070e2071120c91eeb00c8aedb30c7f030f0c3fc7a00bf4795b0afba44c0a9e6c7f07e6cd7f07a288700793099a0615cd6904b686ca0494f17f040f1dd303b7e65603b0c7d70335d81702ff9580029f811a024a8d64
  | 5, 1 => 0xf641318cea977c16a9b7a612a7e1de7ea0589da8a01962399a6df023936700228f0342038af0d27e870f2d887b1ce2dc76eb24fe728a38fd71f40ace718064866eb58df76d3ae60167a9cfd26761e80f661e9ba3657a2d9964f919d663cbc541623e466160208baa5c7cf6cc5c30efa35c303ab75ba073fa5b61388b59babd2959156e53577c4a3f54a4b84753d7f7b552a3c68251a1f9c5513157fc50316dca4ff2325b4ee0eb9e4d7ce16d4c57da304c3a26344b0627bf4a3628d0499101a64812e6be465b4bdf4648b87c45025d6642d0f68342c1d77f42829c10418738263de953c2
  | 6, 0 => 0x3546afb534e789673499db3e334313953147287e308db4e42fef2b282f733ea92d40a9f42c9d50862c21c6632acab2b2290acf4c28fea93e28f0a53928e44d2828bbd335289d02bc270c0712270b03de25a509332557ae112514d4b5244d30ad2261f78e21428e21200c7def1efeb8c61ce122ff1b2929df1b171b191a928cca19cb622218a26f791782a15e17108ead1694a22e1600589415d81e4815d0da491266a7c7125878620f6491320f1fce070f01d2a50e2c67630da784ce0c1f3c870b6e94320afba44c09d78a75072d757706e68d6606af409d05c6879905549da10548be780506640d040f1dd303b0c7d70366aa410335d817029f811a00d7f0ac
  | 6, 1 => 0xa8a13f45a7e1de7e9e1dee099d9588649a88cb9399f91dac9674c1938c98c6548c5e127287ccbffc7fed28667b1ce2dc772c77947445a6b5737f75f7734c6e6271f40ace70ae07ab6ea570046c4fd1666b3e4af76949f7d6693528fa66014baf6594bfe2640b49fc63f1beb46270a27b6241c31861dff08a5ba073fa5b670a3a5b61388b5a282ac159e8ef525915948255c13d2053d7f7b553d6c8e3535b9b955196082551635f9050d47de6506b5b5b4f8fff5f4d7877b94cb623674b5a61c14b22a4df4a21a9704a0593be4580630f42c1d77f42829c104279b1824214f7924036f8073f2d04c03ce2a0a538fbe1c436c7b2c0360accc53588d347354997d8
  | 6, 2 => 0xfde03eecfd12e37afb94c892f641318cdec4724ad89f7cf6c76e9974c6befed0c0871139bf32b01dba4126a8b91eb561b1d62a66af535e0eae8ffcf9ac1af8ec
  | 7, 0 => 0xf641318caf535e0e8c5e12727445a6b56949f7d66594bfe25ba073fa5b61388b55c13d204d7877b92fef2b28270b03de160058940f1fce070da784ce
  | 8, 0 => 0xf1fce07
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffff000000000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000aaaa0000000000000000000000000000000000000000000000000000000000005f5f00000000000000000000000000000000000000000000000000000000000055550000000000000000000000000000000000000000000000000000000000003f3f0000000000000000000000000000000000000000000000000000000000000f0f00000000000000000000000000000000000000000000000000000000000000ff
  | 0, 1 => 0xff0000ffff000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000f0000000f0000000000000000000000000000000000000000000000000000000aa000000aa0000000000000000000000000000000000000000000000000000005f0000005f00000000000000000000000000000000000000000000000000000055000000550000000000000000000000000000000000000000000000000000003300000033
  | 0, 2 => 0xf0a00000f0a00000000000000000000000000000000000000000000000000000f0000000f0000000000000000000000000000000000000000000000000000000c0c0000cccc00000000000000000000000000000000000000000000000000000c0c00000c0c0000000000000000000000000000000000000000000000000000050f0000050f00000000000000000000000000000000000000000000000000000505000005050000000000000000000000000000000000000000000000000000030300000f0f0000000000000000000000000000000000000000000000000000030300000303
  | 0, 3 => 0x33330000ffff000000000000000000000000000000000000000000000000000033330000cccc00000000000000000000000000000000000000000000000000003333000033330000000000000000000000000000000000000000000000000000333300000000000000000000000000000000000000000000000000000000000022220000222200000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000f0f00000000
  | 0, 4 => 0x555500005555000000000000000000000000000000000000000000000000000055000000ff000000000000000000000000000000000000000000000000000000550000005500000000000000000000000000000000000000000000000000000050500000505000000000000000000000000000000000000000000000000000004c4c00004c4c000000000000000000000000000000000000000000000000000044cc000044cc00000000000000000000000000000000000000000000000000004444000044440000000000000000000000000000000000000000000000000000337700003377
  | 0, 5 => 0x99990000999900000000000000000000000000000000000000000000000000008f8f00008f8f0000000000000000000000000000000000000000000000000000888800008888000000000000000000000000000000000000000000000000000080800000808000000000000000000000000000000000000000000000000000005f5f00005f5f000000000000000000000000000000000000000000000000000055ff000055ff000000000000000000000000000000000000000000000000000055aa000055aa000000000000000000000000000000000000000000000000000055550000aaaa
  | 0, 6 => 0xaaaa0000a0a00000000000000000000000000000000000000000000000000000aaaa000000000000000000000000000000000000000000000000000000000000aaa00000aaa00000000000000000000000000000000000000000000000000000aa550000aa550000000000000000000000000000000000000000000000000000aa000000aa000000000000000000000000000000000000000000000000000000aa00000000000000000000000000000000000000000000000000000000000000a8a80000a8a80000000000000000000000000000000000000000000000000000a0a00000a0a0
  | 0, 7 => 0xc0000000c0000000000000000000000000000000000000000000000000000000bbbb0000bbbb0000000000000000000000000000000000000000000000000000bb330000bb330000000000000000000000000000000000000000000000000000afaf0000afaf0000000000000000000000000000000000000000000000000000aaff0000aaff0000000000000000000000000000000000000000000000000000aaff000000ff0000000000000000000000000000000000000000000000000000aaaa0000aaaa0000000000000000000000000000000000000000000000000000aaaa0000aa00
  | 0, 8 => 0xcccc0000cc000000000000000000000000000000000000000000000000000000cccc000033330000000000000000000000000000000000000000000000000000cccc000000000000000000000000000000000000000000000000000000000000cc880000cc880000000000000000000000000000000000000000000000000000cc000000cccc0000000000000000000000000000000000000000000000000000cc000000cc000000000000000000000000000000000000000000000000000000c0c00000c0c00000000000000000000000000000000000000000000000000000c0c000000000
  | 0, 9 => 0xeecc0000eecc0000000000000000000000000000000000000000000000000000eecc0000cccc0000000000000000000000000000000000000000000000000000eeaa0000eeaa0000000000000000000000000000000000000000000000000000ecec0000ecec0000000000000000000000000000000000000000000000000000e0e00000e0e00000000000000000000000000000000000000000000000000000dddd0000dddd0000000000000000000000000000000000000000000000000000ccdd0000ccdd0000000000000000000000000000000000000000000000000000cccc0000cccc
  | 0, 10 => 0xf0a00000f0a00000000000000000000000000000000000000000000000000000f00f0000f00f0000000000000000000000000000000000000000000000000000f0000000f0000000000000000000000000000000000000000000000000000000f000000000000000000000000000000000000000000000000000000000000000eeee0000eeee0000000000000000000000000000000000000000000000000000eeee0000cccc0000000000000000000000000000000000000000000000000000eeee0000aaaa0000000000000000000000000000000000000000000000000000eeee00000000
  | 0, 11 => 0xf3f30000f3f30000000000000000000000000000000000000000000000000000f3f3000033330000000000000000000000000000000000000000000000000000f0ff0000f0ff0000000000000000000000000000000000000000000000000000f0f00000ffff0000000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000f0f00000e0e00000000000000000000000000000000000000000000000000000f0f00000c0c00000000000000000000000000000000000000000000000000000f0f000000000
  | 0, 12 => 0xfafa0000fafa0000000000000000000000000000000000000000000000000000fafa0000f8f80000000000000000000000000000000000000000000000000000fafa0000f0f00000000000000000000000000000000000000000000000000000faf00000faf00000000000000000000000000000000000000000000000000000faaa0000aaaa0000000000000000000000000000000000000000000000000000fa000000fa000000000000000000000000000000000000000000000000000000f8f80000f8f80000000000000000000000000000000000000000000000000000f5f50000f5f5
  | 0, 13 => 0xff000000f0000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000fefe0000fefe0000000000000000000000000000000000000000000000000000fcfc0000fcfc0000000000000000000000000000000000000000000000000000fcfc0000f8f80000000000000000000000000000000000000000000000000000fcfc0000f0f00000000000000000000000000000000000000000000000000000fcfc0000cccc0000000000000000000000000000000000000000000000000000fccc0000cccc
  | 0, 14 => 0xff880000ff880000000000000000000000000000000000000000000000000000ff880000ff000000000000000000000000000000000000000000000000000000ff550000ff550000000000000000000000000000000000000000000000000000ff330000ff330000000000000000000000000000000000000000000000000000ff0f0000ff0f0000000000000000000000000000000000000000000000000000ff0f000000000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000ff000000fa00
  | 0, 15 => 0xffcc0000ffcc0000000000000000000000000000000000000000000000000000ffcc0000cccc0000000000000000000000000000000000000000000000000000ffaa0000ffaa0000000000000000000000000000000000000000000000000000ffaa0000ffa00000000000000000000000000000000000000000000000000000ffaa0000ff000000000000000000000000000000000000000000000000000000ffaa0000aaaa0000000000000000000000000000000000000000000000000000ffaa000000000000000000000000000000000000000000000000000000000000ffa00000ffa0
  | 1, 0 => 0xffff000055550000000000000000000000000000000000000000000000000000ffff000033330000000000000000000000000000000000000000000000000000ffff000000cc0000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000fffa0000fffa0000000000000000000000000000000000000000000000000000fff00000fff00000000000000000000000000000000000000000000000000000fff00000ff000000000000000000000000000000000000000000000000000000ffee00000000
  | 1, 1 => 0xffff0000c0c00000000000000000000000000000000000000000000000000000ffff0000c0000000000000000000000000000000000000000000000000000000ffff0000aaaa0000000000000000000000000000000000000000000000000000ffff0000aa880000000000000000000000000000000000000000000000000000ffff0000aa000000000000000000000000000000000000000000000000000000ffff0000a0a00000000000000000000000000000000000000000000000000000ffff000088880000000000000000000000000000000000000000000000000000ffff00008080
  | 1, 2 => 0xffff0000fff00000000000000000000000000000000000000000000000000000ffff0000ff000000000000000000000000000000000000000000000000000000ffff0000fcfc0000000000000000000000000000000000000000000000000000ffff0000f0f00000000000000000000000000000000000000000000000000000ffff0000cccc0000000000000000000000000000000000000000000000000000ffff0000c8c8
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x845b4829400716c390240091716a39400715b482840084715b2f40090716c39400916a390e400715b463940092716839400845648394008a7867484008f71391040092716348484715b4839500847d644f4008448391a4
  | 4, 0, 1 => 0x91716a27400845b4834400715b391e4007a715b524
  | 5, 0, 0 => 0x8d716548365847d5b48335845d48390c5845b483b0b5847148392e5846a48390e58a715b391d584785b4c395715b532d07579715b4839584716648395946e5b4839584716148395847348391658f715b483955b391d0e075
  | 5, 0, 1 => 0x8b7164483958c715b48395947a5b4839584826248395847167482b584715b4339586715b391c5846448390e5895b48390e59271695839584715b483958471674831584716c4b39584715b3e1b584714c3919584715b4c275
  | 5, 0, 2 => 0x84775b533958471271d19584715b4e39584715b4a21584775b443958471443919584715b4427589716148395715b391d075715b483904591716a48395847157443958471674835584765b4839584715b3922584716c41275
  | 5, 0, 3 => 0x8f84716c39571695b390758e715b483958471635b48592715448395855b48390e584714839175715b4f3907584715b3d395847d5b48355847164483958d7b5b48365845b4839265847d644833584714830125845b4239085
  | 5, 0, 4 => 0x8f715b4827584715a48395927159483950091716a39484716b48395845b48390a58b7d5b483958b715b4827584715b3923588715b4839585715b48395845b4833095844839190e5845b48270e5945b48390f5845748390e5
  | 5, 0, 5 => 0x8471483911584715b39155716c4139075716e5b523958471483919584715b4827580715b48395845b532d0e5847d483319584705b4839584785b48395847d574833584785548395845b483a395946e4839195946e5b48275
  | 5, 0, 6 => 0x84715b392059291716c3959271584839591715b5139584715b4d2d584715b532d5847d5b482a584715e5b3958d715b5239571391d1907584715b49395727148391958471483913571584839015847c5b48395925848390e5
  | 5, 0, 7 => 0x845b48390e584755b4825584774839195847148271958478483919584785b4827591715b391f5847f5b44395844827190e5
  | 6, 0, 0 => 0x845d5b48390e60000847d5b4833592847f715b483970084715b5048396007d715b4839076008474715b391d60084715b39361d6008475715b48396008984715b4839600715b484239076000079715b483950000946e5b483950084715b482719600008471614839500008f715b483950084715f5b391d6
  | 6, 0, 1 => 0x84715b48390160084715b392d1d60084715b483f3960092845b48390e600845b48390e0d60084716e5b483960084715b48392a60084715b48390560084715b4847396008473715b483960084716c5b391d6000084715b483950091716e5b48396008d845b48390e60084715b48390e60084715b58391d6
  | 6, 0, 2 => 0x84715b39331d600716c5b4839076008471695b58396008d84715b4839600847a715b4839600715b5848390760084716c5b413960084715d5b4839600847d715b48336008471675b391d600918d715b48396008a715b4839306008483715b483960000715b391d0750094716e5b483960084715b53391d6
  | 6, 0, 3 => 0x84715b42392d600847f5b484239600845b4839270e60084715b3e391d6009184715b482760084715b391d196009284715b483960084715b48390d6008784715b482760084715b483932600948d715b48396008471625b48396000084716448395008471483919186009291715b483960084715c5b48396
  | 6, 0, 4 => 0x84715b51483960084715b48272560084715b48393760084716d5b483960000844839190e50000845b48270e5008481715b483960084715b482721600845b48390e0b60084715b53482d600845b48391d0e60084715b4f3933600847f7d5b4839600847d715b4439600847f71483919600847f715b48276
  | 6, 0, 5 => 0x84715b482750084714839190e60084715b48270e60084715b48390b60084715b48391d6000084785b483950084715b48390f60084715b4840396008475715b482760084715b4839146009584715b483960084825b48390e600845b5548390e60084715b483927600845b4845390e60084715b4839066
  | 6, 0, 6 => 0x84715b532d5008471695b483960084715b48391f60084716f5b48396008478715b48396008482715b483960084715b48390060084715b4f483960084715b48453960084715b53392d60084715b594839600847f715b391d60084716e5b482760084715b48392c600008471483919500847d5b48390e6
  | 6, 0, 7 => 0x716e5b48390760000847148271950084715b48443960084715b48392460084715b391d1b600847148392719600845b4839330e6008471605b483960084715b48393660084715b48393860084715b483c39600009271584839500847e715b4839600847d715b4839600845b4839360e6008d84715b48276
  | 6, 0, 8 => 0x84715b483925600847d5b48393360084715b48332760000845b48390e500847b5b48393660084715b48362760084715b483b3960084715b48392b600847d715b48276008471483919166009384715b483960084715b48390360084715b48452760084715b483933600845b483b390e60084715b4839096
  | 7, 0, 0 => 0x845b48390e584715b483933684715b4839366847d715b483968482715b4839684715b484539600847148391950084715b4827584715b48391d684715b48392769284715b483968d84715b4839684716e5b483960084715b4839584715b48390e6
  | 8, 0, 0 => 0x84715b48395
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 44
  | 5 => 44
  | 6 => 60
  | 7 => 52
  | 8 => 44
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 8 0) :: stateWires n (ids >>> 8)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x7fff0000000000000000000000000000000000000000000000000000000000007f00000000000000000000000000000000000000000000000000000000000000000f0000000000000000000000000000000000000000000000000000000000007fff0000000000000000000000000000000000000000000000000000000000007ff00000000000000000000000000000000000000000000000000000000000007f3f0000000000000000000000000000000000000000000000000000000000000f1f00000000000000000000000000000000000000000000000000000000000000ff
  | 0, 1 => 0x3fffff00000000000000000000000000000000000000000000000000000000003f80ff00000000000000000000000000000000000000000000000000000000003f800000000000000000000000000000000000000000000000000000000000003c00e0000000000000000000000000000000000000000000000000000000000000000f00000000000000000000000000000000000000000000000000000000003f80ff00000000000000000000000000000000000000000000000000000000003f80f000000000000000000000000000000000000000000000000000000000000c802f
  | 0, 2 => 0x1c00f0f0000000000000000000000000000000000000000000000000000000001c00f000000000000000000000000000000000000000000000000000000000000030ed00000000000000000000000000000000000000000000000000000000000030e100000000000000000000000000000000000000000000000000000000001c38f1f0000000000000000000000000000000000000000000000000000000001c38f100000000000000000000000000000000000000000000000000000000001c08f1f0000000000000000000000000000000000000000000000000000000001c0810f
  | 0, 3 => 0x1ccffff0000000000000000000000000000000000000000000000000000000001cc8ed00000000000000000000000000000000000000000000000000000000001ccf12f0000000000000000000000000000000000000000000000000000000001cc8000000000000000000000000000000000000000000000000000000000000000000f0000000000000000000000000000000000000000000000000000000001fc0fe00000000000000000000000000000000000000000000000000000000001c38f1f0000000000000000000000000000000000000000000000000000000001c38000
  | 0, 4 => 0x1fffff00000000000000000000000000000000000000000000000000000000001c07f000000000000000000000000000000000000000000000000000000000001c07f0000000000000000000000000000000000000000000000000000000000003c70e00000000000000000000000000000000000000000000000000000000000330ed00000000000000000000000000000000000000000000000000000000000330ed00000000000000000000000000000000000000000000000000000000000330ed00000000000000000000000000000000000000000000000000000000001fff1ff
  | 0, 5 => 0x1ccf1200000000000000000000000000000000000000000000000000000000001c38f1f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001ffffff0000000000000000000000000000000000000000000000000000000001ffffff0000000000000000000000000000000000000000000000000000000001c07f0f0000000000000000000000000000000000000000000000000000000001ff800f
  | 0, 6 => 0x3f80f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 0, 7 => 0x1ccf12f0000000000000000000000000000000000000000000000000000000001ccf12f0000000000000000000000000000000000000000000000000000000001c38f1f00000000000000000000000000000000000000000000000000000000003f80ff00000000000000000000000000000000000000000000000000000000003f80ff000000000000000000000000000000000000000000000000000000000000000f0000000000000000000000000000000000000000000000000000000000000000
  | 0, 8 => 0x330e00000000000000000000000000000000000000000000000000000000000033712f00000000000000000000000000000000000000000000000000000000003300000000000000000000000000000000000000000000000000000000000000000e000000000000000000000000000000000000000000000000000000000000000ed00000000000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000000003000c00000000000000000000000000000000000000000000000000000000000300000
  | 0, 9 => 0x330ed00000000000000000000000000000000000000000000000000000000000330ed00000000000000000000000000000000000000000000000000000000000000e0f0000000000000000000000000000000000000000000000000000000000330ed000000000000000000000000000000000000000000000000000000000003000c00000000000000000000000000000000000000000000000000000000001fffff000000000000000000000000000000000000000000000000000000000003f8ef00000000000000000000000000000000000000000000000000000000000330ed0
  | 0, 10 => 0x7000000000000000000000000000000000000000000000000000000000000003f01f000000000000000000000000000000000000000000000000000000000000700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000330edf0000000000000000000000000000000000000000000000000000000000330ed0000000000000000000000000000000000000000000000000000000000033000f0000000000000000000000000000000000000000000000000000000000330000
  | 0, 11 => 0x1fcf1ef0000000000000000000000000000000000000000000000000000000001fcf12f00000000000000000000000000000000000000000000000000000000003ff0ff00000000000000000000000000000000000000000000000000000000003c7fff00000000000000000000000000000000000000000000000000000000003c70e000000000000000000000000000000000000000000000000000000000003c00c000000000000000000000000000000000000000000000000000000000003c00c000000000000000000000000000000000000000000000000000000000003c0000
  | 0, 12 => 0x3c70ef00000000000000000000000000000000000000000000000000000000003c70e000000000000000000000000000000000000000000000000000000000003c70e000000000000000000000000000000000000000000000000000000000003c70e0000000000000000000000000000000000000000000000000000000000000000f000000000000000000000000000000000000000000000000000000000000700000000000000000000000000000000000000000000000000000000000003c70e00000000000000000000000000000000000000000000000000000000001fffff0
  | 0, 13 => 0x1c070000000000000000000000000000000000000000000000000000000000001c0000000000000000000000000000000000000000000000000000000000000003f7eff00000000000000000000000000000000000000000000000000000000003f7ef000000000000000000000000000000000000000000000000000000000003f70e000000000000000000000000000000000000000000000000000000000003f70e000000000000000000000000000000000000000000000000000000000003f0ed00000000000000000000000000000000000000000000000000000000000330ed0
  | 0, 14 => 0x1c07f000000000000000000000000000000000000000000000000000000000001c07f000000000000000000000000000000000000000000000000000000000001fffff00000000000000000000000000000000000000000000000000000000001ccff2f0000000000000000000000000000000000000000000000000000000001c3ff1f0000000000000000000000000000000000000000000000000000000001c380000000000000000000000000000000000000000000000000000000000001c07f000000000000000000000000000000000000000000000000000000000001c07000
  | 0, 15 => 0x1f37fd00000000000000000000000000000000000000000000000000000000001f30ed00000000000000000000000000000000000000000000000000000000001c07f0f0000000000000000000000000000000000000000000000000000000001c07f000000000000000000000000000000000000000000000000000000000001c07f000000000000000000000000000000000000000000000000000000000001c0000f0000000000000000000000000000000000000000000000000000000001c000000000000000000000000000000000000000000000000000000000000001c07f00
  | 1, 0 => 0x1fffff00000000000000000000000000000000000000000000000000000000001fff12f0000000000000000000000000000000000000000000000000000000001ff80d00000000000000000000000000000000000000000000000000000000001ff80000000000000000000000000000000000000000000000000000000000001fc7fef0000000000000000000000000000000000000000000000000000000001fc7fe00000000000000000000000000000000000000000000000000000000001fc7f000000000000000000000000000000000000000000000000000000000001f30000
  | 1, 1 => 0x1ff80c00000000000000000000000000000000000000000000000000000000001ff80000000000000000000000000000000000000000000000000000000000001ff800f0000000000000000000000000000000000000000000000000000000001ff80000000000000000000000000000000000000000000000000000000000001ff80000000000000000000000000000000000000000000000000000000000001ff80000000000000000000000000000000000000000000000000000000000001ff80000000000000000000000000000000000000000000000000000000000001ff8000
  | 1, 2 => 0x1ffffe00000000000000000000000000000000000000000000000000000000001ffff000000000000000000000000000000000000000000000000000000000001fffef00000000000000000000000000000000000000000000000000000000001fff0e00000000000000000000000000000000000000000000000000000000001ff8ed00000000000000000000000000000000000000000000000000000000001ff80c0
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x37f70000000000000000000000000000000000000000000000000000000000003784000000000000000000000000000000000000000000000000000000000000137700000000000000000000000000000000000000000000000000000000000027950000000000000000000000000000000000000000000000000000000000002480000000000000000000000000000000000000000000000000000000000000133700000000000000000000000000000000000000000000000000000000000003150000000000000000000000000000000000000000000000000000000000000073
  | 0, 1 => 0x15b7ff000000000000000000000000000000000000000000000000000000000015807b00000000000000000000000000000000000000000000000000000000001580080000000000000000000000000000000000000000000000000000000000140062000000000000000000000000000000000000000000000000000000000015807b00000000000000000000000000000000000000000000000000000000000180190000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004802a
  | 0, 2 => 0xc38b1d0000000000000000000000000000000000000000000000000000000000c20b040000000000000000000000000000000000000000000000000000000000832ed10000000000000000000000000000000000000000000000000000000000830a1100000000000000000000000000000000000000000000000000000000008388190000000000000000000000000000000000000000000000000000000000820800000000000000000000000000000000000000000000000000000000000040831d000000000000000000000000000000000000000000000000000000000040810c
  | 0, 3 => 0x14cf7ff00000000000000000000000000000000000000000000000000000000014ce6d900000000000000000000000000000000000000000000000000000000014cd12e00000000000000000000000000000000000000000000000000000000014cc008000000000000000000000000000000000000000000000000000000000044912e0000000000000000000000000000000000000000000000000000000000d60b660000000000000000000000000000000000000000000000000000000000c38b1d0000000000000000000000000000000000000000000000000000000000c38808
  | 0, 4 => 0x1aa6c800000000000000000000000000000000000000000000000000000000001aa7f840000000000000000000000000000000000000000000000000000000001aa6c8000000000000000000000000000000000000000000000000000000000012864800000000000000000000000000000000000000000000000000000000000a32e910000000000000000000000000000000000000000000000000000000000b32cd10000000000000000000000000000000000000000000000000000000000a22c8000000000000000000000000000000000000000000000000000000000014cd12e
  | 0, 5 => 0x11942510000000000000000000000000000000000000000000000000000000000d38b5d000000000000000000000000000000000000000000000000000000000011025100000000000000000000000000000000000000000000000000000000001000400000000000000000000000000000000000000000000000000000000001ebef9d0000000000000000000000000000000000000000000000000000000001bfecfb0000000000000000000000000000000000000000000000000000000001bfecfb0000000000000000000000000000000000000000000000000000000001aa5b77
  | 0, 6 => 0x55906a0000000000000000000000000000000000000000000000000000000000558008000000000000000000000000000000000000000000000000000000000054136600000000000000000000000000000000000000000000000000000000004013040000000000000000000000000000000000000000000000000000000000401304000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000001512730000000000000000000000000000000000000000000000000000000000141062
  | 0, 7 => 0x20248000000000000000000000000000000000000000000000000000000000015dd37f00000000000000000000000000000000000000000000000000000000014cd32e0000000000000000000000000000000000000000000000000000000000d79b7f000000000000000000000000000000000000000000000000000000000055937f000000000000000000000000000000000000000000000000000000000055807b000000000000000000000000000000000000000000000000000000000055937f000000000000000000000000000000000000000000000000000000000055930c
  | 0, 8 => 0xb32e800000000000000000000000000000000000000000000000000000000000b319260000000000000000000000000000000000000000000000000000000000b308000000000000000000000000000000000000000000000000000000000000b32ed10000000000000000000000000000000000000000000000000000000000a22ed10000000000000000000000000000000000000000000000000000000000a22e8000000000000000000000000000000000000000000000000000000000003024c00000000000000000000000000000000000000000000000000000000000300000
  | 0, 9 => 0xf33fd50000000000000000000000000000000000000000000000000000000000f32ed10000000000000000000000000000000000000000000000000000000000f7bfff0000000000000000000000000000000000000000000000000000000000b73ef300000000000000000000000000000000000000000000000000000000003434e20000000000000000000000000000000000000000000000000000000001bb6ed10000000000000000000000000000000000000000000000000000000000b32ed10000000000000000000000000000000000000000000000000000000000b32ed1
  | 0, 10 => 0x13c74e2000000000000000000000000000000000000000000000000000000000129f499000000000000000000000000000000000000000000000000000000000128748000000000000000000000000000000000000000000000000000000000012840000000000000000000000000000000000000000000000000000000000000f7bfff0000000000000000000000000000000000000000000000000000000000f7aed90000000000000000000000000000000000000000000000000000000000f79b7f0000000000000000000000000000000000000000000000000000000000f78808
  | 0, 11 => 0x17cf5ee00000000000000000000000000000000000000000000000000000000017cd12e00000000000000000000000000000000000000000000000000000000013df4fb00000000000000000000000000000000000000000000000000000000013c77f700000000000000000000000000000000000000000000000000000000013c74e200000000000000000000000000000000000000000000000000000000013c74e200000000000000000000000000000000000000000000000000000000013c64c000000000000000000000000000000000000000000000000000000000013c4000
  | 0, 12 => 0x17df7ff00000000000000000000000000000000000000000000000000000000017df6fb00000000000000000000000000000000000000000000000000000000017df4ea00000000000000000000000000000000000000000000000000000000017c77e600000000000000000000000000000000000000000000000000000000017dd37f000000000000000000000000000000000000000000000000000000000168778400000000000000000000000000000000000000000000000000000000013d76f30000000000000000000000000000000000000000000000000000000001be7ce2
  | 0, 13 => 0x1ea7c800000000000000000000000000000000000000000000000000000000001ea48000000000000000000000000000000000000000000000000000000000001ffffff0000000000000000000000000000000000000000000000000000000001bf7ef30000000000000000000000000000000000000000000000000000000001bf7ef30000000000000000000000000000000000000000000000000000000001bf7ce20000000000000000000000000000000000000000000000000000000001bf6ed10000000000000000000000000000000000000000000000000000000001bb6ed1
  | 0, 14 => 0x1fb7fd50000000000000000000000000000000000000000000000000000000001fb7f840000000000000000000000000000000000000000000000000000000001ea7f840000000000000000000000000000000000000000000000000000000001eeffae0000000000000000000000000000000000000000000000000000000001ebff9d0000000000000000000000000000000000000000000000000000000001ebc8080000000000000000000000000000000000000000000000000000000001ea7f840000000000000000000000000000000000000000000000000000000001ea7f84
  | 0, 15 => 0x1fb7fd50000000000000000000000000000000000000000000000000000000001fb6ed10000000000000000000000000000000000000000000000000000000001ffffff0000000000000000000000000000000000000000000000000000000001ffffee0000000000000000000000000000000000000000000000000000000001ffff8c0000000000000000000000000000000000000000000000000000000001ffdb7f0000000000000000000000000000000000000000000000000000000001ffc8080000000000000000000000000000000000000000000000000000000001fe7fe6
  | 1, 0 => 0x1ffec880000000000000000000000000000000000000000000000000000000001ffd92e0000000000000000000000000000000000000000000000000000000001ffc8590000000000000000000000000000000000000000000000000000000001ffc8080000000000000000000000000000000000000000000000000000000001ffffff0000000000000000000000000000000000000000000000000000000001fe7fe60000000000000000000000000000000000000000000000000000000001fe7f840000000000000000000000000000000000000000000000000000000001ffc808
  | 1, 1 => 0x1ffecc80000000000000000000000000000000000000000000000000000000001ffec880000000000000000000000000000000000000000000000000000000001ffdb7f0000000000000000000000000000000000000000000000000000000001ffdb5d0000000000000000000000000000000000000000000000000000000001ffdb0c0000000000000000000000000000000000000000000000000000000001ffd86a0000000000000000000000000000000000000000000000000000000001ffca590000000000000000000000000000000000000000000000000000000001ffc848
  | 1, 2 => 0x1ffffee0000000000000000000000000000000000000000000000000000000001ffff8c0000000000000000000000000000000000000000000000000000000001fffefb0000000000000000000000000000000000000000000000000000000001fffcea0000000000000000000000000000000000000000000000000000000001ffeed90000000000000000000000000000000000000000000000000000000001ffeed9
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 150 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 150 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 150 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 150 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 8 0) :: stateWiresD n (ids >>> 8)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 8 0) :: stateWiresS n (ids >>> 8)
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 9 0 (NN s)
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_47 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_47 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_47 == dom_47) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_47 goalM u ys) : RunD dom_47 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_47 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 16 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_16 : ∀ i, 16 ≤ i → i < 20 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 4 16 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 20 → Z 4 i = true := (range_split z4_0 z4_16)
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
private theorem z5_48 : ∀ i, 48 ≤ i → i < 64 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_64 : ∀ i, 64 ≤ i → i < 80 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_80 : ∀ i, 80 ≤ i → i < 96 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_96 : ∀ i, 96 ≤ i → i < 112 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_112 : ∀ i, 112 ≤ i → i < 121 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 9 112 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 121 → Z 5 i = true := (range_split (range_split (range_split z5_0 z5_16) (range_split z5_32 z5_48)) (range_split (range_split z5_64 z5_80) (range_split z5_96 z5_112)))
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
private theorem z6 : ∀ i, 0 ≤ i → i < 144 → Z 6 i = true := (range_split (range_split (range_split (range_split z6_0 z6_16) (range_split z6_32 z6_48)) (range_split (range_split z6_64 z6_80) (range_split z6_96 z6_112))) z6_128)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : ∀ i, 0 ≤ i → i < 15 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 15 0 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 15 → Z 7 i = true := z7_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_0 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := z8_0
theorem checked (s : Nat) (hs : s ≤ 8) : ∀ i < NN s, Z s i = true := by
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
def RootG (s : Nat) : Bool :=
  scr dom_47 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD dom_47 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_47 roots_47 goal_47 9 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_47 goal_47 := by
    have h0 : isConstB dom_47 goal_47 = false := by decide +kernel
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

end S_47

theorem low_47 : Lower dom_47 roots_47 goal_47 9 := S_47.noCircuit

namespace S_62
def pairsG : List (Nat × Nat) := [(6, 14), (6, 22), (10, 14), (10, 26), (10, 42), (12, 14), (12, 28), (12, 44), (18, 22), (18, 26), (18, 50), (20, 22), (20, 28), (20, 52), (24, 26), (24, 28), (34, 42), (34, 50), (36, 44), (36, 52), (38, 46), (38, 54), (40, 42), (40, 44), (48, 50), (48, 52), (56, 58), (56, 60)]
def r1sG : List Nat := [6, 6, 10, 10, 10, 12, 12, 12, 18, 18, 18, 20, 20, 20, 24, 24, 34, 34, 36, 36, 38, 38, 40, 40, 48, 48, 56, 56]
def r2sG : List Nat := [14, 22, 14, 26, 42, 14, 28, 44, 22, 26, 50, 22, 28, 52, 26, 28, 42, 50, 44, 52, 46, 54, 42, 44, 50, 52, 58, 60]
def mpG : Nat := 0xfffffff
def pool6G : List Nat := [11021189781006, 19834261081626, 19817148583446, 13220246722062, 22016205524502, 13237493701134, 19834766371866, 26431431904794, 22041874271772, 22067946461718, 13237763189262, 22068350693910]
def xsM : List Nat := roots_62.map (· &&& dom_62)
def goalM : Nat := goal_62 &&& dom_62
def NN : Nat → Nat
  | 4 => 3
  | 5 => 13
  | 6 => 11
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xa91103de6bf7855d62e395be
  | 5, 0 => 0xe324ca91d3b5bfdea91103de9dd0d40c79e89eaa58d74d1347ccf1b4449cb7de3acfbbbf22b0e5b51901fc09174662b60ebf8666
  | 6, 0 => 0xe324ca91cd5dd687a91103de9352573f276abb79247a69281b12df040fe7d2510ebf866605cc22e2058f0e8d
  | 7, 0 => 0xa91103de
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x44444444000000000000000000000000000000000000000000000000000000004444440044444400000000000000000000000000000000000000000000000000440044004400440000000000000000000000000000000000000000000000000011111111111111110000000000000000000000000000000000000000000000000505050505050505000000000000000000000000000000000000000000000000005500550055005500000000000000000000000000000000000000000000000000005555000055550000000000000000000000000000000000000000000000000000000055555555
  | 0, 1 => 0x55445544554455440000000000000000000000000000000000000000000000005500550055005500000000000000000000000000000000000000000000000000550000005500000000000000000000000000000000000000000000000000000054545454505050500000000000000000000000000000000000000000000000005454545444444444000000000000000000000000000000000000000000000000505050505050505000000000000000000000000000000000000000000000000050005000500050000000000000000000000000000000000000000000000000004444444444444444
  | 0, 2 => 0x55555555550000000000000000000000000000000000000000000000000000005555555544444444000000000000000000000000000000000000000000000000555555550000000000000000000000000000000000000000000000000000000055555500555555000000000000000000000000000000000000000000000000005555550000000000000000000000000000000000000000000000000000000000555550505555505000000000000000000000000000000000000000000000000055550000555500000000000000000000000000000000000000000000000000005555000000000000
  | 0, 3 => 0x5555555555550000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x562e521417a29080b45cc4
  | 5, 0, 0 => 0x11729005ad1aa42d62e5216f17290b58b9465ac5ea2ace2e5216ae5102b58b96a5b45ca3ac5ca2016aa4082b5729015
  | 6, 0, 0 => 0x11729005ac5ca4018158b9485ac5ca4a1ab48b9486c562e521ab28b9486ac5ca40d815729015ac60e521ab1735486
  | 7, 0, 0 => 0x158b9485
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 29
  | 5 => 29
  | 6 => 34
  | 7 => 29
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 5 0) :: stateWires n (ids >>> 5)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x330000000000000000000000000000000000000000000000000000000000000000071c000000000000000000000000000000000000000000000000000000000000001c000000000000000000000000000000000000000000000000000000000fccf8e0000000000000000000000000000000000000000000000000000000000fc3c71c00000000000000000000000000000000000000000000000000000000033f3f030000000000000000000000000000000000000000000000000000000000ff00ff000000000000000000000000000000000000000000000000000000000000ffff
  | 0, 1 => 0xcf3c7ff000000000000000000000000000000000000000000000000000000000cc0c0fc000000000000000000000000000000000000000000000000000000000c00c00000000000000000000000000000000000000000000000000000000000003f38e300000000000000000000000000000000000000000000000000000000003f071f00000000000000000000000000000000000000000000000000000000003c38e300000000000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000000033071f
  | 0, 2 => 0xfffc000000000000000000000000000000000000000000000000000000000000fff071f000000000000000000000000000000000000000000000000000000000fff0000000000000000000000000000000000000000000000000000000000000fc0fffc000000000000000000000000000000000000000000000000000000000fc00000000000000000000000000000000000000000000000000000000000000f3cffe3000000000000000000000000000000000000000000000000000000000f00ff00000000000000000000000000000000000000000000000000000000000f000000
  | 0, 3 => 0xfffff00
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x57304100000000000000000000000000000000000000000000000000000000005734f3f000000000000000000000000000000000000000000000000000000000451423d000000000000000000000000000000000000000000000000000000000a8cb0c0000000000000000000000000000000000000000000000000000000000543461800000000000000000000000000000000000000000000000000000000032a2d020000000000000000000000000000000000000000000000000000000000d500b5000000000000000000000000000000000000000000000000000000000000db6f
  | 0, 1 => 0xdf7dfff000000000000000000000000000000000000000000000000000000000cd5d2fd000000000000000000000000000000000000000000000000000000000c00d248000000000000000000000000000000000000000000000000000000000fffbdf7000000000000000000000000000000000000000000000000000000000fff6fbf000000000000000000000000000000000000000000000000000000000abcb9e700000000000000000000000000000000000000000000000000000000089490e50000000000000000000000000000000000000000000000000000000005734f3f
  | 0, 2 => 0xffff6d8000000000000000000000000000000000000000000000000000000000fff6fbf000000000000000000000000000000000000000000000000000000000fff2490000000000000000000000000000000000000000000000000000000000fffffff000000000000000000000000000000000000000000000000000000000fff2490000000000000000000000000000000000000000000000000000000000fbeffef000000000000000000000000000000000000000000000000000000000f2aff4a000000000000000000000000000000000000000000000000000000000f2a2400
  | 0, 3 => 0xfffffda
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 25 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 25 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 25 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 25 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 5 0) :: stateWiresD n (ids >>> 5)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 5 0) :: stateWiresS n (ids >>> 5)
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_62 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_62 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_62 == dom_62) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_62 goalM u ys) : RunD dom_62 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_62 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
private theorem z5_0 : ∀ i, 0 ≤ i → i < 13 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 13 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 13 → Z 5 i = true := z5_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 11 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 11 0 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 11 → Z 6 i = true := z6_0
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
  scr dom_62 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_62 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_62 roots_62 goal_62 8 := by
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

theorem low_62 : Lower dom_62 roots_62 goal_62 8 := S_62.noCircuit

namespace S_30
def pairsG : List (Nat × Nat) := [(6, 14), (6, 22), (10, 14), (10, 26), (12, 14), (12, 28), (18, 22), (18, 26), (20, 22), (20, 28), (24, 26), (24, 28)]
def r1sG : List Nat := [6, 6, 10, 10, 12, 12, 18, 18, 20, 20, 24, 24]
def r2sG : List Nat := [14, 22, 14, 26, 14, 28, 22, 26, 22, 28, 26, 28]
def mpG : Nat := 0xfff
def pool6G : List Nat := [11021189781006, 19834261081626, 19817148583446, 13220246722062, 22016205524502, 13237493701134, 22067946461718]
def xsM : List Nat := roots_30.map (· &&& dom_30)
def goalM : Nat := goal_30 &&& dom_30
def NN : Nat → Nat
  | 3 => 3
  | 4 => 6
  | 5 => 5
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xe0cd37755440646f04984346
  | 4, 0 => 0xe0cd377542ab9e402e926901153f1cb91102555d067c0848
  | 5, 0 => 0xe0cd37754d80fb4742ab9e40158e9dfc0e629920
  | 6, 0 => 0xe0cd3775
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x444444440000000000000000000000000000000000000000000000000000000044440000000000000000000000000000000000000000000000000000000000004440444000000000000000000000000000000000000000000000000000000000440044000000000000000000000000000000000000000000000000000000000040404040000000000000000000000000000000000000000000000000000000001111111100000000000000000000000000000000000000000000000000000000005500550000000000000000000000000000000000000000000000000000000000005555
  | 0, 1 => 0x55554444000000000000000000000000000000000000000000000000000000005555000000000000000000000000000000000000000000000000000000000000555000000000000000000000000000000000000000000000000000000000000055005500000000000000000000000000000000000000000000000000000000005454545400000000000000000000000000000000000000000000000000000000505050500000000000000000000000000000000000000000000000000000000050005000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xdb974d84340c873
  | 4, 0, 0 => 0xdb9740d9714db96450b92040eb9640db954
  | 5, 0, 0 => 0xdb974db97150d9714db9875dba975
  | 6, 0, 0 => 0xdb974
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 20
  | 4 => 24
  | 5 => 24
  | 6 => 20
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 4 0) :: stateWires n (ids >>> 4)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xcf00000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000f000000000000000000000000000000000000000000000000000000000000000c00000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000f3000000000000000000000000000000000000000000000000000000000000003c3000000000000000000000000000000000000000000000000000000000000003f
  | 0, 1 => 0xfcf0000000000000000000000000000000000000000000000000000000000000fc00000000000000000000000000000000000000000000000000000000000000f000000000000000000000000000000000000000000000000000000000000000c3c00000000000000000000000000000000000000000000000000000000000003ff00000000000000000000000000000000000000000000000000000000000003330000000000000000000000000000000000000000000000000000000000000030
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x5df00000000000000000000000000000000000000000000000000000000000005ca00000000000000000000000000000000000000000000000000000000000005df000000000000000000000000000000000000000000000000000000000000049d00000000000000000000000000000000000000000000000000000000000001570000000000000000000000000000000000000000000000000000000000000a2000000000000000000000000000000000000000000000000000000000000001420000000000000000000000000000000000000000000000000000000000000015
  | 0, 1 => 0xfff0000000000000000000000000000000000000000000000000000000000000fea0000000000000000000000000000000000000000000000000000000000000fea0000000000000000000000000000000000000000000000000000000000000ebd0000000000000000000000000000000000000000000000000000000000000fff0000000000000000000000000000000000000000000000000000000000000b770000000000000000000000000000000000000000000000000000000000000a35
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 15 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 15 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 15 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 15 then wireAt i else 0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_30 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_30 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_30 == dom_30) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_30 goalM u ys) : RunD dom_30 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_30 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 3 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 3 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 3 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 6 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 6 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 6 → Z 4 i = true := z4_0
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
  scr dom_30 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_30 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_30 roots_30 goal_30 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_30 goal_30 := by
    have h0 : isConstB dom_30 goal_30 = false := by decide +kernel
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

end S_30

theorem low_30 : Lower dom_30 roots_30 goal_30 7 := S_30.noCircuit

namespace S_15
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 9), (2, 3), (4, 5), (6, 7), (6, 14), (8, 9), (10, 11), (10, 14), (12, 13), (12, 14)]
def r1sG : List Nat := [1, 1, 1, 2, 4, 6, 6, 8, 10, 10, 12, 12]
def r2sG : List Nat := [3, 5, 9, 3, 5, 7, 14, 9, 11, 14, 13, 14]
def mpG : Nat := 0xfff
def pool6G : List Nat := [2203520468227, 6601533424389, 4402510170373, 6601566979331, 2203520469251, 10999613490435, 8800489571081]
def xsM : List Nat := roots_15.map (· &&& dom_15)
def goalM : Nat := goal_15 &&& dom_15
def NN : Nat → Nat
  | 3 => 1
  | 4 => 3
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xa8d11512
  | 4, 0 => 0xc6abdc4ba8d115124c1ef02a
  | 5, 0 => 0xa8d11512
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00000000000000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000cccc000000000000000000000000000000000000000000000000000000000000aaaa000000000000000000000000000000000000000000000000000000000000555500000000000000000000000000000000000000000000000000000000000000ff
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xb1a4
  | 4, 0, 0 => 0x8d04b1a4b194
  | 5, 0, 0 => 0xb1a4
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 16
  | 4 => 16
  | 5 => 16
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 3 0) :: stateWires n (ids >>> 3)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xf800000000000000000000000000000000000000000000000000000000000000c70000000000000000000000000000000000000000000000000000000000000036800000000000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000000000ff8000000000000000000000000000000000000000000000000000000000000007f
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfc40000000000000000000000000000000000000000000000000000000000000e720000000000000000000000000000000000000000000000000000000000000b6900000000000000000000000000000000000000000000000000000000000005bf0000000000000000000000000000000000000000000000000000000000000a40000000000000000000000000000000000000000000000000000000000000003b
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_15 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_15 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
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
private theorem z4_0 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := z4_0
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
  scr dom_15 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_15 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_15 roots_15 goal_15 6 := by
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

theorem low_15 : Lower dom_15 roots_15 goal_15 6 := S_15.noCircuit

namespace S_47_16
def pairsG : List (Nat × Nat) := [(16, 17), (18, 19), (18, 22), (18, 26), (18, 50), (20, 21), (20, 22), (20, 28), (20, 52), (24, 25), (24, 26), (24, 28), (48, 49), (48, 50), (48, 52), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [16, 18, 18, 18, 18, 20, 20, 20, 20, 24, 24, 24, 48, 48, 48, 56, 56, 56]
def r2sG : List Nat := [17, 19, 22, 26, 50, 21, 22, 28, 52, 25, 26, 28, 49, 50, 52, 57, 58, 60]
def mpG : Nat := 0x3ffff
def pool6G : List Nat := [22067946461718]
def xsM : List Nat := roots_47_16.map (· &&& dom_47_16)
def goalM : Nat := goal_47_16 &&& dom_47_16
def NN : Nat → Nat
  | 4 => 2
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x73240d52201cf257
  | 5, 0 => 0x73240d52
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xffff0000ff000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000cccc0000cccc0000000000000000000000000000000000000000000000000000aaaa0000aaaa0000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x234428a884
  | 5, 0, 0 => 0x46885
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
  | 0, 0 => 0x3fe00000000000000000000000000000000000000000000000000000000000003f0000000000000000000000000000000000000000000000000000000000000038e0000000000000000000000000000000000000000000000000000000000000001e0000000000000000000000000000000000000000000000000000000000000001e0000000000000000000000000000000000000000000000000000000000000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3ff98000000000000000000000000000000000000000000000000000000000003f1100000000000000000000000000000000000000000000000000000000000038e8800000000000000000000000000000000000000000000000000000000000249e4000000000000000000000000000000000000000000000000000000000001245e0000000000000000000000000000000000000000000000000000000000009223
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_47_16 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_47_16 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_47_16 == dom_47_16) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_47_16 goalM u ys) : RunD dom_47_16 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_47_16 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_47_16 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_47_16 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_47_16 roots_47_16 goal_47_16 6 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_47_16 goal_47_16 := by
    have h0 : isConstB dom_47_16 goal_47_16 = false := by decide +kernel
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

end S_47_16

theorem low_47_16 : Lower dom_47_16 roots_47_16 goal_47_16 6 := S_47_16.noCircuit

namespace S_15_16
def pairsG : List (Nat × Nat) := [(16, 17), (18, 19), (18, 22), (18, 26), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28)]
def r1sG : List Nat := [16, 18, 18, 18, 20, 20, 20, 24, 24, 24]
def r2sG : List Nat := [17, 19, 22, 26, 21, 22, 28, 25, 26, 28]
def mpG : Nat := 0x3ff
def pool6G : List Nat := [22067946461718]
def xsM : List Nat := roots_15_16.map (· &&& dom_15_16)
def goalM : Nat := goal_15_16 &&& dom_15_16
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x202b72e1
  | 4, 0 => 0x202b72e1
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00000000000000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000cccc000000000000000000000000000000000000000000000000000000000000aaaa0000
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
  | 0, 0 => 0x3800000000000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000000000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3c80000000000000000000000000000000000000000000000000000000000000274000000000000000000000000000000000000000000000000000000000000012e0000000000000000000000000000000000000000000000000000000000000093
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_15_16 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_15_16 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_15_16 == dom_15_16) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_15_16 goalM u ys) : RunD dom_15_16 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_15_16 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_15_16 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_15_16 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_15_16 roots_15_16 goal_15_16 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_15_16 goal_15_16 := by
    have h0 : isConstB dom_15_16 goal_15_16 = false := by decide +kernel
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

end S_15_16

theorem low_15_16 : Lower dom_15_16 roots_15_16 goal_15_16 5 := S_15_16.noCircuit

def isoMv_55 : List (Nat × Nat) := [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_55 : Lower dom_55 roots_55 goal_55 9 :=
  lower_iso isoMv_55 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47

def isoMv_59 : List (Nat × Nat) := [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)]
theorem low_59 : Lower dom_59 roots_59 goal_59 9 :=
  lower_iso isoMv_59 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47

def isoMv_61 : List (Nat × Nat) := [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem low_61 : Lower dom_61 roots_61 goal_61 9 :=
  lower_iso isoMv_61 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47

def isoMv_23 : List (Nat × Nat) := [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_23 : Lower dom_23 roots_23 goal_23 6 :=
  lower_iso isoMv_23 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15

def isoMv_27 : List (Nat × Nat) := [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem low_27 : Lower dom_27 roots_27 goal_27 6 :=
  lower_iso isoMv_27 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15

def isoMv_43 : List (Nat × Nat) := [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]
theorem low_43 : Lower dom_43 roots_43 goal_43 6 :=
  lower_iso isoMv_43 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15

def isoMv_51 : List (Nat × Nat) := [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]
theorem low_51 : Lower dom_51 roots_51 goal_51 6 :=
  lower_iso isoMv_51 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15

def isoMv_29 : List (Nat × Nat) := [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem low_29 : Lower dom_29 roots_29 goal_29 6 :=
  lower_iso isoMv_29 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15

def isoMv_45 : List (Nat × Nat) := [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]
theorem low_45 : Lower dom_45 roots_45 goal_45 6 :=
  lower_iso isoMv_45 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15

def isoMv_53 : List (Nat × Nat) := [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]
theorem low_53 : Lower dom_53 roots_53 goal_53 6 :=
  lower_iso isoMv_53 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15

def isoMv_55_8 : List (Nat × Nat) := [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_55_8 : Lower dom_55_8 roots_55_8 goal_55_8 6 :=
  lower_iso isoMv_55_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47_16

def isoMv_59_4 : List (Nat × Nat) := [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)]
theorem low_59_4 : Lower dom_59_4 roots_59_4 goal_59_4 6 :=
  lower_iso isoMv_59_4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47_16

def isoMv_61_2 : List (Nat × Nat) := [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem low_61_2 : Lower dom_61_2 roots_61_2 goal_61_2 6 :=
  lower_iso isoMv_61_2 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47_16

def isoMv_23_8 : List (Nat × Nat) := [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_23_8 : Lower dom_23_8 roots_23_8 goal_23_8 5 :=
  lower_iso isoMv_23_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15_16

def isoMv_39_16 : List (Nat × Nat) := [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]
theorem low_39_16 : Lower dom_39_16 roots_39_16 goal_39_16 5 :=
  lower_iso isoMv_39_16 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15_16

def isoMv_39_8 : List (Nat × Nat) := [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]
theorem low_39_8 : Lower dom_39_8 roots_39_8 goal_39_8 5 :=
  lower_iso isoMv_39_8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15_16

def isoMv_27_4 : List (Nat × Nat) := [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem low_27_4 : Lower dom_27_4 roots_27_4 goal_27_4 5 :=
  lower_iso isoMv_27_4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15_16

namespace S_63
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 9), (1, 17), (1, 33), (2, 3), (4, 5), (6, 7), (6, 14), (6, 22), (8, 9), (10, 11), (10, 14), (10, 26), (10, 42), (12, 13), (12, 14), (12, 28), (12, 44), (16, 17), (18, 19), (18, 22), (18, 26), (18, 50), (20, 21), (20, 22), (20, 28), (20, 52), (24, 25), (24, 26), (24, 28), (32, 33), (34, 35), (34, 42), (34, 50), (36, 37), (36, 44), (36, 52), (38, 39), (38, 46), (38, 54), (40, 41), (40, 42), (40, 44), (48, 49), (48, 50), (48, 52), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 1, 1, 1, 1, 2, 4, 6, 6, 6, 8, 10, 10, 10, 10, 12, 12, 12, 12, 16, 18, 18, 18, 18, 20, 20, 20, 20, 24, 24, 24, 32, 34, 34, 34, 36, 36, 36, 38, 38, 38, 40, 40, 40, 48, 48, 48, 56, 56, 56]
def r2sG : List Nat := [3, 5, 9, 17, 33, 3, 5, 7, 14, 22, 9, 11, 14, 26, 42, 13, 14, 28, 44, 17, 19, 22, 26, 50, 21, 22, 28, 52, 25, 26, 28, 33, 35, 42, 50, 37, 44, 52, 39, 46, 54, 41, 42, 44, 49, 50, 52, 57, 58, 60]
def mpG : Nat := 0x3ffffffffffff
def pool6G : List Nat := [1099713873155, 2203520468227, 2203520469251, 8800489571081, 11021189781006, 35188837581601, 4402510168837, 10999613490435, 19795841254659, 6601566979331, 21994629628689, 26392743510801, 13237106311950, 6601533424389, 4402510170373, 13198536082185, 13198603191045, 10999512826633, 8800725370121, 19834176866586, 13219926704910, 13220246722062, 19816996996374, 19795606373137, 22016020251414, 10999815604483, 22041790056732, 41785905513221, 13198603192581, 41785939068163, 41786040255237, 21994830958853, 41786073810179, 19795841257731, 17597054714641, 11000085088515, 13199108475141, 19834261081626, 10999984423689, 13199041365257, 19796312854787, 26465605845786, 22067559072534, 26465925465370, 26431246631706, 26431430984986, 22067946326294, 22041874271749]
def xsM : List Nat := roots_63.map (· &&& dom_63)
def goalM : Nat := goal_63 &&& dom_63
def NN : Nat → Nat
  | 4 => 1
  | 5 => 3
  | 6 => 41
  | 7 => 256
  | 8 => 269
  | 9 => 66
  | 10 => 10
  | 11 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x458d5478
  | 5, 0 => 0x51db74ac0b67627d08f5e3a0
  | 6, 0 => 0xe68b4eb0e36850f2ad3d5ded6560d3b5641670535828741c5617061a4482d64f4122ce743ac4ef71356f4a1333c559da2e5ba7492a9341b8274f4bc7273bf93d2420b6f42319aad0207cd6841ed8a79c1c8510c51b9a17fc1af2f8241804cdac163267b515df5cf0154403d40f1aa6790d6407ae0d24dc5e0c943f0b0b5856c30ac945900a5d916208534f6f0389ab5f03588a0c035869cd02b1191a028418e401b3b3f0
  | 7, 0 => 0x11f424b211ec75f21181a60f1150934e1074c967105d6e780fb82f890f89e43b0f027bcc0ee619670eb269670e9b62770e376c8a0da08c5a0d5688840d435fb60d3bb0f60d0b86630ccf44bc0c84b23a0c47966d0c37d5af0c092c410b5f485c0b3394d10b2827290ad5469c0aa84ed10a0aa5130a02438a08f317a508e52e1508d619800831cdc00831777f07dda4ae075a0f4906e233e806dcf42806cc7267065b5dba061c91c006165d76058240b90550c036053a214104ed5568047d00010407915c03f60fee03e66a8403172ca502e7172e024b422002121bb502059feb01a9d9e901a8fe060161f84600bb3ff4007e055b0039b2080038ea4b000e79ab
  | 7, 1 => 0x272c5f0526ad65e2262a4c2c25d4239025cb15d32478d925242a41b323b87817230b59c9223950ba22184a0121f1d3ee21a43d932126709c20ff172320de57dc2075ca351fe2717f1f98e41a1eee0fe31ecfc8b21e1be9031dad8f231d9c59fa1d3f18661cd71c531c2e33761c234d191bd4e2951a8ca1321a09b2911a0203d119d64a3919d26cf219c6b2651972fc92191d985a185940e6181d49e417dd4acf17a1b5821762397b1716dbda16ef8bb61686fc4916729058166bdd93166069021602420315aef97615559b2a14bb96f214b3e83214a16fa3146d9b4e146c73e31408113b13adf483136c1b3d132b6a0f1300314b127b63721261c1fa124cfc41
  | 7, 2 => 0x4ac5c8aa4a9c152a4a64dc954927ba66482b04a64798907444c4b9bc43cb524b42e9b9da42ad0f5f42a63016411faab44117fbf440e9a58040453e9a3ff5c8443fe994643f314d823d52fe083be058c93bd8aa093b2526c23b135db83a6b88913a29bc5239d86a0f386a6f983862c0d83804df55371edcac36faa05336bd7d7436622ea1352adb9a3516628e35138ce234b4803c34b0396b338da0ae33255a0b32bde15332b7bb3732541150324c62903192b70431247271300c78b83000db6f2ffc9ed02ff4f0102fc863402ef8fb7f2dfadf5a2d7f189d2d56e4632d5480a52d1d7ee12c99723f2a6ef5d02a6b816f29cd75ed2916f304290f44442862d9f7
  | 7, 3 => 0xfa79c624ec80e824e4b5e71fdb4eeeafc05271acb31c0421ab793ff8aaee5cdda459a778a254b9d199008a4d910009738dc6b4438c61d8ac89c937518909a79187776ba78648bc8085f27a5b82f4d1fb81470c0e7dd82b467d93b77878f42466755b529f7513001973db3f53734bd994709948756af633cf6632d64663b592e562950bd9623f33e460baf48d604c6dad5d65149a5d5d65da5962886b591a35e557530f60571f3c8f55d216f055c9d4c055231c6e54eca64a54c118e854b63b1453120c2c52d4bdfc51ed833a51bf9d7e5173bb585126f7755108d2f350f98c29507d9b47507acaf44f6a1ab44e980cc44cabd94d4c4097f84b7016724acd776a
  | 8, 0 => 0xf6fd21b0e78d3d30e288ea60dedfb9d0da24df30d86abda0d37070b0d05cbda0cf439bf0ccdc9130c404ad30c3486130c1e8e5d0c13a5aa0c0bf6ea0c0bb1f00c03b9010be9a9c20b1e47a70ae34fac0adba0700ac5e2020a77f1080a0f28af09cfb1be0919997808c83c6208b46af1088b11c40833854f0821841007f1b6d607ca96c50795c272078f398f078179cf06ba1bbb06a735f905f6f64d04886d4f0423234203c61bcb039e55770375c6cf032c37a902dd9fea02bb338f02b8e7a2029b15580278f4440249a99b023e907d022f2ba1022330b401eac28901cde88101551783012c73fe0124c53e01189ba900f9b8fb00d76e0200ba6fdd002f1772
  | 8, 1 => 0x2341f14023366966232c6add22f62ab92286f0d02278830821eaa96f204fb0ae203a91681ff31b391f928f6b1f6bcfb01ef64fe91edd0b6f1ed55caf1eafe22e1e6f4a801e5fbaf31dd1932c1d1165dd1cd038361ca481c01c97a1af1c8ff2ef1c65a3671c3cdffc1c0dd5381bcb17131b5389921b5233871b3e3b141b1756161b16f5ed1b0fa7561af1a04d1af090411a86fa2d1a69416d1a4dc7a419f37e07194727b518ef4baf1860cf5518595dba181431aa1813153418103f881797b3c917900509176b0666169dfcc61598ecd115974ea714be262c13d5001c13af4bd913aa682413a79d191368c1d31333d4cd1247bf7810ee72f5108d2c50104862a5
  | 8, 2 => 0x4021038c3fb5289a3f291ad13eda04a13dc575e93d7360653d5bb2db3bc63bf83b64e5cb3a9a85bd3a4fc2063a0c98ce3926b9f838c68766381fcf143811c47a380070cc374d282d362738653494bf2d33be1a3732b633db31cb4eaf311d9c7630ddf491309d4af530959c35306aaa7f2fa88bf32f3594f12e9b5e9e2e7e60792e512dbd2e2a89082d98c7d02d618f3b2d5758cd2b811d732b27b74c2ad9fd9b29ffccd429af2b6429a4bf20296ea4dd2912a7492817589127eaac2227c73156279f070c275afc202748e4d02724c80b2711d328270a246826f9178926f168c9263fdb29261ffc0c25c3013925a9c205258dff6a25701cea250aba57236b5ab5
  | 8, 3 => 0x931be89e92b8eaa08cd7ccae8c2742d1873a0c0e863f5b5b855887b97eff2d3a7eb37d267dcd4790772eb6fe77231e6a70120e996f5e8b526ecfcc7c6ea4ed216db7c4656a1ef29e680f799367d43ed9676814c166ce1c2b6685c72065a93de56332600f62381e255f5821df5edb25c45e2796d45d48a8d45a122e43596b75f1595d6b5758b5610057a50d135672b54a56488c3a55100dac509ca3164fb6e46b4fa0569c4f56d3284e3b68614e26286a4d84259f4c16af5f4bf17fed4b50406a4aabf4e84a4249ab498effba4918de8648a6ffde46f568e246946162466bac2745a7f598448d981d4397d140433e816f4336d2af42f91e8b419b578b4028b24c
  | 8, 4 => 0xfb901266f3138d03e74db9f1dfb2a488df974832c20018d3c111313ebc36ee53b13c425aa994b72fa8cca005a6e95aa69f27e99f
  | 9, 0 => 0xbe4be64fab681b8e9e58572e8a81f0ca877c8a9f8492c7cd83f048fb79e15a2877d135d06554bad1651506a464cf00c55c50bd215c0095e65b4388f85b2acd5958905d13568ff7f1530ec13f52f2fea44f490be64ec05ebd4bc969994b0c2c3941d9fb7840455b7a3cedcf813a305add358e7c1331381b073129ad3f2fc976f62f1362052d90db782ca8216328a4a83e2774c4602429651522c735132219ec0a1eb3facb1e08e1531d29fe0a1c1ffead1923eb0b1881f6861581f8c8141a4f1c12baa67712b8884a12324797119811440f6b9a140e7e15130d61f2fb0cabde0a09f5ca2f09ee1b6f06ecbabd06291d8303e36454023f103c0086a50c00273479
  | 9, 1 => 0xe575a6eac1043454
  | 10, 0 => 0xf2854adf7f4590c976f0de335cde0cce5059633d4aee737942b779a33e277fff0e7e151305169eb0
  | 11, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf0f0f0f000000000000000000000000000000000000000000000000000000000505050500000000000000000000000000000000000000000000000000000000030303030000000000000000000000000000000000000000000000000000000000ff00ff00000000000000000000000000000000000000000000000000000000000f000f000000000000000000000000000000000000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000055550000000000000000000000000000000000000000000000000000000000003333
  | 0, 1 => 0x30300000303000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000550000005500000000000000000000000000000000000000000000000000000000ffffffff00000000000000000000000000000000000000000000000000000000ffffffaa00000000000000000000000000000000000000000000000000000000fefefefe00000000000000000000000000000000000000000000000000000000333333330000000000000000000000000000000000000000000000000000000011111111
  | 0, 2 => 0x500050005000500000000000000000000000000000000000000000000000000030003000300030000000000000000000000000000000000000000000000000000ffff0000ffff000000000000000000000000000000000000000000000000000057570000575700000000000000000000000000000000000000000000000000005555000055550000000000000000000000000000000000000000000000000000333300003333000000000000000000000000000000000000000000000000000011110000111100000000000000000000000000000000000000000000000000000f0f00000f0f
  | 0, 3 => 0x30303ff030303ff000000000000000000000000000000000000000000000000030303030303030300000000000000000000000000000000000000000000000000ff00ff00ff00ff00000000000000000000000000000000000000000000000000fe00fe00fe00fe000000000000000000000000000000000000000000000000005500550055005500000000000000000000000000000000000000000000000000330033003300330000000000000000000000000000000000000000000000000011001100110011000000000000000000000000000000000000000000000000000f000f000f000f
  | 0, 4 => 0x545454545454545400000000000000000000000000000000000000000000000033333333333333330000000000000000000000000000000000000000000000003333332233333322000000000000000000000000000000000000000000000000111111ff111111ff00000000000000000000000000000000000000000000000011111111111111110000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000f0f0f0a0f0f0f0a0000000000000000000000000000000000000000000000000505050505050505
  | 0, 5 => 0xaaaaa8a8aaaaa8a8000000000000000000000000000000000000000000000000a8a8a8a8a8a8a8a8000000000000000000000000000000000000000000000000555555555555555500000000000000000000000000000000000000000000000055555550555555500000000000000000000000000000000000000000000000005555550055555500000000000000000000000000000000000000000000000000555554545555545400000000000000000000000000000000000000000000000055555050555550500000000000000000000000000000000000000000000000005555444455554444
  | 0, 6 => 0xcccccc88cccccc88000000000000000000000000000000000000000000000000abababababababab000000000000000000000000000000000000000000000000aaaaaaffaaaaaaff000000000000000000000000000000000000000000000000aaaaaabbaaaaaabb000000000000000000000000000000000000000000000000aaaaaaaaaaaabbbb000000000000000000000000000000000000000000000000aaaaaaaaaaaaaaff000000000000000000000000000000000000000000000000aaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000aaaaaa00aaaaaa00
  | 0, 7 => 0xeeeeee00eeeeee00000000000000000000000000000000000000000000000000eeeee0e0eeeee0e0000000000000000000000000000000000000000000000000ddddddccddddddcc000000000000000000000000000000000000000000000000ccddccddccddccdd000000000000000000000000000000000000000000000000ccccddddccccdddd000000000000000000000000000000000000000000000000ccccccffccccccff000000000000000000000000000000000000000000000000ccccccddccccccdd000000000000000000000000000000000000000000000000cccccccccccccccc
  | 0, 8 => 0xf0f0f0f5f0f0f0f5000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000f0f0f0a0f0f0f0a0000000000000000000000000000000000000000000000000eeeeeeeeeeeeeeee000000000000000000000000000000000000000000000000eeeeeeeeeeeeee00000000000000000000000000000000000000000000000000eeeeeeeeeeee0000000000000000000000000000000000000000000000000000eeeeeee0eeeeeee0000000000000000000000000000000000000000000000000eeeeeecceeeeeecc
  | 0, 9 => 0xfcfca8a8fcfca8a8000000000000000000000000000000000000000000000000fca8fca8fca8fca8000000000000000000000000000000000000000000000000fafafafafafafafa000000000000000000000000000000000000000000000000fafafaf8fafafaf8000000000000000000000000000000000000000000000000fafafa00fafafa00000000000000000000000000000000000000000000000000fac8fac8fac8fac8000000000000000000000000000000000000000000000000f1f1f1f1f1f1f1f1000000000000000000000000000000000000000000000000f0f0f0fff0f0f0ff
  | 0, 10 => 0xfefefeaafefefeaa000000000000000000000000000000000000000000000000fe00fe00fe00fe00000000000000000000000000000000000000000000000000fcfcfcfcfcfcfcfc000000000000000000000000000000000000000000000000fcfcfcfcfcfcfc00000000000000000000000000000000000000000000000000fcfcfcfcfcfc0000000000000000000000000000000000000000000000000000fcfcfcfcfca8fca8000000000000000000000000000000000000000000000000fcfcfca8fcfcfca8000000000000000000000000000000000000000000000000fcfcfc00fcfcfc00
  | 0, 11 => 0xffa8ffa8ffa8ffa8000000000000000000000000000000000000000000000000ff11ff11ff11ff11000000000000000000000000000000000000000000000000ff03ff03ff03ff03000000000000000000000000000000000000000000000000ff00ff55ff00ff55000000000000000000000000000000000000000000000000ff00ff00ff00ff00000000000000000000000000000000000000000000000000fefefefefefefefe000000000000000000000000000000000000000000000000fefefefe00000000000000000000000000000000000000000000000000000000fefefeccfefefecc
  | 0, 12 => 0xfff0aaa0fff0aaa0000000000000000000000000000000000000000000000000ffeeffeeffeeffee000000000000000000000000000000000000000000000000ffccffccffccffcc000000000000000000000000000000000000000000000000ffccaa88ffccaa88000000000000000000000000000000000000000000000000ffaaffaaffaaffaa000000000000000000000000000000000000000000000000ffaaffaaffaacc88000000000000000000000000000000000000000000000000ffaaffaaffaa0000000000000000000000000000000000000000000000000000ffaafca8ffaafca8
  | 0, 13 => 0xffff5550ffff5550000000000000000000000000000000000000000000000000ffff1111ffff1111000000000000000000000000000000000000000000000000ffff0303ffff0303000000000000000000000000000000000000000000000000ffff0055ffff0055000000000000000000000000000000000000000000000000ffff0000ffff0000000000000000000000000000000000000000000000000000fffcfffcfffcfffc000000000000000000000000000000000000000000000000fffafffafffafffa000000000000000000000000000000000000000000000000fff0fff0fff0fff0
  | 0, 14 => 0xfffffafafffffafa000000000000000000000000000000000000000000000000fffff0f0fffff0f0000000000000000000000000000000000000000000000000ffffeeeeffffeeee000000000000000000000000000000000000000000000000ffffccccffffcccc000000000000000000000000000000000000000000000000ffffaaaaffffaaaa000000000000000000000000000000000000000000000000ffffaaaaffccaa88000000000000000000000000000000000000000000000000ffffaaaaf0f0a0a0000000000000000000000000000000000000000000000000ffffa8a8ffffa8a8
  | 0, 15 => 0xfffffffcfffffffc000000000000000000000000000000000000000000000000fffffff0fffffff0000000000000000000000000000000000000000000000000ffffffeeffffffee000000000000000000000000000000000000000000000000ffffffccffffffcc000000000000000000000000000000000000000000000000ffffffaaffffffaa000000000000000000000000000000000000000000000000ffffffaa00000000000000000000000000000000000000000000000000000000ffffff00ffffff00000000000000000000000000000000000000000000000000fffffcfcfffffcfc
  | 1, 0 => 0xffffffffa8a8a8a8000000000000000000000000000000000000000000000000ffffffff11111111000000000000000000000000000000000000000000000000ffffffff03030303000000000000000000000000000000000000000000000000ffffffff01010101000000000000000000000000000000000000000000000000ffffffff00005555000000000000000000000000000000000000000000000000ffffffff000000ff000000000000000000000000000000000000000000000000ffffffff00000055000000000000000000000000000000000000000000000000ffffffff00000000
  | 1, 1 => 0xfffffffffafafafa000000000000000000000000000000000000000000000000fffffffff0f0f0f0000000000000000000000000000000000000000000000000ffffffffeeeeeeee000000000000000000000000000000000000000000000000ffffffffcccccccc000000000000000000000000000000000000000000000000ffffffffabababab000000000000000000000000000000000000000000000000ffffffffaaaaaaaa000000000000000000000000000000000000000000000000ffffffffaaaaaaa0000000000000000000000000000000000000000000000000ffffffffaaaaaa00
  | 1, 2 => 0xfffffffffff0fff0000000000000000000000000000000000000000000000000ffffffffffeeffee000000000000000000000000000000000000000000000000ffffffffffccffcc000000000000000000000000000000000000000000000000ffffffffffaaffaa000000000000000000000000000000000000000000000000ffffffffff00ff00000000000000000000000000000000000000000000000000fffffffffcfcfcfc000000000000000000000000000000000000000000000000fffffffffcfcfc00000000000000000000000000000000000000000000000000fffffffffca8fca8
  | 1, 3 => 0xffffffffffffffcc000000000000000000000000000000000000000000000000ffffffffffffffaa000000000000000000000000000000000000000000000000ffffffffffffff00000000000000000000000000000000000000000000000000fffffffffffff0f0000000000000000000000000000000000000000000000000ffffffffffffcccc000000000000000000000000000000000000000000000000ffffffffffffaaaa000000000000000000000000000000000000000000000000ffffffffffff0000000000000000000000000000000000000000000000000000fffffffffffcfffc
  | 1, 4 => 0xfffffffffffffff0
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x80634f4b385
  | 5, 0, 0 => 0x8079634f4d3868073634641386807363554b386
  | 6, 0, 0 => 0x5b463831150a680797363554d3870099934631260e6806b68624638317806b634b4644387008f8c6b55311d6008c6b5b552d0760099937b4631266806b605b4644317806b63554b38317807673656346447006b5b55310907600806b5b473126600806b5b4f4d44600802d26221d156009379383122026
  | 6, 0, 1 => 0x8e8c6b5b50316807973634b46387806b5b55464331700816b5b46382d6806b635b4e4d44780736b6a5b4d447807c735b4d464478e806b5b553f317005b2d2622150c600806b5b382d21600806b5b46392d692806b5b463f317008e8c55311d156008e8c6b5b36316008078735b4d446999379554644317
  | 6, 0, 2 => 0x3126221d150c600806b5b45372d600999346382d0e6806b5b554d3f31700846b4638311d6008e8c5b552d15680705d5b46383178e8c6b5b4b38317008f6b5b5531096
  | 7, 0, 0 => 0x806b5b52463831700807c6b5b382d22700806b5a46382d1d70099936b5b382d22780766b6563464431800008e8c6b5b311e600806c6b5b38312270093806b50463831700806f6b5b46382d700806b6a634644317008e806b3831201d7008e806b5a38311d700806b5b46403f317806b5d5b4638312e8006b5b4631261b0c7806b655b464442318
  | 7, 0, 1 => 0x8076735b462d26700807e735b46382d7006b5b4644311e0c700806b633831221a700806a5b4d3831157007b6b5b3831220c700806b5b3831220170080796b5b2d2622700786b4638311d0c70080786b5f463831700006b5b2d26220c60080796b634630267008c806b46311e1d70080796b5b3831217006b5b46382d120c7006b554644311d0c7
  | 7, 0, 2 => 0x806b46382d1d0270080726b5b4638317008b806b5b463831700806b5b3831221170099946b5b463126788796b5b55463831880796b5b55463f318005b5a59463831157006b5b3831220e0c70090806b5b463831700807e6b5b4d31267978a746b5b4638318008c805b554d3115700876b6a5b463831700005b462d26150c600806e6b5b3831227
  | 7, 0, 3 => 0x998a795b4631267009980795b462d2670080796b463126047008a803831221d15700806b5b554644277806b634d4a463831800806b46382d291d780746b635b4d46448009980735b312622700685b46382d150c700806b5b38353122700736b4631261d0c700806b4638311d05700806b5b463d382d700806b5b4631260d7008a6b4638311d027
  | 7, 0, 4 => 0x80796b6331262270092806b4644311d700807d6b5b46382d7008a6b5b46383103700806b5b46382d03780796b63554d383180080747346382d1d780796b63554638308007c6b5b4644310c7009b806b3831221d7009a806b4631261d700805b4638312715700766b4631261d0c700807c6b5b4c383170080735b4b46383170099936b633831227
  | 7, 0, 5 => 0x806b5b5746383170099805b463835317008074735b443122780796b634d4644388005b46383118150c7008e805b4d3126157008c803831221d157005b5546382d150c70000806b5b45373160080786b5b4d443170080736b382d221d700806b5b46383431793806b5b4f463831800806b5b5046382d700807963463831137008e806b5b5531237
  | 7, 0, 6 => 0x806b5546442d1d7008e8c796b5b553170080735b46382d107008d804638311d15700a0806b5b4631267006863463831150c700886b5b4638310e7009e806b5b3831227806b5b584b463831800806b5d5b46443170080765b46312613700806b684d38311b7008c6b5b46383106780796b5b5a46382e800978a5b4638311570097805b46382d157
  | 7, 0, 7 => 0x806b5b382d220e700756b4638311d0c700806b5b383122007806b655b46443e3188076736563463831880735b46443f3831800806b5b46442d1e700806b5b463832317006b65633831220c700996b5b46382d04700806b5b3b38312278e8c796b63463831880796b5b55463a318008d805b554631157008e806b5b44311e7998a795b554638318
  | 7, 0, 8 => 0x988a6b5b46383170098806b5b46382d700806b5b4641383170080766b462d261d7008c806b5b463f3179d806b5b55464431800806b5b554b383179380796b55464431800806b4d38311d07780786b635b464431800806b3831221d137006b5b4638310907700806b5b4638312c700928a5b4638311570092805b46382d15700806b5b46382d2a7
  | 7, 0, 9 => 0x806b633831220e700806b5a4638311c700805b46382d181570085805b46383115799936b635546383188079735b4f46383180080736b5b463125700008e6b5b553109600946b5b46383102700806b3831221d12700998a5b4638310e70099805b46382d0e700805b5546383114700806b634d38311879980796355463831800807c6b5b46442d7
  | 7, 0, 10 => 0x80746b4431221d70096806b5b3831227008038312d221d157008e8a4638311d157008e8046382d1d15700008e8c6b5b552d600897e6b5b463831700806b5b4846382d7806b635b4f46383180097806b634631267008a795b4638310270080795b46382d02700876b554638311d70083806b4638311d79280796b5b46443180000803126221d156
  | 7, 0, 11 => 0x806b5b46382d05700805b553831201570086805b46383115700806b5b46383124700805a5646383115700807963463831027008e8c6b5b38312070080796b5b403122700786b5b46382d0c7008e8c4638311d1570080756b46382d1d700938a5b3831221570093805b382d2215700805b4e46383115700804638311d1507700806b5b4638311f7
  | 7, 0, 12 => 0x806b5b463931600807b6b5b46382b70080736b68634d38700006b5b4638310b60080797363383122700806b46382d271d700806b5b46382d0f700806b5f4638311e700807b6b5b46372d780736b676346383180080776b4631261d700806b5b46383331700805b3831221509700936b63463831027958076735b4638318008a6b5b463831057
  | 7, 0, 13 => 0x816b5b463831600806b5b4d44311e700807b6b5b3830227009980795b3126227008a6b5b38312204700806b5b382d22047006b635b3126220c7006b5b4b4638310c700005b312622150c600806b5b514638317009993794d46383170080463831201d15700805a4638311d1570000999479463831600806b5b3831220870000806b5b3831216
  | 7, 0, 14 => 0x806b5b544638317006b5b383123220c700806b635b554d4470082806b5b46382d7806b5b5a4f463831800806b5b46382d17700806b6a4e46383170080736b3126221d700806b635b2d2622700806b5b4b46382d7807973635546383180000805b2d262215600996b5b3831220478e8a7c6b5b463831880796b5b55464031800807d6b5b3831227
  | 7, 0, 15 => 0x6b5b504638310c70092804638311d15700807f6b5b46382d700554638311d150c700806b5b4638352d79d8a6b5b55463831800806b5b46382d0d70091806b5b4638317006b5b463835310c700806b5b46433831700008e8c6b5b5a316807673655b4644318006b5b46382d1e0c700008e8c5b5531156008c826b5b463831700806b5b3126220e7
  | 8, 0, 0 => 0x998073655b463831800805b5a554638311580000806b5b463831197008c806b635b5546318008e806b5b46383113800806b5f5b55463831800008d806b4638311d7000080756b5b3831227000080766b46382d1d700009c8a6b5b463831700009c806b5b46382d700006b68634638310c70000807e6b5b463126700005b46443831150c7008076735b46443831800008c805b554631157
  | 8, 0, 1 => 0x8a806b4631261d700928e806b5b464431800807e6b5b4638312d8000099806b3831221d70080756b635b463831800807c746b63463831800806b695b4d46382d8806b635b5a55463831900008d806b5b5546317009980735b55463831800806b5b4d4638310e800009e806b5b46383170080736b685b463126800806b5e5b46443831800807e766b5b46382d89d99806b5b554638319
  | 8, 0, 2 => 0x806b5b4638310070080796b5b3831220e80080786b5b4638312f800009f806b5b463831700938076735b46383180080796b63554638318008e806b5b46383112800806b6a5b4638312e800806b635b463831108000000803831221d1560080736b5b4638312080000807b6b5b46382d7009b8c806b4638311d80080766b5b46312d2680080736b5b5a46383180000806b5b463b38317
  | 8, 0, 3 => 0x8075746b5b38312280099936b5b4644383189380746b5b4d46383190080736b5b4631261380093806b5b4638311e8000080786b5b4644317008f806b655b46383180000806b5b46382d0e70000806b5c5b463831700008c806b5b5a4631700806b655b4d46382d8000097806b634638317000079735b4638310c70000928a6b5b4638317000092806b5b46382d70092806b554638311d8
  | 8, 0, 4 => 0x9380746b5b46382d8006b685b464438310c80080736b645b4638318008a80796b5b383122800009a936b5b463831700807c796b5b464431800009d80735b463831700008e8a6b5b5538317000093807973463831700008e806b5b55382d700805b4d4644383115800806b5d5b5546383180000806b684638311b7008d8c806b4638311d8008e806b635b46312680000806b4638311d137
  | 8, 0, 5 => 0x806b5b4f463831700928c806b5b46382d8008a806b5b4638311a80080736b635b4d4638800806b5b5546382d1e8008a806b5b4638311e80000746b5b3831220c70000806b5b44382d22700008076735b4d383170000807f6b5b46383170000806b5b4631261070000806b554d38311d70000806b5b5538310770000806b5b46382d187000085806b5b463831700938a746b5b4638318
  | 8, 0, 6 => 0x8c8076735b4638318807b6b635b4d463831900806b5b494638312380000806b686346382d70000805b4644382d157000094805b463831157009c998a6b5b4638318009c99806b5b46382d8008c80796b5b3831228008e80655b4638311580000806b5b4d38311e7807c6b655b4d463831900806b5b463c38311b8000080735b4638310270080756b685b463831800928c8a6b5b4638318
  | 8, 0, 7 => 0x806b4638311d077008d80796b5b46383180000804638312d1d15780786b635b5546383190097806b5b4644383180080736b464438311d80000766b5b46382d0c70000806b38312d221d700008c806b5b46312370080766b5b463831238009c8e80735b4638318008077736b5b463126800806b5b4638312d10800008e8a6b4638311d700008e806b46382d1d7008079735b4d4638318
  | 8, 0, 8 => 0x6b695b4638310c7008073716b5b46383180000806b6346383118700008c806b4644311d7009d8a796b5b4638318009d80796b5b46382d80000938a5b463831157000093805b46382d157008a807c6b5b463831800806b655b463831108000080746b4644311d700008e8c6b4638311d7008f8e8c6b5b463831800806b63615b4638318000096806b5b4638317008f806b4d4638311d8
  | 8, 0, 9 => 0x80796b5b554638310e90093806b5b4d46312680000806b5b553831207000086806b5b46383179280796b5b554638319000080554638311d1570000806b5a5646383170000806b5b463836317807b796b5b5546383190000005b383122150c6000080796b5b464031700806b5a464438311d80000806b5b46383116700008079735b46382d70080766b655b464431800807b6b635b46382d8
  | 8, 0, 10 => 0x8a80796b5b5546383190000807973634638317000093806346383115700806b635b46383109800746b685b4638310c800806b5b5546383127880746b635b4d4638319008c805b4d46383115800006b5b463831130c700978a6b685b46383180097806b685b46382d800008078735b46383170000806b5b3831220970000805b4638311e1570000635b463831150c700807673635b4638318
  | 8, 0, 11 => 0x8e80796b5b46382d80080736b6a5b46383180000806b5b46382d287009780746b5b4638318008a80766b4638311d8008e806b5b4638312380080796b5b46382d2b800806b5b4638312e1e8008e806b665b46383180000806b5b4638310870000006b5b3126220c600806a5b5546383115800006b5b463831120c70000806b463831201d70000806b5a4638311d700806b554638312e1d8
  | 8, 0, 12 => 0x806b5b5046383170000806b5b554d382e70000807d6b5b463831700806b685b46383109800008074734638311d7008e8c796b5b46383180000807b6b5b463830700806b5b4638312d1e8000000805b382d221560080796b5b4638310780000806b695b46382d700008a6b5b4638310470000806b5b46382d04700806b635b4e46383180080796b5b38312d228008e8a796b5b4638318
  | 8, 0, 13 => 0x80796b5b554638312e900006b5b5a4638310c700806b5b554f46383180000996b5b463831047000000806b5b2d26226009980795b55463831800928e806b4638311d80080746b685b46382d800807e796b5b46382d8008e80796b634638318000097805b463831157006b635b554638310c80000006b46382d1d0c600005b55463831150c7008c807b6b5b4638318000080736b3831221d7
  | 8, 0, 14 => 0x80736b554638311d800806b635b5546382d80000805b5546382d15700806b695b4d463126800806b5b55463836318008f8c6b5b4d4638318000099805b4638310e78e80796b5b464438319000080766b4631261d700008e8c6b5b46382d70092806b635b463831800806d6b5b4638311e800806b5b55534638318000092805b4638311570080796b5b4638312080080796b5b5a4638318
  | 8, 0, 15 => 0x80786b5b46382d700008a806b5b31262270000806b5b46382d2b78a80746b685b463831900806b5b5550463831800009993735b463831700806b5b464438310780000806b5b46383105700806b5b4d46383123800806b5b554638310e800806b69685b46382d80000786b5b4638310c700008e804638311d1570000008e8c6b5b553160000796b5b46382d0c70000806b5b484638317
  | 8, 1, 0 => 0x80796b5b5546382d800806b5b463835310e8009d806b5b5546383180000806b5b4638310d700796b5b554638310c800006b5b4638311e0c70000806b5b4638312b700007b7a6b5b463831700806b5b5a5546382d80000806b635b31262270000876b5b55463831780796b5b4d464438319008e807c6b5b4638318
  | 9, 0, 0 => 0x806b5b4638311a780746b5b4d463831800806b5b4638311e7006b635b4638310c7008076735b46383170000806b5b46382d60080796b5b383122700006b5b3831220c600938a6b5b46383170093806b5b46382d7807e6b685b463831800806b4638312d1d780786b5b5546383188c80796b5b463831893806b5b4d463831800746b5b4638310c7
  | 9, 0, 1 => 0x6b5b554638310c700806b635b46382d79793806b5b46383180000806b5b382d22680796b5b4638312d8806b635b4d463831800806b5b4638311b700805b4d46383115794806b635b463831800807c6b5b46383170099936b5b46383170080746b5b46382d70093806b634638317009980795b463831700806b5b4638310978c806b5b4d4638318
  | 9, 0, 2 => 0x8a80746b5b4638318009a806b5b4638317008e806b4638311d78f8e806b5b4638318928c806b5b4638318806b5b554638311e89380746b5b463831800806b5b5546382d7806b635b4638311b80092806b5b463831700807b6b5b4638317806b695b4d46383180080766b4638311d70097806b5b46383170080736b4638311d780796b5b554638318
  | 9, 0, 3 => 0x6b5b46382d0c6806b69685b4638318806b635b5546383180000806b5b31262268a806b5b55463831880746b5b4638312d880746b685b46383180000805b38312215600806b695b463831780796b5b463831308008a806b5b383122797806b685b4638318008079735b4638317807b6b635b46383189d80796b5b46383180093805b463831157
  | 9, 0, 4 => 0x806b5b5a55463831880736b635b4638318
  | 10, 0, 0 => 0x6b5b4638310c6806b5b554638317806b5b4638312d700806b5b383122680746b5b46383178a806b5b463831700806b5b463831693806b5b463831700806b5b46382d6806b5b4d4638317
  | 11, 0, 0 => 0x806b5b4638316
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 44
  | 5 => 52
  | 6 => 60
  | 7 => 68
  | 8 => 76
  | 9 => 68
  | 10 => 60
  | 11 => 52
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 8 0) :: stateWires n (ids >>> 8)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x70f87c3f0000000000000000000000000000000000000000000000000000000070f87c20000000000000000000000000000000000000000000000000000000007008041f000000000000000000000000000000000000000000000000000000000ff803ff0000000000000000000000000000000000000000000000000000000000f8003f000000000000000000000000000000000000000000000000000000000007ffff000000000000000000000000000000000000000000000000000000000007ffe0000000000000000000000000000000000000000000000000000000000007845f
  | 0, 1 => 0xe008000041f000000000000000000000000000000000000000000000000000001ff800003ff000000000000000000000000000000000000000000000000000001ff800003e0000000000000000000000000000000000000000000000000000000007fffffff000000000000000000000000000000000000000000000000000000007ffffc1f000000000000000000000000000000000000000000000000000000000ff7fbff000000000000000000000000000000000000000000000000000000007f0f845f000000000000000000000000000000000000000000000000000000007f0f8440
  | 0, 2 => 0x700780f80020000000000000000000000000000000000000000000000000000070008008001f00000000000000000000000000000000000000000000000000000fff8007ffff00000000000000000000000000000000000000000000000000000fff8007ffff00000000000000000000000000000000000000000000000000000fff8007ffe000000000000000000000000000000000000000000000000000000e388007845f00000000000000000000000000000000000000000000000000000e388007844000000000000000000000000000000000000000000000000000000e0780007c3f
  | 0, 3 => 0x3fffff00807ff0000000000000000000000000000000000000000000000000003fe00f008041f000000000000000000000000000000000000000000000000000071ff8ff803ff000000000000000000000000000000000000000000000000000001ff0ff003ff000000000000000000000000000000000000000000000000000071ff8ff803e0000000000000000000000000000000000000000000000000000070388f08005f000000000000000000000000000000000000000000000000000070388f0800400000000000000000000000000000000000000000000000000000700780f8003f
  | 0, 4 => 0x1ff0ff7fbe00000000000000000000000000000000000000000000000000003fe38ff0f845f0000000000000000000000000000000000000000000000000003fe007f0f841f0000000000000000000000000000000000000000000000000003ffffff0f87ff0000000000000000000000000000000000000000000000000003fe38ff0f84400000000000000000000000000000000000000000000000000003fe07f0f87c3f0000000000000000000000000000000000000000000000000003fe0070f87c1f0000000000000000000000000000000000000000000000000003fe07f0f87c20
  | 0, 5 => 0x3ffffffffffe00000000000000000000000000000000000000000000000000003fff87fffffc00000000000000000000000000000000000000000000000000003fe007ffffc000000000000000000000000000000000000000000000000000003f1ff7ffffbe00000000000000000000000000000000000000000000000000003f1f87fff83c00000000000000000000000000000000000000000000000000003f1c77ff87ba0
  | 0, 6 => 0xf078000000000000000000000000000000000000000000000000000003fe00f008041f000000000000000000000000000000000000000000000000000001ff800003ff000000000000000000000000000000000000000000000000000000388000005f000000000000000000000000000000000000000000000000000000000007845f00000000000000000000000000000000000000000000000000000000000003ff000000000000000000000000000000000000000000000000000000000000001f0000000000000000000000000000000000000000000000000000000000000000
  | 0, 7 => 0xf07800000000000000000000000000000000000000000000000000000001c000f003800000000000000000000000000000000000000000000000000003ffc77fffffa0000000000000000000000000000000000000000000000000000071ff8ff87be000000000000000000000000000000000000000000000000000000fff80f7ffe0000000000000000000000000000000000000000000000000000001ff80f07bff000000000000000000000000000000000000000000000000000001ff80f07be0000000000000000000000000000000000000000000000000000001c700f07ba0
  | 0, 8 => 0x1ff8f0783e0000000000000000000000000000000000000000000000000000001f80f0783c0000000000000000000000000000000000000000000000000000000000f078000000000000000000000000000000000000000000000000000000001c700f07bbf000000000000000000000000000000000000000000000000000001c700f07800000000000000000000000000000000000000000000000000000001c700f00000000000000000000000000000000000000000000000000000000001c000f07b80000000000000000000000000000000000000000000000000000001c700f07ba0
  | 0, 9 => 0xff00000000000000000000000000000000000000000000000000000000000000007f800000000000000000000000000000000000000000000000000000001f80f0783df000000000000000000000000000000000000000000000000000001f80f0783c0000000000000000000000000000000000000000000000000000000000f078000000000000000000000000000000000000000000000000000000001c0000783800000000000000000000000000000000000000000000000000003fff8ff0f87c0000000000000000000000000000000000000000000000000000001ff8f0783ff
  | 0, 10 => 0xff7f81f000000000000000000000000000000000000000000000000000000000007f800000000000000000000000000000000000000000000000000000001ff0ff7fbe0000000000000000000000000000000000000000000000000000001ff0ff7f800000000000000000000000000000000000000000000000000000001ff0ff00000000000000000000000000000000000000000000000000000000001ff0007f800000000000000000000000000000000000000000000000000000000000ff7f800000000000000000000000000000000000000000000000000000000000ff7f800
  | 0, 11 => 0x38e007007fc000000000000000000000000000000000000000000000000000003fe38ff0ffc400000000000000000000000000000000000000000000000000003fe00f00ffc1f00000000000000000000000000000000000000000000000000038ffff007ffe000000000000000000000000000000000000000000000000000038e007007fc00000000000000000000000000000000000000000000000000000001ff0ff7fbff000000000000000000000000000000000000000000000000000001ff00000000000000000000000000000000000000000000000000000000000001c70ff7fba0
  | 0, 12 => 0x380007f00000000000000000000000000000000000000000000000000000000038fc770f7ffbf00000000000000000000000000000000000000000000000000038fc770f7ffa00000000000000000000000000000000000000000000000000003800070f0000000000000000000000000000000000000000000000000000000038e007007fc1f00000000000000000000000000000000000000000000000000038e007000780000000000000000000000000000000000000000000000000000038e0070000000000000000000000000000000000000000000000000000000000380007007f800
  | 0, 13 => 0x3fff87fffffc00000000000000000000000000000000000000000000000000003fe38ffff84400000000000000000000000000000000000000000000000000003fe00fff8041f0000000000000000000000000000000000000000000000000003f1fffff803e00000000000000000000000000000000000000000000000000003f0007ff8000000000000000000000000000000000000000000000000000000038fff7ff7ffe000000000000000000000000000000000000000000000000000038ff87f07ffdf00000000000000000000000000000000000000000000000000038ff87f07ffc0
  | 0, 14 => 0x3f1f87fff83df0000000000000000000000000000000000000000000000000003f1f87fff83c00000000000000000000000000000000000000000000000000003f1c77ff87bbf0000000000000000000000000000000000000000000000000003f1c77ff87ba00000000000000000000000000000000000000000000000000003f0007ff8001f0000000000000000000000000000000000000000000000000003f00070f000000000000000000000000000000000000000000000000000000003f0000f0000000000000000000000000000000000000000000000000000000003f0007ff80000
  | 0, 15 => 0x3ffff7fffffe00000000000000000000000000000000000000000000000000003fff87fffffc00000000000000000000000000000000000000000000000000003ffc77fffffbf0000000000000000000000000000000000000000000000000003ffc77fffffa00000000000000000000000000000000000000000000000000003fe007ffffc1f0000000000000000000000000000000000000000000000000003fe00000000000000000000000000000000000000000000000000000000000003fe007ffffc000000000000000000000000000000000000000000000000000003f1ff7ffffbe0
  | 1, 0 => 0x3ffff800000000000000000000000000000000000000000000000000000000003ffffff0f84400000000000000000000000000000000000000000000000000003fffff008041f0000000000000000000000000000000000000000000000000003fffff00804000000000000000000000000000000000000000000000000000003ffff8007ffe00000000000000000000000000000000000000000000000000003ffff800003ff0000000000000000000000000000000000000000000000000003ffff800003e00000000000000000000000000000000000000000000000000003ffff80000000
  | 1, 1 => 0x3ffff8f0783df0000000000000000000000000000000000000000000000000003ffff8f0783c00000000000000000000000000000000000000000000000000003ffff80f07bbf0000000000000000000000000000000000000000000000000003ffff80f07ba00000000000000000000000000000000000000000000000000003fffff008041f0000000000000000000000000000000000000000000000000003ffff8000001f0000000000000000000000000000000000000000000000000003ffff800000000000000000000000000000000000000000000000000000000003ffff80000000
  | 1, 2 => 0x3ffffff07ffc00000000000000000000000000000000000000000000000000003fffff0f7ffbf0000000000000000000000000000000000000000000000000003fffff0f7ffa00000000000000000000000000000000000000000000000000003fffff007fc1f0000000000000000000000000000000000000000000000000003fffff007fc000000000000000000000000000000000000000000000000000003ffff8ff7fbe00000000000000000000000000000000000000000000000000003ffff8ff7f8000000000000000000000000000000000000000000000000000003ffff8007f800
  | 1, 3 => 0x3ffffffffffa00000000000000000000000000000000000000000000000000003fffffffffc1f0000000000000000000000000000000000000000000000000003fffffffffc000000000000000000000000000000000000000000000000000003ffffffff83c00000000000000000000000000000000000000000000000000003fffffff87ba00000000000000000000000000000000000000000000000000003fffffff8001f0000000000000000000000000000000000000000000000000003fffffff800000000000000000000000000000000000000000000000000000003fffffff7ffe0
  | 1, 4 => 0x3ffffffffffc0
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x30582c2d0000000000000000000000000000000000000000000000000000000020402000000000000000000000000000000000000000000000000000000000001008040c00000000000000000000000000000000000000000000000000000000033802eb00000000000000000000000000000000000000000000000000000000001800290000000000000000000000000000000000000000000000000000000000019de700000000000000000000000000000000000000000000000000000000000111000000000000000000000000000000000000000000000000000000000000008446
  | 0, 1 => 0x2008000041400000000000000000000000000000000000000000000000000000049800000f3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000777bbfef00000000000000000000000000000000000000000000000000000000777bbfef00000000000000000000000000000000000000000000000000000000777bbfef00000000000000000000000000000000000000000000000000000000550a844e0000000000000000000000000000000000000000000000000000000044020000
  | 0, 2 => 0x200400800000000000000000000000000000000000000000000000000000000010008008001800000000000000000000000000000000000000000000000000000edb8005ddf700000000000000000000000000000000000000000000000000000e928005551400000000000000000000000000000000000000000000000000000c920005510000000000000000000000000000000000000000000000000000000a188004845600000000000000000000000000000000000000000000000000000810000400000000000000000000000000000000000000000000000000000000060380004c35
  | 0, 3 => 0x9249900804ff000000000000000000000000000000000000000000000000000092009008041c0000000000000000000000000000000000000000000000000000716d8bb802fb0000000000000000000000000000000000000000000000000000716d8bb802fb000000000000000000000000000000000000000000000000000061240aa00200000000000000000000000000000000000000000000000000000050288908005a00000000000000000000000000000000000000000000000000004020080000000000000000000000000000000000000000000000000000000000300580980039
  | 0, 4 => 0x36db66ee773000000000000000000000000000000000000000000000000000002da38dd0e845e0000000000000000000000000000000000000000000000000002da38dd0e845e00000000000000000000000000000000000000000000000000024879cc0600f3000000000000000000000000000000000000000000000000000248304c0600000000000000000000000000000000000000000000000000000001b607b0d86c3d0000000000000000000000000000000000000000000000000001b607b0d86c3d0000000000000000000000000000000000000000000000000001240620c06000
  | 0, 5 => 0x9049111888eb00000000000000000000000000000000000000000000000000000049011088e300000000000000000000000000000000000000000000000000036db66ee7730000000000000000000000000000000000000000000000000000036db66ee7730000000000000000000000000000000000000000000000000000036db66ee7730000000000000000000000000000000000000000000000000000036db66ee77300000000000000000000000000000000000000000000000000000369b46ee73300000000000000000000000000000000000000000000000000000365a66ee37300
  | 0, 6 => 0x125c722f17ba10000000000000000000000000000000000000000000000000000924991188cff0000000000000000000000000000000000000000000000000000924991188cff0000000000000000000000000000000000000000000000000000924991188cff0000000000000000000000000000000000000000000000000000924991188cff0000000000000000000000000000000000000000000000000000924991188cff0000000000000000000000000000000000000000000000000000924991188cff0000000000000000000000000000000000000000000000000000920011188c0c
  | 0, 7 => 0x1b78633f9ff0c0000000000000000000000000000000000000000000000000001b1cc33f9b3ca00000000000000000000000000000000000000000000000000036df76ef77ba1000000000000000000000000000000000000000000000000000165e72af17ba100000000000000000000000000000000000000000000000000012dd722f57ba1000000000000000000000000000000000000000000000000000125cfa2f17bf3000000000000000000000000000000000000000000000000000125c722f17ba1000000000000000000000000000000000000000000000000000125c722f17ba1
  | 0, 8 => 0x249f84f2793c2000000000000000000000000000000000000000000000000000249f84f2793c2000000000000000000000000000000000000000000000000000249f84f2793c20000000000000000000000000000000000000000000000000001b7cfb3f9ffff0000000000000000000000000000000000000000000000000001b7cfb3f9ff1c0000000000000000000000000000000000000000000000000001b7cfb3f862180000000000000000000000000000000000000000000000000001b7ce33f9ffce0000000000000000000000000000000000000000000000000001b7c733f9ffad
  | 0, 9 => 0x3616d6ff2aae300000000000000000000000000000000000000000000000000030cdb6557f9e30000000000000000000000000000000000000000000000000002dbf9df3f9fff0000000000000000000000000000000000000000000000000002dbf95f3f9fef0000000000000000000000000000000000000000000000000002dbb05f3f9f0c00000000000000000000000000000000000000000000000000028bd156379fa5000000000000000000000000000000000000000000000000000249f84f2793c2000000000000000000000000000000000000000000000000000249f9cf2793f3
  | 0, 10 => 0x3ffffffffffff00000000000000000000000000000000000000000000000000038e927447fd0400000000000000000000000000000000000000000000000000036dff6ff7fbe300000000000000000000000000000000000000000000000000036dff6ff7fb0000000000000000000000000000000000000000000000000000036dff6ff6620000000000000000000000000000000000000000000000000000036dff6dd7f9e300000000000000000000000000000000000000000000000000036dff6ff7fbe300000000000000000000000000000000000000000000000000036db66ff7fb00
  | 0, 11 => 0x38edb7557fde70000000000000000000000000000000000000000000000000003ceb27c47fd0400000000000000000000000000000000000000000000000000039e92f44ffd1c00000000000000000000000000000000000000000000000000038e927447fd0400000000000000000000000000000000000000000000000000038e927447fd040000000000000000000000000000000000000000000000000003ffffffffffff0000000000000000000000000000000000000000000000000003ffff888440100000000000000000000000000000000000000000000000000003fff77fffffad
  | 0, 12 => 0x3c3687f62aec60000000000000000000000000000000000000000000000000003bfdff7ffffff0000000000000000000000000000000000000000000000000003afd776f7ffa50000000000000000000000000000000000000000000000000003a34576f2aea500000000000000000000000000000000000000000000000000039edbf55ffdff00000000000000000000000000000000000000000000000000039edbf55f79b900000000000000000000000000000000000000000000000000039edbf55e601800000000000000000000000000000000000000000000000000039cdb755ff9eb
  | 0, 13 => 0x3fdb67fff73080000000000000000000000000000000000000000000000000003f9347ffe22080000000000000000000000000000000000000000000000000003f324fffa261c0000000000000000000000000000000000000000000000000003f1247ffa22080000000000000000000000000000000000000000000000000003f1247ffa22080000000000000000000000000000000000000000000000000003efff7ff7ffe70000000000000000000000000000000000000000000000000003dffbff7fffff0000000000000000000000000000000000000000000000000003cffa7f67ffc6
  | 0, 14 => 0x3fbfdffffbfff0000000000000000000000000000000000000000000000000003f9fc7fffb3ca0000000000000000000000000000000000000000000000000003f7effffbffff0000000000000000000000000000000000000000000000000003f5e77ffb7ba90000000000000000000000000000000000000000000000000003f36dfffaaeff0000000000000000000000000000000000000000000000000003f36dfef2aeb50000000000000000000000000000000000000000000000000003f36dcfa282d20000000000000000000000000000000000000000000000000003f16d7ffaaaeb
  | 0, 15 => 0x3ffff7fffffef0000000000000000000000000000000000000000000000000003fffe7fffffce0000000000000000000000000000000000000000000000000003ffffffffffff0000000000000000000000000000000000000000000000000003fff77fffffad0000000000000000000000000000000000000000000000000003ffffffffffff0000000000000000000000000000000000000000000000000003ffff888440100000000000000000000000000000000000000000000000000003ffb67fffff0c0000000000000000000000000000000000000000000000000003fdff7ffffbeb
  | 1, 0 => 0x3ffff8994c8f30000000000000000000000000000000000000000000000000003ffffcc8640100000000000000000000000000000000000000000000000000003ffff988c441c0000000000000000000000000000000000000000000000000003ffff888440100000000000000000000000000000000000000000000000000003ffff888551100000000000000000000000000000000000000000000000000003ffff888440f30000000000000000000000000000000000000000000000000003ffff888440100000000000000000000000000000000000000000000000000003ffff88844010
  | 1, 1 => 0x3ffffdfbfdfff0000000000000000000000000000000000000000000000000003ffffcfa7d3d20000000000000000000000000000000000000000000000000003ffffbbfdffff0000000000000000000000000000000000000000000000000003ffffaaf57bb10000000000000000000000000000000000000000000000000003ffff999cccff0000000000000000000000000000000000000000000000000003ffff999cccff0000000000000000000000000000000000000000000000000003ffff999cccde0000000000000000000000000000000000000000000000000003ffff999ccc1c
  | 1, 2 => 0x3ffffffe7ffd60000000000000000000000000000000000000000000000000003ffffffffffff0000000000000000000000000000000000000000000000000003fffffef7ffb50000000000000000000000000000000000000000000000000003fffffddffdff0000000000000000000000000000000000000000000000000003fffffcc7fd140000000000000000000000000000000000000000000000000003ffffeff7fbf30000000000000000000000000000000000000000000000000003ffffeff7fb100000000000000000000000000000000000000000000000000003ffffedd7f9f3
  | 1, 3 => 0x3ffffffffffbd0000000000000000000000000000000000000000000000000003ffffffffffff0000000000000000000000000000000000000000000000000003ffffffffff1c0000000000000000000000000000000000000000000000000003fffffffff3da0000000000000000000000000000000000000000000000000003ffffffff7bb90000000000000000000000000000000000000000000000000003fffffffeeeff0000000000000000000000000000000000000000000000000003fffffffe62180000000000000000000000000000000000000000000000000003fffffff7fff7
  | 1, 4 => 0x3ffffffffffde
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 161 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 161 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 161 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 161 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 8 0) :: stateWiresD n (ids >>> 8)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 8 0) :: stateWiresS n (ids >>> 8)
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
  | 5 => 23
  | 6 => 298
  | 7 => 2035
  | 8 => 1798
  | 9 => 193
  | 10 => 7
  | _ => 0
def CH : Nat → Nat → Nat
  | 5, 0 => 0x8f3ca71c79c9d2705d88a6be54bfd8305401883f49d4c43842b779a340da843d38320e97350d14352d5f5e9026b4cf8422358b96199d0bc20d4668180c4bf4d40b305cfc0b00259309955bdf08fcd98f044c281d0075ed250017d736
  | 6, 0 => 0xb5974690b1381eb0ade7e9409d1550209cb0f9c09b1822a09a220080978c773096febba09199978090d77d808ffe0a108f74600086344c9085a20c2084a45320824bf54080e76040800986e079ec839078fcbb0076c1af4076219910723661d071e892b0705b3ba07018b0606b4f6ce06b41a430664243105d136d0055db91b05339f3805323e3c04ff64a804e757f304d906b304cf795804cc2bc804ca425a04b6af5904840c50045d68c50441cefc040abcfc0342f57b03427c5802dfdd6802b5423d028214ff027dfec601c5b2ea01be7a8801b4ed2e017b6151016dc25601607961014dbc7301180d460105e6ea00f67a9d00b294a700a9e323007ac362
  | 6, 1 => 0x1a208feb18f9743718f3b34318cc188118b45e2e185fc41e185e97b0181297431809c6db17baa4f5175ac3f117286fc016b631e3167ce6481679ca5b166e18d4165b479d15fd4e7415b3c3d0157378ff1518d6fb149251cd146f30b713d6e819136f20cf1364153b133dc9e5133d4de11338cb651302a2c1130000a7126fee8d126c9156125bfe25122bb7001181924111417f60112b9bcf112237ac10e6177810a6aea510870e60105807271048b689101a9dc00fe1e2df0fcdfaa40ea8d1c10e4725b10e2964a70e266e680e0e8c690dfd39ce0dd527340db927eb0db432850d3f24990d31bdf20d2d3ef10cf9fe2b0c665be90c2bd6d30c1c0da50bebd6d9
  | 6, 2 => 0x3404b2bb33f1c94f336e541d3333b1573302234230a67ff830432fae2fd7c33e2fccf43f2f52fed72f4dabc42ec193482e6879972daeb2ee2da850e52d7f74952d0fd3a02d0f5ec12bbcdef72b72dbd82b20025629bb8f2029af2b642986ccde297e93262937eecd28eeaa2f28434827270d7747270b4bd626641523260717a224e85867240f6e2523f9e0f823f05bf6234ad4292317535f22ca696522b032c921cbbf912157602a20c2582d20b341ba201b2f94200e91291fda639f1fd480731f759d891eb4b16d1e9dd0701df3ea901d8638ee1d2d75851cd669401c2bc20e1b40b1d51b0f44f11ae83f6e1ae253941abf79bd1a5cc19e1a5776141a521cb3
  | 6, 3 => 0x61d100415ee4680f5c8317c85ba723af57fc4c1f5777d1b856e9ca3d56dc863e56488c3a54b63b1454750e6053ac99bc53120c2c526ba68f5254cd9b5254bf3051bf9d7e51ad6dce519131b1516cc8ec4f295b164efa14d14d84259f4d6ed5974d692afc4bb4b4eb4b3f5809483370a14752be7f46f2450c462cb5a745a7f59844e7746344a9fdcd4481ffb644156ee343b0155642daa43342b779a340e7327440b92758408559643f439e5d3e8f6e5c3e6bf1373d9c07413ce84c383c29efb73b7ffe003b40495b3a4fc20639a011fc394c6b873904497e37ca88eb3729fbc236f0d9893617550835b2fb7e351a98f534f23e6b34ed928f34d8f51834a502dc
  | 6, 4 => 0xc76f86bec0b7919bbf6ffb7bb9a1ccaab3c66f4aaceb13cd9ce9ebe69ad9fd9498cdfedf973d10ed96cf86f790e857ee8f015b068d11d9348a80a9f98400471b7fea369b7e0e28c87df728617877af9a7513e8cd74dbbafa71e7c10f71e1d44170f5cdab70e8de8b706dd8946f5e8b526f24edb76e3349916e2dbff36e2304016e1a97496d33441d6c2033276b2d152b68bb596b64ecc52164c725bd64a77576638bebb262950bd9
  | 7, 0 => 0x1eb568701eae92e01ea850001e9a20901e407a801e1442101d9077d01d8fdb401cde88101c41b6c01b4fdad01afeb1401a5e674019ff1130194f39b018d2a8b018b2477017cbcb1016f0120016bff2801675260016603570164bc860153195b0141dc9b0139ec00013937b501382f160121a1a1011daf4c010863550104979600fe0b6c00f5cdbe00f0084200e10f6d00d96c6900cee76500c9fa8200c738a500c447de00bbc06900ba7b0800b1af7400aa5b010096cde7009613ef0092b8cb008e7182008dbf67007c6c3c0074da310066198900629024005195c500431774003de4880030e2e9002d875e0027e56d0027347900247b65001b8956000a8106
  | 7, 1 => 0x3af605703ab200c03a24d5a03a019e6039863440391ccca038da68a038ada5c0386747b0383e2ce0376a2da036daac90364d3fb0360499b035e79f803547e680351f98e034095b5033c7fcf0337ec89032fe7d0032ea2bc032b629403229abe03222c490313c39d0310c646030ce361030a418d02f84e7602eebf9402e1387702db950c02cec24302cb849b02bc5aba02afd61502afc2dd02ae186f02abde4002a711b7029abeb1029980f30294122e027bbd120270867d02600d04025f9aa9025d5eeb0249a99b02425043023e0b58023d64df023a73870239791c02305bab022fed3d0229104302218065021b751b021054a601f5829501edd3d501ebdb57
  | 7, 2 => 0x52d31380523d5e5051a1f0e050cdb7e0507b1cc05079c110505ca7204fd562304f9a6df04f93ded04f93b3e04f74ed004f0b24f04eed5e404ed0ed504eb12b104e8fd4704d68c5c04d10ea104bd24f504bca65904b8dd3d04b58b1604b41dcb04aa780404a9f24404a8420e049953cb048d22d604899fd40485d344047905040477450604773d45046b4152046672b704664621045412d00453cecc0450d3430449a1a3044479410442bd86043e340704372bfa042ce527042c8ea5041ecf40041db66f0419ac6d0417b4c604152b6a040f1255040779340400a82a04001ea903e44fed03e1317003d81ef903d502af03d37ec903c9b0dd03c518f303b5d8d4
  | 7, 3 => 0x6aacd9a06a2bd31069c64700698c01b0691115b068bb79a068361b0067f0789067c79860667fa740667948b0661212d065d6775065c130a065b89350654a04d06446257063e1531063bed890638a75e06352c460632a6c1062fa928062e761d062b81aa062ac73c06291d830625ad8e0614b9e806140605061043ec0609632905fba26005f3e6d405f3c93705f0b0fc05e231e705d65c1805ce284305ca702105c62c4b05c1efa005be7d8b05ac474e05aa69b005a4c3a7059615f60591e7f3058c4ce4058b87760588a7a8057fd1b805763b220569c1ba0566d97c0561ab61055f3af5055d8310055326d2054f0a5e054c13ba05425934053f9f860536e2e9
  | 7, 4 => 0x8548af608541e9b08393148083634c8083466900832259f08300d35081aee0508191081080f0604080d383f080970e608071aa50806945107fef41d07fdf50407f1b6d607eb0cb607e84f8507e80f7207dea5a907d976c207d3b7d007c4a69007a90e7d07a7e49a07a53b6a07a1503f079a7492075c38fb075b55ae075af7fc075388ef07423af6073b18bd0739ab2f07360df7072c4857072446ef07173785070a69920701913106fe702506fb896f06fb651706fb132406f6939e06e4336306e1f2d806de3c2406da441806d5cca306d5aba406d2ca1d06d0bdb806cf784206cb2b9606c4ca4306c37c9f06bf327006bafcf806afc80006aec22b06ad5f3d
  | 7, 5 => 0xa6f15680a4c2aff0a4794560a3f0e900a3e21780a3d76200a3be0860a248c6c0a1a119a0a1773310a0f140a0a02a65409f8c20209f5ca2f09f2dc1f09ee1b6f09db435609d3998309ca8ffa09c9c8cb09c539ed09beee1709b9ae5709b7f5a609b77f8509b4283b0999793a0990cf55098632490975baa10966375d095f9c53095c24900956f2670955f1cc0950d81e0949cbc5093a21a409289d100925d5bd092458c9092438e1090f60f00906db6408fdd6dd08f5ba7b08f3866f08e41e0608d985c008d1d70008d0d94208cd578908b4968208b342b208b2f9fa08b0e2a508a5b280088d35b9088778c408828e2d0882854308719c7308713183085f46c7
  | 7, 6 => 0xc76a82a0c69b8af0c669c520c50a23f0c498d8c0c38b8b50c36785b0c35bd590c2ec5760c2525e30c236eef0c095f380c0192bd0bfebe550bf660dc0beba3c40bea14e60be0b7bf0bd56c910bc7b9bb0bc0dbd80bb2d5f60ba1b9670b9fb2450b9dc5d60b9cc7030b911ddd0b8c138a0b843af10b8088cd0b7a9fd10b779d3f0b67a7b50b6441e10b5277e10b52590a0b50f6140b4240350b42145c0b420c200b236dfb0b21436f0b1e24e60b1b8f680b1b13770b12aa570b0905e30b0290b00af4294a0af091190ae653d70adbffc90ad5b9480ad000ed0ac245eb0abb1fd80abaaa930aba5edd0ab8b2690a9e9ea70a95fd7e0a944ae90a78fd900a711aa6
  | 7, 7 => 0xe1cb4fc0e1601f30e140dfe0e104f000e0a0a960e00b84d0dfeb0e30dfe9ae50dede7600dc879c40dc23f740dbb486d0db9c7830db753420db51cee0db3e0ff0db2499c0dacbb1c0daabbb60da1a96c0da0a9b00d9e5caf0d9cbe430d9a232f0d953dcc0d8c34570d8604340d8449940d7c9ad40d652ead0d61f2fb0d61b55b0d5511820d539b590d538c970d4b8d630d4169a00d3e6b910d3ce73e0d28c9a00d2245fd0d1a412b0d16f5830d167a100d0dc8b10d0ad1ee0d0a24500cf439bf0ceaae430ce9653e0ce25c760ce00ea80cd790180cc4a3ca0cb8201c0cabde0a0ca746640c99c0b30c8f063d0c8c75f80c7ee2000c7bcab90c7ae5250c776116
  | 7, 8 => 0x10770279107263c110687cdc10631ec7105994fe1051ac77104ef361104eafe0104c6eb7103c9cf4103026951023760a102341bc1019b52f0fff0aef0ff6fb5a0fe3a7f00fe047420fa5f3930fa490880fa22a3f0f9e1e9c0f9d2bea0f9aa5fd0f99f08b0f895fe50f7a34970f6b9a140f6930270f68cfcb0f67f4c70f616c690f6063ab0f5db08c0f5a619d0f480a240f28b6120f253ce80f1883e90f1277880f124bee0f115ba20f0bfef60f0897250f051cdf0f02939a0ef426f40eec78340ee7c6930ee623630ed31b0b0ece5d980eccc4fb0ec4c2d30ec080630eb7194b0eae29770ea9d03f0ea5b0b60e4ddd170e454ba90e3408940e2f32100e226414
  | 7, 9 => 0x12ae999912a445e4129e8fdd129b35b41298d76812961937128e6a771276aaba1273365b126bfdab1267f2851260d736125be58b1259a0381237c6ff12324797121fcda2121f2e9512193c591211af41120ccbc51202377311ebedd011eaee2211e0b49111da9b1111d80b6011d6c16011d306b611cae9bd11be821411ba04f211b18ddc11a27164119bc654119a093f11981144119326cc118f23961186437311786599117230c7116636fb11662b47116434dd115f0595114ac7de1146e0a91142fa41113a2f5711393b7e1126a39c110fa229110a841711065d7d10fe408d10f0423b10ef660310dee38510da06e410d2047c10a80043109d115610899ffc
  | 7, 10 => 0x152a36761529b670151620f415087f681502cf80150090a014f9191914f16a5914ef082814e0d35f14db292014d3021c14c37a0914b72e1114b2203f149f91561499cfe5149753841483b353147a76d31474746e145f520b145d552b1455c91a144f2ac8144f1120144b2733143eb91814393d881435d2a814334a7c1428c40c141ad29b1417646213fe7f2813fca81113fc25dc13ef3f2713e90d2b13e157aa13bd6b04138aa7c613869fe5138050e2137ce110136d2515136997561366e28b13669e451361706f1356a1bd133fd8f61336d93b132858f71325a18d131b4dd1131a7a561301e7f012d7376612c74bc212c6a9f112bb814412baa67712afdbe8
  | 7, 11 => 0x1748c128173f749d172cf8621729918f172549a21716f6f91712096e17089116170619d11701656116eb0e0416e723d816dbf17016d740a716ce01dc16ca45c416bb8312169191a8168d9524168aaeb216808bd7167dfa6916718ae71666c6e7165eb6bb1653aed21653985c1651a55e164a2e7b1649df441640de2b163cc666163713421631eb8616251b2d161013b4160fd85d160c315a160899b91608592015f4eeb915f3a94215f38b2515f06ebf15ef334b15e7848b15e6d03415e491c715cc3dc715cbb5d415c5203e15b8b36c15b2999c15862d0f1581f8c8157cd5101577792a1572ee67156a912f156445b915602014155e283f1544b83f1536d015
  | 7, 12 => 0x1984d184197c445219737dba196db0f1195c2e3a1952ad48194d6d471949aaa2193875f0193459ae193154df1923eb0b191fb9ad191c3e0a19191c16190d1e2c190a1b2718f6904118ef546318ef3ee918eb074b18de3a1a18dd6c6718c40ebb18b8672d18af348718a94c5918a7b1471895650c188fdb461886faae1881f686187b027f18696a3f18608d1f18506a8718349b3718296ab818261f781812dc1418103f88180b2d5417fccf9d17f99b4717ef437917eedd5217eea81c17ea453517ea003b17e7c6aa17e26cb417e0c63517db42aa17c75ede17b77a5217ac6ebe17a7128e17a514d3179ec817177f676f177360bf176424311760c83917534ed0
  | 7, 13 => 0x1c17861a1c100bfe1c0fa63d1c0690031bfe75ba1bf0c1dd1bee157b1bdc96161bd8c8491bc7fbbc1bbebb881bb3e7b31bac32b71ba9ade81b96c32a1b9216511b8d3bc71b8bbd5d1b89e7b61b7d0e751b7baaae1b6d95da1b68fbf21b38367f1b3816031b34e18b1b251d581b204c261b18873f1b16f5ed1b162a401b10687b1b0feb161acbab401acae50f1ac53fcb1aba67151ab556181ab193a61a9ea50b1a95deb81a9399f11a8ab1011a888b681a7eb9de1a6495481a21bc441a1a0d841a11b0891a0f2ada1a01ee9319fcff4c19f3b12819d68c4119c018d519bf159719b58f4419af892819ac383819a7dd5b198e113a198a3ce51986e6721985f02c
  | 7, 14 => 0x1eb3b6011eaf2bfe1ea8dfff1e9897201e8905ab1e74a5ee1e7359ed1e72be5d1e6910661e5864dd1e5126551e49b66d1e3ffd281e3b2a791e3aec7b1e333dbb1e2da59a1e18d3b51e08e1531dfe75451de420bb1ddf72231dd791df1db0c1da1dab7e8c1d9120861d8bd8661d801b291d5d62181d50fa051d4c65d31d3cb8cf1d3844981d30d4b81d29fe0a1d1cc69e1cfd45131ceddfaa1cbbe72f1cb3453c1cb26a701cb0ac851caf0a401cad31121ca8ab271ca325351c91a9b81c8f981b1c8d42fd1c8ae1541c88dcfd1c70375e1c6af7f01c69f6a41c65ef861c64a6121c53c4361c4a85d91c32d1461c3226781c28900f1c217d981c1ffead1c1d3424
  | 7, 15 => 0x21bc3e9a21a7b57b21a51182219914502190cc6e218c6d472185f9482185771a2162b66221475d352145ca59213c167f213bbced2121ef7d211cf30c210d1be720fd746b20e249a720cf09ba20bb3abb20b256c820b11b4220ab0d7f20a099e72083e9b020810030207e9d78207a94ac2079142920734b3420727e4f20505858204fb0ae204393dc203dbfd6202e5036202b5019202950d92025af5b1fe748c41fdfdfd51fd3c25f1fd0e92d1fb5c2461fa82a8b1f9ffbbb1f9f27891f8a96fe1f8144da1f58531d1f5137c01f4ac3c21f4278e01f3bc7e81f395fe91f25d85c1f1fb39e1f0740291ee7182a1edcdc371edb560c1ed8d4fb1ec20fa71ec0d4da
  | 7, 16 => 0x249369e42490943e247bfc70247b9eae24569a8b243e501024319577242c02932427bbb32424176423e9b7ce23e8e0ac23e3e51a23d76fdd23cf4c0a23c4c09923afded123abc3e9238533472376a87c2367e264235ecc372332695923308957232c6add232bf2d923155cdd230fc2b3230defc9230961092302c01b22fffe0422fd802e22fd1c0c22f6a00322f2f0d722d0938822ce96d722cdca7c22cad95022ca5fed22c7351322c301b722a7ae7922941a3a22906c3b228c6b7a228a845522840592225d9fc222430806222e86a32219ec0a221818aa2216eb44220d4779220b132221fb1e9d21f78a3221f68a3521f30eaa21d2159921c6f27721c2e116
  | 7, 17 => 0x278cf569277bd4de276065ab275cd232275cc72a273e39ff272b4554271c085c271b232e271a957c2714599c270c5ed526f5a46126edf5a126ed0b3426ecf37e26eb9cc526e23bf026dec57c26dab06026d8417526cabe3226c75f7726c09f4926b374c726a9305b26a8efc22695661e267c3f24265d50ef26540f7726516c982649bdd82647cc2a2629777f2627a39e260cfa4e2602ca6f25f4cce125e030e425d56e8125d4f17425c58caf25c35a2e25b7b84b25a73e9e258d7136258d1dd62578416f25699f88255dff40255d906525599462254295f92522b4c2251f31c02512af42250c1fae24f9ef9824f0d78c24e5186e24df459424b54bd424abaa20
  | 7, 18 => 0x2ab77fdf2aa4ee212aa1005d2a9d51a52a9d3f612a8cb8f32a74c2682a71cc3b2a6568252a4f24542a4d11712a1fc85a29fbf4ba29f7871929c4b1c729b62f0f29a4bf20299726e3299230642990a1762979c675294e63bb2937d36d2932f574292330df291438012907065b28d45afa28d0a80228c41c6328bc0b2028b4110828adc56628a803e728a5392c28a4a83e289f02d2289bfdf62899c1c728974a9c288e242628829e812882233c28819c6b287976d82858d837284b61f62840ab0c2840a711283f347028388f0f28297e7d2821b66527fcc69d27f4e50027f2645b27d9de4a27ce579127c5b54427c480bf27c4186327b671de279bd5242795120c
  | 7, 19 => 0x2ead5c382ea785652e9b58932e7b51fe2e6df2382e02b0672dfb01a72de3b8562dd94eca2dd16b5a2dc8960f2db6afde2da536eb2d90db782d9031c42d8f35812d7f0da72d618f3b2d4ede442d0fb9a92d00adc52ceeb2b42ce59c7a2ce2146f2cd2d1182cc2c99c2cbb1adc2ca929c32ca2aa672c8be2dd2c6c88432c627e712c52f7e72c4f5f242c45359f2c40d22b2c3d43922c298c242c23e8932c1ddc852c1a4d4c2c19ccdd2c18fbee2c12e8b92c125c0b2c0d993c2c0513e62bdab0db2bbe1e7f2bb3a1482ba37c1e2b9e97cf2b9c0e2b2b774fe62b711c6d2b52aa7a2b3720452b266c0f2b0550fc2af11c402ae5ffd12ad9fd9b2ac252e62abaa426
  | 7, 20 => 0x32ee34ea32dbbbd332b2b34b32a8c61132a42be5329a9c0132888f2d328762803274046c326c2260324cb2a3324735363236d2b33235785532313fb63205cb1332046c8431fd931f31ec555931e6253a31e192ad31de767a31ca85203177ea883175fe8e316f205631472fc2313951c131381b073129ad3f30f3d61930c4941030accfa430a90ad03080893e3078da7e3068e8dc305b209f30532cd8304dc1753037bc2b3031bd6b303037e92ffa480f2fe825322fe1018e2fda21de2fd5f91c2fcc0be22fca01ca2faba6b72f6b6f362f55da3b2f4e2b7b2f49ca702f37b6b72f15a0e52f1362052f03af3a2eef6e412eebb2f22ed934752ed185b52eccfe76
  | 7, 21 => 0x389688f838871f30385d4fe03829edd43821da66381fcf14381a434737ed01fc37c5ac3a37b9a608379d7233379431c337904a76378345ed37809ff0376a9e86375114fe37405e0136ec0fe036cead6536ad538a36ac6528366fa2723661748c364e45583649da1135ee51be35ea07c735df972735936385358ef95b358e7c13358b22373589df13355171d6353d89183533b0a735296cd2352183cc352081d9351ef782351008bf34f1eb2334d17ce534a73f4f349cd7513484d113342b6ca434271d9a3422b20433f599d133e9c82a33e6ba6133d93c6b33ab4e0f339fdcc23395d87a3377f3813340d20c333627fb332521f73315deda32fa2f9532f0fe10
  | 7, 22 => 0x3dca66533dc7f2d63dbd78093db22c033d7e78233d60b2ba3d558b723d4de0dc3d4990dc3d390dcd3d18139e3d06104e3ceffe5b3cedcf813cda06bb3ca9e5763ca6e7a03ca59dea3c7228023c5f55e03c26c65e3c10aada3bff38bc3bdcd5ad3bc619df3bc2c8903b92059a3b8d02ab3b712aef3b48e60b3b252c693b0884e63aff7a483af2e4423af1f0e13ad81d543ac4e1a13aae6bdb3a4e7b353a20803739f25cd739f206c139ed718839d30efd39ab679439947c5d398e5a4a39851ade396d9dcc393ee8d0393d17e83939bb7d3935a718391c8c9a39157b473910b9f8390dc5a639039e9a38fbefda38f877d938d90ee238bf1bda38bbb16438afcb0e
  | 7, 23 => 0x4264dd9a425b3eb24254886b424d69a14248a3a042331fc7422f72f34229f073422289184215eae741f044c441e31abc41df69bb41c88af741c59a3741a7bf2d418090844166a38141649ba6415a4d3f41532fd5414b8115414a02b24120806d4116e99440f3ba0e40e9a1c040e5429a40db9c8640bb17b44081983040455b7a4012dc343fd055303fbb24c83fba991b3fb453853fb34f8a3f9d16073f9a6dfc3f3d1c973f356dd73f2afc363f2a4bd03f291ad13f0c84c43f0291233f004f3c3ef04d583eebbb0b3ed959463e732aca3e692e3f3e4b1a123e4437d33e15c25d3df964133df803263df61e603df0d3f63df054663de031913ddad2813dd921fc
  | 7, 24 => 0x478fe0964779338347722ff5476ae3fd473c71644712aa5547076e0f46e8eecf46c9384346af4156469ee88e4650d899464d91074645dba5462000d2460ad92d4600692846003a7c45f3a0a645ea3bb645d4474945d0240a45c03e8f45b7253845a7b09e456d4cf9453fa07e452f8bf7452363a745220c60451d0a794519cf8c451538d245009c2a44c3b45c44ad1ab24497cd064473ea7944540250444155d54430fb224411b29043c2d92443b05eeb4399ce9243765905431fa0c14313487b430ef05c42fc329042e93c6542e5d56842e2365142d78fb042b779a342b7323342ad25fb42acc5ef429d7e914297c49a4286bbdc427fd3b5427f0d1c4265adbb
  | 7, 25 => 0x4fc74a1b4f70d3ce4f3e22494f379ed14e3fff6a4e362aae4e343c884e325fa54e29c7d14e0ef5284e0caf094de141eb4ddeef6e4dbae5c44d66e8314d1a0f054d030a514cf86ab54c7afbba4c77c2484c760f734c6803874c30865f4bf5f35c4bc1a5b64bc0263d4ba95a224b95f3244b89218d4b32e3914b2192414b1cd1974b0c2c394aef3ad24ab8a8cd4a913daa4a750f2a4a41bdb04a359b0f4a11a36849ffe09349f0117b49a551a3498effba497e48c7496742c3495c281c494604bb4929324048e95ffa48b7485148a1586d4890f85b4873e3c94852d2c8483862e84834c8654812971147f86ed947f2aca647e3c81a47cdfe5947b90fc247abe42e
  | 7, 26 => 0x58cfc36c589fb1d457cb0a3a576b574c573c09a65711b93d570099e656a7360f569d18b3568ff7f15647456956338b5955e6dfcf55a9c71e5576aa08555e244e551556ce54f5440054d391cb54785c5b5476a805541e754654147764540285f253f2805153f23b5753e59131538f7c87530ec13f530c85d352ff477652fafd3a52d59e6752ae109a528a8ae5527c70b05274e10052747f075253778352470f8c5246623f52427e6852423451523dc2115233ce035205f6cb520402fc51a1126f514bcb6c512a1171510b684c5100e5db50f78d7850de749650c755c150aca6415097eb6a5065269e505caca650407b6b5014987b501478a24ffcc3574ff79a30
  | 7, 27 => 0x61f9335c61ee545c61ee251361ec620e61e8177e61df61126157bdb8613fcc2c613bc6676100b5d460bfac9d60ac09f4608901d56075f2ad60605fa15ffb56605f926ff35f8196225f545a425f4d47335f390eb15f1a0d195ef317bd5ee1fdd95e8c39585e7f86105e4d64025de88ff45ddf2cb65dd08b735db7f7b65d9cf3735d903ee95d87b9505d71535d5d6636025d23a0205d1d69a95d062afa5cc6982e5c9748e95c50bd215c496fc35c403f355bfa1aea5b80adc65b3d881e5b3cabcc5b2acd595b0573375ae254525aba144e5a6f8e8c5a41d7535a4142075a0e560459fab7c759e0aa8559d8fbc559ce7bdf593bd8a85925def159100b8058e13672
  | 7, 28 => 0x6f8846bb6f6fefa56f4d65026f1884f46ea4ed216e8926966e65b5e26d91e6cb6d88637c6cec6d296c8ab5f66c899b716c6bc5066c55b8296c4b6e046c0d62af6bf58d8b6bdfeee06bd670bc6b1645536aa2936769e2f55269db469269cc6ab6697e5fde69795ef368f9456268ef535068c42c276873c5ee68716f406822a36867ba6fea67a9ab2a67a7b8ad67970ff2676f8c8b67234abd66fc07c766f45dff66f3f9df66f1de6466da558d6692d3a26617db0a659d2eef659a838865900bb1655e31bf6553eb66654c3ca665413a11651506a464f1f45764d28813648acbfa641a661e6406fa8e63e88db66397aebc63294eef62a21d51629ab83c626e480a
  | 7, 29 => 0x80cb45e17f78bc997f649aff7f204e527efecce47ea032ce7e397e847df7ccc67dcb9ae47dc3ec247d3d749c7d17292d7cfdc0b27cea112d7c95abe27c83f67b7bf756107bdebe1b7bcf7fc27b4052e47b12d9827b0b2ac27a9a5d427a0e62c179e15a2879d538887920d8f377e62da777d135d077c4cd17779c985d778dd668772ff9b176b871ac769b18e8760c3bf475f381fb75c7461375a3d767753de234751f1145751afb3974bafcc07499cb5974933b7573ee804c73edb81573b9da95738ddc97734eaa0d72ba42dd72a080fd72157d2371bc8fb87193daac718ef002718504747172a408711337c170df027a706912bd7035928e6ffb50266f96cf69
  | 7, 30 => 0x9ecd8a7d9e9b0dc19cefd78c9ba712439b7186cd9b5d65339ac95d2d99ac1ae197abf38f97730edf972eb7d79614c344955d4f26955965c894e56e849499c43194921e3b926d914d91b4a98c915555f0913f335d9126da2890f610e69070bde8905b2ff7905247c78f8075c48f02b7318e97abfd8e91b5dd8e5d91b88e381d3d8da947c18d8dcb358cedacd18cd7ccae8b9326f68acd917a8a89ccf68a81f0ca8a7994f88a40df69899f5c71897343218949899a89359888890ec3a4884e825d87fd89c387315401871fde8584d9c35584c6598884a3c7ae845fbd828393599182fdde2f82f62f6f828b9dd6825093c0821a8c01820c325e81ed8abd81e3502a
  | 7, 31 => 0xf572b552eee316b9dfb2a488de753f3ad96e1605d60ed397d1ab6ad7cda5896dcb6ec6bdcb4f916dca356579c8bd1cebc428ce83c3b854fec36848ecc111313ebf160387be4be64fbd8c29bebc585a51b9e7f9bbb8b7aabcb75f5d0cb64e74f9b4af3a0cb25eb67bb05afbf0af7d2643ad64f2d1accc87b3acbe19ebac142e84abfcb759abba5abfaacf12c7aac6924caa907631a8cca005a84d84a2a7b386c9a68d7567a643c3aba621259fa4cf8df7a397efe2a166ff36a15c99b8a0d28d89a0611847a046c73f9fcf3c72
  | 8, 0 => 0x1a92c6a01a5e67401a17b6b019fd767019f361a019c9fad0199f66e018d82f30188b4400187e4b80185b8510176493d017221e4016a9c2f0169bbd50169389d0166035701652a320164c742015fcb3e0157273d0146034a014268c7014098d40140276b013e7eeb01390b490136f63b01362432013529dc013364f2013290820130dbe3012f4aea012a58400122abad011182d8010887b30104b2f200e17f3d00df762100dad07f00d3cc1400cc13db00c4d48b009728bb0093be3100928629008edf4b0082caf9007bb6a80077b62200627f6900506560003b060f00300e87002d875e0029bfef0020e9ed001e358600102fa70008482900062fc4000008a9
  | 8, 1 => 0x3ceb67b039cfbfe0392a76c038afc7003811d6003752095036f4449035af9f1035987fe03540a5f033d09ee033cda49033b05b5033a727c0323c2e30318212203128307031242510310cef3030a418d02e6e70d02dc927b02dbdddc02d62eff02cc81de02cbcbbd02c5e11702c2f6a802c1a83e02c0cfe002bbb44a02b85de102b24c9d02aa9ddd02a48087029bda2f029b1ac40295a270029474b5029369ee028abe9e0273a18d02712f6c026249d20261fcae0243255802363de2020e426f020c3aa7020b934d020b7f940207f8d401f8826501f71a4e01f20f4b01edb21001eb742001e3cad001e3617e01c6a2fe01c6588901bd8c9c01b879aa01abdea4
  | 8, 2 => 0x628190a06237d4e060e91e7060e01a4060d5ae806062f1a05f21a4805ce1e6e05c1c65805b8980b05ad2f3405aa32f305a5230e059bc52b0590ae57057348a2056adc160564ad43055a6bed053861c505358bdb052aa495052553690519ba9805169eb005161939050f51470509fa1f0504b03604e37e8404d56e3e04d4fdbe04c6564704bca65904bbe67504baedb104b8776804aaa2b004a24a4004824cd404741fde046d4a9404608888045529d3045263e6044a330e0443ecb60442bd8604427f4204427d3b043b8ee20424bd7a041ce19a0419fcb10418d2d40416736e0414c3b204097c4004075e1303f2f3e503e9aa6c03e3645403e2459e03d3d7d6
  | 8, 3 => 0x7ed8a3207e4a71a07e2e00e07de775107d82e3c07cb1c5a07bad17507ba7de007aed42a07ae0a8007a48c6f0791067d0781d5aa0776bf9c07708c780754ea15074e929b074712570737882a073280f7072fd28f07294af207246e590720ca0a072091a80715437d0713de1e0706b5090702ccfa06fe4eef06fc87e006fb5c5206edb28506eccccb06ecbabd06e403a106d1f76806d0ce9106c4169506c0e84306b1cdce06b07a0306ab172f06a8768f06a7f42c069d0f46069a0f1b0694f3f9068bc39d06735b22065dc92d065d568506590aa306540181065356080651e1ee0651b5d50649e88a063f1039063b02a20638a75e062e31230629869d06291d83
  | 8, 4 => 0x9e00b0e09dba5bc09ceff1f09cdd40009c6254009c0e32809bd51ef09b8466109a4e13c09a293c809a1eff20989c7c309895a0909809261096e5dcb09643bad096433860962517709514d1a094cbbc209453e530940e2fa093e73560939c3420938390c0934d1df0933a706092857320917304309144340090dfc8408df973908d1f95708c64fa908b0816608acc47708a96864089e73320899ab5308922ec4086f912c086d870f086a62660865d84f08645e6e085e2e4f085c29ce08567f8f0855da91084f2e670844bf830843d90d0838a6aa083843fe0835ef33082dfc990823ecce08218eae081fee27081c74db08137976080cde01080098ce07f684c2
  | 8, 5 => 0xc118c0e0c068de20bf986140bf4143a0be70d350be629020bd70bfb0bd3d3cb0bce67220bbeefae0bb0c3ae0bacc0a50baa9f6e0ba8c1380b9f7ab30b9beb890b9906dc0b8ad6cc0b8557400b79501f0b76e6c50b4054e30b3a012a0b2c8ce60b2a1cbe0b2912830b2179b20b115a340af89e950af8629e0af197a60aee90220ae653d70acf09dd0ac7610c0ac3727d0abe0fec0ab8b2690aad79ad0aab57e90aa24dd10aa20fda0aa03d900a91be7a0a8ddcc60a7677f50a760a120a7503080a72c0d40a6b07810a5e33fe0a53c4d60a4d41140a3f62350a357efd0a21bc5f0a11d47b0a0589ff0a0093ff09fa548f09ee1b6f09edd67509ea0c3209e06443
  | 8, 6 => 0xe506cec0e4fd72c0e4ddd170e47f8fa0e3485300e33cdf30e1f184a0e1ee4940e0d4aa10e05ccb20dffd9080df6bc470df565b60df435510dd633720dcd46f30dcba9ab0dbef1f50dbd98870db432850da4c7640da096e80d99557f0d98ed0c0d886c890d7f85ab0d7bff170d77c12f0d6e7ee10d6b51460d61a76a0d570f570d49c4170d403ef50d3586890d30f2bd0d2d0b360d15c4ae0d0342060cfc12980cfa3f710ce5939c0ce58d890ce532530cdb7c3c0cbfbe790cb5d1bd0caee28f0ca1c8fb0c8652e40c825c970c81c3a40c7ec55f0c7612850c752af80c6ed2f30c6dad090c6c3e810c5a1d180c498d8c0c481a120c2712710c126e2f0c11f689
  | 8, 7 => 0x1041a16b103c6a2a103759ff1030c0c41027a05f101bd14b1015aee7101570c31006b7aa1004efa20ff651070fe3ec250fe0b3340fcab1080fc0296e0fbe5e370fbc34270fb5b95d0fb1a7760f97fa180f9788b90f85ddb20f808c130f6bbeb00f6688620f622c520f5d31720f57b71c0f56ffe60f561ee80f53334a0f4913560f3efdbb0f39fae20f1a8f2b0f19aa690f1986a90f1768830f16fff20f0b94d40f0530010efe93030efdb5f50efa1ffa0edda4000ed84a080ed0dc180ed09b480ed019dd0ecc811e0ec663f10eb1f56f0ea5796b0ea4e4d20e974d5b0e91bb450e90cf7c0e8cad150e7e15130e7662f60e6aa64a0e6017590e5e65eb0e5e4bcb
  | 8, 8 => 0x12ef861112e7efc912ddb43412cd229412ca98f712c918bb12c2664d12bb814412b84c6412b79fa312a8595d129d33fb1299030512865bc61286558b12780e1b12780deb12755e59126ef838126512481260905e125f53bf125d63881256a112124f1e9d124d6d631234695d122e199512245a68120ffffa120061e011e25e8c11d0a22a11bd50f411ace6f711a50dc91187183a1178a932117804a4116a5cb2115fe76d114e5646114c695c111a0a1811171f8f10f1ff2410eff4c910e4996810e1c67010e0c77910de35ff10d4dd8010d1aa9610d0a52910c8485e109bbfbb10975979109410fb108c07a410763c72106d0df8105e7e0210534db3104af7d6
  | 8, 9 => 0x15ff0cbe15f20cb115f170d915f06b2915e9498b15db995615d9fa5615c1920715b1485615af65f115a578b715783ade157822911575f6c7156e00e1156de64c1528ba3c15228c0d15211ab7151333d914f28f0914e2d7e014db292014d6793d14d18f9714cd9d8a14c66a6614bf256814b7736614a93cb5149cd2011499cfe5148dcb13148a4f1d1489d3a51480f23a1480a01f147f34921470b50714663ea41464f488145f4c0414594a531433d37313f2b9ea13f1fce213ea83c213e95b0113cf2a3e13a311e5139b58061393f6231391ba18138ed0721372876d135a40e9133b38311338a81613346ed1132cb0651326d3ae1311fa7c130fda9f12fdfba2
  | 8, 10 => 0x1895e2741883330c18787ffd1875a700186ca664186a18db185817e918559aff18545dd6183f3731183d9b1f18261f78181bf3fa180d853817ff782d17e7c6aa17e4ed1917e4d13d17d6fff417d64a9117c9e76e17b0da9817a3f1f517a293ea17a23984179c6b2317919a031788409d178832791783de7d177f32be177154d617652ea81758080a174e451d1713a0a5170e1ff81709ad4d1706a80517061d20170036c416d77b9d16cf36c916c1c28216bb0e8816b3f65e16b01e54169d5b1c168ec17d16887c5b168712bd1684358216832647167ca1be166385a0165a1433165990201658d80a16446b9c16355145162da28516100cbf160d2d48160c7aef
  | 8, 11 => 0x1b2f9c521b2895741b27d2611b2600e91b1713e91b163c0e1b0c66d31b0c62171b07696d1b03dc951aef82201ae9b4a21ad7fa621ad655ea1ad308351ac819931ab9ca631ab658ae1ab2ed341aabfc421aa4c0531a9df1a81a90e4691a8c85651a7c026f1a76d2ec1a548add1a36d11a1a1cf3441a04d97919ff9c8019fc1ed919e7001819e4529a19ddb2d519dbcad019d4c81219d2ba4919c75c5a19b868aa19a917ce19a5a29b1997acd7199611ad198916cb19816bd21980bc291978e7af1975bd65196025cd195101d819468cb71922c458190b91071908e45118f1cbdb18ef1cfe18eed24c18de0bda18c190bd18b5ec5418b21c9f18a9afcb189f5575
  | 8, 12 => 0x1e31a0a51e2ed0061e1e3f971e1935ee1e083a961df426f31de631f51dce487d1dbdc9d41db8f29e1db656d01d989e101d93d97a1d85da9b1d7c7ac81d7c0e801d6e9be91d602e211d3b441c1d34fdae1d2a81d31d1dae841d15ffc41d07cbc61cfb10b41cf7e5bd1ceeb9671cd8fdcc1ccf54311cc920801ca29fec1c90981a1c840f491c7fb0ac1c768d151c550dc91c5319951c48f54a1c2580571c1ffead1c193f401c0b27771c013bc41bfaf2791bf68d281bf5be811bedd14d1bebe5001be0b9e61bbb3e5f1bae596b1bacb9031b933b9e1b70e29f1b6c8fc11b57c1c61b52f3321b52b4941b4fb8da1b43d9e11b3fc74d1b3ea7dd1b38188d1b30ac22
  | 8, 13 => 0x21a2898f219d6cb7219a41dd21997fae21944b342177d428216d0cbf215c7000215ae4e1215222c0213bddeb213a8cc1213819c92135f8032122234d21184cbf21134de820fa750020f1cc6220e6b1ae20e2e2e920be91b020b9c6c520b8f05c20a25cc2209bc1b02089d750207ac0b32075f3a02069023f205a8f47204abfc9203cd04e2035f039203524cd2014c6441fecb1011feb16541fd64b0b1fd431311fd3c25f1fbf8e971fac1ffd1f85f2e51f7e44251f2901d41f1bcfe91f0999271f0447dd1ef6a45b1ee0f4801edfb1411ed6b2ce1ec148d41eb99a141eb3facb1e9c07641e7b67461e6cef631e5ad6651e5ac6e21e53d1171e4837591e373b6f
  | 8, 14 => 0x254c3f31251b788f25114ba9250dd4dd250b3e6a24fc7c3524f12d5124ef82e324e1d60e24e0676a24c5423e24bff59924b1517c2476f8172472ec63246969c2246554a62458376f2456f88324534cfb2444866924429b14243f528f243d6afa243971d52437f8a924356c7c24283958241d3313240142b423f4f50423f0081723decb3223d49ada23d2903a23b3c75d23262ea523252c27230a660923038dd422f7858122e0361a22b98ad922b26b5422a0be602289ec0b22888d34227a3692227287d2226d39d42266ccd8225a2ac722569361222b364b2222dbd421e8ce1e21e6cbde21de28f921c8843621c4fcf521b6efd921b5121621a5f96821a5b46e
  | 8, 15 => 0x29245063291d2a9e2915b2952903aa3329038a6728f4dccc28e024ae28df67d928c7512528a9dd1d28a4a83e28a46344289bea9e28754ce52863c74b28554e92284f2ae5284acd9d28279b7728161a7728059e2927fd4ed027f41d6c27e319d327c796b427c0fe942794da6d278d7e2e2785a6f22780d92b2774c460275dc42027523f85274b027f273e087b2737398e271e59ad271a79a326edf6d526caa32026c80c8326beaf6f26ba32f926b6da2026b48b0426ad119126a8dc6a269ac23a26913549268056cf26640762265e43072648e3a82643d2c7263a378e263311a6260ba30225ffff0825bce25925b8ebd6259a3137258a599a257bb4b225594920
  | 8, 16 => 0x2c99b39b2c97f3742c7bdc5c2c7afb6d2c74b9602c6e80d92c58dac22c4bcf602c43cdb72c18d8712c119b4b2bf269d32be239292bdeab172bd9f02e2bd4f2622bd30c7d2bd01c582bc83e262bc2b7902ba705962b963bfd2b81faf52b6d633c2b60031d2b5f3ac12b5913022b3e6d342b397d522b2c9bd22b2b5dd92b23af192b0fca262b08f8cc2b020fdd2afe2ee92af8e8dd2af0062b2aea12282acbe7a42ac4aaa82ac22d972ab1266a2aaeb1ee2a6181452a548dd72a512dd62a50e5e02a3ac93b2a245e7b2a0c25862a06981029f9c57229f0b1cd29e1d04229caf7df29a8ef232992b93229687f152946ed2829428e4b293fda99293a228829259dd7
  | 8, 17 => 0x31940982317af60a3177ea88316c7a2331671e4231660f0b3161f28d314170fb31389c993130c5a8311b564131156766310f6e4330ebd3b330dba21430ce302a30c667be30c2d50d30add32f3067284c3051e25f302ca7773014f8752fd476f42fd3d8332fcb6be12fc7f4722fb130be2f9f57ca2f9ce5452f98f4ff2f42037b2f402dcd2f3d6bb72f2d39052f1d2f5b2f1279782f0f84b02efae7b82ef229c52eceee252ec5fcde2e7f88942e7ac5422e67d1922e48c46f2e429cd82e04cc1e2dfd78c52dee12a82de6358a2dcb3d022da395e12d75b14c2d71bf282d70ced82d41b42d2d3edd1d2d3e70562d0c91bf2d033ef52cdf1b752cc795ae2ca82163
  | 8, 18 => 0x36b521a236a00a6f367589d13660a0ce363ff4043609387935fb20c135efdcf035ef196835eb6e8135d88d8b35d5f5fa35a563b8357193a63567e8773555d10b3545382f353ae604353aa3c6352f6fa83525ef7e351fe109351d01f93511a84634d051b534a771a73471b89a34609909345ddff534487e123417a98234047aae33e54ac833db546e33c3d97933b3ed5733ac51d333ab1bdb33a78c68339b61663398d185336c58ca3334150b332fd28b33157192330961a632f10ebc32e16b8932d2f28e32b5e2b032abbdbd32a1bcd5328fc94b327f06ae327af811324bd83b3241705c32353a94322c07963200e54b31ffed8331dfa8ce31bb9f0b319b1141
  | 8, 19 => 0x3bcc95993bb748253ba5b0c43b8a452c3b7586483b5dfe273b5dab7f3b405b7c3b3477b43b33662f3b0f10343b08dcd23acd1b283a926f333a65b9973a64e63a3a59cc033a4d6a953a4a0afd3a305add3a2d4b643a27c44b3a03ef1e3a03d4b139f7e21b39d3cbf039c0034139b5e92239871e9039803f4c3971c655396f966f396f14dd3960a71539500340394f142039234c0738f915a338f3abf438ef98d238e1a69e38e002c538cb099b38aac4cb389d4dff3882faa6387479253873feea386538dc3863a14d385ada93383a0cba3818091338120974380f433b38096b7238040c7937bb1045377dd31b374a5bdb3743a61d3742ad1b36fb0cce36fa7d39
  | 8, 20 => 0x413ce7b0412c1b3840fe085a40f10c3e40e5429a40b8bfcd406f21e9405c6c46405125dd404b3013401a1c4f3fdba9f43f72adaf3f6aee9b3f5aa7ff3f4f65e43f4df06d3f4622693f4542213f2afc363f1fb8673f15457d3f13cdeb3f1151243ef484683ef216f93eec98d43ee699ea3ed2b9b03ecf8d4e3ecb96d93eae87cb3eac3c5f3ea6d90b3e4ff8403e444aad3e3c0ae43e3a3ac43e39f5ca3e2f2ebf3e277fff3e186ce73e1753ff3db2c72d3da41e5d3d8a3cae3d814b4f3d6d79af3d3709663d31264b3d19a12d3d18d5d93d1127193d04ad5f3d007c543cedcf813cda06bb3cd44ec93c8fe41f3c87a7f63c5158263c3cc46f3c01ff8b3bcdc310
  | 8, 21 => 0x49bb2fc3499b08ca4987e8284973e9a949574604492acee949148db04903b7e948fc092948f0ff0048bc1d4a48b067a348873e03487c5550484d6d43484bff8a47fa34f747e94fce47ba59f7476f2d1a47614e3b474db18c471dd813471718c446f43ede46f1b31146ec901e46eac39246de75944695f7c14667f2b7466574da4626019546158aff45f9397145f28fa6456f53d34529a6cb4524c9574512b08b44d636b544cf451c447811ba4408d56743a4fea4439f5156434ac03243415181433a22d7433474fb43027fd24300136842c678d342c2143b42bd0ff042b779a34270b5be41ee6d4841d9fb7841d387bf41c3198a4193af6741670281414e039e
  | 8, 22 => 0x51eeed2951e3ee9c51e2bba651bcef7851b7e58451b036c45163629a514b87865136a9a351255b02510d0d4b50dc89c5509f5416509290e95059633d504ae16c5034e0034ff820184fa5f4514fa260824f7571594f490be64f446a1c4f050fd04ec05ebd4e5372144e3a3a904e3583694e2daf5a4e1db72a4e152f604deb38d84dc6a24a4dadc86d4d673e904d50bac34cff7ae04cfd734b4cd6bec54c94daf04c64df214c5f84084c434dbc4c23a9c54c0687544be24f2b4bacc54f4ba463a24b9250a84b73de524b7335804b6e21e64b48acc94b2b9ed64b0c2c394aee73794acad7b24abed1e84a7b60674a2ad56949f79d6949f00a2149e8ca8149bb5d58
  | 8, 23 => 0x5a178b655a0fdca559fcbebe59f462ec59f11cdb59a304185996f4f5597bfa895936765a59340dde592ec8a9592e5a0458f9541e58eb481b58a46bf7589bec5e586260e757fbeb4457f3a88a57bc0bc957830f60576d47815744b4ce5707fb67570099a356bd3a83569a739256529637564dd522564030685635a39c56208e7f5600570755fd7a6355f9c36e559424ef55823b41557d62d5557d5be655630fcc5562c4b5552f2a3b5523a6b555122fc954dd04ca54c66e2d54b8020854acafc4549e56ae5477b79f5476a805540a4dbd53ba4dec53816ed05343260f52f2fea4529e3bc752942b7252747f0752534f945251f931524a17a8523dc21151f69be9
  | 8, 24 => 0x64e7238064cf00c564cbcc5164c7281e6487b6f7646b21fb64660c076407b6b263e50b4763e21a0263bad2eb63b3242b6361c72f634cc69562ccb708629b149e6274fa01621f063b621271ab61a45f8b6192a10c6177d4e66165c32c61197806610f36b560fe5bb260f47f6c60877a035ffd80e75fa1e12a5f9873855f8c75c85f859ca75ef408b65edd48d25e77e9735e1b34d25dfe16575dd08b735dc437625d9d7bfb5d82ca825d44141d5cde0cce5cce8c455ccc6a355c4542b75c0095e65b6b678f5b51232f5b4cc3c35b45bb155b4388f85b35ecca5b2d1c075ae1bb5f5ab0e6ff5a8d74075a8322685a81f34e5a6ca6835a62dc0f5a4badc85a331951
  | 8, 25 => 0x7584e5a57523065074a635e6749d362b748267da747ec00a7399a6297393454b736460c6734eaa0d731a9a377306d81172ac96e472847ea27260e48f7209e47d71a6f1d77127341170d2059070baf60f70a579f87026e8ab6ec47ef56e473f2f6e3c3ed26d72ad596d1991cf6ccb0d096c5ea0a76b7deff76b7d0aad6b7c11ab6b6ab2916b5c44c96b3b236469fc0e8069da0c1f69c01d5e697e9cbf69355588691df4ae68a1c61f682efe61681aa5ce680cff3167a95d8e679fb9b46771a872675e86876732258166e5ae6b666aceee6617db0a65b3f9f765b2ecb165a0be6f6589894a65717f97656311cf65524fc6652acfc4651907d964ffcc4e64ec195f
  | 8, 26 => 0x8ccacfc48c60cfbe8b79ad848aa52e8b8aa3b04f8a80a9f989df08ff89bebf2c89b552858961d94d894ebb5e8934bc8a886c5728885f7a2188462d34882be4e18826fc39880776cf880753198730fd46869b75948614004e856d47fc8532273284eea13b84afead68492c7cd83f8730f835e188882e2ff47827963fa8258082b81e7838881497f46812adf778040f4c280082fa67f4590c97e1233eb7d8c1f807d4df2407c4bfba17c3872ad7b7539d47b71c7f47b507d547aaa992a7a399f0c797234ad78fa365c78ebc89478d131967846d65277fe922e77d135d0772ff9b1771433bf76f0de3376d6e32176d57d5a76b871ac766c84577606abbd7601ef87
  | 8, 27 => 0xd9d0d343cdade437c996b3b6c82542e3c4949487befa2055be4be64fbd82ee2ab72f93ffb6c50266b5b5ed52b3f9acfcaf072a82ae5d685eac7b9e87abc73af8ab681b8eaa83c7b5aa2ce68ba827e4dca7a2a7a3a7880e9da6f3a76da6ad03e4a696d22ba68f5104a5ffff96a5a4f33ba5a40141a4f5f8a9a2572215a190e7d3a0d7ce83a0bc6bc6a084d294a0527868a046c73f9edbc97b9e1370af9daae7409d8d1f3a9cad2a7e9bc7651a9b5115669aa3e7d79a7b8b4197a4f387967fbfcb962dc6db960d9c3f95b2b537957b37e59543782694e56e8493f36dc692db64f091b5576b91a53cfe917adf6f90f610e6900b9d9b8eee6a888ee5c6058e53da0b
  | 8, 28 => 0xfab495f5f8b72109f2854adfe575a6eae298b8f8dede789b
  | 9, 0 => 0x19e3604919b1d4481979f417196672e11900f429181aa941175a929b1729918f16b50ee915f86a801561a43a1528ba3c13b5da6d136d10ac1317dd2b129997eb124e263511ed84b711d748061187183a11761aa81142fa411134c93410d1aa96103ead2a0fc22fb60f5c5cfb0edd17080e8414b20d9cbe430d4d98860cea20e10cc7aa850cb3009d0c867e660c2cfbb60c22507d0c167f100bd753a90b989d440b41c7720acf09dd0a9628be0a172c490878675807d82e3c0754ea15075140fd06b07a030663442505c61dd605ad2f34059e8b170590310f05869eb105169eb0040745c602e9d44b0291d00a0188fb4b01013f3600dd496a0064991500103def
  | 9, 1 => 0x4309ffd842b779a341d622d340bb28343ee6de3d3e277fff3d8620523d6d0b963c9f3cdf3c8fe41f3b3c318a3afd7b253a8b1a653a47663439de879e395003403724f45b366fa27235d89aaa359aee6d357bcd5733d93c6b330961a6315024ba3122199e302ca7772eedfa852d770a592d6df75a2cf085992cb7e2692b0f56702a6bdfc02a5e00e12964176b291abe562775450f2705880d26beaf6f26bb2fef26aa53c3265363bb26488ebe24cb7b29246554a623038dd422d85c9a22543c1c21a5f968204aaf2d203e530f203cd04e1fd3d3851f608b651f3d31db1ee4e3db1ebb13731e7359ed1d989e101c53b96d1b70b1901b52f3321a5d39541a2bfa9c
  | 9, 2 => 0xfab495f5f8b72109f2854adfe2f7dbbfe2f02cffdede789bd69e993fbeb2f988b6edc245b12375bdaa38618d981b7e9292b08ece8bbc73f08a7994f8886bb2a5869b759485210b037f4590c97f27d8097dad4e397cea112d7b2b17a17b25f4ae7a85129f76f0de3376db0b2e727daf3d72739f547260e48f6f3b46226c4b6e046b7c11ab67044c4c64ffcc4e63275f156129ea2960d158045d7bf2db5d2e415c5cde0cce5992adb05640306853b7a8b552942b72523dc2115059633d4e1db72a4de27c5e4d2b306b4d17706a4cd8ba054ca60af44b62f61f4aee7379499b08ca49148db048b0ac9d475141bb46e1bded465e79d545f6b58445c07cca457c5ed1
  | 9, 3 => 0xfabc44b5
  | 10, 0 => 0x8a7994f87cea112d2eedfa851e7359ed1729918f1561a43a1142fa41
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 5, 0 => 0x28062010001253500300000000480e20000145304c03010010540441305000000180220300000000000000000001802200000002044120f00000000121000000002802201000125244030064485520414010000052041205069512148440200000038022000018c5444130500000000411150000053041205000000000000500000038062000014910440302000164350c300
  | 6, 0 => 0x1500000000000030010d32501303000000480e203000000380a20000000048022050000004802205000120380a300000000010d11000000000000170000000012100000000480a2020000a018023010014d2048030100000000000000000000000013000000380620100191058413040000002806205000002148120300189500c530000000000021010000003806204000000000a10000012524c0300000000480e2000000e018023000000000041101000000000610c000125244030000016204803020000003802203
  | 6, 1 => 0x380220200006544c03010000004885200000000008110100000028062000000052440200000000380220500000028022040000000000005000120380a300000000000a106000000000a104000000280620500000028022010014d1044030300000038062000015121484301000c55304130100006524c03010000251480301000000000e105000000480a200000000000e10100016304c0301000000480e202000000000a10000000324c1202000000380a2000000000002102000000000000500000000000050000003806201
  | 6, 2 => 0x280620400000500c52050000000000015000000000000500000018022020000002802200000000480e2000001202802302000000380a2030000000101100000000000e10500000001051110000e0180230200000038062040000000081103000000090d2010000003806201000852044130100000500c92050000000012104000120380a3020000003802203000000000a10500180214813000000a5444030000000000411030000001802204000000000a10200191500853010000043041206000000000000f0000000000001
  | 6, 3 => 0xe01802304000120380a301000000280620100000544c12010014d10440302000000000a10200000500852020000000006104000000000000000000028022040014910440303000000390520300000000000020000e0280630300000000c9105000000010d110000000000a105001915100e3010001a5344030300000000c9105000120380a3010000a0180230100000000000140010d424c93040000e52440301000000380a203000000000210500000000061010000000002101001940484130300194028c1301000000480e205
  | 6, 4 => 0x5444120500000000c9106000000000e109000000000610c00006525003000000003802202000c530441301000c93048130400000000000080000000012100000000280620500000000c9106000120280230300184544c1303000065444030300000434c920500000028062010001a520c1301000120280630200000544c120000000000c91060000000002105000000280620100000048022010000000105111000000000e10000000410c92060000a01802300000000010d11000000510c9205000000000a1080000e02806302
  | 6, 5 => 0x125244030000012038063010000a018023000000a544c0300000000480620400000534402010010d424c930400000000000110000a018023020018021441302000000480a20400000028062000018c5244130200000000021000010941485301000c5504c4301000000000a10200000000c9106000000000000e0000000002100000000480e2040000000006103000000480a2000000e5448030100000018022000000253440303001855010d30000000048062040000000000000000065348030100000204412040008550484302
  | 6, 6 => 0x2514c0301000000180220500000000000020000002806201000120380630000000038062050000000000000000120380a300000000380a205000000000e1000000001802201000000008110100000000000120000000002106000000000000f000000001210200145204c03010018453481303000000280620000191325013020000a544c030100194028c1302000000004110100189500c530100000000121050000a544c0301000000000210400006524403030000e028023010000004802200000000000000000148510c1301
  | 6, 7 => 0x10d10000000058842000000000000000000000000a101000c9304813030000e02802300000000000000700194324413040000a0180230000194028c13010000004806204001094148530200185058c1301000000000000f0000000006105000120380630000000544c1200000000000e1010000a514c0301000000000a105000000000210500000434852000000003802200000855048430200000400c9206000000390d2000001202802302000000000000200085504843010000000041106000000480e2000001202802300
  | 6, 8 => 0xe0280630100085304c030100000000c9106000000190520300184544c13000000000085101000000010d10f000000000610300000000c910600000028062050000000006100001895010d300000120180230300000000411060000004802200000000000e1050000001802204000000008510000000018022050001202802303000000000000200000400c92060000000000005000025448430200000000021000000e10440303000005008520100189058c13020000000041106000005008520200194018c130200191058c1301
  | 6, 9 => 0x130000000000000000120380a3030000000885200000000001210000012018023040018d500853000018c5048430100000544412040019132501303
  | 7, 0 => 0x30000000041106000000380a205000000590d201000005040e201000000000000c000000380a202000000000210c0000000000000000000180220000000000121040000003802204000000480e20200000048c12020000003806200000000010510200000000c51010000003806201000000590d202000002148120100000000c9106000000480e2040000031441201000000480220200000058c52000000000000008000000280220200000008812030000000105100000000380220400000038062010000000006102
  | 7, 1 => 0x48c120100000000c91010000000000000000000000000100000000c11060000000081111000000590920000000000021030000002841201000000000000f000000000001200000000c1103000005040a2010000030481202000000480620000000001011050000000000003000000000001100000415012010000000002102000000090520100000018022030000000002104000000590d200000000000000b000000000000600000018c12040000003802200000000000e105000000000a10000000434c12040000000000001
  | 7, 2 => 0xc9106000000000e105000000390120100000058812010000000006101000000008510500000058c520400000000000100000002905203000000000a10d000000000a10200000510022030000e0280230300012038063040000002806203000000480e20100000038412010000005841202000000480220200000544c520100000058c920300000038c120000000544c52010000e0180230200000001011110000002802202000000480a20400000434852020000001881204000000000e106000000000e106000000000e105
  | 7, 3 => 0x48062020000004806202000000380a2000000000000013000000480e203000000000e10d000000000a1070000001881204000000000210000000000061020000000006106000000090d20200000000061010000000002106000000000000900191315013040000004841202000000000e10d00000000c51060000000006100000000000001200000000000010000001802202000000000e100000000000610400000000c91050000032501204000000000610000000530022010000000000007000000000000e0000000000002
  | 7, 4 => 0x17000000480620200000008c920000000000851010000000081105000000000000000000058852020000052002204000005240620300000048022030000001802201000000004110500000544c02010000004802205000000000e105000000180220400000514c0201000000480a20200000018c12010000052406200000000000001000000028062040000001802200000000000000f000000280220200000018c120400000048c1202000000588120400000424812000000054485202000000480620200000000c1101
  | 7, 5 => 0x190d20200000000c910600000058c920100000000000030000000081106000000000a1030000003802202000000000000000000524c020100000000c9106000000000000f0000000085104000000000000000000058c12010000003881204000000000000f0000000085102000000380620000109215013020000002905204000000000000200000000000070000000041106000000380220300000000851060000030441204000000280220000000000411050000002802203000000380a2020000000012105000000000000e
  | 7, 6 => 0xa109000000090d201000000000000c0000e02806300000000000000f00000038062000000000012102000000280220000000435012020000000000017000000090d202000002148120000000000c9106000000380a200000000010d100000000000e10600000000c9106000c93048130200000324c120000000000c9106000000000e10200000008c520100000000c510600000028c1201000000000a105000000180220000000019012000000000006101000000290d2040000031501201000000480e2010000002806201
  | 7, 7 => 0x390520000000500c920400000000000160000043501202000000090d202000000000a1050000000000011000000480e200000000000e105000000388120200000038812040000000002106000000000610e00000000c11060000001905203000000180220200000000c910600000039012000000053402204000005440e200000000000e101000005340220300000028412010000000002102000000280220100000424852010000003802200000004248120200000000000030000000002102000000290d2010000000041105
  | 7, 8 => 0x61010000000000003000000480220500000001051010000000002101000000010110f000000480220400000314812030000051402202000000000210200180214413010000003802204000000000001500000008852000000000000009000000380a2040000000085106000000390120100000000851060000004806203000000000210000000008c52010000000000009000000000210300000008c9204000000180220100000434852020000002806201000000000a101000005340220400000008c92000000010440203
  | 7, 9 => 0x300000000061000000000000003000000000e102000005008520200000000121000000000000010000000000001700000544c1200000000000e1010000000000005000000000a10500000038022030000000041105000000384120200000000000050000051402201000000000000f0000002802204000000001210100012028063030000000000011000000000000a0000000006106000000590120000000000000040019053481303000000380a201000000000000a000000480e20300194214c13020000001802200
  | 7, 10 => 0xc1102000000000e10500000008852010000000881202000000480a201000000000a10e00000028062020000000041102000000390d20000000001091050000005881201000c5304413030000003901203000005308520100000000c91050000054441204000004250120100000009092010000000000011000000000000500000048c12020000005909201000000384120000000058c1203000000280220500000019092030000000012100000005404120300000514c0201000000000610300000000000120000000002102
  | 7, 11 => 0x1400000028022010000054481202000000380620500000534852040000000012105000000000a10600000000c1105000000000000500000314c1203000000000a10400000008c9203000000090d202000000000000000000000000050000000002100001913250130100000315012010000004806203000000000000c00000038c120000000048c120100000059012010000001909200000000380a20300000000021050000000006103000000190d20000000314c12000000000041105000000190d2000000000000002
  | 7, 12 => 0x2885200000004248120000000544c9203000000380a2040000000105103000000000a100000000004110600000000c910100000544c92000000003802200000000480220000000058c12000000042505201000000000000100000028062040000000002106000000008510600000000000100000051002202000000000a105000000001210000000028c1200000000000e10d0000000002100000000001210100000000000160000051402202000000280620300000000c5105000000480e20200000000811030000030481203
  | 7, 13 => 0x2841201000004348520000000000000030000000885201000005340a20000194214c1302000000000000600000028022020000042501202000000180220200000000061050000004802203000120280230100000000411050000001802204000000284120100000000000000000002802204000000010d1000000001909200000000000000f000000000001100000000000030000000105104000000000210400000018022030000003802202000000000000f0000002806203000002148120300000028022030000a01802301
  | 7, 14 => 0xa00000058c92040000000002105000000000000500000544c92020000005909201000000000a10100000414c120400000001051110000002806200000000000a10d0000004885200000000000000400000534412040000005885201000005340220100000028c5201000000008110600000000411020000002841202000000180220100000018022030000003881200000000000a100000000000000100000000811030000021441200000000000610400000000000010000005840201000000000000f00000000c1100
  | 7, 15 => 0x1210400000028412040000003802200000000480e201000000290d2030000000006102000000004110600000000000050000000000001000000480a200000000380a201000000000000400000544062000000000085101000000010d10000000000c1104000000000e10700000048c1200000000000610200000000411060000002802200000120280630200000520022000000000002100000000480e20000000324c120100000019012010000043501201000000090d2010000053481202000000290d2000000002905204
  | 7, 16 => 0x90920300000058c92030000000081104000000000a105000000001210200000000021030000000000000000000380220200000028062010000000002104000000480a2010000000000012000000000a106000000000a105000000000610000000018022000000000000013000000000001200000038022040000042501201000000000000300000000000120000054441200000000000a103000000380620100000018c92000000053002203000000590920000000028c1201000000004110600000544c920100000000c5106
  | 7, 17 => 0x10000000000000a000000380a2010000002806206000000000000f000000008510d0000000085102000005100220300000008852000000001802200000000010d10000000001011010000003802204000000000000000000000021050000004806200000000000000f00000028022010000000885200000000004110f000000380a2030000002802200000000000a10200000504062020000000006104000000000000f000000000000e0000042501200000000000e104000003048120200000059052030000005841201
  | 7, 18 => 0x6109000120380a3000000002881201000000008510100000000c11000000001901202000005040e201000000000e10e00000325052030000000012105000000000000500000038062020000003881201000000000000600000434c12010000000000017000000010810000000544c520000000000811060000000000000000000000000500000029012000018c5244130100000048c52020000003802201000000000a10900000000851060000003881200000000490d202000005040620200000544812000000000006101
  | 7, 19 => 0x380a202000000000000300000000c110f0000000002105000004150120300000000021060000000002106000000000e1040000000000006000000010d10000000434c9203000000290120000000048c9202000000000610700000214412020000005885200000000000001200000000c1106000000000610600000544c120200000008c520300000544c1200000000380a201000000001210100000304412040000003885204000000000000f00194324413030000050406203000000000a101000000190d203000000000000a
  | 7, 20 => 0x8c9200000004348520200000018c12010000003802203000005348520000000510c120200000544022000000004806203000000000000300000000121000000004806200000000000000400000000411060000002841200000000000a1060000051081203000000180220100000048852020000003806203000000380a2060000e028023030000000000007000000000000f000000000001100000058c120100000214c12010000002901201000000480a2000000002841200000000380620100000058c52000000054402203
  | 7, 21 => 0x280620200000434c120100109414853010000000109100000000088120300000048022030000000012100000000480220000000000c9103000000000a10100000028022000000000002109000000000000100000000c5106000000488520000000314c120100000058c9201000000000610100000000c910600000000000150000000000012000005348520200000000121040000020441202000000010d1050000000000003000000380620000000000c910600000000851010000000081106000000000a104000000000a101
  | 7, 22 => 0x851060000000000003000000000000900000000851060000043485200000000480e20000000314c1201000000380620500000008c12040000053041201000120380a302000000488120000000000411060000000041106000000000a10c00000324c1200000000000000400194214c130100000000c9106000000000a105000000000000500000000811160000000006100000000000000f00000000000030000000000003000000010d1000000000000002000005040a20100000028c120100000008412020000000000005
  | 7, 23 => 0xc110100000000021020000042501203000000000000000000009092030000000006105000005040a2000000001881202000000000610500000524402000000003802201000003048120300000504c8201000005100220300000038412030000000012102000000380a20100000058412030000000885204000000390520100012018023030000000006107000000000a10100000008c1203000000000e1020000004901204000000590d200000000088120000000434c12020000004841200000000480a2020000053440201
  | 7, 24 => 0x43485200000120280230300000000021040000043485200000000000e103000000000000a0000051402202000000000000c0000005885200000000000210c0000004806203000000000e10100000000000110000053485203000000000000f0000000002100000000388520000000510022030000043485200000000008510200000039052020000000000004000005244020100000000c9103000000001210400000038852030000000909201000004248120400000008c9204000000000e100000000000e1020008520441301
  | 7, 25 => 0x12000000480a2000000000002103000000000000000000000c910500000000c110500000039092020000e028063020000032481203000000000e101000000000000100000000c1100000000000a1060000000085106000000280220100000544c020000000000061030000e02802302000000480e20300000544c9202000005348120300000214812030000053440203000000180220000000000000060000000000001000000000000500000018022030000000000003000000000a100000000380a205000000010d100
  | 7, 26 => 0xc11060000003802201000000000610300000018c9203000000000000500000000000100000000000016000000000610500000544c0202000000480e203000000480620100000524c020000190524413000000000000000000000480a200000120280230000000000000050000004806203000000000000e0000000000006000000000e1050000000041106000005240e20100000018c12040000041501204000000380a20100000544c9202000000480220100000544c1200000000000001100000424c5200000000000e105
  | 7, 27 => 0x81106000005300220200012038023010000000000010000000000610100000544c02010000000000001000000380220100000000000100000000000005000000180220000000304c020200000028c12030000000012100000003250520400000000c1106000000390120300000028c1200000000000000f0000000000000000000280220300000544c0203000000280220100000324c1200000000000a100000000480620200000000c910600000018c920300000000411060000050085201000005300220300000000c5102
  | 7, 28 => 0xf0000e0280230200000000000000000000041106000000180220000000314412020000000000003000000000210400000434c120100000000000050018d214c13020000005881203000000000000f0000003802202001805348530300000008c120200000000411000000000002105000000000a10000000215012010000000000004000000490d20000000028022000000043501200000000480a2050000000000005000000284020300012018023040000000000011000003250120300000009052000000000081104
  | 7, 29 => 0x2802203000000480e20000000048062050000000000015000000388520200000000c91050000000000000000000000001700000028062000000003802201000000000000500000544412030000000041104000000000000a000000000a106000000000a1060000003885203000000000001100000544c5200000000000e10100000008c1201000000590d20000000008c120400000544c9204000004348520000000524412010000000000007000000290d200000000388520100000000c910600000028022040000000002100
  | 7, 30 => 0x28022020000000000013000005240e20100012028023030000002806200000c53044130100000000021050000001840203000000480e200000000480a20000000008c1202000000000000100000018022020000032441201000000000e102000000000210d00000048852020000050109202000000000610400000008412020000000000010000000000e102000000000210d00000544c020100000000000020000054440201000000390120200000000000040000000002104000000000000700000000000040000000000010
  | 7, 31 => 0x500000000811110000000041106000000000000400000304c02010018d214c130200000544c0201000000000000500000000000050000000006106000005440220000000018c120300000434c12020000000006105000000000610000000000000080019132501303000005140a200000000380a200000000000000e0000002806201000000480620100000059012000000000002108000000000a10700000000411010000000000005000000000a10100000544c1201000120280230100000214412000000054481203
  | 7, 32 => 0x5000000000210400000324c120200000048412010000000000004000000180220300000001091050000000000011000002148120200000058c120000000058812010000000006100000000480a2000000003901200000120280230000000059092000000031441201000000000000c0000e02806300000000000001000000048812000000000000001000000000000000000038062030000030441201000000000e104000000588120000000434852000000000041106000000000210400000000021020000054481201
  | 7, 33 => 0x54485202000000088520200000000411060000000012102000000090d20000000514c020100000000c1102000000090d2000000003901202000000000e106000000000001000194214c1304000000380a2000000a018023030000000000008000000000e1010000000000000000000480e2000000000085100000000380620300000028062000000002901201000003250520400000058c9202000000380220100000000000010000000002104000000000e1010000000000001001804350130000000000c91050000000000005
  | 7, 34 => 0xa01802300000000000e101000000090d2000000000041106000000480e20100000514c02000000000012105000000000000200000544c02000000000041106000000000a104000000180220300000008c120100000000c1106000000380a201000000390d20200000018c1203000000280220000000000021040000003802200000000000000d00000028022010000004802203000000480a200000003244120300000000000110000004901200000000480e20200000000000040000000006105000000000000100000434c1200
  | 7, 35 => 0xe100000000000000f0000053481203000000000000500000314c12040000000000005000000290d204000000000a106000000000e10000000000411050000054402202000000480e2000000000000000000000000210000000000121020000000085105000c530441304000000000e10000000048c120200000544c0200000000280220300000000121010000000881201000000480e2000000000002101000003248120400000018022050000002802201000000000000300000000c9105000000090d2000000002806200
  | 7, 36 => 0xe000000000000100000000000100000002802200000000001210500000000c910500000000000050000000000011000000001210000000018c920100000000000050000050412200000005444120400000000411050000043501200000000000000c000000000000f0000051402204000000000e1000000000041106000000000a1030000000006106000000380220500000000c5104000000000e101000000488520300000000000150000000000007000000000000300000534802000000001909200000000000a102
  | 7, 37 => 0xe1050000042501203000000000000f000000000a104000000090920300000018022030000002802203000000000e10200000544c02000000000000007000000480e2030000051480202000005300220100000534022010000002802200000000001210500000514c02010000a01802302000004348520000000000121040000000006104000000588520000000000000160019150085301000000000e101000000000000f0000005905201000000000000e0000030441203000000010110f0000032481203000000000e105
  | 7, 38 => 0x10941485301000000000a10100000000000030000000000011000000000a103000000388120100000000411050000003905203000000480e2020000004806203000004350120400000000000010010d3250130300000500c5201000000590d202000000000001300000008c5204000000000a102000000590d2020000004806204000000000610a00000000000030000000000009000000284120000000000000040000000041106000c93048130300000435012000000002841201000005040620300000028062000000a01802300
  | 7, 39 => 0x32505204000000290520000000008c1201000000480e204000000008510600000000c910600000000c9106000000000210100000000021020000a01802302000000584120200000504c8201000000480220100000008c1200000000000001000000514c0201000000000210e00000058412000000021501201000000000000600000000c1101000005240e20100000544c12020000e02806301000000000a1060000041501203000000090520300000544402010000000841201000000000001400000000000070000000085106
  | 7, 40 => 0x214c1201000000280620300000000000000000000002100000000000001700000000c9106000000000000c00000000c5106000000480e203000000000210300000504062000000e02802300000000380a2010001202802300000000180220300000028062040000002901202000000000a1000000004802200000000000001100000019012030000001802203000000000610a0000054484201000005000a20200000000851000000e028063020000053441201000000000000e000000000000000000000021000000005885200
  | 7, 41 => 0x110000000000010000000380a204000000390120200000000411060000043501201000000000000f000000280620100000000000020000000000000000000280620500000048812030000054406203000000000000d000000000610100000028412030000a01802300000000000a1020000e02802302000000480a20000000000000100001202802300000000380a2000000053002201000000000000500000000000160000054484202000000000000500000000c9100000000390120000000324c1204000000380a202
  | 7, 42 => 0xc110500000434c1200000000380620000000510c1203000000380a205000000380a2050000000012104000000000a1050000000000000000000000001300000000411060000000000011000000480e200000000000000100000000000130000000006105000000480a203000000000a101000000180220300000038812000000003802201000005308520000000001011120000000002104000000000000f000000000a10a000000000000f00000000c9106000000088520000000534852030000000002104000000000000f
  | 7, 43 => 0x4881200000000008110600000048022010000000012103000005344020000000524412020000050085201000000480e20200000214c1201000000380a2030000000101105000000001210000000000411050018d21481302000000480220100000514c0201000000480a20100000000000110000000000013000000380a20000000435012010000004802200000005210120000000001011050000000012105000000000e105000000000000100000000000040000041501203000003248120400000000000150000003909200
  | 7, 44 => 0x3885200000000000a10600000001051020000000000001000000000000000000000c9106000000001210400000214412010000000000005000000000e10300000000061090000042481203000000480e2000000042501203000000000e1050000000000009000000004110500000038c1201000000000000100000000000050000043485200000000480e205000000000e100000000004110500000000c510600000029012030000002802203000000000000e000000008510100000000c91050000051402200000000010d100
  | 7, 45 => 0x4110600000534412010000000081100000000000a1040000032440203000000000000600000018022030000000000002000000000a103000000000000800000504c82010000001881202000000380620400000544c120000000504062000000001802201000000284120000000000c91060000004802201000000010d10f00000000411040000000000010000000000e101000000000000600000510c1203000000000610a000000000a106000000000e1010000001881200000000010510300000058c92030000030481204
  | 7, 46 => 0x210500000029052030000000105111000000000000e0000000885202000000010d101000000000210b0000000101105000004150120300000009052030000001802203000000284120300000510022010000000081106000000000001400000001011120000002806201000000084120100000001051110018d50085301000000000a100000000090d200000000000001000000000000110000000000002000000000610600000544c120000000048022040000000002103000002144120000000001051040000043509203
  | 7, 47 => 0xc9106000000000a10400000000c9106000000000e100000005110d2030000002802200000005444120300000000c910600000038c120100000434c92050000004905204000000584120300000000000110000004802202000000488120300000048c920400000000000010000000006104000000380a2000000004802204000004150120400000009052040000002885200000000000e102000852044130200000000c91050000003802202000000280220000000000c110000000414852020000a018023000000000085100
  | 7, 48 => 0x1881200000000390520400000324812000000053440200000000000000500000514022040000003806202000000480e20000000000061050000000109101000000010910500012028063000000000105103000000588120300000000000000000000000010000000000e1060000053406203000000480e2010000000002102000000010d10100000008c1202000000000000000000008c52000010941485302000c9304813040000004802200000000380a200000000280620000000000411050000a0180230000000000c9105
  | 7, 49 => 0x544c920400000414412040000000000001000002148120100000008c12020000000000005000004344120200000000000000000000000005000000000610000000000c110600000000c9106000000480220100000038022030000000041103000000004110600000048412020000000002107000000000610e00000214c1202000000280220500000000c110500000000c91050000000000002000000380a20300000000000000000000006103000000290d200000000000000700000544c520000000534852040000000000001
  | 7, 50 => 0x8852000000052441200000000000210200000314c1203000000010d1000000003806205000003044120200000008c920400000058852000000000905204000000000210d0000053441201000000480e2000000004802204000000380620300000500c9203000000588120000000000000010000000012103000000290d20100000000c5106000000000a1040000000000005000000000000100000000061000000001802203000000190d200001895010d3000000000105104000003144120100000000000060000054441203
  | 7, 51 => 0x29052010000000000005000000000000b000000590d2000000000881203000000008110000000000000060000003802200000001044020300000000000100000000000005000000480220100000038062060000021481200000000000000f0000050484202000003148120400000000c91060000000012103000000380a20000000524c0201000000480a202000000380220300000000000130000000012103000005448120200000000061030000005881200000005040620300000000121040000053002201000000480e200
  | 7, 52 => 0x214c1201000000000000c00000000000050000000000007000000480e200000005300220100000059092010000000000005000000284120300000000000050000052441200000005100220000000048812020000000000006000000000001700000500c9204000000380a20300000524c02010000032505204000000000000f000000000000300000000c910500000000000000000000002101000000000000f0000000012101000000010d11000000000000050000000012102000005100220300000524062000000000006106
  | 7, 53 => 0x325052000000000006106000000010d102000005240220200000039012010000000000002000000000610c00000000c9105000000190d200000000010110000000000021040000000012103000000000610900000000000010000052441202000000090d201000000000e10500000038c1204000000000000100000008852000000052002202000000290d202001912150130100000000000170000000002100000000388520000000000000050000000012104000000000e100000000390520200000000000050018d21481303
  | 7, 54 => 0x21020000003802202000005344020300000008c920100000000c9106000000380a20400000534802010000054406203000000290d2020000043501200000000480e2020000054441203000000000a100000000000000f00000048022000000005841204000000001210000000544022040000001802205000005244120000000000c0101000000380a204000000000000f0000000041106000000000e10a000000004110600000000411060000052441200000000000610500000000061030000000105100000000090d201
  | 7, 55 => 0x84120200000058c92030000000000017000000280620300000000000000000000000014000000000001500000000061030000000000006000000000000f00000214c12020001203802301000000480220100000324412030000000000005000000000000400000048c12040000000105111000000000a106000000000a10000000058c12000000000002103000000000000f00000544c02020018d214c13010000001802206000000010d10100000038062060000000105111000000280620200000000061000000053481203
  | 7, 56 => 0x210300000000000050000002806200000004348520000000000c91060000050085201000000590d20000000524412000000004806204000000380220000000000000050000004841204000000480a20000000000000100000000000000000000180220400000058c1202000000190120400000018022040000000012105000000000a100000000000210000000510c920300000000c9106000000480a20000000544c1200000000004110500000304c0201000000480e200000000000e10500000000000060000000085102
  | 7, 57 => 0x21040000000000016000000000e1040000003885200000005240e201000000180220600000504842010019131501303000000000000f0000000085100000000010111100000000121040000000002100000005348120000000500852000000000002102000000180220300000018c9203000000000000100000000000110000000109105000000000000000000000021000000000041106000000000000900000038852000018d214c13020000003802200000000000210a000000000210300000000121000000000000011
  | 7, 58 => 0x204c0201000000280620000000018022040000000000014000000000210a000000004110600000000021000000043485200000000000000f000000480e20000000028062000000000905203000000004110500000000021040000000085102000000000000a00000425052010000053402201000000480220100000500852020000000012100000000000a1000000001802205000000000610300000019012030000000085100000001044020300000000c9106000000000a102000000000000600000514022040000000000001
  | 7, 59 => 0xa100000000480a202000000480620200000000411060000043485202000000000000f000000480e201000000390520300000001011040000000002104000000000a106000000000000000000000c91050000000040100000000480220100000008c120100012028063000000000000006000000000000400000048022010000043501203000000090d2030000002841200000000380a204000000480a200000000000000600000514c020100000104402040000053481200000004144120400000000021020000000885200
  | 7, 60 => 0x10d10f0000000000011000005444020300000530022010000003885201000000001210200000038022000000002806200000000008410000000435012010000000000005000000000000f000000090d20000000000c91050000000000009000000008510600000000c9106000000380a203000000280620100000000121010000050406203000000000000f0000000081100000005444120400000415012020000000905202000000084120400012028063010000001802203000000000000600191325013040000000000000
  | 7, 61 => 0xc01010000000000000000000000210100000038022010000002802202000000180220200000038022020000000000005000000000001100000000021000000000002105000000000000f00000008412030000000000000000000480e20000000058c0201000000000e10500000000c9106000000000000200000434c120000000544c0201000000000e10500000028022000000031441203000000000210000000000411060000000000013000005010520300000048c92020000000000011000000000000f0000000000011
  | 7, 62 => 0x500000000000000000000000000001094148530100000000000100000020441201000005444120500000000c91060000000041106000000000000400000008c9200000000000a10600012028063020000000000011000000480e20000000008c9200000000000000900000008c920200000544402030000043485200000000090d20000000028062010000000000005000000480620300000544c120200000000411060000000000000000000380a2030000000002101000000000001600000530852010000000000012
  | 7, 63 => 0x2104000000001210500000058c120100000000000000000000000005000000000000f00000000000000010d424c930400000544c92030000003802201000000010d1020000000000013000000000000500000048c920300000000000160000053002201000000480a20000000000021000000000000011
  | 8, 0 => 0x314c120300000000c910600000000851030000000085100000000000000000000058c120200000000c91060000000109100000000000210200000000c5101000003148120400000000c9102000000000a101000000010910000000000851030000004885203000000000000f000000000e10100000435092040000054485202000000010d1050000000000012000000088120300000039012030000002802202000000001210400000000000070000000000011000000000000d00000000811010000000105102000000000000f
  | 8, 1 => 0x109101000000000000a00000000000100000000012101000000000210000000000c510100000000c51020000000041101000000010910000000000c510400000000851020000005905200000000090d20200000434c120400000000061030000042501202000000180220400000000c11000000000041103000000380a202000000190920200000018812010000000002101000000000000f000000000a1000000021481200000000000000800000000121020000000109104000005448520300000000000150000000006102
  | 8, 2 => 0x43501204000000090d2040000000105103000000000000200000000c5104000000000a10100000001011020000000002101000000000210400000000c910300000000c910500000000000000000004885202000000001210100000000021030000000041101000000000210400000048022040000000002103000005244120300000000c11010000000081103000000000001000000544c92010000000105105000000010110200000019092030000053505201000000590520200000000121030000000006100000000000e100
  | 8, 3 => 0x210500000000411020000000109102000000000a106000000000610400000018c1201000000000a1020000000085101000000010d1000000005885202000000000000800000544c92030000000000001000000000000200000000c11030000000000002000000004110100000424c9203000000484120100000038022020000000000006000000000e1000000002802202000000000000900000000000110000000000011000000004010300000000c510300000008c92040000000081100000000188120000000000c5104
  | 8, 4 => 0x10d102000000000000200000000411010000000000017000000010d1000000000041101000000190920100000000121050000000002103000000010110400000028022000000005841201000005348120200000000c11030000000109100000000380220400000000c51000000000006100000004348520000000001051030000000012100000000000e101000000000a10100000058412030000000000006000000000a1040000000041104000000010910200000001091010000000085101000000010910300000028c1203
  | 8, 5 => 0xa1010000000002105000000000000c000000480220300000001051050000000000000000000010d100000000590920200000000c51000000003802202000000001210000000000c910000000000021000000003901200000000000000f00000001011000000000101103000000000610300000000c110000000000c910500000001051000000000000004000000010d10000000000021020000000081100000000000e10200000000c510300000000061030000030441202000000000a1010000042485201000000000000f
  | 8, 6 => 0x11000000008510000000000c910100000000411010000032501204000000001210400000008c92030000000101103000000000610000000000411030000002905200000000000e1000000000012101000002148120300000000c110400000000811010000000006101000000000610300000001011000000000000007000000090520000000000000010000000000010000003248120000000000021030000000101102000000000210200000008c12010000000000008000000008510200000001051010000000002102
  | 8, 7 => 0x1210200000414412040000000101101000000000000a00000000c1100000000000000c00000000021000000000002100000000000210600000000000060000000000010000000000610300000000c1101000000008110100000000c510000000000411020000000000005000000010910500000000811010000031501201000003250520400000000000150000000101102000000000000600000000000130000000002102000000010110100000000411020000000002101000000000001600000000811040000000000005
  | 8, 8 => 0xa1020000030481203000000010510200000544c9202000000000000400000009012000000000006103000000010d103000000000001000000000121000000032481204000000480220000000008c520200000001051000000000000001000000090520000000038812010000031441202000000000a10200000000c1102000000000a10300000000811010000042505202000000000000e00000018c1202000000000000f000000008510500000038062000000000041105000000000a10000000008852010000000006100
  | 8, 9 => 0xf0000000105102000000010d101000004150120200000009052020000000000002000000000e100000000000210000000000121000000032481204000000000000f0000000002102000000010d1020000031441200000000010d1020000000105102000000000a10300000000c510200000058c520200000008c1200000000000000f00000000811000000000000004000000000001400000001011010000002802200000000084120300000000811000000000101100000000010110100000000000020000000002101
  | 8, 10 => 0xe0000000002102000000010d1000000000000012000000488520400000000000050000001802201000005448120000000000851010000000000016000000000a101000000004110100000059052040000000012104000000010d10000000000c110100000000000060000000006102000000000e101000000000000300000000c510200000544c520000000000c9100000000000a1060000043501204000000000a102000000390920000000000021010000000002100000000008510200000001051000000000109101
  | 8, 11 => 0x48022000000054441204000000004110100000001011050000000002103000000000e101000000000000500000000c51030000000000014000000190d202000000000000500000000c91060000000000016000000010d1030000000002103000000000000300000000000110000000000000000004348520000000000c110100000000121030000000041103000000000000400000000c91040000000105102000000000a102000000000e102000000010d100000000001210000000000c110400000000021050000052441203
  | 8, 12 => 0x1210300000000c1104000000000a10400000000000020000000002103000000190d2000000000909200000000001210100000000021030000000006100000000390120000000000c11000000000105104000000004110600000000851010000000105104000000084120100000000411030000000002105000000090520000000000c910100000544c120100000434852020000000002101000000010d10200000038812000000000041106000000000000900000028c5201000000000a10000000000c91060000000105103
  | 8, 13 => 0x488120000000028c5204000000000000a00000009092000000000000010000000010d1010000000085104000000000000a0000003885202000000000e10200000000c9103000000000000d000000000e101000000010510200000000000060000000081100000000000000a000000000001100000001011020000000000005000000000000f00000000021020000000085105000000004110000000534852040000000002105000000010910000000214412010000000000002000000000210300000000121030000003806202
  | 8, 14 => 0xf000005244120200000001051030000000081106000000010d10400000000c510300000000121020000000002102000003148120100000000c110400000058c120000000434c12030000000041100000000010110400000544852010000000002104000000000e1000000000109103000000000e1010000003802200000000000001100000000c1100000000000a104000000000a100000000001210100000000000030000000002100000000188120000000544c5200000000000a105000000010d1010000003881202
  | 8, 15 => 0x8110000000000c110200000534852000000000000011000000000001200000000c11040000000000000000000010d10500000001051010000000105101000000008110300000000c91030000005881202000000000e1010000000000011000000000001100000000c1100000000000a10100000000021030000053481203000000000a10100000058c1203000000000210000000000811010000000006102000000008110200000000c510400000000c91040000000000004000000008510100000000000040000021481200
  | 8, 16 => 0x60000003802201000003048120300000000c510400000000021030000000081104000000001210400000000c110200000544c12000000000101100000000000a10100000001091000000000041105000000000610000000000000040000000002103000000010d1020000000085103000000000210100000000c9100000000000a1000000001901203000000000001100000000061000000000109102000000180220000000000411030000000041104000000000000500000028c520000000000c1103000000000e101
  | 8, 17 => 0x105103000000008510000000028022000000000000000000000010910400000544c120100000544812030000003806201000000000000f00000534812000000000002100000000010d1000000000000010000005348120200000058412030000000000001000000000000f000000008510500000000000050000042501201000000001210200000214c12010000000909201000000000e10000000001011000000000041100000000000000300000000c9104000000000e103000000000210e00000028062020000000081105
  | 8, 18 => 0xe10100000001051020000054485204000000010510000000000c51040000000000003000000000e103000000488520000000534852000000000000006000000290120400000000811030000000105105000000010d10000000000c910300000058c920300000000411000000000041100000000000e10000000544852020000000109102000000010d1000000000085105000000000001000000048c5200000003044120200000000121030000000085100000000000001200000000c9102000000000000c0000003802201
  | 8, 19 => 0x10110500000000851050000000002103000000000001400000000c910000000000121010000054485204000000000e101000000590d200000000000a10400000001011020000000000005000000000000200000000851010000000081106000000000a103000000000a10000000000c9106000000000e100000000000e1060000000000015000000000a1000000002802200000000000610200000058412030000000012102000000088520300000000021030000000085100000000004110400000000c9100000000000000b
  | 8, 20 => 0x411060000000000004000000000000f000000000000500000214c1202000000000000f000000388520000000028c5203000000000e1010000000012101000000008510000000000c510400000001011030000000109100000000000e10200000544c120100000000c910000000058c120000000008c92000000032481202000003144120200000000c91010000000006105000000004110300000000000120000000085103000000000000b0000043501202000000090d20200000000811010000000000006000000480a200
  | 8, 21 => 0x280220200000000121030000000000001000000010110100000008c52010000054441201000000000000a000000010d1000000000041102000000000000f0000000000011000000000a10500000028c1200000000001210500000534812010000000000004000004144120200000000021030000000000002000000008110400000008c12000000000000003000000000e10000000000c51060000000041102000000000a100000000010d102000000004110200000000c9106000000000000300000008c92030000000081100
  | 8, 22 => 0x12000000000210e000000000210400000000021030000054481201000000010110500000008c1200000000008510b0000000002100000000000000f0000000885201000000010110300000000021030000030481203000000480a20100000000c510200000000c5103000000008510300000038022010000000000005000000000610d00000000411000000005901200000000000210000000000000060000000085102000000088120100000018c9204000005448120000000000c110400000544c12000000000002103
  | 8, 23 => 0x424852020000000000012000000000a101000000000a1040000000000001000000000e102000000390520400000000c11000000000000012000000000a10100000000c1106000000001210200000058c920100000008852040000000105101000000000a1040000000041100000000000a1030000000041103000005244120200000000c510000000500852020000000000000000000010910000000001051040000003881200000000010d100000000000a1010000000105100000000000000500000000851040000000000001
  | 8, 24 => 0x10d10200000000000100000000000012000003248120000000000851000000000085100000000008510600000000021010000000012105000000000610300000000851000000000006101000000590120000000000c1104000000000e10000000000c510400000000c11050000000000017000000010d10100000544c12010000000081100000000000000f00000000411050000004885202000000000210100000058812020000000000005000000010d101000000000000600000000c510300000000000060000032505203
  | 8, 25 => 0x2104000000000000b000000010510300000544412020000000000003000000004110300000000000050000000000006000000000001600000000061000000000002103000000000a100000000000000e0000000000006000000010910200000000c110000000000c910000000039012000000005901200000000000210400000000121010000043501201000000090d2010000000041104000000590d2000000000105102000000000000300000000c910600000000c910500000214412030000000081100000000000000f
  | 8, 26 => 0x411000000053441202000000488520200000000000020000000006104000000004110400000324c12010000000006104000000480a201000000000a10200000000000030000000085100000000088520000000000c1105000005344120300000008412010000000000009000000000a102000000000000f000000000000500000325052000000000101103000000000000600000000c1100000000010d10100000000c110200000048c120100000000021020000000885202000000000e10300000001051000000000002102
  | 8, 27 => 0x544c9202000000190120200000039092010000000000007000000000a106000000000a100000000000000f000000000001000000000c110000000008c120000000000c1102000000010110000000001051030000000006104000000008110100000000c910400000000c9103000000190d201000000010d1020000000085101000000000000500000058c920000000000c1105000000010d100000000010510400000000c1100000000000a1010000000000010000000000001200000000c510100000000411050000000012101
  | 8, 28 => 0x1100000000c110600000000c910500000038412030000000000009000000008510100000000c1104000000000a101000000010d10000000000c910200000414c1202000000010d1000000000002101000000000e1020000000000010000004150120400000009052040000000000001000005010d20000000000851010000000000006000000010910500000001051000000002901203000000000a10100000000c1100000000000000700000039092000000000002101000000000000200000000021010000003885201
  | 8, 29 => 0x2148120000000001011010000000006103000000588520400000000000030000000000004000000008510500000058c520400000028c1203000000000000f000000004010300000048c120100000304812010000000002103000000010910000000048c1203000000000a100000000384120200000000c1106000000008110100000000000030000000000000000000590520000000000811040000000000004000000000000400000000c1104000000010d1000000000000002000000590d202000000008110300000000c9101
  | 8, 30 => 0x10d100000000000e103000000000e10000000000000010000032505202000000000e10600000424c520000000000411010000000885200000000000210000000000c510400000008852040000000105103000000280620000000048812020000000000001000000000000f000000008510100000000c1100000000000000400000028062040000000012101000000010d105000000000a10d0000000000006000000000000f00000324c1200000000000a1030000000002100000000000000400000048412000000000002100
  | 8, 31 => 0x544c120000000000000000000000041103000000290d20100000000000010000000002101000000000001500000434c920400000000c110500000059052010000000002103000000000a103000000000e1030000000101101000000010d101000000000e1000000042481200000000004110500000000c1100000000004110300000001011020000000105104000000001210200000001011030000000041100000000008510200000000c1102000000290d204000000010d100000000000e10000000000021010000000000005
  | 8, 32 => 0x2102000000010d1000000000101100000000000a106000000001210200000058c52010000000000011000000010d1010000052441200000000010d10400000544c12020000000081103000000004110500000018c12000000000101103000000000e1060000000081103000000280620300000214812040000000041103000000001210300000000000010000000002102000000000e10400000000c1100000000004110400000000c910400000001051040000000002103000005008520100000544c1203000000380a204
  | 8, 33 => 0xc1102000000090d2000000000085100000000000e100000000000a1020000000000011000000000610300000434c12010000000109102000000000210200000000000010000000105103000000010d100000000010d1000000000041103000000484120100000000c910300000029052040000000002100000000000000a00000000411030000004841203000000000000300000000c910600000000c11020000000002101000000000000200000000000000000000085102000004148520100000001011040000000002104
  | 8, 34 => 0xf000000000000f0000000002103000000000610000000000c1103000005244120000000324c1203000000000000500000000c910400000000000110000000101102000000010d1010000000041101000000000000d000000000000600000000c1105000000010910000000048412000000000002102000000390920100000048c1201000000590d20000000000c11010000000002104000000008110600000000c9102000000000610500000000c910400000000c110000000000c5103000000000000300000000c9100
  | 8, 35 => 0x2101000000000000000000000000020000000000000000005448520200000000c110200000000000060000000000000000000000000300000000c510100000000c910500000000000160000001909204000000010d1010000000006106000000010910000000000021020000043501200000000008110200000000c1103000000010d101000000000a10200000000811020000053481204000000008510500000435012010000000000006000000000e10b00000000c1102000000001210000000001051040000000105101
  | 8, 36 => 0x210100000000c510200000000c91030000000085101000000010110100000000000040000000000013000000000000f0000000085100000000010d100000000000610100000001091010000000085100000000000e10100000048c92010000000006103000000004110000000414412000000000085101000000001210200000000c9101000000000e103000000000000f00000001011000000000012102000000590d202000000000e109000000010510400000000021030000000109103000000000000e0000000101103
  | 8, 37 => 0x380a20300000000c110300000000411000000000109100000000000001000000001051020000000109103000000010510500000058c12010000000000002000000010110000000001051020000000000002000000000e100000000010d10200000000811000000000885200000000000000f000000000210100000434c1201000000000000600000000c9100000000290d2030000000000006000000000001700000000c5102000000584120000000000c1106000000000e104000000000a10300000000411000000042481202
  | 8, 38 => 0xc9100000000000a10600000000021030000000000000000000000210100000000000110000030441204000000010d100000000000a10000000000c91030000000041105000000000001100000008c120300000058c920000000000000170000004885200000000010d10000000029012020000000002101000000000610000000000401030000000000005000000001210000000000c110300000000000110000000002106000000000000f0000000085100000000000e102000000088520000000000c91040000053485203
  | 8, 39 => 0x6100000000000001600000000000100000000012104000000000000f000000000000f000000001210400000039012020000000085100000000000001000000000000000000000000003000000000000b000000010510000000008c1201000000000a1010000000012104000000000000200000000000160000000081102000000010d10100000000c51060000000085100000000000a100000000010d102000005448120400000000021020000000000006000000000a100000000008110100000000c91050000000101103
  | 8, 40 => 0x610c00000000021080000000081103000000480220200000000c910300000000021000000003885200000000010910500000000000000000000000005000000390920000000001011010000041441201000000008110200000324c1200000000000210000000000c110300000000c9105000000000000c000000010110100000000021010000000000007000000004110400000000c1101000000000000c000000590d204000000010510000000000000050000004841203000000010d10200000000c910300000434c1200
  | 8, 41 => 0x41104000000000a1020000000006103000000000a101000000000610600000008c1201000000000a102000000004110400000000c91050000000000003000000000a104000000000e10400000544852000000000002100000000000e100000000001210000000000c11010000000012102000000000e1000000000002105000000008110500000000000050000000000012000000004110300000000000000000000000005000000000000f00000000c110100000058c12010000000002100000000000e1010000000000008
  | 8, 42 => 0xe100000002148120100000000c510000000000021030000021441202000000000e10100000000c910600000524412000000000012100000000010d1030000000002101000000000e10200000000c5105000000000e10100000000000040000000006104000000000e103000003250120300000000c110300000001091010000000101100000000010110300000000c11060000000000000000000010d10200000058852000000000002102000000000000000000000c9105000000000210100000000c11000000002841200
  | 8, 43 => 0x480e20400000000021030000000002103000000090120000000001051020000000012100000000000a1000000000000006000000000000600000000000050000000002105000000000a104000004350120000000000851000000053481204000000000001100000324c120200000048c52030000000041100000000000e102000000001210000000534852020000001901201000000000a100000000010110100000000021020000000002101000000010d1000000004806204000000004110300000000021040000000081102
  | 8, 44 => 0x10d100000000090920400000000c9101000000000000f00000000c910600000000061000000000002101000000000e1010000000006104000000000a1050000053481200000000000000000000000c1101000000000e10000000000c910400000000000110000000041100000000010110400000544c9200000000000000000000000061050000000002102000000000210300000000000000000000081100000000000e10000000000811030000000000003000000000610300000000c910300000028022040000000002106
  | 8, 45 => 0x90d2010000000000000000000000000800000000c9102000004250120300000009092030000000000006000000000a100000000000610000000000811010000000041102000000000e102000000000a100000005244120400000001051000000000109102000000000000500000000061000000000041105000000000a10100000001051000000000085100000000010d102000000000e1010000000006103000000480a200000000000210200000000021010000003901201000000000610200000000021030000002802203
  | 8, 46 => 0x2000000010d100000000000000300000000c9103000000590120000000000000110000053485203000000010d102000000000a10100000544c9203000000010d1010000000000000000003150120100000000000050000000000005000000480a20100000000000170000000002101000000000210300000000c110200000058c1203000000000001300000000411060000000081100000000390920200000000851020000000002102000000000210000000000c9100000000000000400000000021040000043501201
  | 8, 47 => 0x10110400000000021040000000006103000000000610300000000c1101000000000a100000000000e100000000000a1010000000002100000000000000f0000000000003000000010d10200000000c1101000002144120400000048c5203000000000001100000325052000000000081100000000000000f000000010110400000000021040000000002105000000000210300000000061030000000002102000000010d10000000000c5103000000000210400000534412000000000002103000000010d10200000000c5105
  | 8, 48 => 0x434852000000002806200000000000001600000214c12020000000002102000000000a10000000028062020000000041104000000000210300000059052010000005905203000000000a10000000000811000000000085101000000004010300000000c11010000000000006000000004110300000214c1201000000000e100000000010d1000000000000014000000090d20000000029052000000000105100000000010d100000000280620000000000021020000054481200000000010d10000000000000060000005885201
  | 8, 49 => 0x1210100000000c91000000021441204000000000a10200000000c9106000000000000300000028022020000053481200000000001210000000008c5203000000000000600000000000060000000012100000000004110600000000c110000000000000110000000000001000000000000f000000000e1000000000000005000000590d200000000000610500000000c9104000000008110100000000000100000000000006000000010510300000414412040000000002100000000008110000000000000050000000081102
  | 8, 50 => 0x5448520400000028c1204000004144120200000000c91040000000002101000004250520200000000851000000000000006000000000000b00000000000100000000006103000000008110400000000c110000000000000100000053441202000000010d1000000000085100000000010110200000000811000000000000000000000480a20000000038022040000000101103000000000001100000028022000000000085106000000000a1050000000000005000000010d101000000000001100000000c01010000043509203
  | 8, 51 => 0x105104000000000e10200000000c110600000008c520300000000000050000000041106000000000000600000001011010000000002105000000000000500000000c010100000000851000000000081100000000010d10000000000021000000000085101000000008510200000000c91050000000000006000000488520000000028022010000000085100000000000210300000058c920000000544c92000000000000006000000010110300000059052040000000041100000000000000f00000038022020000000085100
  | 8, 52 => 0xc11010000000041104000000000610600000000000030000000085106000000008510000000000851000000000006103000000280220000000000061030000000002103000000010d10100000058c92040000002802200000000000000000000000000070000003802200000000010910300000028c12030000000000005000000010d10100000534852030000000081102000000000000500000048852010000000002100000000001210000000000121030000002806200000000000a10000000415012030000000012102
  | 8, 53 => 0x5000000000610000000000c9103000000000000400000001011040000000000004000000000000a000000008510a00000001091030000000006106000000000e105000000000000300000038812020000000006104000005448520100000000000000000000105100000000010510300000000000070000000000005000000000210000000000021030000000041103000000010d10100000000c1101000005348120300000000021010000000041105000000010d1000000000012105000000008110300000000c0101
  | 8, 54 => 0x488520200000000000110000000000005000003150120300000000000020000000000005000000000210100000000c9103000000000000f000000000000300000544852000000000085101000005348520200000058c92030000000000001000000000210100000000061010000000105100000000010110000000000c91050000000000017000000480e2010000000101104000000000e100000000000210300000001011040000000000000000000480220300000000c9104000000010d10200000000411060000000041103
  | 8, 55 => 0x85100000000010d10100000000411030000000041104000000000000000000000021000000000002100000000010d100000000010510200000000411040000000000013000000000000f00000000c91050000005885200000000000e1020000000085100000000008110200000544c1200000000000000a000000000000400000000000060000000000005000000001210100000000021000000000000011000000004110600000000c910300000000c9103000000000000e000000000000f00000001051030000000000013
  | 8, 56 => 0x210000000000021000000000000000000000004110300000000021000000000002100
  | 9, 0 => 0x4000000010d101000000000610000000000c9103000000000a104000000000000b00000001091010000000000003000000000610000000000000050000000000000000000000000600000000411000000000000006000000004110200000000000000000000041103000000000000100000000000040000000012101000000008110100000000000010000000000002000000000000300000000c51020000000000002000000004110100000000000000000000000001000000000000100000000000030000000000001
  | 9, 1 => 0xa1030000000101101000000000610200000000c510000000000c910200000000000040000000000000000000000000600000000000010000000000003000000000000900000000c110200000000000010000000000005000000000000000000000000020000000105102000000000210000000000000050000000000002000000000000100000000c91000000000109103000000000000100000000411000000000101100000000010d1010000000000003000000000000300000000000060000000000002
  | 9, 2 => 0x200000000000000000000000003000000000000400000000000030000000000002000000000000600000000000050000000000000000000000000200000000000020000000105100000000010510300000000c5103000000000000400000000000000000000002101000000004110200000000000010000000041100000000000000100000000000000000000000003000000000000100000000000000000000000000000000010110300000000000030000000085100000000000210100000000000010000000085100
  | 9, 3 => 0x40000000000000000000000210300000001051000000000006101000000000000000000000c1100000000004110300000000121000000000105100000000000000100000000c91030000000000003000000001210300000000000000000000000005000000000000000000000000030000000000000000000010910200000000000010000000000002000000000e102000000000a1000000000000005000000000a1020000000000000000000000000000000000c9104000000000000000000000121040000000101104
  | 9, 4 => 0x851000000000000006000000000000200000000021000000000002100000000010d100000000000000300000000000010000000000003000000000000000000000021030000000085100000000008510200000000021040000000000001000000000000e000000000000000000000000000000000081101000000000000300000000c5101000000000210000000000000000000000002103000000000a1000000000002104000000000000500000000000000000000000000000000000e10100000000000050000000002101
  | 9, 5 => 0x2100000000000210000000000000000000000000000000000000210000000000000050000000000000000000000210300000000000000000000002104000000010510300000000c510300000001011030000000000004000000000000300000000000000000000002100000000010110400000000000030000000000005000000010110000000000000040000000000002000000000000100000000000000000000000005000000008110200000000121020000000000000000000000000600000000000060000000000005
  | 9, 6 => 0x0
  | 10, 0 => 0x3000000000000400000000000000000000000000000000000000000000000000030000000000001
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 12 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_31 roots_31 9 s ws hint
  | 1 => checkCutEntry dom_47 roots_47 9 s ws hint
  | 2 => checkCutEntry dom_55 roots_55 9 s ws hint
  | 3 => checkCutEntry dom_59 roots_59 9 s ws hint
  | 4 => checkCutEntry dom_61 roots_61 9 s ws hint
  | 5 => checkCutEntry dom_62 roots_62 8 s ws hint
  | 6 => checkCutEntry dom_30 roots_30 7 s ws hint
  | 7 => checkCutEntry dom_15 roots_15 6 s ws hint
  | 8 => checkCutEntry dom_23 roots_23 6 s ws hint
  | 9 => checkCutEntry dom_27 roots_27 6 s ws hint
  | 10 => checkCutEntry dom_43 roots_43 6 s ws hint
  | 11 => checkCutEntry dom_51 roots_51 6 s ws hint
  | 12 => checkCutEntry dom_29 roots_29 6 s ws hint
  | 13 => checkCutEntry dom_45 roots_45 6 s ws hint
  | 14 => checkCutEntry dom_53 roots_53 6 s ws hint
  | 15 => checkCutEntry dom_47_16 roots_47_16 6 s ws hint
  | 16 => checkCutEntry dom_55_8 roots_55_8 6 s ws hint
  | 17 => checkCutEntry dom_59_4 roots_59_4 6 s ws hint
  | 18 => checkCutEntry dom_61_2 roots_61_2 6 s ws hint
  | 19 => checkCutEntry dom_15_16 roots_15_16 5 s ws hint
  | 20 => checkCutEntry dom_23_8 roots_23_8 5 s ws hint
  | 21 => checkCutEntry dom_39_16 roots_39_16 5 s ws hint
  | 22 => checkCutEntry dom_39_8 roots_39_8 5 s ws hint
  | 23 => checkCutEntry dom_27_4 roots_27_4 5 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_55 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_59 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_61 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_62 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_30 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_43 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_51 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_29 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_45 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_53 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_55_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_59_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_61_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39_8 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27_4 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_63 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
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
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := z5_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 16 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_16 : ∀ i, 16 ≤ i → i < 32 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_32 : ∀ i, 32 ≤ i → i < 41 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 9 32 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 41 → Z 6 i = true := (range_split (range_split z6_0 z6_16) z6_32)
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
private theorem z7 : ∀ i, 0 ≤ i → i < 256 → Z 7 i = true := (range_split (range_split (range_split (range_split z7_0 z7_16) (range_split z7_32 z7_48)) (range_split (range_split z7_64 z7_80) (range_split z7_96 z7_112))) (range_split (range_split (range_split z7_128 z7_144) (range_split z7_160 z7_176)) (range_split (range_split z7_192 z7_208) (range_split z7_224 z7_240))))
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
private theorem z8_144 : ∀ i, 144 ≤ i → i < 160 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_160 : ∀ i, 160 ≤ i → i < 176 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_176 : ∀ i, 176 ≤ i → i < 192 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_192 : ∀ i, 192 ≤ i → i < 208 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_208 : ∀ i, 208 ≤ i → i < 224 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 208 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_224 : ∀ i, 224 ≤ i → i < 240 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 224 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_240 : ∀ i, 240 ≤ i → i < 256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 240 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_256 : ∀ i, 256 ≤ i → i < 269 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 13 256 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 269 → Z 8 i = true := (range_split (range_split (range_split (range_split (range_split z8_0 z8_16) (range_split z8_32 z8_48)) (range_split (range_split z8_64 z8_80) (range_split z8_96 z8_112))) (range_split (range_split (range_split z8_128 z8_144) (range_split z8_160 z8_176)) (range_split (range_split z8_192 z8_208) (range_split z8_224 z8_240)))) z8_256)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_0 : ∀ i, 0 ≤ i → i < 16 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_16 : ∀ i, 16 ≤ i → i < 32 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_32 : ∀ i, 32 ≤ i → i < 48 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 16 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_48 : ∀ i, 48 ≤ i → i < 64 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 16 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_64 : ∀ i, 64 ≤ i → i < 66 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 2 64 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 66 → Z 9 i = true := (range_split (range_split (range_split z9_0 z9_16) (range_split z9_32 z9_48)) z9_64)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_0 : ∀ i, 0 ≤ i → i < 10 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 10 0 = true)
private theorem z10 : ∀ i, 0 ≤ i → i < 10 → Z 10 i = true := z10_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z11_0 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := span_ok (by decide +kernel : span (Z 11) 1 0 = true)
private theorem z11 : ∀ i, 0 ≤ i → i < 1 → Z 11 i = true := z11_0
theorem checked (s : Nat) (hs : s ≤ 11) : ∀ i < NN s, Z s i = true := by
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
  · exact fun i hi => z11 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_63 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 7 5 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 11) (h : RunD dom_63 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_63 roots_63 goal_63 12 := by
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

theorem low_63 : Lower dom_63 roots_63 goal_63 12 := S_63.noCircuit

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

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 16]⟩], 17⟩

theorem wit_mono : PEqualNP.MetaComplexity.Monotone2 wit := by
  simp [wit, PEqualNP.MetaComplexity.Monotone2]

theorem wit_sz : wit.size ≤ 12 := by decide

set_option maxRecDepth 40000 in
theorem wit_ev : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = Nat.testBit (4278124202 * 2 ^ 32 + 4276808360) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_63.testBit r.val = (fun x : Fin 6 → Bool => Nat.testBit (4278124202 * 2 ^ 32 + 4276808360) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) (pt6 r.val) := by decide +kernel

theorem lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124202 * 2 ^ 32 + 4276808360) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) t → 12 ≤ t :=
  lower_to_circuit6 (fun x : Fin 6 → Bool => Nat.testBit (4278124202 * 2 ^ 32 + 4276808360) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) goal_63 12 hT6 (by unfold IsConst; decide) low_63

end PEqualNP.Outside.L_meta_44976_aux

theorem PEqualNP.Outside.L_meta_44976 :
  ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124202 * 2 ^ 32 + 4276808360) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124202 * 2 ^ 32 + 4276808360) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  exact ⟨PEqualNP.Outside.L_meta_44976_aux.wit, PEqualNP.Outside.L_meta_44976_aux.wit_mono, le_trans PEqualNP.Outside.L_meta_44976_aux.wit_sz (PEqualNP.Outside.L_meta_44976_aux.lower s hs), PEqualNP.Outside.L_meta_44976_aux.wit_ev⟩
