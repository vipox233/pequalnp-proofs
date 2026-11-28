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

namespace PEqualNP.Outside.L_meta_38141_aux

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
def goal_55 : Nat := 0xfefeeeeeeeee8080fefeeeeeeeee8080fefeeeeeeeee8080fefeeeeeeeee8080
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59_4 : Nat := 0xf0f0f0f0f0f0f0f0
def goal_59_4 : Nat := 0xffffffeeffeeff88ffffffeeffeeff88ffffffeeffeeff88ffffffeeffeeff88
def roots_59_4 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_31 : Nat := 0xffffffff
def goal_31 : Nat := 0xfeeefa80feeefa80feeefa80feeefa80feeefa80feeefa80feeefa80feeefa80
def roots_31 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_51_4 : Nat := 0xf000f000f000f0
def goal_51_4 : Nat := 0xffffeeeeeeee8888ffffeeeeeeee8888ffffeeeeeeee8888ffffeeeeeeee8888
def roots_51_4 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfafafaaafaaafa00fafafaaafaaafa00fafafaaafaaafa00fafafaaafaaafa00
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfcfcfcccfcccf000fcfcfcccfcccf000fcfcfcccfcccf000fcfcfcccfcccf000
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61_2 : Nat := 0xcccccccccccccccc
def goal_61_2 : Nat := 0xfffffffffffffaa0fffffffffffffaa0fffffffffffffaa0fffffffffffffaa0
def roots_61_2 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_15 : Nat := 0xffff
def goal_15 : Nat := 0xfa80fa80fa80fa80fa80fa80fa80fa80fa80fa80fa80fa80fa80fa80fa80fa80
def roots_15 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0]

def dom_29_2 : Nat := 0xcccccccc
def goal_29_2 : Nat := 0xfffffaa0fffffaa0fffffaa0fffffaa0fffffaa0fffffaa0fffffaa0fffffaa0
def roots_29_2 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xfeeefeeefa80fa80feeefeeefa80fa80feeefeeefa80fa80feeefeeefa80fa80
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_23 : Nat := 0xff00ff
def goal_23 : Nat := 0xeeee8080eeee8080eeee8080eeee8080eeee8080eeee8080eeee8080eeee8080
def roots_23 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0]

def dom_39 : Nat := 0xff000000ff
def goal_39 : Nat := 0xeeeeeeee80808080eeeeeeee80808080eeeeeeee80808080eeeeeeee80808080
def roots_39 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0]

def dom_45_2 : Nat := 0xcccc0000cccc
def goal_45_2 : Nat := 0xfffffffffaa0faa0fffffffffaa0faa0fffffffffaa0faa0fffffffffaa0faa0
def roots_45_2 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_53 : Nat := 0x33003300330033
def goal_53 : Nat := 0xfafaaaaaaaaa0000fafaaaaaaaaa0000fafaaaaaaaaa0000fafaaaaaaaaa0000
def roots_53 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_57_4 : Nat := 0x3030303030303030
def goal_57_4 : Nat := 0xffffffaaffaaff00ffffffaaffaaff00ffffffaaffaaff00ffffffaaffaaff00
def roots_57_4 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_54 : Nat := 0x55005500550055
def goal_54 : Nat := 0xfcfccccccccc0000fcfccccccccc0000fcfccccccccc0000fcfccccccccc0000
def roots_54 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_58_4 : Nat := 0x5050505050505050
def goal_58_4 : Nat := 0xffffffccffccff00ffffffccffccff00ffffffccffccff00ffffffccffccff00
def roots_58_4 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfefefeeefeeefa80fefefeeefeeefa80fefefeeefeeefa80fefefeeefeeefa80
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

namespace S_55
def pairsG : List (Nat × Nat) := [(1, 17), (1, 33), (2, 18), (2, 34), (3, 7), (3, 19), (3, 35), (5, 7), (5, 21), (5, 37), (6, 7), (6, 22), (6, 38), (16, 17), (16, 18), (20, 21), (20, 22), (20, 52), (32, 33), (32, 34), (36, 37), (36, 38), (36, 52), (48, 49), (48, 50), (48, 52)]
def r1sG : List Nat := [1, 1, 2, 2, 3, 3, 3, 5, 5, 5, 6, 6, 6, 16, 16, 20, 20, 20, 32, 32, 36, 36, 36, 48, 48, 48]
def r2sG : List Nat := [17, 33, 18, 34, 7, 19, 35, 7, 21, 37, 7, 22, 38, 17, 18, 21, 22, 52, 33, 34, 37, 38, 52, 49, 50, 52]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [6618814222599, 39668336890164, 5511251759623, 6610763387143, 6619083710727, 22003926176007, 39596112220423, 52781192057121, 52781460496657, 52785487024674, 52785755464210]
def xsM : List Nat := roots_55.map (· &&& dom_55)
def goalM : Nat := goal_55 &&& dom_55
def NN : Nat → Nat
  | 4 => 1
  | 5 => 12
  | 6 => 11
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x47baa070
  | 5, 0 => 0xfd05eeb0ae2f928597b5c1246b85db7447baa0703d0687ed28206f8320d129b41644d9061638e054077aa6ae066ead81
  | 6, 0 => 0xfd05eeb0c29480866b85db74514fa09150eeb30f47baa070290a2e9c20b49e3817bdcd4415dbc31515521a2e
  | 7, 0 => 0x47baa070
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xcc00cc00cc00cc00000000000000000000000000000000000000000000000000cc000000cc000000000000000000000000000000000000000000000000000000aa00aa00aa00aa00000000000000000000000000000000000000000000000000880088008800880000000000000000000000000000000000000000000000000033003300330033000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000000ff000000ff0000000000000000000000000000000000000000000000000000000000ff00ff
  | 0, 1 => 0xff00000000000000000000000000000000000000000000000000000000000000fc00fc00fc00fc00000000000000000000000000000000000000000000000000fa00fa00f000f000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000f000c000f000c000000000000000000000000000000000000000000000000000f0000000f0000000000000000000000000000000000000000000000000000000ee00ee00ee00ee
  | 0, 2 => 0xff00ff00f000f000000000000000000000000000000000000000000000000000ff00ff00cc00cc00000000000000000000000000000000000000000000000000ff00ff00cc000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000ff00cc00ff00cc00000000000000000000000000000000000000000000000000ff000000ff0000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x12830e55
  | 5, 0, 0 => 0x940e512c9851855872840b261ca15941872aca2c3156506208b2394415941a72ace0c39565051cab582ce55
  | 6, 0, 0 => 0x1281ca25a4a0c39581261ca1594187289a50620e5604a0c3956507b0e5694189395a5061ca3694187315a50730e56
  | 7, 0, 0 => 0x12830e55
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
  | 0, 0 => 0x1c7c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003f300000000000000000000000000000000000000000000000000000000000000700000000000000000000000000000000000000000000000000000000003ffe38300000000000000000000000000000000000000000000000000000000038c607f00000000000000000000000000000000000000000000000000000000007c1fff000000000000000000000000000000000000000000000000000000000003ffff
  | 0, 1 => 0x38000000000000000000000000000000000000000000000000000000000000000739ffc0000000000000000000000000000000000000000000000000000000000739f800000000000000000000000000000000000000000000000000000000000739f8000000000000000000000000000000000000000000000000000000000007000000000000000000000000000000000000000000000000000000000000000039c0000000000000000000000000000000000000000000000000000000000000380000000000000000000000000000000000000000000000000000000000000001fff
  | 0, 2 => 0x3ff9f800000000000000000000000000000000000000000000000000000000003fc1c7c0000000000000000000000000000000000000000000000000000000003fc00000000000000000000000000000000000000000000000000000000000003fc0000000000000000000000000000000000000000000000000000000000000383fc7c000000000000000000000000000000000000000000000000000000000383e000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x1295cfc0000000000000000000000000000000000000000000000000000000001014824000000000000000000000000000000000000000000000000000000000094a7f300000000000000000000000000000000000000000000000000000000000004f00000000000000000000000000000000000000000000000000000000002d6a30300000000000000000000000000000000000000000000000000000000018c606f00000000000000000000000000000000000000000000000000000000003c16da000000000000000000000000000000000000000000000000000000000001edb5
  | 0, 1 => 0x3c2000000000000000000000000000000000000000000000000000000000000037bdffc0000000000000000000000000000000000000000000000000000000002f79fd20000000000000000000000000000000000000000000000000000000002739f9000000000000000000000000000000000000000000000000000000000027212000000000000000000000000000000000000000000000000000000000002639d9000000000000000000000000000000000000000000000000000000000024389000000000000000000000000000000000000000000000000000000000001bdffff
  | 0, 2 => 0x3ff9fda0000000000000000000000000000000000000000000000000000000003ff5efe0000000000000000000000000000000000000000000000000000000003ff5a6e0000000000000000000000000000000000000000000000000000000003fe124a0000000000000000000000000000000000000000000000000000000003ebfdfd0000000000000000000000000000000000000000000000000000000003c3e925
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 22 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 22 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 22 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 22 then wireAt i else 0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_55 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_55 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]]
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
private theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 12 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 12 → Z 5 i = true := z5_0
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

namespace S_59_4
def pairsG : List (Nat × Nat) := [(4, 12), (5, 7), (5, 13), (5, 21), (5, 37), (6, 7), (6, 14), (6, 22), (6, 38), (20, 21), (20, 22), (20, 28), (20, 52), (36, 37), (36, 38), (36, 44), (36, 52)]
def r1sG : List Nat := [4, 5, 5, 5, 5, 6, 6, 6, 6, 20, 20, 20, 20, 36, 36, 36, 36]
def r2sG : List Nat := [12, 7, 13, 21, 37, 7, 14, 22, 38, 21, 22, 28, 52, 37, 38, 44, 52]
def mpG : Nat := 0x1ffff
def pool6G : List Nat := [6618881594631, 39668404262196, 39608274716454, 22016087623446, 39603996591909, 22011809498901, 39604232390437, 22012314781461, 6619151082759]
def xsM : List Nat := roots_59_4.map (· &&& dom_59_4)
def goalM : Nat := goal_59_4 &&& dom_59_4
def NN : Nat → Nat
  | 4 => 9
  | 5 => 21
  | 6 => 10
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x89a9a1a24c42d3b14774676138ef8e9531230a5e2c43643d2533bed9179912bb08f73c81
  | 5, 0 => 0x89a9a1a281d51cc75dfaef2556266a4a4c42d3b140c9955c39d3bb79382bc5712ed334af24fc98871c1fd7b516a2ecc714922a9e145a7bdb125f5771109e7e830ece67ec0be8b62f09c88c08096d94f4019d7270
  | 6, 0 => 0xddf3538389a9a1a281d51cc75dfaef2536d1f9c6346712e021e7ef5620def6a21fc19f2516a2ecc7
  | 7, 0 => 0x89a9a1a2
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x303030303030303000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000c000c000c000c000000000000000000000000000000000000000000000000000500050005000500000000000000000000000000000000000000000000000000000f0f00000f0f0000000000000000000000000000000000000000000000000000000f0000000f000000000000000000000000000000000000000000000000000000000f0f0f0f0
  | 0, 1 => 0xe0e0e0e0c0c0c0c0000000000000000000000000000000000000000000000000e0e0c0c0e0e0c0c0000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c0000000000000000000000000000000000000000000000000c0c00000c0c00000000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a0000000000000000000000000000000000000000000000000a000a000a000a00000000000000000000000000000000000000000000000000080808080808080800000000000000000000000000000000000000000000000005050505050505050
  | 0, 2 => 0xf0f00000f0f00000000000000000000000000000000000000000000000000000f0c0f0c0f0c0f0c0000000000000000000000000000000000000000000000000f0a0f0a0f0a0f0a0000000000000000000000000000000000000000000000000f0a0f0a0f000f000000000000000000000000000000000000000000000000000f030f030f030f030000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000e0e0e0e0e0e0e0e0
  | 0, 3 => 0xf0f0f0f0c000c000000000000000000000000000000000000000000000000000f0f0f0f0a0a0a0a0000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000f0f0f000f0f0f000000000000000000000000000000000000000000000000000f0f0f000f000f000000000000000000000000000000000000000000000000000f0f0c0c0f0f0c0c0000000000000000000000000000000000000000000000000f0f0a0a0f0f0a0a0000000000000000000000000000000000000000000000000f0f0a000f0f0a000
  | 0, 4 => 0xf0f0f0f0f0f00000000000000000000000000000000000000000000000000000f0f0f0f0f000f000000000000000000000000000000000000000000000000000f0f0f0f0c0c0c0c0
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x1d5d234b501d715350085c54d481e5d2414075948e401d716210079750d40215cd0d007d758b4
  | 5, 0, 0 => 0x1d5cb1c6501d71648b501d5cb184501d6d734b589d69234b601748d2c5501d48d2c2501d5d2409501d48d2c1501d5d348b50215d134b501d552342501748d200501d61234b501d5d23cb501d71634b5
  | 5, 0, 1 => 0x1d5d234b501d5d548d501d5cd2c6501d5d5346500075c54d4
  | 6, 0, 0 => 0x75748d2c6601d5d234b501d5d548d501d5cd2c6575748d30b675748d2c0679d5d234b675748d2ca685d5d234b601d48d2c25
  | 7, 0, 0 => 0x1d5d234b5
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 34
  | 5 => 40
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
  | 0, 0 => 0x1fe1f000000000000000000000000000000000000000000000000000000000001ffff000000000000000000000000000000000000000000000000000000000001e00000000000000000000000000000000000000000000000000000000000000001e0000000000000000000000000000000000000000000000000000000000001ffe1000000000000000000000000000000000000000000000000000000000001e1ff000000000000000000000000000000000000000000000000000000000001e1ff0000000000000000000000000000000000000000000000000000000000001fff
  | 0, 1 => 0x1e000000000000000000000000000000000000000000000000000000000000001e000000000000000000000000000000000000000000000000000000000000001e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001ffe1
  | 0, 2 => 0x1e0000000000000000000000000000000000000000000000000000000000000001e0000000000000000000000000000000000000000000000000000000000000001e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001fe1f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001fe
  | 0, 3 => 0x1e000000000000000000000000000000000000000000000000000000000000001e01e000000000000000000000000000000000000000000000000000000000001e0000000000000000000000000000000000000000000000000000000000000001e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001fe00000000000000000000000000000000000000000000000000000000000001e1e0000000000000000000000000000000000000000000000000000000000001e00
  | 0, 4 => 0x1fe00000000000000000000000000000000000000000000000000000000000001e000000000000000000000000000000000000000000000000000000000000001e1e0
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x1ba1d00000000000000000000000000000000000000000000000000000000000177ba000000000000000000000000000000000000000000000000000000000001711000000000000000000000000000000000000000000000000000000000000045a20000000000000000000000000000000000000000000000000000000000015580000000000000000000000000000000000000000000000000000000000000e17700000000000000000000000000000000000000000000000000000000000061320000000000000000000000000000000000000000000000000000000000000eef
  | 0, 1 => 0x65f200000000000000000000000000000000000000000000000000000000000047ea00000000000000000000000000000000000000000000000000000000000045e20000000000000000000000000000000000000000000000000000000000000480000000000000000000000000000000000000000000000000000000000000223e00000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000022000000000000000000000000000000000000000000000000000000000001ddc1
  | 0, 2 => 0x11e88000000000000000000000000000000000000000000000000000000000000cde7000000000000000000000000000000000000000000000000000000000000aa7f000000000000000000000000000000000000000000000000000000000000a855000000000000000000000000000000000000000000000000000000000001ba5d0000000000000000000000000000000000000000000000000000000000008845000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000067fe
  | 0, 3 => 0x1f150000000000000000000000000000000000000000000000000000000000001f33e000000000000000000000000000000000000000000000000000000000001f1100000000000000000000000000000000000000000000000000000000000019ecd00000000000000000000000000000000000000000000000000000000000198450000000000000000000000000000000000000000000000000000000000015fea0000000000000000000000000000000000000000000000000000000000013ebe0000000000000000000000000000000000000000000000000000000000011e8c
  | 0, 4 => 0x1ff98000000000000000000000000000000000000000000000000000000000001f955000000000000000000000000000000000000000000000000000000000001f5f2
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 35 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 35 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 35 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 35 then wireAt i else 0
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 6 0 (NN s)
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_59_4 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_59_4 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_59_4 == dom_59_4) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_59_4 goalM u ys) : RunD dom_59_4 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_59_4 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 9 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 9 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 9 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_16 : ∀ i, 16 ≤ i → i < 21 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 5 16 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 21 → Z 5 i = true := (range_split z5_0 z5_16)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 10 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 10 0 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 10 → Z 6 i = true := z6_0
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
  scr dom_59_4 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_59_4 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_59_4 roots_59_4 goal_59_4 8 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_59_4 goal_59_4 := by
    have h0 : isConstB dom_59_4 goal_59_4 = false := by decide +kernel
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

end S_59_4

theorem low_59_4 : Lower dom_59_4 roots_59_4 goal_59_4 8 := S_59_4.noCircuit

namespace S_31
def pairsG : List (Nat × Nat) := [(1, 9), (1, 17), (2, 18), (3, 7), (3, 11), (3, 19), (4, 12), (5, 7), (5, 13), (5, 21), (6, 7), (6, 14), (6, 22), (8, 9), (8, 12), (10, 11), (10, 14), (10, 26), (16, 17), (16, 18), (20, 21), (20, 22), (20, 28), (24, 25), (24, 26), (24, 28)]
def r1sG : List Nat := [1, 1, 2, 3, 3, 3, 4, 5, 5, 5, 6, 6, 6, 8, 8, 10, 10, 10, 16, 16, 20, 20, 20, 24, 24, 24]
def r2sG : List Nat := [9, 17, 18, 7, 11, 19, 12, 7, 13, 21, 7, 14, 22, 9, 12, 11, 14, 26, 17, 18, 21, 22, 28, 25, 26, 28]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [6610089675015, 6610123229447, 8800724651017, 6618881331463, 5510846876679, 17600860981010, 17596582856465, 21994629367569, 17596649965841, 8813323814668, 10999512696585]
def xsM : List Nat := roots_31.map (· &&& dom_31)
def goalM : Nat := goal_31 &&& dom_31
def NN : Nat → Nat
  | 4 => 1
  | 5 => 25
  | 6 => 19
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xac05225e
  | 5, 0 => 0xf0b2ef13de66a692d591247cb7fbf71eac05225ea571db928c616cec81ea162e7873cae76f5141bc6baa58136a3f50af64d480336112f50b5e1d4aa85299e96d4ca62407419de0e53a6b8d4132f633fb32bc99002637312d25e0cf661ac7d7cf08a43bb3
  | 6, 0 => 0xd051f507ce00c9b9be3a6442ac05225ea0508cfd93c0f7228c616cec7ecfa1837702c5a9744473ec554c825e5299e96d3a6b8d4130706e42276bea4325303d37206585ea1b8a7ef10241d3e1
  | 7, 0 => 0xac05225e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xaa00aa0000000000000000000000000000000000000000000000000000000000a0a0a0a0000000000000000000000000000000000000000000000000000000008888888800000000000000000000000000000000000000000000000000000000555555550000000000000000000000000000000000000000000000000000000033333333000000000000000000000000000000000000000000000000000000000f0f0f0f0000000000000000000000000000000000000000000000000000000000ff00ff000000000000000000000000000000000000000000000000000000000000ffff
  | 0, 1 => 0xf000f00000000000000000000000000000000000000000000000000000000000eeeecccc00000000000000000000000000000000000000000000000000000000cccccccc00000000000000000000000000000000000000000000000000000000cccc888800000000000000000000000000000000000000000000000000000000cc00cc0000000000000000000000000000000000000000000000000000000000c0c0c0c000000000000000000000000000000000000000000000000000000000aaaaaaaa00000000000000000000000000000000000000000000000000000000aaaa0000
  | 0, 2 => 0xfcccfccc00000000000000000000000000000000000000000000000000000000fafafafa00000000000000000000000000000000000000000000000000000000fafaf0f000000000000000000000000000000000000000000000000000000000faaafaaa00000000000000000000000000000000000000000000000000000000fa00fa0000000000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000f0c0f0c0
  | 0, 3 => 0xffffaa0000000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000fff0fff000000000000000000000000000000000000000000000000000000000ffccffcc00000000000000000000000000000000000000000000000000000000ffaaffaa00000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000fcfcfcfc
  | 0, 4 => 0xffffff0000000000000000000000000000000000000000000000000000000000fffff00000000000000000000000000000000000000000000000000000000000ffffcccc00000000000000000000000000000000000000000000000000000000ffffaaaa
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x1e6923495
  | 5, 0, 0 => 0x79a48c255a349080579a48e255e6890c257da48d255e74f349579a349095e692103589a48d255e692344578d242055e695349579a58d195e4d23495792344055e69448d5
  | 5, 0, 1 => 0x1e69828958d948d255e6d2347579a40d255e692349548d241015e48d241579c48b255e6974895
  | 6, 0, 0 => 0x1e692349579a48d245679a612349601e48d241579a48d24368de692349679a48d289679a48d248601e68d242501e692344579c692349681e692349679a48f349679a592349679a48d240679a4913496
  | 6, 0, 1 => 0x79a48d244685e692349679a6523496
  | 7, 0, 0 => 0x1e6923495
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
  | 0, 0 => 0x38000000000000000000000000000000000000000000000000000000000000000380000000000000000000000000000000000000000000000000000000003fffc440000000000000000000000000000000000000000000000000000000003fc63c300000000000000000000000000000000000000000000000000000000038fe03f00000000000000000000000000000000000000000000000000000000007c1fff000000000000000000000000000000000000000000000000000000000003ffff
  | 0, 1 => 0x39c3c0000000000000000000000000000000000000000000000000000000000039c3c000000000000000000000000000000000000000000000000000000000000003800000000000000000000000000000000000000000000000000000000000380000000000000000000000000000000000000000000000000000000000000001c0000000000000000000000000000000000000000000000000000000000000003bb0000000000000000000000000000000000000000000000000000000000000000
  | 0, 2 => 0x39c3c0000000000000000000000000000000000000000000000000000000000701ffb0000000000000000000000000000000000000000000000000000000000701fc000000000000000000000000000000000000000000000000000000000000003bb00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000701fc000000000000000000000000000000000000000000000000000000000007000000000000000000000000000000000000000000000000000000000000000001c00
  | 0, 3 => 0x3fc00000000000000000000000000000000000000000000000000000000000003fc00000000000000000000000000000000000000000000000000000000000003f3ffc0000000000000000000000000000000000000000000000000000000000383fc3c000000000000000000000000000000000000000000000000000000000383e3bb000000000000000000000000000000000000000000000000000000000383e00000000000000000000000000000000000000000000000000000000000038000000000000000000000000000000000000000000000000000000000000000739ffc
  | 0, 4 => 0x3ffe0000000000000000000000000000000000000000000000000000000000003fc00000000000000000000000000000000000000000000000000000000000003ff9c3c0000000000000000000000000000000000000000000000000000000003fc03bb
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x80a111000000000000000000000000000000000000000000000000000000000010078800000000000000000000000000000000000000000000000000000000000084b800000000000000000000000000000000000000000000000000000000036b58440000000000000000000000000000000000000000000000000000000002d4634300000000000000000000000000000000000000000000000000000000018ea03700000000000000000000000000000000000000000000000000000000003c16ae000000000000000000000000000000000000000000000000000000000001edd9
  | 0, 1 => 0x24149400000000000000000000000000000000000000000000000000000000001bf9ebe00000000000000000000000000000000000000000000000000000000012b9cbc00000000000000000000000000000000000000000000000000000000012a94bc00000000000000000000000000000000000000000000000000000000010388100000000000000000000000000000000000000000000000000000000000211c88000000000000000000000000000000000000000000000000000000000094a7bb0000000000000000000000000000000000000000000000000000000000940222
  | 0, 2 => 0x36bddfc0000000000000000000000000000000000000000000000000000000002f5fffb0000000000000000000000000000000000000000000000000000000002f55fea0000000000000000000000000000000000000000000000000000000002d5effb0000000000000000000000000000000000000000000000000000000002c1e9510000000000000000000000000000000000000000000000000000000002715fc800000000000000000000000000000000000000000000000000000000027012000000000000000000000000000000000000000000000000000000000002615dc8
  | 0, 3 => 0x3feb3370000000000000000000000000000000000000000000000000000000003fe12260000000000000000000000000000000000000000000000000000000003f3ffd90000000000000000000000000000000000000000000000000000000003ebfdfd0000000000000000000000000000000000000000000000000000000003d7effb0000000000000000000000000000000000000000000000000000000003c3e9510000000000000000000000000000000000000000000000000000000003c2000000000000000000000000000000000000000000000000000000000000037bdffc
  | 0, 4 => 0x3fffb770000000000000000000000000000000000000000000000000000000003ff5b660000000000000000000000000000000000000000000000000000000003ff9ebe0000000000000000000000000000000000000000000000000000000003feb7bf
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 36 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 36 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 36 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 36 then wireAt i else 0
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 6 0 (NN s)
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

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
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
private theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_16 : ∀ i, 16 ≤ i → i < 25 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 9 16 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 25 → Z 5 i = true := (range_split z5_0 z5_16)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 16 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_16 : ∀ i, 16 ≤ i → i < 19 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 3 16 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 19 → Z 6 i = true := (range_split z6_0 z6_16)
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
  scr dom_31 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_31 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_31 roots_31 goal_31 8 := by
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

theorem low_31 : Lower dom_31 roots_31 goal_31 8 := S_31.noCircuit

namespace S_51_4
def pairsG : List (Nat × Nat) := [(5, 7), (5, 21), (5, 37), (6, 7), (6, 22), (6, 38), (20, 21), (20, 22), (20, 52), (36, 37), (36, 38), (36, 52)]
def r1sG : List Nat := [5, 5, 5, 6, 6, 6, 20, 20, 20, 36, 36, 36]
def r2sG : List Nat := [7, 21, 37, 7, 22, 38, 21, 22, 52, 37, 38, 52]
def mpG : Nat := 0xfff
def pool6G : List Nat := [6618881594631, 39668404262196, 39608274716454, 22016087623446, 39603996591909, 22011809498901, 22011810551317]
def xsM : List Nat := roots_51_4.map (· &&& dom_51_4)
def goalM : Nat := goal_51_4 &&& dom_51_4
def NN : Nat → Nat
  | 3 => 3
  | 4 => 6
  | 5 => 5
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xc163301810fa662002c60f84
  | 4, 0 => 0xc16330187c560ccc1fed428713bf65a30a68344304bd6b78
  | 5, 0 => 0xc163301885cfe8d85175445f1fed42871a9f8aef
  | 6, 0 => 0xc1633018
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xe000c000e000c000000000000000000000000000000000000000000000000000c000c000c000c000000000000000000000000000000000000000000000000000c000c00000000000000000000000000000000000000000000000000000000000a000a000a000a000000000000000000000000000000000000000000000000000a000a00000000000000000000000000000000000000000000000000000000000500050005000500000000000000000000000000000000000000000000000000030003000300030000000000000000000000000000000000000000000000000000000f0000000f0
  | 0, 1 => 0xf000f000c000c000000000000000000000000000000000000000000000000000f000f000a000a000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000f000c000f0000000000000000000000000000000000000000000000000000000f000a000f000a000000000000000000000000000000000000000000000000000f0000000f0000000000000000000000000000000000000000000000000000000e000e000e000e0
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xc9644ed9840eb43
  | 4, 0, 0 => 0xc96440e95440c94140c6204ed96450c9744
  | 5, 0, 0 => 0xc9644c96435ca96450c9414c96405
  | 6, 0, 0 => 0xc9644
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
  | 0, 0 => 0x3800000000000000000000000000000000000000000000000000000000000000380000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ff80000000000000000000000000000000000000000000000000000000000000fc70000000000000000000000000000000000000000000000000000000000000e3f
  | 0, 1 => 0xe380000000000000000000000000000000000000000000000000000000000000e070000000000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000000000001c000000000000000000000000000000000000000000000000000000000000001c700000000000000000000000000000000000000000000000000000000000001c0000000000000000000000000000000000000000000000000000000000000003f
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x4fb00000000000000000000000000000000000000000000000000000000000004b90000000000000000000000000000000000000000000000000000000000000420000000000000000000000000000000000000000000000000000000000000024f00000000000000000000000000000000000000000000000000000000000002040000000000000000000000000000000000000000000000000000000000000db00000000000000000000000000000000000000000000000000000000000000b46000000000000000000000000000000000000000000000000000000000000062d
  | 0, 1 => 0xfbd0000000000000000000000000000000000000000000000000000000000000f6f0000000000000000000000000000000000000000000000000000000000000f240000000000000000000000000000000000000000000000000000000000000df20000000000000000000000000000000000000000000000000000000000000bdf00000000000000000000000000000000000000000000000000000000000009d200000000000000000000000000000000000000000000000000000000000006ff
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_51_4 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_51_4 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_51_4 == dom_51_4) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_51_4 goalM u ys) : RunD dom_51_4 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_51_4 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
  scr dom_51_4 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_51_4 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_51_4 roots_51_4 goal_51_4 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_51_4 goal_51_4 := by
    have h0 : isConstB dom_51_4 goal_51_4 = false := by decide +kernel
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

end S_51_4

theorem low_51_4 : Lower dom_51_4 roots_51_4 goal_51_4 7 := S_51_4.noCircuit

namespace S_61
def pairsG : List (Nat × Nat) := [(1, 9), (1, 17), (1, 33), (4, 12), (5, 13), (5, 21), (5, 37), (8, 9), (8, 12), (16, 17), (20, 21), (20, 28), (20, 52), (24, 25), (24, 28), (32, 33), (36, 37), (36, 44), (36, 52), (40, 41), (40, 44), (48, 49), (48, 52), (56, 57), (56, 60)]
def r1sG : List Nat := [1, 1, 1, 4, 5, 5, 5, 8, 8, 16, 20, 20, 20, 24, 24, 32, 36, 36, 36, 40, 40, 48, 48, 56, 56]
def r2sG : List Nat := [9, 17, 33, 12, 13, 21, 37, 9, 12, 17, 21, 28, 52, 25, 28, 33, 37, 44, 52, 41, 44, 49, 52, 57, 60]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [21995134918929, 39668336890164, 26392910695433, 8800994135049, 43985366223881, 8800724651041, 35189006012705]
def xsM : List Nat := roots_61.map (· &&& dom_61)
def goalM : Nat := goal_61 &&& dom_61
def NN : Nat → Nat
  | 4 => 2
  | 5 => 7
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x995298d158bd7002
  | 5, 0 => 0xd268f7e7c04ab063995298d17d443c493e3ca5392ac4f6e505a2181e
  | 6, 0 => 0x995298d1
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x33003300330033000000000000000000000000000000000000000000000000003232323232323232000000000000000000000000000000000000000000000000303030303030303000000000000000000000000000000000000000000000000022222222222222220000000000000000000000000000000000000000000000001111111111111111000000000000000000000000000000000000000000000000030303030303030300000000000000000000000000000000000000000000000000330033003300330000000000000000000000000000000000000000000000000000333300003333
  | 0, 1 => 0x3333333333003300000000000000000000000000000000000000000000000000333333330000000000000000000000000000000000000000000000000000000033333300333333000000000000000000000000000000000000000000000000003333000033330000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xa875450b9544
  | 5, 0, 0 => 0xa87535a85415a87545a87645a87425a75405a97545
  | 6, 0, 0 => 0xa87545
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
  | 0, 0 => 0x19861800000000000000000000000000000000000000000000000000000000000071c7f0000000000000000000000000000000000000000000000000000000000071c7800000000000000000000000000000000000000000000000000000000000000770000000000000000000000000000000000000000000000000000000001ffff880000000000000000000000000000000000000000000000000000000001f8e3870000000000000000000000000000000000000000000000000000000000679e7f00000000000000000000000000000000000000000000000000000000001f81ff
  | 0, 1 => 0x1ffe1800000000000000000000000000000000000000000000000000000000001ff80000000000000000000000000000000000000000000000000000000000001f87f800000000000000000000000000000000000000000000000000000000001e07e00
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x19a69990000000000000000000000000000000000000000000000000000000001ffffff0000000000000000000000000000000000000000000000000000000001575d780000000000000000000000000000000000000000000000000000000000a9a6f700000000000000000000000000000000000000000000000000000000015659080000000000000000000000000000000000000000000000000000000000a8a287000000000000000000000000000000000000000000000000000000000065966600000000000000000000000000000000000000000000000000000000001b81dd
  | 0, 1 => 0x1fff9dd0000000000000000000000000000000000000000000000000000000001ff90440000000000000000000000000000000000000000000000000000000001fe7fbb0000000000000000000000000000000000000000000000000000000001e47e22
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 12 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 12 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 12 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 12 then wireAt i else 0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_61 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_61 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_61 == dom_61) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_61 goalM u ys) : RunD dom_61 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_61 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
private theorem z5_0 : ∀ i, 0 ≤ i → i < 7 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 7 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 7 → Z 5 i = true := z5_0
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
  scr dom_61 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_61 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_61 roots_61 goal_61 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_61 goal_61 := by
    have h0 : isConstB dom_61 goal_61 = false := by decide +kernel
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

end S_61

theorem low_61 : Lower dom_61 roots_61 goal_61 7 := S_61.noCircuit

namespace S_62
def pairsG : List (Nat × Nat) := [(2, 18), (2, 34), (4, 12), (6, 14), (6, 22), (6, 38), (8, 12), (10, 14), (10, 26), (10, 42), (16, 18), (20, 22), (20, 28), (20, 52), (24, 26), (24, 28), (32, 34), (36, 38), (36, 44), (36, 52), (40, 42), (40, 44), (48, 50), (48, 52), (56, 58), (56, 60)]
def r1sG : List Nat := [2, 2, 4, 6, 6, 6, 8, 10, 10, 10, 16, 20, 20, 20, 24, 24, 32, 36, 36, 36, 40, 40, 48, 48, 56, 56]
def r2sG : List Nat := [18, 34, 12, 14, 22, 38, 12, 14, 26, 42, 18, 22, 28, 52, 26, 28, 34, 38, 44, 52, 42, 44, 50, 52, 58, 60]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [17601383375378]
def xsM : List Nat := roots_62.map (· &&& dom_62)
def goalM : Nat := goal_62 &&& dom_62
def NN : Nat → Nat
  | 4 => 1
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xa91103de
  | 5, 0 => 0xa91103de
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x55555555000000000000000000000000000000000000000000000000000000005555000055550000000000000000000000000000000000000000000000000000550055005500550000000000000000000000000000000000000000000000000050505050505050500000000000000000000000000000000000000000000000004444444444444444
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x46885
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
  | 0, 0 => 0x3ff00000000000000000000000000000000000000000000000000000000000003c0fc00000000000000000000000000000000000000000000000000000000000330c3c000000000000000000000000000000000000000000000000000000000000e383c00000000000000000000000000000000000000000000000000000000000003bb
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3ff22220000000000000000000000000000000000000000000000000000000003c8fd11000000000000000000000000000000000000000000000000000000000334d3cc0000000000000000000000000000000000000000000000000000000002aeb8fc0000000000000000000000000000000000000000000000000000000001534fbb
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_62 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_62 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
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
private theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
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
  scr dom_62 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_62 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_62 roots_62 goal_62 6 := by
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

theorem low_62 : Lower dom_62 roots_62 goal_62 6 := S_62.noCircuit

namespace S_61_2
def pairsG : List (Nat × Nat) := [(2, 18), (2, 34), (3, 7), (3, 11), (3, 19), (3, 35), (6, 7), (6, 14), (6, 22), (6, 38), (10, 11), (10, 14), (10, 26), (10, 42)]
def r1sG : List Nat := [2, 2, 3, 3, 3, 3, 6, 6, 6, 6, 10, 10, 10, 10]
def r2sG : List Nat := [18, 34, 7, 11, 19, 35, 7, 14, 22, 38, 11, 14, 26, 42]
def mpG : Nat := 0x3fff
def pool6G : List Nat := [6610123361031]
def xsM : List Nat := roots_61_2.map (· &&& dom_61_2)
def goalM : Nat := goal_61_2 &&& dom_61_2
def NN : Nat → Nat
  | 4 => 2
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xf32b51407e9683f3
  | 5, 0 => 0xf32b5140
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xcccccccccccc0000000000000000000000000000000000000000000000000000cccccccc00000000000000000000000000000000000000000000000000000000cccc0000cccc0000000000000000000000000000000000000000000000000000cc00cc00cc00cc00000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c00000000000000000000000000000000000000000000000008888888888888888
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
  | 0, 0 => 0x3c0000000000000000000000000000000000000000000000000000000000000003c0000000000000000000000000000000000000000000000000000000000000003c
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3333000000000000000000000000000000000000000000000000000000000000222200000000000000000000000000000000000000000000000000000000000011110000000000000000000000000000000000000000000000000000000000003c880000000000000000000000000000000000000000000000000000000000000bc4000000000000000000000000000000000000000000000000000000000000047c
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_61_2 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_61_2 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
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
  scr dom_61_2 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_61_2 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_61_2 roots_61_2 goal_61_2 6 := by
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

theorem low_61_2 : Lower dom_61_2 roots_61_2 goal_61_2 6 := S_61_2.noCircuit

namespace S_15
def pairsG : List (Nat × Nat) := [(1, 9), (3, 7), (3, 11), (4, 12), (5, 7), (5, 13), (6, 7), (6, 14), (8, 9), (8, 12), (10, 11), (10, 14)]
def r1sG : List Nat := [1, 3, 3, 4, 5, 5, 6, 6, 8, 8, 10, 10]
def r2sG : List Nat := [9, 7, 11, 12, 7, 13, 7, 14, 9, 12, 11, 14]
def mpG : Nat := 0xfff
def pool6G : List Nat := [8813323814668, 8800489441033, 6610089675015]
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
  | 0, 0 => 0xf0000000000000000000000000000000000000000000000000000000000000000f80000000000000000000000000000000000000000000000000000000000000cc60000000000000000000000000000000000000000000000000000000000000037
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfad0000000000000000000000000000000000000000000000000000000000000afa0000000000000000000000000000000000000000000000000000000000000cd60000000000000000000000000000000000000000000000000000000000000577
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

def symsG : List (List (Nat × Nat)) := [[(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]]
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

namespace S_29_2
def pairsG : List (Nat × Nat) := [(2, 18), (3, 7), (3, 11), (3, 19), (6, 7), (6, 14), (6, 22), (10, 11), (10, 14), (10, 26)]
def r1sG : List Nat := [2, 3, 3, 3, 6, 6, 6, 10, 10, 10]
def r2sG : List Nat := [18, 7, 11, 19, 7, 14, 22, 11, 14, 26]
def mpG : Nat := 0x3ff
def pool6G : List Nat := [6610123361031]
def xsM : List Nat := roots_29_2.map (· &&& dom_29_2)
def goalM : Nat := goal_29_2 &&& dom_29_2
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x3162df00
  | 4, 0 => 0x3162df00
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xcccc000000000000000000000000000000000000000000000000000000000000cc00cc0000000000000000000000000000000000000000000000000000000000c0c0c0c00000000000000000000000000000000000000000000000000000000088888888
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
  | 0, 0 => 0x3800000000000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000000000000e
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x24900000000000000000000000000000000000000000000000000000000000003a40000000000000000000000000000000000000000000000000000000000000172000000000000000000000000000000000000000000000000000000000000009e
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_29_2 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_29_2 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)]]
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

def isoMv_47 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]
theorem low_47 : Lower dom_47 roots_47 goal_47 8 :=
  lower_iso isoMv_47 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31

def isoMv_23 : List (Nat × Nat) := [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_23 : Lower dom_23 roots_23 goal_23 5 :=
  lower_iso isoMv_23 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15

def isoMv_39 : List (Nat × Nat) := [(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]
theorem low_39 : Lower dom_39 roots_39 goal_39 5 :=
  lower_iso isoMv_39 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15

def isoMv_45_2 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]
theorem low_45_2 : Lower dom_45_2 roots_45_2 goal_45_2 5 :=
  lower_iso isoMv_45_2 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_29_2

def isoMv_53 : List (Nat × Nat) := [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]
theorem low_53 : Lower dom_53 roots_53 goal_53 5 :=
  lower_iso isoMv_53 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15

def isoMv_57_4 : List (Nat × Nat) := [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem low_57_4 : Lower dom_57_4 roots_57_4 goal_57_4 5 :=
  lower_iso isoMv_57_4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_29_2

def isoMv_54 : List (Nat × Nat) := [(0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)]
theorem low_54 : Lower dom_54 roots_54 goal_54 5 :=
  lower_iso isoMv_54 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15

def isoMv_58_4 : List (Nat × Nat) := [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0x2222222222222222222222222222222222222222222222222222222222222222, 1), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem low_58_4 : Lower dom_58_4 roots_58_4 goal_58_4 5 :=
  lower_iso isoMv_58_4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_29_2

namespace S_63
def pairsG : List (Nat × Nat) := [(1, 9), (1, 17), (1, 33), (2, 18), (2, 34), (3, 7), (3, 11), (3, 19), (3, 35), (4, 12), (5, 7), (5, 13), (5, 21), (5, 37), (6, 7), (6, 14), (6, 22), (6, 38), (8, 9), (8, 12), (10, 11), (10, 14), (10, 26), (10, 42), (16, 17), (16, 18), (20, 21), (20, 22), (20, 28), (20, 52), (24, 25), (24, 26), (24, 28), (32, 33), (32, 34), (36, 37), (36, 38), (36, 44), (36, 52), (40, 41), (40, 42), (40, 44), (48, 49), (48, 50), (48, 52), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 1, 1, 2, 2, 3, 3, 3, 3, 4, 5, 5, 5, 5, 6, 6, 6, 6, 8, 8, 10, 10, 10, 10, 16, 16, 20, 20, 20, 20, 24, 24, 24, 32, 32, 36, 36, 36, 36, 40, 40, 40, 48, 48, 48, 56, 56, 56]
def r2sG : List Nat := [9, 17, 33, 18, 34, 7, 11, 19, 35, 12, 7, 13, 21, 37, 7, 14, 22, 38, 9, 12, 11, 14, 26, 42, 17, 18, 21, 22, 28, 52, 25, 26, 28, 33, 34, 37, 38, 44, 52, 41, 42, 44, 49, 50, 52, 57, 58, 60]
def mpG : Nat := 0xffffffffffff
def pool6G : List Nat := [6610089675015, 6618814222599, 6610123229447, 8800724651017, 6618881331463, 5510846876679, 6610123360519, 10999512696585, 8813323814668, 39668336890164, 26392910695433, 43985366223881, 6619150819591, 5511116360711, 6618713098503, 22003252463879, 11029745635593, 21995134912273, 5510611536135, 17597088408082, 17614268277266, 35189006012962, 52862627482676, 52931345910836, 11016692565769, 52781192057121, 52781460490513, 11012347070220, 39587052523809, 11008102631177, 6610123361031, 52785487024674, 52931228403508, 39668403999028, 8809584069641, 8809585320201, 17596649965841, 8809314585609, 8809316880649, 17605240949009, 21995134918929, 22024644790028, 39616829785868, 35197425944865, 5510781997575, 17635221767954, 8818174004233, 17600860981010]
def xsM : List Nat := roots_63.map (· &&& dom_63)
def goalM : Nat := goal_63 &&& dom_63
def NN : Nat → Nat
  | 5 => 3
  | 6 => 58
  | 7 => 338
  | 8 => 169
  | 9 => 18
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0xed65c9fb78541dd67010173f
  | 6, 0 => 0xfd1d4291f575c6d4e78d20c5df56d5c9cda5896dccbba923cc64bb85caf8f81aca26cc2cc6fbbdf5c6a053cbc116d5dfb5ed93e0aff02e82ae01e74498b5a1d38c1703868be042807fa656687d8c10b57c5792297bae4c587b28099b722eeeb66a8772f9691baf8e68eb1e2568e68a6d667fe38c5f398d535e2d8aab5cfd29e957530f6054eca64a4f2565134cc9bc584c50b96c3c74836f3954a7aa31547fe42a836aa22a2686ce28b4110827c418632779c54f249d0b201eb4b16d1e8896f91985f02c18987ba512b6646c0fa3bbb50d0157ba09c29ef208f317a50821dcde06e4336306165d76
  | 7, 0 => 0x2089ff201f25d85c1efe2b8f1e0576261d85da9b1cd038361ca481c01c96ea491c3b9b761b5233871afecaa01a63b4731a4dc7a41a33b1c319f37e0718f302eb1891280c181c7acd17e4d13d1797b3c9172decb916c91dcd16845b24161648bc13d5001c13aa6824118eca2110ef4723104862a50fceabe00ee0af2a0d3586890d05cbda0cf439bf0cad16120c825c970c1e8e5d0bb0c3ae0b2c8ce60a7677f509ec2ffe08cdebfc08b46af10899ab53081d1c6e07ca96c507073daf060e91e7060e01a40535f29d04d8394304824cd40442bd860375c6cf029b155802363de2020b934d01eac28901cde8810198403d0166035701427f89013ad0c900d76e02
  | 7, 1 => 0x43c1fcc9433e816f4221143d41751586416e44234166956340e8120340e5429a40bbc12740936de1401a1c4f3fca826d3f3bf5403f291ad13e8cd15e3e791ea93d2c7c353cda06bb3c21f90f3b40a23f3a8512d93a4fc20639b5e922390ed69f38962217388be5c43872edd93799ae2b3791ff6b374d282d364691d8362738653615bd78361262443587494434df5d8934a750a933cd017f30ddf49130dba214301b2a852fa88bf32f1279782e9b5e9e2d9f970e2d70ced82d4518622aa00b9d2a63475229f9c57229e0d67129af2b6429259dd72817589127d2573727be783b26f168c926c5d4a5260ba3022604931525c30139232c6add225693612145ca59
  | 7, 2 => 0x66e4732066b2ba9b65b3f9f764b153c1649ea5e0640f62e36302bf7262dfa08f62515d59623466375f9873855eb5ede35e4be6235da6006b5c4918f65c0bbbc75bb639285b34bf745a859b925a7ee5485a3ecee1598cb1c55925466958f8fc515794d580578d26c057685cd7574ab38e5672b54a567043f556488c3a551f842c5462936b52b48e1052a2b541527782b3506b190f5014114e4fd06e7f4e2566f84d84259f4c4491e44b8c97694b6978864aeba8ec4ae43b454a9428d24a8291714a2e534949c3e2a949bb2fc34850b42846de759446c7cf0746c7c6354625da824606ca5745f28fa645a7f598457c8acd44f40dc34458f2e5441784af440fd5ef
  | 7, 3 => 0x8f34bfe78f052a2c8b27f4e189e77a5d89a86b2589312aef88ceb155881af389863f5b5b860c78ef85bc0dd784d7d6fc8475b5338433dbed82e2ff4782585f94817106db812adf778078c4e0805e0348805c6b597fa4b67a7f7ed9fb7f6323277e9aa7927e0371a67ca8786f7bd0c69379c219c97920d8f378a6665978120717778509c276863e3b7677af7c765ba6437613d46a75cf5cc174cf39e473627f61730c5ff872e9411571ff99de7166cf8770b68b1c706f245a6ee314666dafa0f16cac52696c9c25686c70829f6c64553c6c49cc986c0ebf3a6be5d2566b302ff16ae97d196a8097696a610cd96921832768ade54568a1dd9c6805cfb76786b847
  | 7, 4 => 0xdfe0ba32df6c049ade8141e7db4f33a9da9b4bd4d86386c7d838eecfd6acef47d67aeb44d0bc4cc0cc636961cb5a385fcb08702ac6cb05bec2932210c05d52e2bebb555abc67da83bc62e41ebaf70c47b9218214b91d4ce9b5bed785b57368d5b4c2348eb49852fdb0d3c397b0b15514afaab267af6b3d75ab583dfdab3f45e1aa6b2cfca7cfd832a5ed4e39a5ed1e7ba49fea3ba494c22fa2c55a8fa20c58259ec0d7899d55141e9cdb422c9cccd4969c82e8309c718f149bf3e9d49b4d17b599fe664c98386cf69823da6494ce77af94ae29a594a83048949f308d947384999372f1e393064ed592fea01592d1d6d892b8eaa0901284728fa972eb8f5f73c9
  | 7, 5 => 0xffcceadcf9876158f37e6192f0e272b8ecb660fdeb93c63be9e0e609e863d8b7e849f352e63d73aee5c83741e4c7a25de44891f6e3ddc213e2f6af66e2835ba7e1760161e0f77e7b
  | 8, 0 => 0x49e125c648b0ac9d46e149a2413f306a4025ca0a3f086e6d3d6d0b963cedcf813c3d49423c21f90f3a8b9b213a476634396f572d387c221636e4026d366fa272359f67e73574355934064f6c3129ad3f3122199e30bda81a2f7655c82de85b922d90db782d6df75a2cb7e2692b81626d2b0f56702acd7a9829f0f18429e942c429c478db28a4a83e2774c46026beaf6f23afce9222c7351320df43cc20292edb1eb3facb1e1aa3ae1e08e1531c1ffead1923eb0b1881f68616e8db1816b50ee91581f8c81317dd2b12baa677119811440f8898390e7e15130d9cbe430cabde0a0c22507d0acf09dd09f5ca2f09ee1b6f07d82e3c06291d83023f103c00273479
  | 8, 1 => 0x992721c298553ede9710a458968ac1e995a996be92b08ece925c0be49117715e8f6e24048ebf00228c8386ea8bc68b508a81f0ca88ede02887cdddd08651842c85ba4fb985210b038492c7cd833df90381bd8a2f7f27d8097dfd47397d356db97a2bfc5d7a2bf4367892577578493a7f76f0de337521769373f60c3a72b2833971fb25a2705b5d9f6f6c29a26f3b46226d483b2f6a7ff6686a4f22086a0139de69c0add4683fb3fc67044c4c66fb4c91651506a461aa33685ec6f1c75b4388f85b2acd595aa8a6b958905d13568ff7f15640306854b47b98531915d1523dc21151bf3f2b51099cc64fb2394c4f717d1d4e9d19034e2ce2974c1e35cd4b02825d
  | 8, 2 => 0xffcceadcff939ceffc3cf275fb192d73ed71b5aeed5ae6a4e73f702cdf91a28ddede789bd96359b3d958a3e4d3152e0bd0aaf3a4c8d8951dc62ad07cc44be902c33e8ebcc31b6fd9c23de552beb2f988bde1cfb5bc545819bab08b31ba45dd7fb69fded2b253eee6b23cd636b0e1dcffabbe6e52aabfa2cbaab1140caa950ad3aa2867c5a8d69abba5e4c2a9a494c22fa36baaf79db654639d61744b9aec1f2b9985b807
  | 9, 0 => 0xd1efb8f39b34b1218a7994f87e1a8a567cea112d76f0de33705b5d9f61ca40085fbac6fd5e22a7545cde0cce5059633d4aee737942b779a33e277fff34064f6c1b78d4bc0e7e1513
  | 10, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x3f3f3f3f00000000000000000000000000000000000000000000000000000000333333330000000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000550055000000000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000555500000000000000000000000000000000000000000000000000000000000000ff
  | 0, 1 => 0x5555000055550000000000000000000000000000000000000000000000000000333300003333000000000000000000000000000000000000000000000000000000ff000000ff00000000000000000000000000000000000000000000000000000000ffffffff000000000000000000000000000000000000000000000000000000005f5f5f5f00000000000000000000000000000000000000000000000000000000555555ff00000000000000000000000000000000000000000000000000000000555555550000000000000000000000000000000000000000000000000000000050505050
  | 0, 2 => 0xf0f0f5f0f0f0f5f0000000000000000000000000000000000000000000000000f0f0f0f0f3f0f3f0000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000000000000000000000000000000000000ff00ff00ff00ff000000000000000000000000000000000000000000000000005500550055005500000000000000000000000000000000000000000000000000330033003300330000000000000000000000000000000000000000000000000000ffff0000ffff0000000000000000000000000000000000000000000000000000777700007777
  | 0, 3 => 0x30303030303030300000000000000000000000000000000000000000000000002f2f2f2f2f2f2f2f00000000000000000000000000000000000000000000000022222222222222220000000000000000000000000000000000000000000000001f1f1f1f1f1f1f1f000000000000000000000000000000000000000000000000151515151515151500000000000000000000000000000000000000000000000011111111111111110000000000000000000000000000000000000000000000000f0f5f5f0f0f5f5f0000000000000000000000000000000000000000000000000f0f3f3f0f0f3f3f
  | 0, 4 => 0x55555555555555550000000000000000000000000000000000000000000000005555555555550000000000000000000000000000000000000000000000000000555555555500550000000000000000000000000000000000000000000000000055554444555544440000000000000000000000000000000000000000000000005544554455445544000000000000000000000000000000000000000000000000505050505050505000000000000000000000000000000000000000000000000044444444444444440000000000000000000000000000000000000000000000003333333333333333
  | 0, 5 => 0xaaaaaaaa88888888000000000000000000000000000000000000000000000000aaaaaa00aaaaaa00000000000000000000000000000000000000000000000000aaaa8888aaaa8888000000000000000000000000000000000000000000000000aa88aa88aa88aa88000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a0000000000000000000000000000000000000000000000000999999999999999900000000000000000000000000000000000000000000000088888888888888880000000000000000000000000000000000000000000000005f5f5f5f5f5f5f5f
  | 0, 6 => 0xcccccccccccc8888000000000000000000000000000000000000000000000000cccccccc88888888000000000000000000000000000000000000000000000000cccc8888cccc8888000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c0000000000000000000000000000000000000000000000000aaaaaaaabbbbbbbb000000000000000000000000000000000000000000000000aaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000aaaaaaaaaaaa0000000000000000000000000000000000000000000000000000aaaaaaaaaa00aa00
  | 0, 7 => 0xeeeeeeeeeeeecccc000000000000000000000000000000000000000000000000eeeeeecceeeeeecc000000000000000000000000000000000000000000000000ecececececececec000000000000000000000000000000000000000000000000eaeaeaeaeaeaeaea000000000000000000000000000000000000000000000000e0e0e0e0e0e0e0e0000000000000000000000000000000000000000000000000dddddddddddddddd000000000000000000000000000000000000000000000000d0d0d0d0d0d0d0d0000000000000000000000000000000000000000000000000cccccccccccccccc
  | 0, 8 => 0xf0f0f0f0a0a0a0a0000000000000000000000000000000000000000000000000f0f0f0f080808080000000000000000000000000000000000000000000000000f0f0f0c0f0f0f0c0000000000000000000000000000000000000000000000000f0f0f0a0f0f0f0a0000000000000000000000000000000000000000000000000f0f0e0e0f0f0e0e0000000000000000000000000000000000000000000000000f0f0c0c0f0f0c0c0000000000000000000000000000000000000000000000000f0f0a0a0f0f0a0a0000000000000000000000000000000000000000000000000eeeeeeeeeeeeeeee
  | 0, 9 => 0xf0f0f0f0f0f0f0a0000000000000000000000000000000000000000000000000f0f0f0f0f0f0c0c0000000000000000000000000000000000000000000000000f0f0f0f0f0f0a0a0000000000000000000000000000000000000000000000000f0f0f0f0f0f00000000000000000000000000000000000000000000000000000f0f0f0f0f0c0f0c0000000000000000000000000000000000000000000000000f0f0f0f0f0a0f0a0000000000000000000000000000000000000000000000000f0f0f0f0f080f080000000000000000000000000000000000000000000000000f0f0f0f0c0c0c0c0
  | 0, 10 => 0xff11ff11ff11ff11000000000000000000000000000000000000000000000000ff00ff55ff00ff55000000000000000000000000000000000000000000000000ff00ff00ff33ff33000000000000000000000000000000000000000000000000ff00ff00ff00ff00000000000000000000000000000000000000000000000000fafafafafafaaaaa000000000000000000000000000000000000000000000000fafafafaeaeaeaea000000000000000000000000000000000000000000000000fafafaeafafafaea000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0
  | 0, 11 => 0xffeeffeeffeeffee000000000000000000000000000000000000000000000000ffccffccffccffcc000000000000000000000000000000000000000000000000ffaaffaaffaaffaa000000000000000000000000000000000000000000000000ffaaffaaffaaff00000000000000000000000000000000000000000000000000ff88ff88ff88ff88000000000000000000000000000000000000000000000000ff55ff55ff55ff55000000000000000000000000000000000000000000000000ff44ff44ff44ff44000000000000000000000000000000000000000000000000ff22ff22ff22ff22
  | 0, 12 => 0xffffaaaaffff8888000000000000000000000000000000000000000000000000ffffaaaacccc8888000000000000000000000000000000000000000000000000ffffaa88ffffaa88000000000000000000000000000000000000000000000000ffffa0a0ffffa0a0000000000000000000000000000000000000000000000000ffff8888ffff8888000000000000000000000000000000000000000000000000ffff5555ffff5555000000000000000000000000000000000000000000000000ffff0000ffff5555000000000000000000000000000000000000000000000000ffff0000ffff0000
  | 0, 13 => 0xffffff00ffffff00000000000000000000000000000000000000000000000000fffff0f0ffffc0c0000000000000000000000000000000000000000000000000ffffeeeeffffeeee000000000000000000000000000000000000000000000000ffffccccffffcccc000000000000000000000000000000000000000000000000ffffccccaaaa8888000000000000000000000000000000000000000000000000ffffc0c0ffffc0c0000000000000000000000000000000000000000000000000ffffaaaaffffaaaa000000000000000000000000000000000000000000000000ffffaaaaffffaa00
  | 0, 14 => 0xffffffffaaaaaa00000000000000000000000000000000000000000000000000ffffffffa0a0a0a0000000000000000000000000000000000000000000000000ffffffff88888888000000000000000000000000000000000000000000000000ffffffff55555555000000000000000000000000000000000000000000000000ffffffff44444444000000000000000000000000000000000000000000000000ffffffff00000000000000000000000000000000000000000000000000000000ffffffccffffffcc000000000000000000000000000000000000000000000000ffffffaaffffffaa
  | 0, 15 => 0xffffffffff00ff00000000000000000000000000000000000000000000000000fffffffff0f0a0a0000000000000000000000000000000000000000000000000ffffffffeeeeeeee000000000000000000000000000000000000000000000000ffffffffeaeaeaea000000000000000000000000000000000000000000000000ffffffffe0e0e0e0000000000000000000000000000000000000000000000000ffffffffcccccccc000000000000000000000000000000000000000000000000ffffffffc0c0c0c0000000000000000000000000000000000000000000000000ffffffffaaaaaaaa
  | 1, 0 => 0xffffffffffffc0c0000000000000000000000000000000000000000000000000ffffffffffffaaaa000000000000000000000000000000000000000000000000ffffffffffffa0a0000000000000000000000000000000000000000000000000ffffffffffff8888000000000000000000000000000000000000000000000000ffffffffffff0000000000000000000000000000000000000000000000000000ffffffffffccffcc000000000000000000000000000000000000000000000000ffffffffffaaffaa000000000000000000000000000000000000000000000000ffffffffff88ff88
  | 1, 1 => 0xffffffffffffffaa000000000000000000000000000000000000000000000000ffffffffffffff00000000000000000000000000000000000000000000000000ffffffffffffcccc
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x7260502a1457260542a155837f4438325
  | 6, 0, 0 => 0x725d503830116007260544f383260054504029110c60060544029150c60072605438321760072605432201e6007854503830116006054503830096726054514538327837f6c5d503832700726054493832600726f604a383260054502720110c60072605450401060072504029141160060542720150c6
  | 6, 0, 1 => 0x6054503a210c60075726050401460060545038320a600837f6f50382760000726054502a50072605438321660054322015110c60083816f50383260084726054504060077605450322060060543938270c60083726354504060072605d5030206007263605440156007269545031206007860545030206
  | 6, 0, 2 => 0x72605450322a600837f6f503220600836b5450383260072605445382760072605c5032206007f756054504067f6b6054503832700867f6f50383260060544438320c6837f695e5038327008360544a383260060545038310960060502720140c600726050291a1460050382714110c6007260544a38276
  | 6, 0, 3 => 0x726054291a1560054382715110c6007f6f50383203600726a695450406837f6f50383229700836f5038320560050322014110c6007260544a322060072605439272060063605450400c6
  | 7, 0, 0 => 0x6054503834270c7007263605450382770083726c503832147006054503a38270c700725450382720117008a72605450383278372695e54503832800726054504138277006054503827210c7007d726050383214700726d6054383215700726a6954503832700726054382720157007f78605e5038327007f72605e5038277005450403832110c7
  | 7, 0, 1 => 0x7260545038270d70072605654503832700007260544b3832600747260545027207006f69545038320c7000072605d503830600726f60545040297000060545040290c6007260545040380f7007872605450403670072706054503827700726054504732207007f7260544b38327007872605032201470072605450272220700726660545038327
  | 7, 0, 2 => 0x7260503832140e700725b5450383211700726054503b382777f786c605450383280000726360545040600605450382b270c78372605b5450383280075726054383215700897269545038327007f726f695038327007260575450383270086726f545038327007260503832140f70083726f5e5038327000072605450402f600726c60503220147
  | 7, 0, 3 => 0x726860545038327000077605450383260072605450322d20700726054503832027006960545038270c70072545040382711700817254503832117000072503220141160072605d5038320d7007269545038320370083726050322014700797260545038277006c60543832150c7007372605450382770072605440382715700757254503832117
  | 7, 0, 4 => 0x726054503832107006054504238320c700726054503231207000054383215110c60072503832291411700726f6954503827700725a5450382711772605450414038328007f72545038271177f726c605d5038328007f60545038320970087726054503832700726c60504032147007250383227141170086726054503827700726160545038327
  | 7, 0, 5 => 0x8872605450382770072605450433832700726054503d382777f72636054503832800837f6c545038327007260503227201470060545038320f0c700787260543827157007472545038321170072605438321506700726960544438327005d54503832110c700837960545038327007260545040272070081726054503220700725450383222117
  | 7, 0, 6 => 0x54503220110c6007260545038333270000726054502720600726054503222207007a7254503827117000060543220150c600726054503827257007260545038271f7007260585450322070072605e5038320d70072605a545027207007f7860545032207007f726054502720700726f695d503832700726c60543827157007f725d503832117
  | 7, 0, 7 => 0x5450383227110c70078605450383205700757260545040327007260503832140370083786c5450383270083726c54503827700726054504c38277006054383227150c700747260545032207007c72605450383270072605032201d1470072545038321311700605d545032200c700726054503827247006460545038320c7007d7260545038277
  | 7, 0, 8 => 0x726d6054503532700726c60545027207005450383229110c7006a60545038320c7006054383229150c7007f72605d5032207007254503832281170083726f5450322070083605450383209700726054504238277000072543827151160072676054503832700726960544038157007872605450272070083786054383215700837260543827157
  | 7, 0, 9 => 0x6054503227200c783726f5450383229800725438322015117007f725e5038321170072605450322013700837269545040387837a605d5450383280072545038322f117000060503827140c6007260555450383270072605038321a147007260545032291a7005e54503832110c700837a6054383215700725d5450382711700827260545038277
  | 7, 0, 10 => 0x8372545041383270072605d54502720700726460545038277006050383220140c700817260544a3832700726e6054503832700007254502720116007260545034321a7008378605450322070083726054502720700726054503228207005450383432110c7008360545038320570083726950383214700007260542720156007260545038270e7
  | 7, 0, 11 => 0x725e54503827117007260545027201f700725450382927117007265605450383270060545038322e0c70072605450403b297007872605040381470078726054504029700726c605450402770083727054503832700007860545038316008372635450383270000726054503f3260078726054503c387007262545038320f700725a54503832117
  | 7, 0, 12 => 0x72605a54503220700726f545038320370078726054503732700726054382721157008572605450383270081726f605038327006960543832150c700725440383215117007e72605450383270083605450483832700726054503832187007254503b3832117007b72605450383270072605438342722700545038322b110c700726f605b5038327
  | 7, 0, 13 => 0x72605e5450272070089726054503827700726050382720147007f726f6050382770083726054504029700726054504e383270000726054402915600726054503832247006050403832140c7006054504032290c700726054525038327008472605450383270086726054383215700787260545040347007260545032200d7006054503c38320c7
  | 7, 0, 14 => 0x72605450383219700726054383215097006054504034320c7000072605c503832600726f605444383270083726054503732700726054504d38327006960545032200c70072605954503827700726054503827037007260545027201d70072605440322015700726054503b322070000726054503e32600605450322b200c700867260545037327
  | 7, 0, 15 => 0x726f6050383213700726050403827147007572605038321470072605450382726700726054503c38277006054503827220c7007f7254503220117007260545038271a700837f695450383270072605f545038277008972605d5038327007a605450383203700887260543832157008672605450322070060545038322c0c700726054503a27207
  | 7, 1, 0 => 0x726f605d5038277007a766054503832700726c60543220157007972605450403277f7269605e50383280072605450322009700726054502b27207007254503832110570000837f6f50383260083786954503832700837269545038277007f7860545040387007872605432201570072605e545040277006260545038270c7006c60503832140c7
  | 7, 1, 1 => 0x7260545038320b7007260545042322070078726050382714700837260543220157008376605450383270072605450322720700726054504c32207008972605e5038327000050383214110c600007260544a38326007260543834322270072605450383200700007260543938276007260545040342770074726054504038700726054503832077
  | 7, 1, 2 => 0x7260543227201570072605d544a3832700726460545032207007f7560545038327008372605038271470000726054503a216007260545027201a7000072695450382e600726c6054502721700726054535038327000072605450402c600726c60544032157007260545038321c70072605450383204700726c6050382714700726054503832087
  | 7, 1, 3 => 0x7260545032200370086726054504038700726054503827127000054503827110c6006960545040380c700897260545032207007f726f605032207007260545038272370072605438321a1570000726054393832600726054383215037000072605027201460072605432201d157007260545032302070080726054503832700726054504240327
  | 7, 1, 4 => 0x83726f5d50383270072605040322014700726054503832017007260545038321b70000726050402914600726054504638327005450383220110c7006054504138320c7008672605038321477f726f605038322980083726f54503827700726f60503832057000072605450291a60072605e54502721700726050382721147006960503832140c7
  | 7, 1, 5 => 0x72605450403827700887260503832147
  | 8, 0, 0 => 0x726054503832067007472605450383270072605450383212700605d545038320c7000054503832110c60000726054503827600726054503832227000060543832150c6007260503832291470072605a545038277007f7860545038327007f726054503827781787260545038328007260503832271477a726f60545038328006c60545038320c7
  | 8, 0, 1 => 0x72605450383228700007260543827156726f6054503832278006054503832270c7787260545038322080072605450383213700726f60545032207000060545032200c68172605d545038328767260545038322b80072716054503832700726c60545038277007f72605d50383270083726f5450383277f72605450383220800787260545038277
  | 8, 0, 2 => 0x726054383220157007f72605e50383270072605450403832700726960503832147007260545038322f700837a605450383277f72605450403832800605e545038320c70072605d545038277726f6054503832298006054503832290c70000725450382711678726054503836328007269605450403870083786054503832700837260545038277
  | 8, 0, 3 => 0x72605e54503827700726054503829277726d6960545038328007260545038320d77a7260545038322f80072605a54503832772605450403b3832800727060545038327787260545040383280000726054502720672605d54503832208006054503834320c700726360545038327007254503832201178372605450383220800726054504138327
  | 8, 0, 4 => 0x7f72545038321170000726054504029678726c60545038328008672605450383270072605450383427700726054503a3827772605d5450403832800726054503827217006960545038320c7007254504038321177260545038322720883726054504038328007972605450383270072605440383215700726054503b383270060545038322b0c7
  | 8, 0, 5 => 0x8683726054503832800007260545032206726c605d54503832878726054503832098007260545038321f700726c60543832157008872605450383277872605d54503832800726054503d3832772605450403832278007260545038320970072605450382b27700787260543832157007260545040322078678726054503832889726f60545038328
  | 8, 0, 6 => 0x8883726054503832878726054503832298726c6054503832278007260545038321d7000060503832140c67872605450383227800726c605450322078372605d545038328827f72605450383280072605450423832700787260545032207008372605438321570072605450383227700726054504c383277260545038322b208007d7260545038327
  | 8, 0, 7 => 0x726054503832307837260545038322980072605438322915700726c60545040327726960545041383287872605450383432883726054503832278007260543832271570072605d54503220700726460545038327726054504038322b8008372605450322070000726054322015600726054503a38327726c60545042383287872605e545038328
  | 8, 0, 8 => 0x72605e5450383227800726054503832037007260545032201d70072605e5450322070089726054503832700726050383220147007f726f60503832778726960545038328726c60545038322b88372605450383432800726054503227207787260545038322b8000072605038271467f726960545038328007260545032201f78372605e545038328
  | 8, 0, 9 => 0x72605450382722772605f5d545038328007260545038322c7007260545040343270072605450322b207898372605450383280072605e5450403270072605040383214700726054504032297726054503d38322b87260545038343227800726054503c38327007260545038321a7726054503832272180072605f545038327837260545038322b8
  | 8, 0, 10 => 0x72605450403827700007260503220146007260545038323170072605b54503832772706f60545038328008372605038321470072605450382720700726c6050383214700747260545038277
  | 9, 0, 0 => 0x72605450383432772605e54503832772605450383229772605450383227700726054503220672605d545038327007254503832116837260545038327007260543832156726c605450383277872605450383270072605450383267f7260545038327726054504038327726054503832207007260545038276
  | 9, 0, 1 => 0x72605038321467260545038322b7
  | 10, 0, 0 => 0x7260545038326
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 44
  | 6 => 60
  | 7 => 68
  | 8 => 68
  | 9 => 60
  | 10 => 52
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 8 0) :: stateWires n (ids >>> 8)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x1fffc3fff00000000000000000000000000000000000000000000000000000001ff0c3e07000000000000000000000000000000000000000000000000000000003f03ffff000000000000000000000000000000000000000000000000000000003f03c2180000000000000000000000000000000000000000000000000000000000ffffff000000000000000000000000000000000000000000000000000000000003fe000000000000000000000000000000000000000000000000000000000000ffc218000000000000000000000000000000000000000000000000000000000003ffff
  | 0, 1 => 0x3fe00ffc218000000000000000000000000000000000000000000000000000003fe000c3e070000000000000000000000000000000000000000000000000000007e0003ffff00000000000000000000000000000000000000000000000000000001ffffffff00000000000000000000000000000000000000000000000000000001ffffc3ff00000000000000000000000000000000000000000000000000000001ffffffff00000000000000000000000000000000000000000000000000000001ffffc218000000000000000000000000000000000000000000000000000000003c03c200
  | 0, 2 => 0xffffc3ffc3ff0000000000000000000000000000000000000000000000000000ff87fffc3fff0000000000000000000000000000000000000000000000000000ff87c3fc01ff00000000000000000000000000000000000000000000000000001c7e3f03ffff00000000000000000000000000000000000000000000000000001c7e3f03c21800000000000000000000000000000000000000000000000000001c7e3f003e07000000000000000000000000000000000000000000000000000003fe00ffffff000000000000000000000000000000000000000000000000000003fe00fffe1f
  | 0, 3 => 0x783c003e000000000000000000000000000000000000000000000000000000ff87c3fc3dff0000000000000000000000000000000000000000000000000000000000003c070000000000000000000000000000000000000000000000000000fffffffc03ff0000000000000000000000000000000000000000000000000000fffffffc02180000000000000000000000000000000000000000000000000000ffffff0c02000000000000000000000000000000000000000000000000000000ffffc3ffc3ff0000000000000000000000000000000000000000000000000000ffffc3fc3fff
  | 0, 4 => 0xffffffffc2180000000000000000000000000000000000000000000000000000ffffff0000000000000000000000000000000000000000000000000000000000ffffc0fc00000000000000000000000000000000000000000000000000000000fc01fff3c0180000000000000000000000000000000000000000000000000000e381c0ffc018000000000000000000000000000000000000000000000000000000783c03c2000000000000000000000000000000000000000000000000000000000000f3c0180000000000000000000000000000000000000000000000000000ffffff0c3e07
  | 0, 5 => 0x1e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001e000000000000000000000000000000000000000000000000000000000000001e00000000000000000000000000000000000000000000000000000000000003c000000000000000000000000000000000000000000000000000000ffffff0c03e000000000000000000000000000000000000000000000000000000000000001e00000000000000000000000000000000000000000000000000000ffffffffc3ff
  | 0, 6 => 0x1e000000000000000000000000000000000000000000000000000000000000001e000000000000000000000000000000000000000000000000000000000000001e0000000000000000000000000000000000000000000000000000000000003c00000000000000000000000000000000000000000000000000000000001ff0c3fe70000000000000000000000000000000000000000000000000000000000003de700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 0, 7 => 0xf3c1f80000000000000000000000000000000000000000000000000000000000f3c1f80000000000000000000000000000000000000000000000000000000000f3fdf8000000000000000000000000000000000000000000000000000000000003fde7000000000000000000000000000000000000000000000000000000000003fc000000000000000000000000000000000000000000000000000000ffffffffc3f8000000000000000000000000000000000000000000000000000000783c03c2000000000000000000000000000000000000000000000000000000000000f3c1f8
  | 0, 8 => 0x7800003c000000000000000000000000000000000000000000000000000000007800000000000000000000000000000000000000000000000000000000000000003c03c000000000000000000000000000000000000000000000000000000000003c003c00000000000000000000000000000000000000000000000000000000003c03fc00000000000000000000000000000000000000000000000000000000003c03c000000000000000000000000000000000000000000000000000000000003c003c000000000000000000000000000000000000000000000000000000000000f3fdff
  | 0, 9 => 0x783c003c00000000000000000000000000000000000000000000000000000000783c03c000000000000000000000000000000000000000000000000000000000783c003c00000000000000000000000000000000000000000000000000000000783c000000000000000000000000000000000000000000000000000000000000780003c0000000000000000000000000000000000000000000000000000000007800003c000000000000000000000000000000000000000000000000000000007800000000000000000000000000000000000000000000000000000000000000780003c000
  | 0, 10 => 0xfffffffc02000000000000000000000000000000000000000000000000000000e3ffc0ffc2180000000000000000000000000000000000000000000000000000e381fffc3e070000000000000000000000000000000000000000000000000000e381c0fc0000000000000000000000000000000000000000000000000000000000783c003de7000000000000000000000000000000000000000000000000000000780003fde7000000000000000000000000000000000000000000000000000000003c03fde7000000000000000000000000000000000000000000000000000000783c03fe00
  | 0, 11 => 0xe381c0fffdff0000000000000000000000000000000000000000000000000000e381c0ffc1f80000000000000000000000000000000000000000000000000000e381c0fc3de70000000000000000000000000000000000000000000000000000e381c0fc00000000000000000000000000000000000000000000000000000000e381c0fc01e00000000000000000000000000000000000000000000000000000ffffffffc2180000000000000000000000000000000000000000000000000000e381c0ffc0180000000000000000000000000000000000000000000000000000e381c0fc3c07
  | 0, 12 => 0xfc01ff0001e00000000000000000000000000000000000000000000000000000fc00000001e00000000000000000000000000000000000000000000000000000fc01ff0001e00000000000000000000000000000000000000000000000000000fc01ff003c000000000000000000000000000000000000000000000000000000fc01ff0001e00000000000000000000000000000000000000000000000000000ffffffffc2180000000000000000000000000000000000000000000000000000fc01ffffc2180000000000000000000000000000000000000000000000000000fc01ff000000
  | 0, 13 => 0xff81fffc00000000000000000000000000000000000000000000000000000000fc79ff03c0000000000000000000000000000000000000000000000000000000fc01fff3fdff0000000000000000000000000000000000000000000000000000fc01fff3c1f80000000000000000000000000000000000000000000000000000fc00000001e00000000000000000000000000000000000000000000000000000fc01ff03c0000000000000000000000000000000000000000000000000000000fc01ff003de70000000000000000000000000000000000000000000000000000fc01ff000000
  | 0, 14 => 0xfffe000000000000000000000000000000000000000000000000000000000000fffe00003c000000000000000000000000000000000000000000000000000000fffe000001e00000000000000000000000000000000000000000000000000000ffffffffc2180000000000000000000000000000000000000000000000000000fffe00f3c0180000000000000000000000000000000000000000000000000000fffe000000000000000000000000000000000000000000000000000000000000ff81ffffc1f80000000000000000000000000000000000000000000000000000ff81fffc3de7
  | 0, 15 => 0xffffc0fc00000000000000000000000000000000000000000000000000000000fffe3c003c000000000000000000000000000000000000000000000000000000fffe00f3fdff0000000000000000000000000000000000000000000000000000fffe0003fde70000000000000000000000000000000000000000000000000000fffe0003fc000000000000000000000000000000000000000000000000000000fffe00f3c1f80000000000000000000000000000000000000000000000000000fffe0003c0000000000000000000000000000000000000000000000000000000fffe00003de7
  | 1, 0 => 0xffffff03c0000000000000000000000000000000000000000000000000000000ffffff003de70000000000000000000000000000000000000000000000000000ffffff003c000000000000000000000000000000000000000000000000000000ffffff0001e00000000000000000000000000000000000000000000000000000ffffff0000000000000000000000000000000000000000000000000000000000ffffc0ffc1f80000000000000000000000000000000000000000000000000000ffffc0fc3de70000000000000000000000000000000000000000000000000000ffffc0fc01e0
  | 1, 1 => 0xfffffffc3de70000000000000000000000000000000000000000000000000000fffffffc00000000000000000000000000000000000000000000000000000000fffffff3c1f8
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x1d75c1acb00000000000000000000000000000000000000000000000000000001550c1a03000000000000000000000000000000000000000000000000000000000f0154aa000000000000000000000000000000000000000000000000000000000a01000800000000000000000000000000000000000000000000000000000000003cce61000000000000000000000000000000000000000000000000000000000028ce2000000000000000000000000000000000000000000000000000000000002882000000000000000000000000000000000000000000000000000000000000004420
  | 0, 1 => 0x33400aa8210000000000000000000000000000000000000000000000000000002aa000c2a050000000000000000000000000000000000000000000000000000001e0002653400000000000000000000000000000000000000000000000000000001df7ddeeb00000000000000000000000000000000000000000000000000000001db7d82cb000000000000000000000000000000000000000000000000000000019a69c628000000000000000000000000000000000000000000000000000000019a6982080000000000000000000000000000000000000000000000000000000118298200
  | 0, 2 => 0x6d96c3d601df00000000000000000000000000000000000000000000000000006d86c7d411df00000000000000000000000000000000000000000000000000006d86c3d401df00000000000000000000000000000000000000000000000000001c5e2f0375be000000000000000000000000000000000000000000000000000018542a0300180000000000000000000000000000000000000000000000000000144a25003006000000000000000000000000000000000000000000000000000003be00beef75000000000000000000000000000000000000000000000000000003be00aeaa15
  | 0, 3 => 0x926934083a0000000000000000000000000000000000000000000000000000006d8ec7d439df0000000000000000000000000000000000000000000000000000248a450438070000000000000000000000000000000000000000000000000000ffe7f3dc03df0000000000000000000000000000000000000000000000000000db65b2c80218000000000000000000000000000000000000000000000000000092613008020000000000000000000000000000000000000000000000000000006fb6c3fe83df00000000000000000000000000000000000000000000000000006faec3dc2bdf
  | 0, 4 => 0xdb75baeb82180000000000000000000000000000000000000000000000000000db75bac300180000000000000000000000000000000000000000000000000000db75b0ea82100000000000000000000000000000000000000000000000000000d955bae380180000000000000000000000000000000000000000000000000000cb359aeb821800000000000000000000000000000000000000000000000000009271382b8200000000000000000000000000000000000000000000000000000049148ae380180000000000000000000000000000000000000000000000000000b6eb750c3a07
  | 0, 5 => 0x248a001065e400000000000000000000000000000000000000000000000000002480451418c300000000000000000000000000000000000000000000000000002400451055e20000000000000000000000000000000000000000000000000000208040144de10000000000000000000000000000000000000000000000000000000804007c2000000000000000000000000000000000000000000000000000009261301847e000000000000000000000000000000000000000000000000000000000001045e00000000000000000000000000000000000000000000000000000fff7fbff83df
  | 0, 6 => 0x49148ad345f800000000000000000000000000000000000000000000000000004914009245f0000000000000000000000000000000000000000000000000000048008a5145e8000000000000000000000000000000000000000000000000000000100823c4200000000000000000000000000000000000000000000000000000248b551c7fe70000000000000000000000000000000000000000000000000000248a45147de70000000000000000000000000000000000000000000000000000248a450031860000000000000000000000000000000000000000000000000000248a40142945
  | 0, 7 => 0x6d9ecff3f5fe00000000000000000000000000000000000000000000000000006d94cff7ddfb0000000000000000000000000000000000000000000000000000491c8ef3fdf80000000000000000000000000000000000000000000000000000249a4d37fde7000000000000000000000000000000000000000000000000000000180c23fc200000000000000000000000000000000000000000000000000000db75bafbc7f800000000000000000000000000000000000000000000000000009271382bc620000000000000000000000000000000000000000000000000000049148af3c5f8
  | 0, 8 => 0x927824027c200000000000000000000000000000000000000000000000000000927820026420000000000000000000000000000000000000000000000000000092713c2bde20000000000000000000000000000000000000000000000000000092693c29fe20000000000000000000000000000000000000000000000000000090593c23fc20000000000000000000000000000000000000000000000000000090513c23d420000000000000000000000000000000000000000000000000000090493c017c2000000000000000000000000000000000000000000000000000006d9ecff7fdff
  | 0, 9 => 0x92793c2bfe20000000000000000000000000000000000000000000000000000092793c23f420000000000000000000000000000000000000000000000000000092793c037c20000000000000000000000000000000000000000000000000000092793c03300000000000000000000000000000000000000000000000000000009279382bee2000000000000000000000000000000000000000000000000000009279342afe2000000000000000000000000000000000000000000000000000009279302aee20000000000000000000000000000000000000000000000000000092782823e420
  | 0, 10 => 0xf3e1f0fc8a410000000000000000000000000000000000000000000000000000e3b5d0fe8a510000000000000000000000000000000000000000000000000000e3a1d5fc9a430000000000000000000000000000000000000000000000000000e3a1d0fc8a410000000000000000000000000000000000000000000000000000b6fb7d177de70000000000000000000000000000000000000000000000000000b6fa6d37fde70000000000000000000000000000000000000000000000000000b6fb7d3fffe7000000000000000000000000000000000000000000000000000092793c2bfe20
  | 0, 11 => 0xefbfdfffffff0000000000000000000000000000000000000000000000000000ebb5daffcff90000000000000000000000000000000000000000000000000000e7abd5fcffe70000000000000000000000000000000000000000000000000000e7abd5fcbbc70000000000000000000000000000000000000000000000000000e3a1d0fccfe10000000000000000000000000000000000000000000000000000fbf5faff8a590000000000000000000000000000000000000000000000000000ebb5daff8a590000000000000000000000000000000000000000000000000000e7abd5fcba47
  | 0, 12 => 0xfccbff5175ee0000000000000000000000000000000000000000000000000000fccaaa5165ec0000000000000000000000000000000000000000000000000000fcc1ff555deb0000000000000000000000000000000000000000000000000000fc49ff417caa0000000000000000000000000000000000000000000000000000fc41ff5155ea0000000000000000000000000000000000000000000000000000ff75ffeb929a0000000000000000000000000000000000000000000000000000fc41ff69928a0000000000000000000000000000000000000000000000000000fc41ff41108a
  | 0, 13 => 0xffe1fffd9acb0000000000000000000000000000000000000000000000000000fe79ff63f4aa0000000000000000000000000000000000000000000000000000fddffff7fdff0000000000000000000000000000000000000000000000000000fd55fff3d5fa0000000000000000000000000000000000000000000000000000fd54659255f20000000000000000000000000000000000000000000000000000fc51ff63d4aa0000000000000000000000000000000000000000000000000000fccbff557def0000000000000000000000000000000000000000000000000000fccbff5539cf
  | 0, 14 => 0xfffe659639d70000000000000000000000000000000000000000000000000000fffe24827d340000000000000000000000000000000000000000000000000000fffe209265f40000000000000000000000000000000000000000000000000000ffffbaeba31c0000000000000000000000000000000000000000000000000000fffeaae3a11c0000000000000000000000000000000000000000000000000000fffe208221140000000000000000000000000000000000000000000000000000fff5ffffdffb0000000000000000000000000000000000000000000000000000ffebfffdffef
  | 0, 15 => 0xfffff0feab550000000000000000000000000000000000000000000000000000ffff3c837d340000000000000000000000000000000000000000000000000000fffeeff7fdff0000000000000000000000000000000000000000000000000000fffe6db7fdf70000000000000000000000000000000000000000000000000000fffe2ca3fd340000000000000000000000000000000000000000000000000000fffeaaf3e5fc0000000000000000000000000000000000000000000000000000fffe28a3e5340000000000000000000000000000000000000000000000000000fffe65967df7
  | 1, 0 => 0xffffffe3f5be0000000000000000000000000000000000000000000000000000ffffffd77dff0000000000000000000000000000000000000000000000000000ffffffc37dbe0000000000000000000000000000000000000000000000000000ffffffd375fe0000000000000000000000000000000000000000000000000000ffffffc3319e0000000000000000000000000000000000000000000000000000fffffaffeffd0000000000000000000000000000000000000000000000000000fffff5fefff70000000000000000000000000000000000000000000000000000fffff0feeff5
  | 1, 1 => 0xffffffffffff0000000000000000000000000000000000000000000000000000ffffffffbbdf0000000000000000000000000000000000000000000000000000fffffff3f5fe
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 139 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 139 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 139 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 139 then wireAt i else 0
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
  | 5 => 14
  | 6 => 383
  | 7 => 1653
  | 8 => 528
  | 9 => 15
  | _ => 0
def CH : Nat → Nat → Nat
  | 5, 0 => 0xb85668eea35c9dd69989d3589576008f93ac296c91e01e08751613f142b779a33002d57c25afa38e23bd94b21b462b871338cb650dfb5be7
  | 6, 0 => 0x1f25d85c1ebee3311e98d7fb1e64a3c31d9a3f801d319dd51bf0c1dd1acbab401abd85511a0f2ada19d5fa50197c4452190d1e2c19019d1518f26c4c1873f326172decb9170619d116edab6c16eb0e0416a935fd15a66114150bb68414e0d35f14c02039149b001d144f7296126bfdab12648d5b124b577f11cd770e119217d80f8898390f1dc2390f124bee0ee0af2a0e7e15130e19b75f0dede7600d4473350cabde0a0a1efef009cab3ef097029c8096e9438085918430800986e079e46270723661d0614060505a805b70561d331054f0a5e0505ca7204773d450407793403c8d54902e1387702afd61501af582a01607961012ce06c00bbc0690030e2e9
  | 6, 1 => 0x361db8d535abd85b3556e607355171d635251e1134f1c3d1343ac70234313a1333b438b6335bf754333d305e32fe99e432e5408e32df0cd031f5645b315c08073156fc5330ad46723037bc2b302bd484300024392fe020b62e1ae90a2dacfc532c91587f2c8d536e2be3fc842bbb27802b81626d2b5b865a2a71cc3b2a5af1be2a12819329eedbb829b0636c2942705b291cbfc32907425528eeaa2f28d3502328a4a83e286c5b0a28388f0f27bb1a0227320b4f26e23bf026c09f4925d756d925b7ff1b2567253724c7002124c5f1c123c93236233b2059230fc2b32244ea1620e75282206d0bcf203249bb20292edb1fe06bb91f426e131f32ec5b1f2cd9af
  | 6, 2 => 0x557c9ff55513114f54b1935f533e1533527f69b85255b2c551ea98385065269e4fb709214fa7655e4f1bb8244f0d9c4b4d22e55a4d18a3a44c30865f4c2c4d784c249eb84ba9615b4a1426de48558c394852d2c847fc363747722ff54724ee6c472220064659100f464d91074551190a44e7746344aba825448215ee445dc3ea4313dfbf42b779a3429d7e9142918769426fe94d41b5718540c083b340460409400c02e73f92d8f93dff0bee3df59e8a3d0ec8b73cd66dcc3cd1bc7e3c90e5203c2925b63c25d59f3c21f90f3b6273ae3a86104b394c6b873921cc4438a27cd73864abd737809ff0377b24af376135eb374526f736c912c236c1640236bd7d74
  | 6, 3 => 0x7cbd4f4a7ca8f3cc7ca64a5e7c9bc0df7afb0e987ac6b3ce795a4378791aa0e67872794e777cb77e776eb37a7592030a749699f1745c250a7361d26272c5d620727718da71dfcdf671b7b36370aa5d93706736e6705b5d9f700ba7156f8cf6046d66356b6be70a5e6b9195906b43cd8a6aae745d67aab8ca65b059d464f1f45764872474643c3a0c643988c963f5006b6370981062dd5da662ad825262501bbd61fc53ca60a194d3608535a5600ad1db5ff48c105f9defbf5ed2da4c5e511c6f5dc3d5e05d8c42c05bb301e15b07e1615aa8a6b959a378655925466958e8376558e2513058cf38005860c0ca578a31685780f3a45766e5cc56488c3a559c0449
  | 6, 4 => 0xae525f4bad99850ead567612aace425ca904c2a6a90236f8a8cc9955a84edc83a5853147a47ac71da1d961dfa04b2e569db654639d1391c59cefd78c9c82e8309c0721c59a84967399c20cf0989eac8e9860223597ac0d10967fbfcb953c586294d2bf9d94b907ca93ea938093476c1e930c3edc92c480a292b31f9291e1c78e91d33365906fd3e18fcf31768e8df0778e224abf8dd06eaf8c9dac058c17c5f68a81f0ca89f27f84890f53db88687eb288653585883b35ad8619545784d9c35583e31f41832189ea82074cbe81e9f85c81bd8a2f81a3228881556ecc81054269808a1dfc805e03487f80c8097f1c9e7d7f0ee6617e601bf47d3057b87cd0d058
  | 6, 5 => 0xff939ceffe6030bcfdec0418fac52187f8d12158f6e8e1d2f4de7774f3d6a6a3f371c819f0e4b2fded842573ed3e6f98ed159572ecf2aac2ebf02961eaec73cceaa3af2fea3a6045e919e04ae76d2b90e580cb8ae4dd38a3e0e88400e063e247db91cf32db350d38d9e9df8fd9adc4b4d7ca6921d375ec65d343e014d238c8add0bc4cc0ccadb8b9cb5a385fcb125ab9cafa56c2cab40ff3c8add0d6c7e6be8ec77f38fbc48f4b0ac42d6449c423a3c7c24f89c6bf9e48dcbf3d61acbeae8066be407366bd55a3cfbcab4e6dbb000829bac57ff1ba5a85b2b8e76ab4b751fa15b36d65c4b3088cf5b2a96dddb1d08fcbb0a652f6b01f9a61ae5e17ac
  | 7, 0 => 0x65401810651b5d5064cb8090638a75e06291d83060f596e05e9221005c61dd605ad2f34057c0b7a052aa49505169eb00509fa1f04d32ad804bca65904aea85504aaa2b0048faf4c046088880459b5e304427d3b0414c3b2035987fe0355cd58033b05b503124251030a418d02dd1e5f029f514b029aef9e0295a2700294122e028de01e026249d20257db270254d8c402502c670249a99b02470b1b023f5c5b01a6e4da019fd767019f361a0191869801794b5f016e641e01652a32015fcb3e01551783014ecf68014268c701385c4e0124c53e011182d800f9b8fb00f5a3d200ea38dd00b912070096f2260095544100481fea003e83f9002d875e0029bfef
  | 7, 1 => 0xcd896110ca165b80c867e660c7bcab90c6ed2f30c6d8e9c0c687b0e0c232aad0c0bf6ea0c04ca010c03b9010bf303a40bd3d3cb0ba77e000b9beb890b80dabe0b76e6c50b50e2ee0b41c7720b2179b20b09f3650af89e950af23e1b0af197a60ae653d70ae34fac0acf09dd0ac5e2020abb3de50ab8b2690aad79ad0a5e33fe09ee1b6f09d9969709bd51ef09695d40096433860938390c092491bd0919997808df973908c7c03908c5dc3f086d870f0865d84f085c29ce0856ca260844bf83081c74db07f70b8707f1b6d607ed8a320790b29f078b6284078179cf07246e590720ca0a06fb5c5206a8768f068bc39d06735b220665520c065dc92d065d5685
  | 7, 2 => 0x12ff424112c3605312bb814412a8595d127638531233466a12300b711228cbf912245a68120d1dd3120061e011c1f92a11bd50f41187183a117804a4115e10321147bf4e1142fa4110de35ff10ba906310a80043109bbfbb109410fb108bef5710835d311004efa21004221f0ffdfe370fde41e30fcb33c20fb1a7760f9aa5fd0f8899180f808c130f7093b80f56ffe60f53334a0f3a3da50f1c66040f1986a90f16fff20edf18670ed019dd0ecc23a60e90cf7c0e7e15130e7db3450e5d94ed0e1f184a0e05ccb20dfb96ef0df435510df1ea5d0dd633720db9c7830da46fb90d9cbe430d92daa50d743a280d6e7ee10d570f570d49c4170d40e0e10cedec0c
  | 7, 3 => 0x196672e119468cb719403fcf1921f28d19169d3318ef4baf18c40ebb18787ffd186366e318545dd6184ab457183afea7182bf92618261f78181c0a6c180f36f817ddd95917d6fff417d64a9117d15ef517c5c22e17c2243517bf920f17bba65117b7e34f17a3f1f5179c6b23175a929b1729918f16f2b34516d77b9d16d21d8816bd508a16bcc03716b50ee9168bc85d166385a01612f341160c7aef15d3b4e415cb6ef015c1920715ba6e6315af65f115a578b7155ed0bb154b3952153fc09e14e907ff14e2d7e014db292014cc20391480f23a14696ac214466a841420fefd1413d60813e90d2b13e0e2a713aad82f13346ed11317dd2b130a5a891302c08c
  | 7, 4 => 0x21a5f968219016092177d428213bddeb20df43cc208879802064873a2062e284204fb0ae203ca24720292edb1fed21a51fecb1011fd3c25f1fa939b01fa23c8a1f5f0d481f4cfea11f0286b71edb86661ed8ca961ea663541e2d04af1df73f721de631f51de45f961de177831dbe4d991d98a19b1d826c881d55e79b1d2d215e1d2a81d31d160c6b1d07cbc61ca81a3a1ca0b1831c8d62a61c5377201c228a231c1ffead1bf725aa1bd1fa481bc210541baf8e761b9935371b78d4bc1b61a0cd1b55df541b52f3321b29bf4b1b25678b1ae9b4a21a87fcc01a4058c31a1cf3441a04d97919fc1ed919ddb2d519c7c79119ba301a198e7f10198916cb1980bc29
  | 7, 5 => 0x297c99f8296b38aa29428e4b29342757291385ac28c73e9828bd116f28b210de28a4a83e286658d0286028b1285f6112285879f1284514cc282426c9281a4d9f281909f628170bbb27c3516e27bb223c279f070c276fb0f9273e087b26eeeb7b26beaf6f26bb2fef26b3685326ad1191266407622648e3a8263fdb29262a32f4260a164f25afebbc259a3137258a6ea4258a599a256dcb2f25471fea253ef9ad250aba5724f9d1c424f59d0824ef47cf24c9ba2d24429b14243e50102437f8a9241c5d5a241b265d2414ae9a2409402823f0c29e23e65466231bcad9230229b922d85c9a22c96b3022c4f10a22baad2d21eaa96f21e6cbde21de28f921c636b8
  | 7, 6 => 0x2fbdf3d12fbbf89b2fb1aafd2fb10f502f954dd02f86b33f2f67316b2f3c81e32f2d39052f2cdf472f1d2f5b2f1abea52ee8e9622ea523322e8a65942e89c73d2e7ac5422e28d5a52df741622df013cb2dec4b6b2dd75a262dcb18752d90db782d618f3b2d52d1502d3ff5e92d3e70562cf8cd042ce139a22cc795ae2c97836b2c8e77b92c7c27652c7afb6d2c611b6b2c58dac22c2937292c18d8712c119b4b2be239292bbea46f2b9c405e2b87620c2b81626d2b811d732b5913022b3e6d342b2246622b19bbf42b1903882b13e5c22b0fca262b08f8cc2af8e8dd2acd7a982a5617002a245e7b29ed6e3b29e942c429d4eeb929990f442993998d2989cbc0
  | 7, 7 => 0x3743a61d36f0769736e2575236b521a23679dd0b366fa272366ef2333669c03b36648703364ef29f3644f7dd3601d28435e7486435d89aaa35a563b8359f67e7359e2116358833f83579865d3541768b353aa3c635239d6d35099e5634f524f934ceb8d134b9287734a771a73481cae4347c735e3466ebee3453b6c534064f6c33e6b2b633a0067c339be830338d060c33511330334a7e36330bca3f330a8e35330961a632d045d132cae7bc32ba82ac32b9632332a889b13294f0e0328546223264f194326007a83252e2e03241705c3177ea883122199e3118539930ff3b4730d5282030b973d630748bb1303f34b8303037e9301052cd300601422fc6445a
  | 7, 8 => 0x3e2119413e04e1c63d3e89f93cfeefc53cedcf813cedc83e3cbde0b03cba78eb3c82fc633c26260f3c21b4153c0ce04f3c01ff8b3bbe60cd3bb1f7013b945c8c3b8aa58d3b5dab7f3b4bea9a3b43ce223b33d6c03b08dcd23b05d6f73af6ada23accd4263aca75eb3a9a85bd3a97b4d03a8e04dd3a67daad3a64e63a3a4d6a953a2d4b6439ff1f0a39fa66b039f7e21b39e37c1a39c6347939ae44eb39a8adfd39a3264a396f572d392d295a39234c0738facf2638ed825b38eb527838e1a69e38bbb164389cbe3638889640387c2216382f747e381fcf1438096b7237ff1f0037d4a1c237b0b97137a858a737a4666c378f8af0378ba63f376ecd62375462ab
  | 7, 9 => 0x46074adf45d7d33445d0247445a2cc4a458c33fc4529a6cb4526b40844d46f7844cd758b44ae84d94486548a447c8c184422f3d5441caf3c4408d56743eb0c0643a9f8484397d140435ea178434f7809434bdc18433cb82e432dfd824325dcc4431f7df7430c7f9b4305883642f2e46442b779a342b451b04270b5be425bc8a4424d728e424083084214fad141d387bf41b5ff6441a0c128418c58194183d887414a8c1f4149098f4110f4a840c96f0f40a60e3740846bf6405e8a73404b3013403af74d3fe000373fd72a663fd3ef6d3fb101cf3f8398af3f5aa7ff3f4622693f2afc363f15457d3f086e6d3ef484683e444aad3e402f123e2e73473e277fff
  | 7, 10 => 0x4c1e35cd4c173de94c16af5f4bd8a0d14bacc54f4b6231954b5e75fd4b51d8934b50406a4b2472944b226b904b0c2c394aee73794aca3bcf4ab9f0674ab9d7494a932f4e4a44957f4a3ff2504a3f5f3c4a0125c049f3d2f349e8ddff49e125c649af3f14497e1ccf4975de44496885e5492acee9491e4f5449148db0490584c948f6d72e48f4f2fe48f0ff0048b1927048b0ac9d485a11cb483afab9480eeebd47e43cbf47d0c7f247ba59f747b76ea34795ee6d478f996047703dcb476a5be94755b844473069034727debc471a541a470caff646f43ede46f1b31146ec901e46df279b46b112e2469461624683e1554667f2b7466764c54658932546463055
  | 7, 11 => 0x53dd4ed053ca920853c0149953b2be7253ad163d538428525372efcc5372c47953514afd53466db852ce9ec252747f075253af29523dc21151b101cb519006da5184d1d4516b02655136a9a3512f757251099cc650e499dd50a60db55096359d507c4096507546385070134c5059633d50490acd500139404fff2dd54ffcc3574fc71f074fbdd0064fa260824f7787d34f56d3284f3260114f135c524f050fd04f0494734ea817a54ea4fa1c4e9d19034e9a87094e5372144e3b68614e3a3a904e2cfa994e2ce2974dc9c7c04d43a2314d3c580d4d2ff4d14d1a0f054cfd734b4cf7eb524ced469a4ccdf14b4cc999094c99f1af4c70a3534c46545e4c29021d
  | 7, 12 => 0x5aecd9575aadae925aa8a6b95aa5f5965aa52f8d5a97a4eb5a8d74075a6afd255a62dc0f5a5bc66559fcbebe59f11cdb59b3a05959a1fc3b59a0c2fc5996f4f5597bfa89593f5843592f019858ec052358bb531a58b561005878a6a45875705b585fd550583019b9581a3e365810d46d5808a3535802414f57ef778e57a487195795fc8d578e67bf576d47815707fb6756c5d00a568ff7f1568d8c7e567ee6cd5672a48756427f9256403068563580cb5600570755f9c36e55f5a32a55d8ab8a555d1ca255067f9c54fdc76d54de0ffe54d89be654b8020854b47b9854a96c0954a16d3c5476a805546df95f5467b4c65463ff8b540a4dbd53e591e853e18f1b
  | 7, 13 => 0x63020dca62d73fc862d4bd236296bc1f62623a35624d6d5b620aa7726202e0dd61d0c2e561ca400861b8723761b6a79261aa336861a45f8b6169ffad613f4bb66108511860fe5bb260c0e6cc60afae3b60ad45a2607f1ebe6049964d604693fd604411db60205a02601bbe09601579706008d5905fe332f45fce787b5fbac6fd5f4d90645f26c7b65f18482b5ef408b65e618c165e56e6485e5492d85e394d3c5e22a7545dd41be55dd08b735d87d7425d5fdc975d5624535d53729c5d48a8d45d0b15675cde0cce5cc14cd15cb746015cab1e5b5c91de815c7a05f25c50e6185c1888cf5bf13ab45bccb9a15bb357745b8c3f8e5b6b6fdf5b65c3955b4dbe2c
  | 7, 14 => 0x6bba30316bba04806ba8c5c26ba44eea6b9d976b6b846d316b0d63fc6afac8926ae5c9b86ac5c8b56abcdfc56a8f01346a4320db6a41599e6a2e06a76a13aebb6a08291469da0c1f69c0add469b0c44b6909bb466909685e6909578d68ec85cb68c3ac2e689b990368742b92682efe61680f799367eb4a3067a71cda67891a30672edba167240676671ea51e671066ce66fc748866fb4c9166c97e4e6644c8f8663dd1146625b9e965f74f0265d6d88f65a7b45e65524fc6653315e465291588651f036864edbd3264e6ab02646b28aa643ac406643a3fff643988c9642d74f3641ca4e7641019b86407b8f163a6a9d3637c7ea66332600f631fb153630aea45
  | 7, 15 => 0x76c6508b76b871ac766e04be76607b8d7654909976509acf7621525d7601ef87756b3d6c755160847539d2697502d39f74ae2b347485a1e97481ccfa74238cce7419ba3e73f993ba73bcfd3f739a9980736647aa734eaa0d73251f9b72bb7e8b72b28339727718da7238707e72301b0f721cd83370ff2e0470e9cc8f70a579f87066c39370607efa705b5d9f701d07ab70120e996fb93c616fb8decd6f596a256f4ebd9a6f1873fa6f0f44366edb0ec36ea4ed216e5e503d6e16b7eb6df7e42c6def4db26dec12c46de93f766dab2ce86d948d4f6d65318d6d483b2f6d3b7e216cfdbf986cbe1d396c85f2fa6c4b6e046c2229556bf899566bf58d8b6bd3e868
  | 7, 16 => 0x7f4590c97f2c02b87f28314b7f0df4cc7ef20d5d7edbceae7ed1cb467e7a0a4c7e704a887e63c5ee7e5772597e4b07f87e22428f7e1a8a567dfb85ac7ddeb6337dd765af7dc60fd37db1e1917db173387da0a7537d2a63907d21396f7cf8a35a7cea112d7cb391007c88cd607c69c65e7c4faf817c4bfba17c4260817c40fcff7c140d477c08287b7bf8b5337bf0b2df7ba3c0797b665f577b5e52fc7aea77727ab2e3267ab1cd807aa157477a92749f7a36543c7a2bf43679cce61979bb6d1e797234ad796deb39795cf9c5795acc8c791c125478b01035789257757872d02677a74e95777652a77746c839772c48f476ffb0b376f0de3376ef06c676d6e321
  | 7, 17 => 0x8a51c9de8a516cc38a37c65d8a0d8ef789ecd54589d1b07b89ba9fdf89b52b5089a3f71c899788de899729b28983c1878974814d893fe42c88ede02888d9be1688b00c9588a4fc218826fc398823b6e487f03d1a87b2ceb4876ece5a8752d38b872dc005871ec9f886bb689486ade397867726a1864102a8861a00e985d3fdb585c39cf28550a2d985260ae184cbc23a847e8567844c64498422cac9840781d783e740ff83e4146483b0d4c883a21eb183621177833df90382b3ae80828511a48265c20c814d04b781303d8c8121dfbc80efac3f80d5104480b8cef280ab0b5c80aa07e3809286e3806266ad804281917fe1a60d7f75ea277f54e5c77f4af1e4
  | 7, 18 => 0x94b8834e94aba5ca947da14a945287619419634b93f91dd793f2e948932ed1f7931b6b2992e04bde92d649fa921c7d4491ed9b5991e8ccbe919ac8ae919a80f8918c7c03918b0169915bff5891503a309117715e9112800b90f610e690c13a9b9049058a90061e318fb5d0938fa19e1f8f80fc978f7b76b18f6e24048f4809be8ee20b498ed973b68ebf00228eb70d658eac49d78e7679718e5d90ed8e596ff18e3f8c778e2302ba8e1426838dc0b2f38d72216c8d395ff68d219bf58d1b84e68d089c908ced12b28cd766ed8caed4eb8cae17488cad401e8ca456c68bc68b508b7531c58b1fd6d78b080e6a8abb56b98aa3b04f8a81f0ca8a7994f88a571a71
  | 7, 19 => 0x9ff394c19fc0bc2f9f77feb79f5ea4e59f1c706f9efebd529edbc97b9ed1e5489e93ebe99e418da49db654639daae7359d648c2e9d0504429cd8b9f79cd4fd939cbb54e09cad2a7e9caba4cf9c01232b9bbf435b9b34b1219aec1f2b9ae5da449a88f9d89a7a06c29a6914bc9a07492d99bed3f999be6db8999971879997d904992e097f992b58e798f4ca5a98e9771598bfc762989a8dc39882dab297f3060497a9fca097a4f38797a00225977b024e976491d0970cd65e96df7e3496a2e0f996964552968ac1e99689804d967fbfcb963297ec9630ff519629a52f95fda25095ddc41b95d81225956ca7b19566b56d94fe5d2694e8477894e56e8494c7ea72
  | 7, 20 => 0xae68ce65ae1e846dae064aa9adec3e13adeaf2e8ade6658daddfe763ad965e55ad58a5d0aca9b064ac41cfbeabc6268babb46943ab81f633aab1140caaa9f7f4aa99e01daa2cb15caa00aaa3a994b72fa9647ee6a8e9f882a8e78fc4a8e5934da89398e1a88cc9a6a828f69ba81c3a5aa7ba35d6a7a2a7a3a6f3a76da6910249a65c3616a6563cc3a6193286a5b36a13a57a8d62a57519cca56543e4a5323c56a4e3c223a4b0cd10a434b4b6a42b4680a411e8baa3f2435da3d73c45a3c65a94a39ec2eea3913837a34731dba3147353a2ce5e77a2a97873a2821498a26a9449a26534afa2501c7ba1f2e5c7a1878b6fa16c4690a1521c33a0bf578aa09db9cc
  | 7, 21 => 0xbc398ae1bc1a5d6dbc042ef7bbe49247bba66d37bb75fc4ebaed3e7abae8aadfbadd43f2bac49c6dba701036ba45dd7fb9e4c7c8b9bbecabb97b0eeab94d1047b932cbabb8fcb82bb8b7e9f7b7dce78eb7892a55b7186549b691c424b67647cbb668942eb666254db601f9d2b5e82352b59006feb5863046b512b256b4c2adf4b4b7aa29b4abe74eb47be621b435aab5b41b0a9db37999dbb34db4edb325de37b3152a51b22053d7b2109beab1ff7463b1ce22c6b18eaca0b169bc48b0e1dcffb0b60c78b08080b4b0231954b017831cafc0504aafa8260baf647c31af1123ebaeef6ae1aeeb3210aedf1679aed94acbaecb59f7aebe772faeb95c8fae9f7f72
  | 7, 22 => 0xcbd77c2fcbaeeccfcb308914cb2d3d5ccae6a019c96f57afc91a9764c8f1bc47c8e779a6c8dcf1b0c8d8951dc85ae621c82cddd4c827157fc8038de5c7ac348bc7327c7fc6dfc8e3c694f8b9c63e6ab8c5e5017dc5899ec0c510d9fac4e635f6c4e09fabc4d7a737c4bb9dfec4b48854c496691ec4745ea1c453a13bc44be902c3b4db41c3ad2618c3651e39c33e8ebcc3347db3c31b6fd9c25c674ac2472df4c22bf79cc1fa1783c1f2c1fcc1dbd993c16a70b1c14551f7c1041042c0e08b57c0d8bcdac07b6c73c031db64c01695c8bf98043bbeffe354befa2055be4769d9be2639d5be20deedbde1cfb5bdce499fbd20e303bd1c3529bcc91ac8bc545819
  | 7, 23 => 0xdb4f7d39db29855cdb23cb92db01ce84dae9e1fadaa10b17da868145da5cb472da4ab022da446b89d9fbacb2d96359b3d920e647d9196516d85d0165d80862e0d803eed7d7e8ebedd7894d3cd786c099d68b73c0d67f4dd9d612c66fd5ce88c2d5c0efffd594088dd58ce416d5628c56d5092ac7d46c70aad445852fd41d6596d4001a12d3fa20bfd3980975d317dc6dd3152e0bd2b422bed23dc786d2370a95d1efb8f3d1e7bd46d137f74ed1293c1cd0e64a54d0e05608d0dd3a20d0c08da1d0aaf3a4d07c82add028b587d0188098d00c244bcfa1a4c1cf96c9c3cf8f1c3ecf1f3ed4ce40adbdcdd2d617cd4ef236cccaebe6cc804dadcc6d1337cc452051
  | 7, 24 => 0xed3bc136ed270113ec36d44aec3462fdeb85b3b1eb7dc701ead186cfea99b7d8ea39f55dea326695e9f83c15e967135fe95a7ff1e8fb991ee8da166de8027d18e7e9c17be7b0d071e76202ffe74be456e73f702ce7283c3de6d0b57ee6a1abd0e606f433e5cb74e9e5786fb8e52d0e51e4f751b8e4e88dfde3ecbae8e3e18a9be3a5ddcee35a848ce2ff2848e2e6d92ae2d732e2e2b94eb5e29f438ce281e22ce24d2a46e232c2d0e22a0b63e21fca1de1ccafbce175a2ade152e27ee1283faae064565ce0626e26e046d2d6e0129c16dfe22038dfafa89bdf7206c2dede789bde74f913de727c2ddd6521e7dd4db3aadd420304dc35b29bdb56751ddb51c5cf
  | 7, 25 => 0xffd5b11cffc6e326ff939cefff6dda91ff6283a0fef288ebfeb8db38fe811e1cfd7e6266fc86bf18fc807a7ffc465d48fc266c52fbf342e7fbccf7fafb192d73fac274d4fa06476af9cab482f9b835b8f9050bc6f8f8ed24f8d5ce41f8bf6874f8a016c6f7efd299f7e6759ef743fdf9f6338be1f58b144bf57698bff52ab2dbf3b0d898f3983283f389ecdef2572628f20f2a2ef2000644f1c51099f12be4b6f0db7a90f053c1fdefbd7900efb98f2eefaf60deeee26649eec40f0cee8f1728ee8dd083ee4f0bb0ee1e2c58ed8d35c2ed56b179
  | 8, 0 => 0x16d8a81c1606144c15f86a801561a43a13b5da6d136d10ac135211a2131bfefa12b8ab4112b8884a12ae5da3129997eb124e263511d748061187183a11761aa81142fa4110d1aa96103ead2a0fc22fb60f8b2a5f0f5c5cfb0f3badb20edd17080ea68d810e8414b20e7dd0190e783ebe0df078900d61f2fb0d52c9a60d4d98860cf91d9f0cea20e10cc7aa850cb3009d0c867e660c2cfbb60b989d440b41c7720a71f95609eba6f40878675807bd347d07af559e0754ea15075140fd06b07a030663442505c61dd605ad2f3405a3eb0a0590310f05169eb0040745c602e9d44b0296f5790291d00a0188fb4b0129b75501013f3600dd496a0086a50c00103def
  | 8, 1 => 0x2ba0a43a2a6cf0712a6bdfc02964176b291abe56284db2db272770732705880d26d2458e26aa53c326a4b5bf26488ebe26396ad4262d41fb261c309d2609324125bece64258a6ea4255ffecb24cb7b292485a9342429651523a7fde62310763b23038dd422d85c9a2219ec0a21e9d24d21a5f9682179389d2081cc61204aaf2d2046aaad203e530f203cd04e1fd3d3851fb72b911ee4e3db1ebb13731e7359ed1e3d0e221d989e101c53b96d1bea35011bde45011b8548e61b78d4bc1b61a0cd1b52f3321b2d157f1a45ab1d1a4058c31a0ece7019e3604919b1d4481979f417196672e1191531f41900f42918e3fb0a17d07b0017a820261729918f170db67f
  | 8, 2 => 0x40455b7a3f49363a3e277fff3e1c8eb63df1aaf13d8620523d18fbc93c9f3cdf3c9dc2fe3c9d75a23c8fe41f3b3c318a3b23954e3afd7b253a8b1a653a861c9939de879e395003403899ed1837a1ed1c378f31e8375fd1e83732d33a3724f45b36c744ae368990f73678c0eb363c57f436224d1b361b1af435d89aaa358e7c13357bcd57355e29ce354bc4fd3518dab13481847a34746a9f342cdee933193e9a330961a632ba82ac3294bf40326a06213264f1943243d5cd317141fd315024ba31381b0730ccd1eb3055c0a6302ca7772fc976f62f1d68d52f1362052efbd9642eedfa852e9e70832d014b912cf3c0ef2cae27f22ca821632c1543872baacaed
  | 8, 3 => 0x56dbe56f56da22f0567ee6cd56240dff55ab6c46558b875054c1de10531692945314eaf652acbe7d528ca24251d2062b516924ff515c2919514f645450c9577f50c4b4ed5059633d5038abd64f9b055d4f943bc44f8c57c24f490be64f0fba7a4e79bd534e1db72a4e0e9fc94e00c0ea4dc27b5b4cfd734b4cd8ba054c173de94bff26be4bb8974e4b62f61f4b0c2c394afc5e1e4aee73794a6707154a5928364a3f78dc4a0d1974499b08ca49226c8f49148db0475141bb46e1bded465e79d54609964845f6b58445c07cca45179a8f44cd758b43b9f0a343a9f8484305883642b779a34214fad141d9fb7841d622d341a8390640db2d8b40bb28344079af63
  | 8, 4 => 0x727daf3d721cd83370946692707cee8d6f69601f6e9f1e276e834bca6e8018a76e38e6f66ddedbb86cd622c66bc490ee6b1be3666af785736a5eea176a510b3869b2eaed692e70ee6920920f688d1b55679d352a6709aa616659a12a663575426554bad164ffcc4e647899486449b75d640159026379a67663669d956347643b633af01163353df463275f1562623a3561ca400860b58bf55fbac6fd5f5d13a95f492eb65eebace45e90082e5e22a7545e1657ce5dc82fa15d93d62e5d7bf2db5d2e415c5d23bf8f5cde0cce5c9fbd605c91de815bff541c5ba915895a7078f859f223e559e9c31b59d66aa0596bf2065923c1c658a5f177581fb8f65806ebe2
  | 8, 5 => 0x94b8834e94552299944ede0093602c46928df7689272b1cc91b98d12908ca444900c696690061e318f7fd14d8f78512d8e7679718d3d413a8ce77a638bbc73f08aef68758ab84b5d8a8bfac78a7994f889beef4c87ec2302877c8a9f877910e2876b320387080352867726a1862851b983f048fb83c5bc52828511a482739f208241b05981b633a5806266ad804281917f97da8d7f4590c97f1797dc7e8559377e22428f7e1a8a567d303bbe7cea112d7c439fcf7c0721267bf0d3337bc86ac17b4614867b2b17a17aa157477a85129f78f04d3477f10ba277d135d076f0916b76bdf4b976b015da766385db764e5f61745a681c7341d2fd7333c42e72e03d9b
  | 8, 6 => 0xbbb69bf5baa8a17cba477786b9782853b84d21e0b81d78f4b65f3e8fb55b444cb559ed2fb47be621b3feb3cab3f8265db37ef559b272f2abb22e7c90b1b17014b12375bdb080f6ebb07bc511aec64c0eae064aa9adab993dada32de2ad85a160ace974c5acac34b6ac3ab49dab94b348aa8df529aa87c3f1a9cb11c2a98c5b5da9647ee6a8e78fc4a6563cc3a623790ea5cabbeaa5103ec2a4dede88a4a02823a499e38aa3f2435da02ef21b9eab30d29e58572e9d42bc1d9d3508f49d2d50bb9bfcd7929b71391a9b34b1219ab47d5a9ab0be7a9a36658d99bbfbc9985a34f798411d81981b7e9297a5128c96e3fc35965f3458963c456d9603a498956125c6
  | 8, 7 => 0xeeab662cee22ff53ee1e2c58ec164c1eebc28ee5ea39f55de8b54ab1e7283c3de7199440e606f433e45c7de4e2f6cc76e21fca1de1ccafbce1c2a466e1b94d76e1283faae088d44de07b344edf6d0221de1b0bb2ddd7f9c9dd4db3aada8fa153da0af02ed9eccea3d7d8277ed7c2c847d697c1d4d56748abd3fa20bfd38eac86d1efb8f3d0dd3a20d0a7e5c1d051c79bcfe713d2cf6e15b1ceeb1ad8cecb96dfcea2794ccdd2d617cda803e7c9a019fdc707ac1ec5dca5abc5690328c4ac2c82c483e9fec34f33b5c2afde01c21dcfbbc1c6e06ec1c16a74c110cb7dbf4172fabef4bb49be907f01be2639d5be107ab6bddd5bacbd2744b8bcf5d0c6bbec3344
  | 8, 8 => 0xfe12eeb4fce2758bfc3e0176fac274d4f80ff336f734b506f6e94291f6657479f5a8ee32f5210d0ef1027f58f053c1fdf03d9387efdef6d4eec76f65eeae7dab
  | 9, 0 => 0xc2afde01b47be621a6563cc38ab84b5d7f4590c9764e5f614f8c57c22efbd9642eedfa851e7359ed1729918f1606144c1561a43a1142fa4105169eb0
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 5, 0 => 0x12102000000000000500000424c9205000000000e100000000000000b00000000061020000000006100000000000000000000000021020000053500202000005350020000000000000000000000002100000000000000b
  | 6, 0 => 0x480e200000000000000b000000280620300000104402020000000002100000005150020200000000000000000000000007000000480a200000000000a102000000000a105000000000000b000000480e20100000514c02000000000006101000000000000500000000000060000000002100000000000210300000000000060000000006103000000380220000000048062000000010440204000000000000600000000000000000000006103000000000a105000000000e10100000520c520300000018022020000000000009
  | 6, 1 => 0x544c0200000000000000500000000c91050015110440301000000000e1050000000002103000000000e1000000003802200000000000610500000048062010000004802200000000480a202000000000000000000324c520400000104402000000000000006000001044020300000000000100000000000006000000380220300000304c02040000001802200000004350520000000514c0201000000010d1020000000006100000005350420100000000000000000000012103000000000000600000000000070000000000005
  | 6, 2 => 0x60000000006103000000000000c00000324c520400000000021020000000000010000000000000b00000511012020000002802200000000000e102000000000e102000005050420000000048022020000053500200000000480e20200000000c010400000038022030000000012103000000000000500000000c01020000052105200000000000000c000000000e10300000000121050000032481204000001044020100000435012000000004806200000000001210200000104402020000000006100000000000000b
  | 6, 3 => 0xa102000000000000300000000000020000003806202000000000000600000000c9105000000000210200000104402030000000000006000000000000600000544c4201000000000e103000000180220100000000000030010d52105300000000000000c00000544402010000000002102000000480e2010000053500202000000000210500000544c520100000000c9104000000000000d00000000061000000052101200000000000000c000000000000f00000038022000000053500202000000000e1000000000000007
  | 6, 4 => 0x8000000000000000000038022000000000000003000000000000c0000000002103000000000000300000104402030000010440200000000000e10000000000021050000004802203000005350020100000000121010000053500202000000000a10500000544c0203000000000e10200000018022000000000000002000000000000600000434802040000000000007000005110120300000405002000000004802203000004350520100000038062020000050504202000000000000200000000021020000002806204
  | 6, 5 => 0x2103000005150020300000000121000000001802200000005110120200000000021020000000000006000000001210300000434c12000000000000003000000280620200000504c420100000520c1202000002048020400000038022010000000000006000000000000600000514c02020000000012105000000000000f0000000000006000000480e200000000000000000000000021020000000000006000000000210500000048022030000000000003000000000000600000304c020000000520c120300000304c0203
  | 6, 6 => 0xe1020000000000002000005110120200000038022000000000002102000000010d10000000000061010000003802202000000000000b000000000000b000000000e1030000053504202000000000000f00000104402030000000000010000000000000f0000000000006000000000e10300000514c020200000544c0200000001044020000000000c9105000000180220300000000021000000000006102000000000210100109324c130100000505042000000000000006000000000000700000018022010000000000002
  | 6, 7 => 0xa103000000380620000000000000080000040500203000000480220100000000000020000000000002000000000000c0000000000010000000000a1020000000000007000000480a2020000054440201000004350520100000520c52000000000000009000000000000500000018022020000010440202000000000210000000000000050000000006100000000000000300000000021030000000000000000000000000c000000000a103000000480220100000424c9201000000380220400000000000060000000002102
  | 6, 8 => 0x1001030000000000006000000000a105000000480e20200000520c120000000000000060000000006105000000000000f000000280620000000514c02000000004806202000005050420200000424c920500000000000060000001802202000000001210300000000000010000000000003000000000000f000000001210200000000121000000052101200000000480a2030000000000003000000000000b0000053500202000000000000900000000000080000000006103000000000610500000000021020000032485204
  | 6, 9 => 0x8110400000000c910400000000c0104000000000000b00000521012000000000006102000005350020000000544c4200000000001210300000038062000000002802203000000000000000000000021000000000002103000000000210000000000000060000051101202000000000001000000000000010000000006102000000000210500000018022000000000002103000000000000600000048062030000000006105000005110120300000414802040000000000007000000000000b00109215013010000000000006
  | 6, 10 => 0x50000000000006000000000000f00000018022000000000012100000001044020400000000021000000000000006000000010010000000000061050000010440202000000380620200000018022030000002806202000000010910500000104402030000010440202000000000000b00000000021000000000000010000000000000900000000061000000002806201000000380a20400000000c910400000000000050000000002105000005050420100000535002010000002802203000000480e20000000544c0200
  | 6, 11 => 0x6100000000000000700000000000050000000002105000000180220100000018022010000000000007000000480e200000000000a1050000000000010000000000000f000000280220200000000000050010d404c130100000000c91040000000000006000000480e2020000000000006000000180220100000000000070000001802204000000000210300000535042020000043485204000000180220000000000c910400000000000000000000000005000000000000700000544c42000000000000010
  | 7, 0 => 0x2101000000010d10000000001011030000000000006000000000210300000000000070000000000002000000000210200000000000020000000012103000000000210200000000000010000000000002000000000000b00000000c1102000000380a20000000028022010000002802203000000000210300000000c510300000000021010000000000002000000000610100000000000020000000002103000000000000d000000000000500000000021030000000002105000000000000100000028022000000000012105
  | 7, 1 => 0x300000000021010000004802200000000000000900000000021000000010440200000000000a10000000000000050000000012102000000480620200000000000050000000081100000000000610100000000000020000000000000000000000000400000000411030000000012100000000280220200000000c9104000000000610200000404c1201000000010d1020000000002103000000000000300000000000040000003802200000000000000200000028062020000000000005000000000a1030000000002101
  | 7, 2 => 0x2100000000000a105000000000e1020000000000007000000008510400000001011000000000105103000000000a10400000038022010000000002103000000000e1000000000012102000000480220200000000000030000000000000000000000a1000000000006100000000000000100000000000070000000012100000000000610000000000c510300000000c9104000000010110000000000000090000000000006000000001210000000000061030000000006104000000004110100000001011020000000000008
  | 7, 3 => 0x3000000008010300000000061000000000000006000000000210300000048062000000003806203000000180220200000000021010000000109105000000000000700000000000020000000000001000000000000f00000000411040000000000010000000000e10400000001011000000000006101000000000e10000000000c11040000000012102000000000000f0000001802201000000000000d00000000000070000000002100000003248120100000000c910500000000000060000001802203000000000e103
  | 7, 4 => 0x105101000000000210200000018022000000000000005000000000000500000000121020000000000003000000000000700000000121000000000000007000000000e102000000180220100000000121030000000002100000000380620100000000401030000000006101000000000e100000000000000000000001051000000000006102000000000000a000000001210500000000c51040000000002101000000000001000000000c9105000000000000000000038062000000000012101000000000a104000000000000b
  | 7, 5 => 0x10d100000000008010200000038062030000004802200000000000000f000000000000500000000121050000000000003000000000e101000000000a1030000002806200000000001210300000038022030000000000001000000000000b0000000002100000000004110200000000c810000000000021000000000012102000000000000500000000061020000001802202000000000a10000000048c9201000000010510000000000000020000000000003000000008010300000000061000000000002101000000000a105
  | 7, 6 => 0x10110000000000000050000000002102000000000210200000000000100000000006103000000380a2000000003802202000000000000500000000c11000000004802202000000000a10500000001011000000000006101000000000000700000000401040000002802200000000000a10200000028022020000001802203000000010510200000000801030000000012105000000000000300000001001020000000000006000000000000500000018022000000000012101000000000210200000000000050000000000004
  | 7, 7 => 0x6100000000000000600000001001030000000000001000000000000300000000000010000000002105000000000e1000000000006101000000004110000000000000080000000002102000000000000c000000000000f000000000000100000424c9201000000180220200000000000000000000000007000000000000600000038022000000021501201000000001210200000000000030000004802202000000000e102000000000a10200000000000010000000100100000000000000600000000121030000000002102
  | 7, 8 => 0x12103000000000000b0000010440201000000000e102000000000000100000000c51010000000000003000000000210500000000021030000000000002000000000000c0000000006100000000000a1020000000006102000000000610000000000000030000000040104000000000210300000001011020000000000006000000001210000000000000000000000000000000000010510200000000000060000000000003000000000210500000000c11040000000006104000000000000b0000000002101000000480a203
  | 7, 9 => 0x21030000000000006000000000a10200000000c110000000000061000000000002100000000000000100000000000060000000002104000000010d1010000000006102000000000e1000000000006105000000480a203000000000210300000000061010000000006102000000000000b000000000000000000000021050000000000007000000000610000000000121020000000081104000000000000600000000000070000000006104000000000000e0000000002103000000000000700000000000050000000000003
  | 7, 10 => 0x21020000000000005000000000210000000000061030000000000005000000010510200000000c510100000000000020000000000007000000000000500000000021040000000108102000000000610000000000000020000000000007000000000000500000000c1104000000010110100000000021040000000006100000000000a10500000000021000000000000005000000000000b0000000040102000000000e105000000000610100000000021000000004802201000000000e1010000000012100000000000a101
  | 7, 11 => 0xc00000000000050000000002101000001044020300000000c110400000000401000000000000005000000000000b000000000210100000018022000000000006102000000010010000000018022020000004806202000003248120100000001051030000000000000000000000a10200000000021010000000085104000000001210100000000021040000000012100000000480e20000000000021020000000000001000000000000c000000280620000000000c11020000000040104000000000000b0000000000000
  | 7, 12 => 0x388520100000008c9201000000000e10200000000000020000000000001000000000000500000000021000000000000003000000010d102000000000e1040000000041100000000000e1010000000002103000000380a2010000000000000000000000000200000000061010000000006102000000008410200000000121000000000002100000000010d10200000000121000000000041103000000000e1000000000006104000000000e10000000000021020000000000010000000010510200000000000050000003806200
  | 7, 13 => 0xc0000000012102000000000e1000000000000006000000000000100000000c1101000000000a1010000000101100000000000210100000000061020000000006102000001044020200000001051020000000006100000000000e10100000000c5102000000000e10000000000021050000010440200000000001210500000000411010000000000007000000000000b0000000002100000000000000b0000010440201000000000000000000000000100000000000000000000000610400000000000070000000002103
  | 7, 14 => 0x100000000021010000000000001000000280620000000048062030000000000004000000000000b000000000a102000000000e100000000000210300000000021020000000006101000000000000600000000c91040000000006100000000000000c000000000e101000000000000300000048022030000000012100000000000000000000000401020000000002103000000000a1000000010440202000000000000c000000008510100000000021050000000012105000000480220000000000000030000000000000
  | 7, 15 => 0xe10000000000c91040000000000005000000000a104000000000000000000000c1101000000004110400000038062000000010440202000000000000b0000000012105000000000000300000000121020000000000002000000000000000000000061010000000000005000000000a103000000280220300000000401000000000002100000000000000300000000000010000000006102000000000000300000000c510300000000c510000000000000030000000041104000000000a10000000000021030000000041100
  | 7, 16 => 0x10d10300000000c5104000000000a103000000010d1000000000000006000000000a1050000000000001000000010910500000000c51030000000040103000000008510100000000021030000000080102000000000e10100000000c0102000000000a102000000000000b0000003802202000000000a10400000000061030000000085104000000000a101000000008110400000434c520100000000000030000000041102000001044020100000000401020000000006103000000000000600000000c11020000000101100
  | 7, 17 => 0x1051000000000000006000000000a105000000000610500000000c11000000000002104000000000e103000000000e101000000000000700000000000060000002806201000000000000700000000c51040000000012102000003248120100000000061020000000002102000000001210500000000841020000000000007000000004010000000001051010000000006104000000000610000000000c0104000000010d1000000000000007000000000000000000000061000000000000000000000000a1030000000000000
  | 7, 18 => 0xe102000000001210000000000021000000000000002000000010d10300000520c520000000001011020000000040102000000000000f000000000e1030000000006103000000000001000000544402010000000002100000000000610000000000c1101000000001210100000000061010000000000005000000001210500000028062030000000002104000000000e10200000000121000000000006101000000000000600000000021000000000000002000000480220000000000c510200000000121000000000000000
  | 7, 19 => 0x61010000000101100000000000210000000000021020000000000001000000000e1000000000000002000000010110100000000061020000000000003000000001210500000000061000000000012101000000480a201000000000e100000000000210100000000061000000000002101000000000e104000000000000b000000000e100000000000e100000000000e1040000000006102000000480e201000000000e10500000000061010000000002105000000000000000000000c5102000000010d1000000000012101
  | 7, 20 => 0x180220300000000c01020000000000006000000000000700000000021050000000002100000000010d107000000000e104000000000610000000000411030000000041102000000000210400000000000020000000000003000000000a1040000000002101000000000610400000434c1200000000000a103000000000a103000000000210000000001011030000000002100000000000210300000104402020000000002100000000000000a00000425012010000000002105000000000e101000000000000b00000000c5101
  | 7, 21 => 0x411010000000006102000000480e201000000000e1020000000000007000000000000e000000000210200000000000070000000081104000000000e103000000004110000000000021010000000101100000000000000a000000000000b0000000000004000000000000f000000000610100000000c510400000000c51010000000000003000000001210200000000021050000000002100000000010d1020000000041100000000000000c00000000000060000000012102000000008110400000000121010000000006103
  | 7, 22 => 0x1001000000003806201000000000a1030000000081104000003248120100000001011020000000084102000000000e10000000000000060000000006101000000004110200000001051010000000002100000000480a202000000000e1010000000002100000000000e1030000000041101000001044020200000000c91040000000000005000000380a20000000000411040000000006102000000004110400000000c9101000000000000300000001051000000000000007000000000210000000000000010000000002105
  | 7, 23 => 0x6100000000000e10100000048062010000000002102000000000000500000000411000000000080103000000000000f0000000040102000000000610200000000021010000000002100000000000000f000000000210500000000000000000000012102000000000e10500000000000030000000006102000000010010200000000411030000000000006000000000000b00000000c110100000000000050000000002100000000000000700000000c5100000000480e2030000000000000000000000a1020000000012101
  | 7, 24 => 0x2000000000e10100000000000070000000006101000000480a2020000000101102000000000a1010000000002100000000004010300000000000000000000002101000000004110200000000000000000000041101000000000000600000000c1104000000010010000000000000100000000000005000000001210100000000c1102000000000000600000000000060000000006100000000000000200000000021010000000012101000000480a201000000010d10000000000c110000000000411030000000006100
  | 7, 25 => 0x300000000021050000000000005000000004010200000000061030000000006103000000010d1020000000000003000000010d1020000000012105000000000610100000000c110300000000000030000000101103000000000e101000000480a201000000000e10100000000000010000000002104000000000000700000000000030000000012101000000010510100000000021020000000000002000000000000000000000000030000000006104000000010d1010000032485201000000000e1030000000000009
  | 7, 26 => 0x6100000000000210400000038022010000002806202000000000000c000000000210200000000021010000000002100000000010d100000000001210500000028062000000043501201000000480620200000000000020000000012103000000000e1010000002806201000000000a100000000000610000000048062010000000000004000000000610200000000121000000000041103000000000000b000000000000700000000021050000000000007000000000000b0000000012102000000000a104000000000000f
  | 7, 27 => 0x6101000000000001000000000c11030000000000003000000000610000000000401000000000012102000000000210000000048062020000000000000000000000000d00000000411040000000000005000000000210100000000000080000000000000000000480a200000000000000d0000000000003000000000000b000000380620000000000021050000000012101000000000000100000000c9104000000000000600000000021010000002802201000000380620100000000411040000000080102000000000e100
  | 7, 28 => 0x1210300000000061050000000006101000000480e20200000000000000000000002101000000000000300000000411010000002806202000000380a200000000000000a000000000e1020000000000006000000000000600000000061030000000012101000000010d10100000000000060000000000002000000000610100000000021050000000000007000000000000500000000061030000000006102000000000000b000000000210400000000411010000000006102000000280620100000000061030000000000002
  | 7, 29 => 0x210200000000121030000000000007000000000000000000001011010000004881201000000001210300000000000020000000012102000000000e101000000380620100000000401030000004806202000000000610100000000c1104000000000000b00000000021000000000002103000000004110100000000000070000000000005000000010d1000000000002102000003250120100000001051010000000002104000000000000200000000061010000003802201000000001210500000000000020000000002101
  | 7, 30 => 0x2101000000280220100000000061000000000040101000000380a20100000325052010000001802201000000010d10200000000000030000000000002000000001210000000000000100000000000001000000000e104000000000000f000000000000d000000000000900000001011020000000006101000000001210000000425012010000000000008000000000610100000000061050000000000006000000000000200000028022010000000000001000000000000b000000000a10300000000021010000000041102
  | 7, 31 => 0x28062000000002806202000000000610400000038022030000000002105000000000000000000000c110400000000121000000000080102000000000a104000000000610200000000000100000000002101000000480620000000000411040000000000006000000000000b0000000002101000000000210400000038062030000000012103000000000000600000000411030000000006100000000004110200000000000050000000000005000000000e102000000000210100000000c910400000000c51010000002802200
  | 7, 32 => 0x210200000000000000000032485201000000000000200000000000010000000006101000000000000200000000021000000000000005000000000001000000000061020000000000005000000000000700000000c51010000000002105000000000000f00000038022020000000012100000000000000600000000000060000000041104000000180220100000000061020000000002100000000000e103000000001210200000000121020000000000005000000010d1020000000002100000000000000c000000000e100
  | 7, 33 => 0x851000000000000000000000000000c000000001210200000000000000000000002102000000010d1010000000000008000000480a20000000000000000000000041101000000000000a000000004010000000000000000000000000005000000000000b000000000210300000000021000000000000000000000000000000000048062010000000000006000000000e100000000004110100000000401000000005881201000000000610400000000000050000000000002000000000610100000000021010000000000005
  | 7, 34 => 0x6100000000010d103000000010d103000000000000500000000021010000000002103000000180220000000000c5101000000004110100000000021050000000002101000000000000000000001011000000000000005000000000a10300000000021030000000006100000000480e200000000000a103000000000210100000000c91040000000000006000000000000500000048022010000000000000000000000000f00000000000050000000002100000000000210500000000061030000000006100000000000e100
  | 7, 35 => 0x841020000000040100000000008010400000000c110200000038022020000000041102000000001210000000000401000000000002100000000010d10300000434c120100000000000030000000000000000000000001000000000000060000000000003000000000210100000000c11010000000105102000000000000600000000000000000000002103000000000610100000000000050000000000003000000000e103000000010110100000000000000000000000005000000010110300000000000050000000006100
  | 7, 36 => 0x6000000010110000000000c1101000000000e10200000000021020000000002100000000010110200000018c9201000001044020100000000021050000000002105000000000210400000000801030000000000005000000000000000000048022010000000000001000000000610000000048022030000000002102000000000e102000000000000600000000021030000000006102000000000000f0000000006101000000000210000000000021030000000000007000000000610100000000841000000000002104
  | 7, 37 => 0x5000000000a102000000000000200000000c51010000000000000000000004010200000000851040000000000005000000000e1000000000000001000000010d102000000000000500000048062000000000000002000000000000500000048022000000000002105000000000000000000000000000000000002100000000000210100000000000070000004802201000000000e10200000000121010000000006100000000000000c0000000000005000000480e20000000000021010000000006100000000010d101
  | 7, 38 => 0x101100000000000000200000524022010000000000007000000000610000000000c11010000000000002000000000000700000000000020000000000000000000000210100000000000000000000000007000000000e10000000000121020000000000009000000010d1000000000041103000000000e1020000000002103000000004110000000000061030000040441201000000000000800000000000010000000105100000000000a1000000000002100000000000a1050000000000007000000480e2030000000006105
  | 7, 39 => 0x20000001802201000000000000500000000021050000000002101000000000210100000000000060000000002102000000004110000000000021000000000002100000000000000100000000000100000000041101000000000000000000000021040000000040104000000008510400000028022030000000100102000000000000c00000000801000000000006101000000000000600000000061050000003806202000000280220000000000021000000000000002000000000a102000000180220100000000c1102
  | 7, 40 => 0x610300000000c910000000000061020000000002100000000004110000000000061010000052402201000000000000500000000000000000000000005000000000000100000058852010000000006104000000000610000000000c51020000000000003000000480220200000001011010000000040100000000000001000000000000030000010440200000004350520000000521012000000000002102000000000000f00000000061000000000002103000000010d101000000000000c000000000a1010000000006105
  | 7, 41 => 0xe105000000000210000000000000050000000041101000000000210400000018022000000000000003000000000000600000000000050000000000005000000000210100000000000050000000000005000000000610300000000061000000000000005000000000e10300000000061040000000000001000000000610400000000021010000000006100000000000000100000000c11010000000000005000000010d1000000000006102000000000e102000000010d1000000000000008000000001210000000000c5101
  | 7, 42 => 0x401020000000006101000000000000000000000021030000000000005000000000000700000000c0104000000000000600000000000020000000000001000000000a105000000000210000000000000060000000101101000000000000200000000000050000043505200000000000000700000028022000000000006100000000010d101000000000000600000000021000000000100100000000000a10100000000000070000000006105000000000000100000000c9104000000000210200000058c9201000000000000b
  | 7, 43 => 0xe10300000018022000000000002104000000001210200000000021030000000002101000000000e1000000000006100000000000000500000000841020000000000002000000004110000000000021000000000002102000000010d100000000004010000000000000050000000002104000000000210100000000021040000000002100000000000610000000000000070000000012100000000010d1010000000000005000000000000100000000c51020000000006102000000008410300000000061010000003806203
  | 7, 44 => 0x10000000002103000000480e20200000000411000000000006104000000000000500000000000050000000084102000000000210000000000021040000002806201000000000000600000000c0102000000010d103000000000610400000000000070000010440201000000010d10100000000061010000000006100000000010110300000000061000000000002102000001044020100000000121000000000000008000000004110100000000000010000000000006000000000610000000000021000000000000007
  | 7, 45 => 0x480e20200000000000070000000000003000000000210100000000061020000000000006000000000000000000000c11020000000000000000000000000700000000061010000000000000000000000610500000000811010000000000006000000000a1030000000000007000000000000f0000000000002000000000000100000000061040000000000000000000000e10200000000c910400000000c1103000000000610400000000000040000000006105000000000a101000000000000f00000000000050000000041100
  | 7, 46 => 0x610300000000061010000000000005000000000210200000000401000000000006101000000280620100000000000070000000000000000000480e201000000000000000000000000000000000040102000000000000000000000021010000000000005000000004110100000000c110200000000411010000000012102000000001210300000000121030000000006100000000000000800000000000060000000002100000000000610100000000000050000000000008000000000000900000104402000000000000007
  | 7, 47 => 0x380620200000000061030000000041100000000000000f00000000000050000010440200000000004110100000000000010000000002101000000280220100000000c910400000000021010000000002103000000000210000000000000010000000041101000000000a100000000000000f000000010d100000000000000500000000061010000000000006000000000a1030000010440200000000000000300000000000020000000000001000000000000b0000000100100000000004110400000000000070000000002100
  | 7, 48 => 0x6101000000000000500000000061010000000000005000000480e200000000000000600000000021000000000006102000000000a105000000480e2010000000000005000000000610000000000021000000000000007000000000210500000000021010000000000006000000000210400000000000000000000006102000000010110300000000000060000000000007000000000210200000000021000000000041104000000004110400000000021010000000000010000000000a10500000000411040000000885201
  | 7, 49 => 0x4010400000000c91040000000000007000000000610400000000000050000000002101000000004110100000524402010000000002102000000000000700000000000070000000000008000000188120100000000000050000000000001000000000210000000000000070000000002101000000480e2010000000002104000000000210500000000021030000000040102000000010d100000000000210000000000000060000000002104000000180220000000000000060000000002101000000000000f0000000000006
  | 7, 50 => 0x411040000000000006000000000210000000000411020000000002105000000000000500000000061000000000002104000000000210100000000000000000000002101000000004010400000000000010000000002101000000000000400000000021000000000002100000000004110300000000000010000000000006000000000610000000000c9101000000000000500000000021010000000002105000000004110400000000000060000000002100000000000a105000000000000000000000000010000000000006
  | 7, 51 => 0x50000000006100000000000610000000000121020000000002101000000000210300000000061010000001802201000000000000100000000000050000000006104000000280620000000000000000000002802200000000480e200000000004010000000000021000000000041104000000004110100000000851040000000000010
  | 8, 0 => 0x8010000000000000000000000000005000000010d103000000000610000000000000040000000000001000000000610200000000841000000000000003000000004110200000000061000000000006102000000004110000000000000020000000041101000000000000300000000000050000000012103000000000000500000000c1101000000000000100000000c5100000000000000000000000841020000000041103000000000000200000000000020000000000000000000000000300000001091010000000000003
  | 8, 1 => 0x3000000000000100000000c1100000000000000300000000801020000000002100000000000000200000000c51010000000000000000000000000200000000000000000000002102000000000000100000000000000000000000001000000010910100000000000030000000041102000000008510100000001011020000000080103000000010d10300000000000030000000000001000000000a101000000000000d0000000000002000000000000400000000000000000000101101
  | 8, 2 => 0x105103000000000000300000000411020000000000003000000000000100000000000030000000000002000000000000200000001011000000000101101000000000000100000000000010000000085101000000000000400000000000050000000000003000000000210300000000801000000000000000000000000000000000001011020000000000002000000000000400000001011030000000006100000000004010000000000c510200000000000020000000040102000000000000800000000000020000000000004
  | 8, 3 => 0x400000000000040000000000000000000000000100000000000050000000006103000000004110200000000000000000000000000000000000000200000000841000000000000000000000000000000000000000020000000012101000000000000500000000000050000000006103000000000000100000001051020000000000007000000008110100000000c510000000000c110100000000c51010000000000005000000000e10100000000c110000000000021030000000000009000000010d1010000000041100
  | 8, 4 => 0x30000000000001000000000000500000000000000000000000005000000008110100000000121020000000000002000000000e100000000000610100000000000020000000080100000000000e101000000010d100000000010d100000000000a1020000000000001000000010d10100000000c1103000000000a10000000000c910100000000000000000000012101000000000000000000000000020000000000000000000000000300000000000030000000000003000000010910100000001051020000000000007
  | 8, 5 => 0x10000000040101000000000000000000000c1100000000000000200000000c1102000000000e101000000001210200000000c5100000000000000100000001051020000000000000000000000000500000000000040000000000001000000001210000000000000020000000002101000000000a1020000000084103000000000000300000000801000000000101100000000000000200000000000010000000000003000000000000200000000c1102000000000000500000000000010000000000002000000000a101
  | 8, 6 => 0xe100000000000000400000000021020000000002101000000010d1030000000000002000000010d10000000000000020000000002100000000000e1020000000002101000000000a100000000000a1020000000000006000000001210000000000000020000000000005000000000e10300000000021010000000000000000000000610200000000000020000000006100000000000610100000000000000000000002101000000000000f00000000000100000000000007000000004110300000001051020000000085101
  | 8, 7 => 0x500000000c910100000000021000000000012101000000000000500000000c1102000000000000000000000401020000000000005000000000210200000000c5102000000000000300000000000000000000040102000000010d103000000010d1010000000085101000000000000300000000401000000000002103000000004010100000000000030000000105101000000000610100000000021000000000000007000000000000000000000c11020000000000001000000000000500000000000010000000006102
  | 8, 8 => 0x5000000000210000000000021020000000000005000000000000000000000c91010000000000003000000000000700000000000000000000084102000000010510300000000000020000000101103000000008410000000000000010000000000001000000000000300000000000010000000000001000000000610000000000061020000000000005000000000000400000000841000000000000002000000004010100000000c510200000000000070000000000005000000004010200000000000000000000006101
  | 8, 9 => 0x12100000000000210100000000411010000000000003000000000000700000000c11030000000080100000000000000800000000000050000000000001000000000e102000000000000300000000000000000000000003000000000000000000000c5102000000000a1030000000040100000000004010200000000000030000000041101000000000000300000000000020000000084102000000000000a0000000000000000000000000500000000121000000000000007000000000610000000000000010000000000004
  | 8, 10 => 0x600000000000070000000000005000000000210000000000000020000000000001000000000610100000001011010000000000005000000000000000000000061030000000000005000000000000500000000411000000000000004000000000000500000000000000000000000000000000000000500000000000020000000006101000000000000700000000000010000000080102000000008410000000000841020000000101102000000000000000000000c9101000000000000600000000000000000000000009
  | 8, 11 => 0x50000000000001000000000a101000000000000400000000000010000000000000000000010d101000000000000800000000801030000000000005000000000610300000000000000000000002100000000000610000000000c5101000000000000700000000c51030000000000000000000000000500000000000010000000040103000000000000200000001011010000000080100000000008010200000000000010000000000005000000000000000000000c5101000000000210300000000021030000000000000
  | 8, 12 => 0x210200000000000010000000000001000000010d10000000000411000000000000001000000000a1000000000000001000000000a10100000000061010000000000001000000000000500000000811010000000000002000000000000f0000000000000000000000000f000000000610000000000000010000000101100000000010d1010000000041101000000010510000000000c5100000000000000400000000000050000000041101000000008110100000000000050000000000000000000000000f0000000000000
  | 8, 13 => 0x81101000000008510100000000000040000000040101000000000000500000000000050000000006102000000000000100000001051010000000000000000000004110000000000c510100000000021010000000000004000000010d103000000000000000000000000060000000040101000000000000100000000000030000000000005000000000e1020000000000007000000000000300000000061010000000000000000000000000500000000000070000000000005000000000210100000000000000000000000004
  | 8, 14 => 0x2101000000000610300000000c5100000000010d100000000000000600000000000050000000000001000000000a1000000000006101000000000000800000000000000000000000001000000000000400000000811010000000000005000000000610000000000c5102000000000000000000000c51000000000000003000000010d1010000000012103000000000000000000000000030000000000004000000000e10200000000000010000000000000000000000000600000000000060000000000003
  | 8, 15 => 0x610100000000000000000000000004000000000000000000000021020000000002100000000000210300000001011000000000002100000000000a100000000000000100000000061000000000002100000000000000000000000851010000000002101000000004010100000000000010000000041100000000010d10000000000061010000000002101000000000210100000001011010000000000000000000001210200000000000010000000000004000000000000600000000061010000000000000
  | 8, 16 => 0x4010000000000841000000000002100000000004010000000000061020000000002100000000004110100000000000070000000000001000000000000000000000061000000000000004000000000000000000000061000000000040100
  | 9, 0 => 0x1000000000000000000000000010000000000001000000000000300000000000000000000000002000000000000200000000000020000000000000000000000000100000000000030000000000001
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 12 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_55 roots_55 8 s ws hint
  | 1 => checkCutEntry dom_59_4 roots_59_4 8 s ws hint
  | 2 => checkCutEntry dom_31 roots_31 8 s ws hint
  | 3 => checkCutEntry dom_47 roots_47 8 s ws hint
  | 4 => checkCutEntry dom_51_4 roots_51_4 7 s ws hint
  | 5 => checkCutEntry dom_61 roots_61 7 s ws hint
  | 6 => checkCutEntry dom_62 roots_62 6 s ws hint
  | 7 => checkCutEntry dom_61_2 roots_61_2 6 s ws hint
  | 8 => checkCutEntry dom_15 roots_15 5 s ws hint
  | 9 => checkCutEntry dom_23 roots_23 5 s ws hint
  | 10 => checkCutEntry dom_39 roots_39 5 s ws hint
  | 11 => checkCutEntry dom_29_2 roots_29_2 5 s ws hint
  | 12 => checkCutEntry dom_45_2 roots_45_2 5 s ws hint
  | 13 => checkCutEntry dom_53 roots_53 5 s ws hint
  | 14 => checkCutEntry dom_57_4 roots_57_4 5 s ws hint
  | 15 => checkCutEntry dom_54 roots_54 5 s ws hint
  | 16 => checkCutEntry dom_58_4 roots_58_4 5 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_59_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_51_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_61 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_62 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_61_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_29_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_45_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_53 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_57_4 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_54 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_58_4 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_63 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
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
private theorem z6_32 : ∀ i, 32 ≤ i → i < 48 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_48 : ∀ i, 48 ≤ i → i < 58 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 10 48 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 58 → Z 6 i = true := (range_split (range_split z6_0 z6_16) (range_split z6_32 z6_48))
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
private theorem z7_336 : ∀ i, 336 ≤ i → i < 338 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 2 336 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 338 → Z 7 i = true := (range_split (range_split (range_split (range_split (range_split z7_0 z7_16) (range_split z7_32 z7_48)) (range_split (range_split z7_64 z7_80) (range_split z7_96 z7_112))) (range_split (range_split (range_split z7_128 z7_144) (range_split z7_160 z7_176)) (range_split (range_split z7_192 z7_208) (range_split z7_224 z7_240)))) (range_split (range_split (range_split z7_256 z7_272) (range_split z7_288 z7_304)) (range_split z7_320 z7_336)))
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
private theorem z8_160 : ∀ i, 160 ≤ i → i < 169 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 9 160 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 169 → Z 8 i = true := (range_split (range_split (range_split (range_split z8_0 z8_16) (range_split z8_32 z8_48)) (range_split (range_split z8_64 z8_80) (range_split z8_96 z8_112))) (range_split (range_split z8_128 z8_144) z8_160))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_0 : ∀ i, 0 ≤ i → i < 16 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_16 : ∀ i, 16 ≤ i → i < 18 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 2 16 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 18 → Z 9 i = true := (range_split z9_0 z9_16)
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

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 14]⟩], 16⟩

theorem wit_mono : PEqualNP.MetaComplexity.Monotone2 wit := by
  simp [wit, PEqualNP.MetaComplexity.Monotone2]

theorem wit_sz : wit.size ≤ 11 := by decide

set_option maxRecDepth 40000 in
theorem wit_ev : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = Nat.testBit (4278124270 * 2 ^ 32 + 4277074560) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_63.testBit r.val = (fun x : Fin 6 → Bool => Nat.testBit (4278124270 * 2 ^ 32 + 4277074560) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) (pt6 r.val) := by decide +kernel

theorem lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124270 * 2 ^ 32 + 4277074560) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) t → 11 ≤ t :=
  lower_to_circuit6 (fun x : Fin 6 → Bool => Nat.testBit (4278124270 * 2 ^ 32 + 4277074560) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) goal_63 11 hT6 (by unfold IsConst; decide) low_63

end PEqualNP.Outside.L_meta_38141_aux

theorem PEqualNP.Outside.L_meta_38141 :
  ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124270 * 2 ^ 32 + 4277074560) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124270 * 2 ^ 32 + 4277074560) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  exact ⟨PEqualNP.Outside.L_meta_38141_aux.wit, PEqualNP.Outside.L_meta_38141_aux.wit_mono, le_trans PEqualNP.Outside.L_meta_38141_aux.wit_sz (PEqualNP.Outside.L_meta_38141_aux.lower s hs), PEqualNP.Outside.L_meta_38141_aux.wit_ev⟩
