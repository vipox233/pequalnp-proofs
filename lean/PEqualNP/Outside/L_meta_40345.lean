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

namespace PEqualNP.Outside.L_meta_40345_aux

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

def forceN {α : Type} (n : Nat) (k : Nat → α) : α := match n with | 0 => k 0 | m + 1 => k (m + 1)
theorem forceN_eq {α : Type} (n : Nat) (k : Nat → α) : forceN n k = k n := by cases n <;> rfl
def bsr (read : Nat → Nat) (h : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo + 1 < hi then
      forceN ((lo + hi) / 2) fun mid =>
      if read mid ≤ h then bsr read h f mid hi else bsr read h f lo mid
    else lo

def hw256 (seed w : Nat) : Nat :=
  forceN ((((w &&& 4294967295) ^^^ seed) * 2654435761 +
           (((w >>> 32) &&& 4294967295) ^^^ seed) * 2246822519) &&& 4294967295) fun x =>
  forceN (((x ^^^ (x >>> 16)) * 2246822519) &&& 4294967295) fun y =>
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
  forceN (idxH s h) fun i =>
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
         forceN (hk seed cz) fun h =>
         !(foundH S N htAt idxH s h cz) && !(cutHitH s h cz)))

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
         forceN (hk seed cz) fun h =>
         !(foundH S N htAt idxH s h cz) && !(cutHitH s h cz))
      have hF (zs) (hz : RunD dm (T &&& dm) s zs) : F zs = true := by
        have hcz := hr hz
        have hcutf : cutHitH s (hk seed (ori zs)) (ori zs) = false := by
          cases h : cutHitH s (hk seed (ori zs)) (ori zs) with
          | false => rfl
          | true => exact absurd hcz (hcut h)
        simp only [F, forceN_eq, coversP_ok hd pairs hpairs hz, scr_no pool hz, hcutf, Bool.not_false, Bool.true_and, Bool.and_true, foundH]
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
            forceN (hk seed cz) fun h =>
            !(foundH S N htAt idxH s h cz) && !(cutHitH s h cz)))) = F := by
        funext zs
        have hfst : (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))).map Prod.fst = zs := by
          simp [List.map_map, Function.comp_def]
        rw [coversD_eq, hfst]
        simp only [F, Bool.and_assoc]
      rw [hFeq, hN] at hb
      contradiction

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

theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with | nil => rfl | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
def goal_all : Nat := 0xfeeaeee0fae8aaa0
def dom_63 : Nat := 0xffffffffffffffff
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]
def dom_x1_0_x5_1 : Nat := 0x3333333300000000
def roots_x1_0_x5_1 : List Nat := [0x2222222200000000, 0x3030303000000000, 0x3300330000000000, 0x3333000000000000]
def dom_x1_0 : Nat := 0x3333333333333333
def roots_x1_0 : List Nat := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]
def dom_x1_1_x3_0_x5_0 : Nat := 0xcc00cc
def roots_x1_1_x3_0_x5_0 : List Nat := [0x880088, 0xc000c0, 0xcc0000]
def dom_x1_1_x3_0 : Nat := 0xcc00cc00cc00cc
def roots_x1_1_x3_0 : List Nat := [0x88008800880088, 0xc000c000c000c0, 0xcc000000cc0000, 0xcc00cc00000000]
def dom_x2_0_x4_1 : Nat := 0xf0f00000f0f0000
def roots_x2_0_x4_1 : List Nat := [0xa0a00000a0a0000, 0xc0c00000c0c0000, 0xf0000000f000000, 0xf0f000000000000]
def dom_x0_0_x4_1_x5_1 : Nat := 0x5555000000000000
def roots_x0_0_x4_1_x5_1 : List Nat := [0x4444000000000000, 0x5050000000000000, 0x5500000000000000]
def dom_x0_0_x4_1 : Nat := 0x5555000055550000
def roots_x0_0_x4_1 : List Nat := [0x4444000044440000, 0x5050000050500000, 0x5500000055000000, 0x5555000000000000]
def dom_x1_0_x4_1_x5_0 : Nat := 0x33330000
def roots_x1_0_x4_1_x5_0 : List Nat := [0x22220000, 0x30300000, 0x33000000]
def dom_x4_1_x5_0 : Nat := 0xffff0000
def roots_x4_1_x5_0 : List Nat := [0xaaaa0000, 0xcccc0000, 0xf0f00000, 0xff000000]
def dom_x1_0_x4_1 : Nat := 0x3333000033330000
def roots_x1_0_x4_1 : List Nat := [0x2222000022220000, 0x3030000030300000, 0x3300000033000000, 0x3333000000000000]
def dom_x3_0_x4_1_x5_0 : Nat := 0xff0000
def roots_x3_0_x4_1_x5_0 : List Nat := [0xaa0000, 0xcc0000, 0xf00000]
def dom_x4_1_x5_1 : Nat := 0xffff000000000000
def roots_x4_1_x5_1 : List Nat := [0xaaaa000000000000, 0xcccc000000000000, 0xf0f0000000000000, 0xff00000000000000]
def dom_x3_0_x4_1 : Nat := 0xff000000ff0000
def roots_x3_0_x4_1 : List Nat := [0xaa000000aa0000, 0xcc000000cc0000, 0xf0000000f00000, 0xff000000000000]
def dom_x4_1 : Nat := 0xffff0000ffff0000
def roots_x4_1 : List Nat := [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000]
def dom_x2_0 : Nat := 0xf0f0f0f0f0f0f0f
def roots_x2_0 : List Nat := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]
def dom_x1_0_x5_0 : Nat := 0x33333333
def roots_x1_0_x5_0 : List Nat := [0x22222222, 0x30303030, 0x33003300, 0x33330000]
def dom_x3_0_x5_0 : Nat := 0xff00ff
def roots_x3_0_x5_0 : List Nat := [0xaa00aa, 0xcc00cc, 0xf000f0, 0xff0000]
def dom_x3_0 : Nat := 0xff00ff00ff00ff
def roots_x3_0 : List Nat := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]
def dom_x1_1_x5_0 : Nat := 0xcccccccc
def roots_x1_1_x5_0 : List Nat := [0x88888888, 0xc0c0c0c0, 0xcc00cc00, 0xcccc0000]
def dom_x5_0 : Nat := 0xffffffff
def roots_x5_0 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]
def dom_x0_0_x5_1 : Nat := 0x5555555500000000
def roots_x0_0_x5_1 : List Nat := [0x4444444400000000, 0x5050505000000000, 0x5500550000000000, 0x5555000000000000]
def dom_x5_1 : Nat := 0xffffffff00000000
def roots_x5_1 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]
def dom_x1_1 : Nat := 0xcccccccccccccccc
def roots_x1_1 : List Nat := [0x8888888888888888, 0xc0c0c0c0c0c0c0c0, 0xcc00cc00cc00cc00, 0xcccc0000cccc0000, 0xcccccccc00000000]
def dom_x0_0 : Nat := 0x5555555555555555
def roots_x0_0 : List Nat := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]

namespace S_x1_0_x5_1
def pairsG : List (Nat × Nat) := [(33, 37), (33, 41), (33, 49), (36, 37), (40, 41), (44, 45), (44, 60), (48, 49), (52, 53), (52, 60), (56, 57), (56, 60)]
def r1sG : List Nat := [33, 33, 33, 36, 40, 44, 44, 48, 52, 52, 56, 56]
def r2sG : List Nat := [37, 41, 49, 37, 41, 45, 60, 49, 53, 60, 57, 60]
def mpG : Nat := 0xfff
def pool6G : List Nat := [48521121902889, 48521189009701, 57317080704305, 57317282031909]
def xsM : List Nat := roots_x1_0_x5_1.map (· &&& dom_x1_0_x5_1)
def goalM : Nat := goal_all &&& dom_x1_0_x5_1
def NN : Nat → Nat
  | 4 => 5
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xdaa29e0ed9246cde51b2e97e404f366434576818
  | 5, 0, 0 => 0x404f3664
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x3333000000000033003300000000030303030000000011111111000000003333000000000000330033000000000030303030000000002222222200000000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x646468544474688468c4
  | 5, 0, 0 => 0x6884
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 16
  | 5 => 16
  | _ => 0
def stateM : Nat → Nat
  | 4 => 0xffff
  | 5 => 0xffff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x7f000000000000038f0000000000000c970000000000000ff80000000000000f800000000000000c7000000000000003680000000000000007
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x3b000000000000018d00000000000004960000000000000a400000000000000fc40000000000000e720000000000000b6900000000000005bf
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 8 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 8 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 8 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 8 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 8 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0x7) :: stateWiresD n (ids >>> 3)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0x7) :: stateWiresS n (ids >>> 3)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 4 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 2 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x1_0_x5_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x1_0_x5_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x1_0_x5_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x1_0_x5_1 goalM u ys) : RunD dom_x1_0_x5_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x1_0_x5_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 5) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool := scr dom_x1_0_x5_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 3 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_x1_0_x5_1 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x1_0_x5_1 roots_x1_0_x5_1 goal_all 6 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x1_0_x5_1 goal_all := by
    have h0 : isConstB dom_x1_0_x5_1 goal_all = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub; have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq; rw [hcov] at hbad; contradiction
end S_x1_0_x5_1
theorem low_x1_0_x5_1 : Lower dom_x1_0_x5_1 roots_x1_0_x5_1 goal_all 6 := S_x1_0_x5_1.noCircuit

theorem low_x1_0 : Lower dom_x1_0 roots_x1_0 goal_all 7 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3333333300000000, 17, 49)] (by decide +kernel) (by decide +kernel) low_x1_0_x5_1

namespace S_x1_1_x3_0_x5_0
def pairsG : List (Nat × Nat) := [(3, 7), (3, 19), (6, 7), (6, 22), (18, 19), (18, 22)]
def r1sG : List Nat := [3, 3, 6, 6, 18, 18]
def r2sG : List Nat := [7, 19, 7, 22, 19, 22]
def mpG : Nat := 0x3f
def pool6G : List Nat := [6610258105095]
def xsM : List Nat := roots_x1_1_x3_0_x5_0.map (· &&& dom_x1_1_x3_0_x5_0)
def goalM : Nat := goal_all &&& dom_x1_1_x3_0_x5_0
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x60d97ac0
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xcc00000000000000c000c00000000000880088
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x243
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 10
  | _ => 0
def stateM : Nat → Nat
  | 3 => 0x3ff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x30000000000000000c0000000000000003
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x3a000000000000002d0000000000000017
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 3 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 3 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 3 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 3 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 3 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0x3) :: stateWiresD n (ids >>> 2)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0x3) :: stateWiresS n (ids >>> 2)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 2 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x1_1_x3_0_x5_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x1_1_x3_0_x5_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x1_1_x3_0_x5_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x1_1_x3_0_x5_0 goalM u ys) : RunD dom_x1_1_x3_0_x5_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x1_1_x3_0_x5_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool := scr dom_x1_1_x3_0_x5_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x1_1_x3_0_x5_0 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x1_1_x3_0_x5_0 roots_x1_1_x3_0_x5_0 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x1_1_x3_0_x5_0 goal_all := by
    have h0 : isConstB dom_x1_1_x3_0_x5_0 goal_all = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub; have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq; rw [hcov] at hbad; contradiction
end S_x1_1_x3_0_x5_0
theorem low_x1_1_x3_0_x5_0 : Lower dom_x1_1_x3_0_x5_0 roots_x1_1_x3_0_x5_0 goal_all 4 := S_x1_1_x3_0_x5_0.noCircuit

theorem low_x1_1_x3_0 : Lower dom_x1_1_x3_0 roots_x1_1_x3_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc00cc00000000, 6, 38)] (by decide +kernel) (by decide +kernel) low_x1_1_x3_0_x5_0

namespace S_x2_0_x4_1
def pairsG : List (Nat × Nat) := [(17, 19), (17, 25), (17, 49), (18, 19), (24, 25), (26, 27), (26, 58), (48, 49), (50, 51), (50, 58), (56, 57), (56, 58)]
def r1sG : List Nat := [17, 17, 17, 18, 24, 26, 26, 48, 50, 50, 56, 56]
def r2sG : List Nat := [19, 25, 49, 19, 25, 27, 58, 49, 51, 58, 57, 58]
def mpG : Nat := 0xfff
def pool6G : List Nat := [28661159440665, 28661260097811, 55049035846449, 55049539164435]
def xsM : List Nat := roots_x2_0_x4_1.map (· &&& dom_x2_0_x4_1)
def goalM : Nat := goal_all &&& dom_x2_0_x4_1
def NN : Nat → Nat
  | 4 => 5
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xe7dbc970bce3f3408893c3164c61689a2d4927ce
  | 5, 0, 0 => 0x4c61689a
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xf0f0000000f0000000f0000030300000303000005050000050500000f0f0000000000000f0000000f0000000c0c00000c0c00000a0a00000a0a0000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x646468c4447468846854
  | 5, 0, 0 => 0x6884
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 16
  | 5 => 16
  | _ => 0
def stateM : Nat → Nat
  | 4 => 0xffff
  | 5 => 0xffff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x7f000000000000038f0000000000000c970000000000000ff80000000000000f800000000000000c7000000000000003680000000000000007
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x3b000000000000018d00000000000004960000000000000a400000000000000fc40000000000000e720000000000000b6900000000000005bf
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 8 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 8 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 8 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 8 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 8 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0x7) :: stateWiresD n (ids >>> 3)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0x7) :: stateWiresS n (ids >>> 3)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 4 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 2 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x2_0_x4_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x2_0_x4_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x2_0_x4_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x2_0_x4_1 goalM u ys) : RunD dom_x2_0_x4_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x2_0_x4_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 5 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 5 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 5) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool := scr dom_x2_0_x4_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 3 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_x2_0_x4_1 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x2_0_x4_1 roots_x2_0_x4_1 goal_all 6 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x2_0_x4_1 goal_all := by
    have h0 : isConstB dom_x2_0_x4_1 goal_all = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub; have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq; rw [hcov] at hbad; contradiction
end S_x2_0_x4_1
theorem low_x2_0_x4_1 : Lower dom_x2_0_x4_1 roots_x2_0_x4_1 goal_all 6 := S_x2_0_x4_1.noCircuit

namespace S_x0_0_x4_1_x5_1
def pairsG : List (Nat × Nat) := [(50, 54), (50, 58), (52, 54), (52, 60), (56, 58), (56, 60)]
def r1sG : List Nat := [50, 50, 52, 52, 56, 56]
def r2sG : List Nat := [54, 58, 54, 60, 58, 60]
def mpG : Nat := 0x3f
def pool6G : List Nat := [57390296480310]
def xsM : List Nat := roots_x0_0_x4_1_x5_1.map (· &&& dom_x0_0_x4_1_x5_1)
def goalM : Nat := goal_all &&& dom_x0_0_x4_1_x5_1
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x7228e998
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x550000000000000050500000000000004444000000000000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x243
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 10
  | _ => 0
def stateM : Nat → Nat
  | 3 => 0x3ff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x30000000000000000c0000000000000003
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x3a000000000000002d0000000000000017
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 3 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 3 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 3 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 3 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 3 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0x3) :: stateWiresD n (ids >>> 2)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0x3) :: stateWiresS n (ids >>> 2)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 2 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x0_0_x4_1_x5_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x0_0_x4_1_x5_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x0_0_x4_1_x5_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x0_0_x4_1_x5_1 goalM u ys) : RunD dom_x0_0_x4_1_x5_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x0_0_x4_1_x5_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool := scr dom_x0_0_x4_1_x5_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x0_0_x4_1_x5_1 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x0_0_x4_1_x5_1 roots_x0_0_x4_1_x5_1 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x0_0_x4_1_x5_1 goal_all := by
    have h0 : isConstB dom_x0_0_x4_1_x5_1 goal_all = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub; have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq; rw [hcov] at hbad; contradiction
end S_x0_0_x4_1_x5_1
theorem low_x0_0_x4_1_x5_1 : Lower dom_x0_0_x4_1_x5_1 roots_x0_0_x4_1_x5_1 goal_all 4 := S_x0_0_x4_1_x5_1.noCircuit

theorem low_x0_0_x4_1 : Lower dom_x0_0_x4_1 roots_x0_0_x4_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555000000000000, 26, 58)] (by decide +kernel) (by decide +kernel) low_x0_0_x4_1_x5_1

namespace S_x1_0_x4_1_x5_0
def pairsG : List (Nat × Nat) := [(17, 21), (17, 25), (20, 21), (20, 28), (24, 25), (24, 28)]
def r1sG : List Nat := [17, 17, 20, 20, 24, 24]
def r2sG : List Nat := [21, 25, 21, 28, 25, 28]
def mpG : Nat := 0x3f
def pool6G : List Nat := [22063651494165]
def xsM : List Nat := roots_x1_0_x4_1_x5_0.map (· &&& dom_x1_0_x4_1_x5_0)
def goalM : Nat := goal_all &&& dom_x1_0_x4_1_x5_0
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xfb501748
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x3300000000000000303000000000000022220000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x243
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 10
  | _ => 0
def stateM : Nat → Nat
  | 3 => 0x3ff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x30000000000000000c0000000000000003
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x3a000000000000002d0000000000000017
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 3 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 3 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 3 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 3 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 3 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0x3) :: stateWiresD n (ids >>> 2)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0x3) :: stateWiresS n (ids >>> 2)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 2 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x1_0_x4_1_x5_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x1_0_x4_1_x5_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x1_0_x4_1_x5_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x1_0_x4_1_x5_0 goalM u ys) : RunD dom_x1_0_x4_1_x5_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x1_0_x4_1_x5_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool := scr dom_x1_0_x4_1_x5_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x1_0_x4_1_x5_0 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x1_0_x4_1_x5_0 roots_x1_0_x4_1_x5_0 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x1_0_x4_1_x5_0 goal_all := by
    have h0 : isConstB dom_x1_0_x4_1_x5_0 goal_all = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub; have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq; rw [hcov] at hbad; contradiction
end S_x1_0_x4_1_x5_0
theorem low_x1_0_x4_1_x5_0 : Lower dom_x1_0_x4_1_x5_0 roots_x1_0_x4_1_x5_0 goal_all 4 := S_x1_0_x4_1_x5_0.noCircuit

theorem low_x4_1_x5_0 : Lower dom_x4_1_x5_0 roots_x4_1_x5_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccc0000, 17, 19)] (by decide +kernel) (by decide +kernel) low_x1_0_x4_1_x5_0

theorem low_x1_0_x4_1 : Lower dom_x1_0_x4_1 roots_x1_0_x4_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3333000000000000, 17, 49)] (by decide +kernel) (by decide +kernel) low_x1_0_x4_1_x5_0

namespace S_x3_0_x4_1_x5_0
def pairsG : List (Nat × Nat) := [(17, 19), (17, 21), (18, 19), (18, 22), (20, 21), (20, 22)]
def r1sG : List Nat := [17, 17, 18, 18, 20, 20]
def r2sG : List Nat := [19, 21, 19, 22, 21, 22]
def mpG : Nat := 0x3f
def pool6G : List Nat := [19864560735507]
def xsM : List Nat := roots_x3_0_x4_1_x5_0.map (· &&& dom_x3_0_x4_1_x5_0)
def goalM : Nat := goal_all &&& dom_x3_0_x4_1_x5_0
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x1a967a91
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xf000000000000000cc00000000000000aa0000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x243
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 10
  | _ => 0
def stateM : Nat → Nat
  | 3 => 0x3ff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x30000000000000000c0000000000000003
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x3a000000000000002d0000000000000017
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 3 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 3 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 3 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 3 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 3 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0x3) :: stateWiresD n (ids >>> 2)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0x3) :: stateWiresS n (ids >>> 2)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 2 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x3_0_x4_1_x5_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x3_0_x4_1_x5_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x3_0_x4_1_x5_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x3_0_x4_1_x5_0 goalM u ys) : RunD dom_x3_0_x4_1_x5_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x3_0_x4_1_x5_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool := scr dom_x3_0_x4_1_x5_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x3_0_x4_1_x5_0 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x3_0_x4_1_x5_0 roots_x3_0_x4_1_x5_0 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x3_0_x4_1_x5_0 goal_all := by
    have h0 : isConstB dom_x3_0_x4_1_x5_0 goal_all = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub; have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq; rw [hcov] at hbad; contradiction
end S_x3_0_x4_1_x5_0
theorem low_x3_0_x4_1_x5_0 : Lower dom_x3_0_x4_1_x5_0 roots_x3_0_x4_1_x5_0 goal_all 4 := S_x3_0_x4_1_x5_0.noCircuit

theorem low_x4_1_x5_1 : Lower dom_x4_1_x5_1 roots_x4_1_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa000000000000, 48, 49)] (by decide +kernel) (by decide +kernel) low_x0_0_x4_1_x5_1

theorem low_x3_0_x4_1 : Lower dom_x3_0_x4_1 roots_x3_0_x4_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff000000000000, 17, 49)] (by decide +kernel) (by decide +kernel) low_x3_0_x4_1_x5_0

namespace S_x4_1
def pairsG : List (Nat × Nat) := [(17, 19), (17, 21), (17, 25), (17, 49), (18, 19), (18, 22), (20, 21), (20, 22), (20, 28), (24, 25), (24, 28), (26, 27), (26, 30), (26, 58), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [17, 17, 17, 17, 18, 18, 20, 20, 20, 24, 24, 26, 26, 26, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [19, 21, 25, 49, 19, 22, 21, 22, 28, 25, 28, 27, 30, 58, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0xffffff
def pool6G : List Nat := [61646105613105, 28661159432985, 57248461166101, 55049035846449, 28661260097811, 57248562420758]
def xsM : List Nat := roots_x4_1.map (· &&& dom_x4_1)
def goalM : Nat := goal_all &&& dom_x4_1
def NN : Nat → Nat
  | 5 => 3
  | 6 => 7
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x9117bc2c712aa9a91066b989
  | 6, 0, 0 => 0xefd062d2cf84214ec8a6a23caf970ecb6dc8fddb3c805a533048116e
  | 7, 0, 0 => 0x6eb47690
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xffff0000ffcc0000ffcc0000ffaa0000ffaa0000eeee0000eeee0000aaaa0000aaaa0000cccc0000cccc000000ff000000ff0000ffff000000000000ff000000ff000000f0f00000f0f0000055550000555500003333000033330000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x432105426155427055
  | 6, 0, 0 => 0x4a3267604327054328676042675503267b549326760432615
  | 7, 0, 0 => 0x432675
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 24
  | 6 => 28
  | 7 => 24
  | _ => 0
def stateM : Nat → Nat
  | 5 => 0xffffff
  | 6 => 0xfffffff
  | 7 => 0xffffff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x3fff0000000000e3be300000000000e03e0f000000000003b83f000000000000000f000000000003b83000000000001fc1ff0000000000ffc0000000000000e03e0000000000001c01c00000000000fffff00000000000fc47cf
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x1ff70000000000fbbfb50000000000f6ff5f00000000006ffaff000000000024ca5f00000000004bb8b100000000000dc0fb0000000000ffe0080000000000f23f0400000000009d15e20000000000db35a00000000000b4474e
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 12 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 12 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 12 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 12 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 12 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0xf) :: stateWiresD n (ids >>> 4)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0xf) :: stateWiresS n (ids >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 4 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 5 => 8
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xef9bbf8ea3bb6eb583ce5c327327a10b704cc23142004b420f88d211047f5ed5
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x28400000000610000000028400000000e10000000008400000000e100000000184000000002100
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 4 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_x2_0_x4_1 roots_x2_0_x4_1 6 s ws hint
  | 1 => checkCutEntry dom_x0_0_x4_1_x5_1 roots_x0_0_x4_1_x5_1 4 s ws hint
  | 2 => checkCutEntry dom_x0_0_x4_1 roots_x0_0_x4_1 5 s ws hint
  | 3 => checkCutEntry dom_x4_1_x5_0 roots_x4_1_x5_0 5 s ws hint
  | 4 => checkCutEntry dom_x1_0_x4_1_x5_0 roots_x1_0_x4_1_x5_0 4 s ws hint
  | 5 => checkCutEntry dom_x1_0_x4_1 roots_x1_0_x4_1 5 s ws hint
  | 6 => checkCutEntry dom_x3_0_x4_1_x5_0 roots_x3_0_x4_1_x5_0 4 s ws hint
  | 7 => checkCutEntry dom_x4_1_x5_1 roots_x4_1_x5_1 5 s ws hint
  | 8 => checkCutEntry dom_x3_0_x4_1 roots_x3_0_x4_1 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x4_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x4_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x4_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x4_1 _ hc
  · contradiction
def p0Subs : List Nat := [0, 2, 5, 3, 7, 8, 1, 4, 6]
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)) ||
  p0Subs.any (fun k => checkCutByIdx s ws k)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x4_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq, Bool.or_eq_true] at h; rcases h with h1 | h0
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2
  · obtain ⟨k, _, hk⟩ := List.any_eq_true.1 h0; exact checkCutByIdx_sound hk
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x4_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x4_1 goalM u ys) : RunD dom_x4_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x4_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 7 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 7 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
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
def RootG (s : Nat) : Bool := scr dom_x4_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_x4_1 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x4_1 roots_x4_1 goal_all 8 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x4_1 goal_all := by
    have h0 : isConstB dom_x4_1 goal_all = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub; have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq; rw [hcov] at hbad; contradiction
end S_x4_1
theorem low_x4_1 : Lower dom_x4_1 roots_x4_1 goal_all 8 := S_x4_1.noCircuit

theorem low_x2_0 : Lower dom_x2_0 roots_x2_0 goal_all 7 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f00000f0f0000, 3, 19)] (by decide +kernel) (by decide +kernel) low_x2_0_x4_1

theorem low_x1_0_x5_0 : Lower dom_x1_0_x5_0 roots_x1_0_x5_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x33330000, 12, 28)] (by decide +kernel) (by decide +kernel) low_x1_0_x4_1_x5_0

theorem low_x3_0_x5_0 : Lower dom_x3_0_x5_0 roots_x3_0_x5_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc00cc, 17, 19)] (by decide +kernel) (by decide +kernel) low_x1_1_x3_0_x5_0

namespace S_x3_0
def pairsG : List (Nat × Nat) := [(1, 5), (3, 7), (3, 19), (4, 5), (6, 7), (6, 22), (6, 38), (17, 19), (17, 21), (17, 49), (18, 19), (18, 22), (20, 21), (20, 22), (33, 37), (33, 49), (34, 38), (35, 39), (35, 51), (36, 37), (36, 38), (48, 49), (50, 51), (50, 54), (52, 53), (52, 54)]
def r1sG : List Nat := [1, 3, 3, 4, 6, 6, 6, 17, 17, 17, 18, 18, 20, 20, 33, 33, 34, 35, 35, 36, 36, 48, 50, 50, 52, 52]
def r2sG : List Nat := [5, 7, 19, 5, 7, 22, 38, 19, 21, 49, 19, 22, 21, 22, 37, 49, 38, 39, 51, 37, 38, 49, 51, 54, 53, 54]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [38508965201190, 55049471464979, 55126007350577, 18718307783429, 55001940890390, 55048698987825, 57325214958886, 57200662876966]
def xsM : List Nat := roots_x3_0.map (· &&& dom_x3_0)
def goalM : Nat := goal_all &&& dom_x3_0
def NN : Nat → Nat
  | 5 => 17
  | 6 => 17
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xfc6186b5f6b07824d44682d9d2764d4da542467ea22b8d0ea0dd3c668f1cbef18f028b4c7e36a1b87b0cbde979ebcb4579d197a06cf22bba68111a2b32d7b03e236d2b7b
  | 6, 0, 0 => 0xfc6186b5fab4a6aef7570b67f150752eede69525a5e2e6eb9661eed3963660d16e21827527b801ee2659db28236d2b7b2352f7d611927a610ed4e76f0893e0840322b61c
  | 7, 0, 0 => 0xa5e2e6eb
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xff00ff00a000a000fa000000fa000000c800c800c800c800fa00fa00fa00fa00a000a000a000a000ff00ff008800880000000000ff00ff000000ff000000ff003300330033003300aa00aa00aa00aa000f000f000f000f00ff00ff0000000000ff000000ff000000f000f000f000f000cc00cc00cc00cc0055005500550055
  | 1 => 0xff00ff00f000f000f0000000f0000000cc000000cc000000c000c000c000c000ff00ff00aa00aa00aa000000aa0000008800880088008800ff00ff00f0000000ff00ff00cc0000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x418820520c4d32bc62099543104ca3098a95238413290262a148331caa4118e85188204ac062099483080aa410408520d815a906201d623104ca4184c55
  | 6, 0, 0 => 0x418820520c41301a8418826620c41b19883104cb601062099483104c5620d82099883104d2600c41325483106a6601061315404104c850106231d483104d3620c57099b04188266
  | 7, 0, 0 => 0x4188265
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 29
  | 6 => 34
  | 7 => 29
  | _ => 0
def stateM : Nat → Nat
  | 5 => 0x1fffffff
  | 6 => 0x3ffffffff
  | 7 => 0x1fffffff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x3ffc0000000000003003380000000000006007600000000031ef3ff00000000000000000000000003ffc0060000000000003fff00000000001fc07f000000000338f389000000000006c3870000000000e7cf870000000003ffc0000000000003e03f8000000000031830780000000000c70c760000000003f93c78
  | 1 => 0x3fff07800000000030030000000000000c00c0000000000000000700000000003ffc387000000000000038000000000000600060000000003fff0000000000003ffcc00
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x3ffd35b0000000003e4bfa40000000002d72cf60000000003ffffff00000000010a511b0000000003ffc6d60000000000003dbf00000000001b405b000000000128d30900000000016ed79f00000000006486840000000003ffc2400000000003e4bfa400000000039b797b0000000002d72cf60000000002912860
  | 1 => 0x3fffb7b00000000038039200000000002c42ca400000000029328720000000003ffd7df000000000164978400000000004604960000000003fffb600000000003ffeee4
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 25 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 25 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 25 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 25 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 25 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0x1f) :: stateWiresD n (ids >>> 5)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0x1f) :: stateWiresS n (ids >>> 5)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 6 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 2 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_x1_1_x3_0 roots_x1_1_x3_0 5 s ws hint
  | 1 => checkCutEntry dom_x3_0_x4_1 roots_x3_0_x4_1 5 s ws hint
  | 2 => checkCutEntry dom_x3_0_x5_0 roots_x3_0_x5_0 5 s ws hint
  | 3 => checkCutEntry dom_x1_1_x3_0_x5_0 roots_x1_1_x3_0_x5_0 4 s ws hint
  | 4 => checkCutEntry dom_x3_0_x4_1_x5_0 roots_x3_0_x4_1_x5_0 4 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x3_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_1_x3_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_1_x3_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x4_1_x5_0 _ hc
  · contradiction
def p0Subs : List Nat := [0, 2, 1, 3, 4]
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)) ||
  p0Subs.any (fun k => checkCutByIdx s ws k)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x3_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq, Bool.or_eq_true] at h; rcases h with h1 | h0
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2
  · obtain ⟨k, _, hk⟩ := List.any_eq_true.1 h0; exact checkCutByIdx_sound hk
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x3_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x3_0 goalM u ys) : RunD dom_x3_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x3_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 17 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 17 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 17 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 17 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
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
def RootG (s : Nat) : Bool := scr dom_x3_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_x3_0 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x3_0 roots_x3_0 goal_all 8 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x3_0 goal_all := by
    have h0 : isConstB dom_x3_0 goal_all = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub; have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq; rw [hcov] at hbad; contradiction
end S_x3_0
theorem low_x3_0 : Lower dom_x3_0 roots_x3_0 goal_all 8 := S_x3_0.noCircuit

theorem low_x1_1_x5_0 : Lower dom_x1_1_x5_0 roots_x1_1_x5_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc00cc00, 3, 11)] (by decide +kernel) (by decide +kernel) low_x1_1_x3_0_x5_0

namespace S_x5_0
def pairsG : List (Nat × Nat) := [(1, 5), (1, 9), (3, 7), (3, 11), (3, 19), (4, 5), (6, 7), (6, 22), (8, 9), (10, 11), (12, 13), (12, 28), (14, 15), (14, 30), (17, 19), (17, 21), (17, 25), (18, 19), (18, 22), (20, 21), (20, 22), (20, 28), (24, 25), (24, 28), (26, 27), (26, 30)]
def r1sG : List Nat := [1, 1, 3, 3, 3, 4, 6, 6, 8, 10, 12, 12, 14, 14, 17, 17, 17, 18, 18, 20, 20, 20, 24, 24, 26, 26]
def r2sG : List Nat := [5, 9, 7, 11, 19, 5, 7, 22, 9, 11, 13, 28, 15, 30, 19, 21, 25, 19, 22, 21, 22, 28, 25, 28, 27, 30]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [15406485342469, 15406385071369, 28600423549203, 22063684653829]
def xsM : List Nat := roots_x5_0.map (· &&& dom_x5_0)
def goalM : Nat := goal_all &&& dom_x5_0
def NN : Nat → Nat
  | 5 => 2
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x599be9b214e17f6b
  | 6, 0, 0 => 0x1f16380d
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xaaaaaaaa000000000f0f0f0f00000000ffff000000000000ff00ff0000000000f0f0f0f000000000cccccccc0000000055555555
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x233aac6885
  | 6, 0, 0 => 0x468e5
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 19
  | 6 => 19
  | _ => 0
def stateM : Nat → Nat
  | 5 => 0x7ffff
  | 6 => 0x7ffff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x1c01f0000000003c7c31f0000000003ffc0000000000003c03f000000000000383ce000000000030632dc0000000003fe3fe0
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x14bd77f000000000143431a0000000003ffe8900000000003e13f0a0000000002bcbce500000000031672dc0000000002b42880
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 7 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 7 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 7 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 7 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 7 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0x7) :: stateWiresD n (ids >>> 3)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0x7) :: stateWiresS n (ids >>> 3)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 2 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_x1_0_x5_0 roots_x1_0_x5_0 5 s ws hint
  | 1 => checkCutEntry dom_x1_1_x5_0 roots_x1_1_x5_0 5 s ws hint
  | 2 => checkCutEntry dom_x3_0_x5_0 roots_x3_0_x5_0 5 s ws hint
  | 3 => checkCutEntry dom_x4_1_x5_0 roots_x4_1_x5_0 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x5_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1_x5_0 _ hc
  · contradiction
def p0Subs : List Nat := [0, 1, 2, 3]
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)) ||
  p0Subs.any (fun k => checkCutByIdx s ws k)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x5_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq, Bool.or_eq_true] at h; rcases h with h1 | h0
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2
  · obtain ⟨k, _, hk⟩ := List.any_eq_true.1 h0; exact checkCutByIdx_sound hk
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x5_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x5_0 goalM u ys) : RunD dom_x5_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x5_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
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
def RootG (s : Nat) : Bool := scr dom_x5_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_x5_0 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x5_0 roots_x5_0 goal_all 7 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x5_0 goal_all := by
    have h0 : isConstB dom_x5_0 goal_all = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub; have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq; rw [hcov] at hbad; contradiction
end S_x5_0
theorem low_x5_0 : Lower dom_x5_0 roots_x5_0 goal_all 7 := S_x5_0.noCircuit

theorem low_x0_0_x5_1 : Lower dom_x0_0_x5_1 roots_x0_0_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555000000000000, 44, 60)] (by decide +kernel) (by decide +kernel) low_x0_0_x4_1_x5_1

theorem low_x5_1 : Lower dom_x5_1 roots_x5_1 goal_all 7 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccccccc00000000, 36, 38)] (by decide +kernel) (by decide +kernel) low_x1_0_x5_1

theorem low_x1_1 : Lower dom_x1_1 roots_x1_1 goal_all 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc00cc00cc00cc00, 3, 11)] (by decide +kernel) (by decide +kernel) low_x1_1_x3_0

theorem low_x0_0 : Lower dom_x0_0 roots_x0_0 goal_all 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555000055550000, 6, 22)] (by decide +kernel) (by decide +kernel) low_x0_0_x4_1

namespace S_63
def pairsG : List (Nat × Nat) := [(1, 5), (1, 9), (3, 7), (3, 11), (3, 19), (4, 5), (6, 7), (6, 22), (6, 38), (8, 9), (10, 11), (10, 42), (12, 13), (12, 28), (14, 15), (14, 30), (14, 46), (17, 19), (17, 21), (17, 25), (17, 49), (18, 19), (18, 22), (20, 21), (20, 22), (20, 28), (24, 25), (24, 28), (26, 27), (26, 30), (26, 58), (33, 37), (33, 41), (33, 49), (34, 38), (34, 42), (35, 39), (35, 43), (35, 51), (36, 37), (36, 38), (40, 41), (40, 42), (44, 45), (44, 46), (44, 60), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 1, 3, 3, 3, 4, 6, 6, 6, 8, 10, 10, 12, 12, 14, 14, 14, 17, 17, 17, 17, 18, 18, 20, 20, 20, 24, 24, 26, 26, 26, 33, 33, 33, 34, 34, 35, 35, 35, 36, 36, 40, 40, 44, 44, 44, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [5, 9, 7, 11, 19, 5, 7, 22, 38, 9, 11, 42, 13, 28, 15, 30, 46, 19, 21, 25, 49, 19, 22, 21, 22, 28, 25, 28, 27, 30, 58, 37, 41, 49, 38, 42, 39, 43, 51, 37, 38, 41, 42, 45, 46, 60, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0xffffffffffffff
def pool6G : List Nat := [57235474881558, 38543324940586, 18752264866053, 48529677095689, 57247856461105, 57235322636572, 48529121936678, 55049034797873, 38595316155667, 48529709733418, 38543324939558, 57389639468310, 57325164823857, 28661190624531, 18752701465865, 28648022287894, 38556662373395, 57248460444421, 48438929593126, 38543878132489, 38543474168581, 38594812445971, 57248057133317, 57286559597852, 57287216077846, 28661192398355, 18752669297161, 55036299379990]
def xsM : List Nat := roots_63.map (· &&& dom_63)
def goalM : Nat := goal_all &&& dom_63
def NN : Nat → Nat
  | 5 => 12
  | 6 => 243
  | 7 => 856
  | 8 => 358
  | 9 => 31
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xfadf2db3f5349309ebbc17cbe66532dde1656550de61ae49c3706beda798be0675574408630251121ede97f31b464dd3
  | 6, 0, 0 => 0x3d6089e83b565e153ad916173aaaf6cd39433a0538d4220938c294a837f9b7c136499911362447b5357076da356bb79a34f6604933d88edc3347b36532fc7e7c31fd177f31c5695e30b3da172ef458bf2e8b01f82dfc2c7f2d7eac952bedc5d129e8541f263f8ca3255d61c424cd0bc3237b1fe72315db42223769d3220a3b1221a84b1b201efaa41de864821cf8dd4c1cd9c0c21b969b1a1ae4d3311aace10f1933962016e6d166153d1f10105a1a7f0f7752f40efd143c0dbec9420d891f440d61dec90ca3b5de0c75a06b0b925cf40aca5035090fc5e10872a45507d1280907cbaed3073c0d4905fcea2e05f8641705e8bf9201d122d0004f2ece001b1c23
  | 6, 0, 1 => 0x79c55aac782f5f2277e14e1977a096e0759c9ab27474f9a274297a2b737c144a731e434272ae5bbd71e3266f703f5e6d6ff0f0146ea6c4f46e05fc7f6c8c203a6888bd1f68333a56682bbc9866bc797d66ad06a56679c769656b5a93656951e75fb68be25f3c4d2a5cb4d9595c86ba0f5b7d72645aeec79159df37c558c3b61b5881a3d7584e97405806b1d2574f87ec5738c89656c84aaa563c4d6355e3a3fc55c4d39e54b154c5545d52c453508384528f9d59519fd314508cbf0e4ffc86634fbcce014b68829549652280493bf4dc4926b51048d8f3fd48d7a10748893a7a48222d0d464ff956447e59e442ad9c6542634ab1418260783f83d3803f17325f
  | 6, 0, 2 => 0xc0d41187c0ced793c021bcacbd3387afbb698a2bba04a7adb8d08cf3b839177ab7ac8ca9b5ba88abb5810b20b434601db3de26c4b3d0ece6af6484b2aebd64ebac9ab39ca919135da835cc5ca6b9e057a5200459a33975a3a29cf83ba0a99746a03bbf519f91c9d09d5f2b019d13f6189b35c5219972b11f98c0f21497a7848896053d6d9562efe794b018d39393e0598f8bdc5a8f4b88a18dfc1c578ce1a1a98cac943f8b766b3b8b2beac58abef05a8a3672408a34f76c8952c9e8882f52c4875d8dfa8755af51858dec3084a3fbae833bb76a8324d2d5831e706f823172d882079cb0802964717fefa5537fda4eaa7cb131b67c7d84847c2cfebf7b3832d6
  | 6, 0, 3 => 0xfeae66dcfe65f37afe1444fcfc248e7bf72087f1f6f91945f6b5bc52f524d58ef2aa9b9bf29d61bdf1750596f1069169ef488453ee947181ed2150faeb1a9f27eaa71707ea99dd29e986d3dae87825bde69f9199e1fd7feee1ad083ee1a0a153de3b5545dd82b20ada14dabcd9cd73c7d94512aad8ae62b1d836fecbd7b11757d5acb028d42f64bed1de03e0d1b7e16cd02ede41cf994254cf80c983cf2ace27cebcaa6dcda92b94caf4d69fc9fe5dacc7adf1c2c7a52644c6ecb9a1c6a6f670c66d49fec231b1bac0dfc246
  | 7, 0, 0 => 0x1255565b1229b7271227f09d11f4b1611182c6e9115b2e17113c00b610e737ec109959ad108dfb0010873aff107eac710fe3bfab0f6a88660f4801f60f4449ac0ed4fd100e5684bd0de050250db766cd0d2f75e70cbb9b490c7772010c4d96010c3025590c1de1fe0c1b94cd0bb355150b24a2690a3a77c00a28d6d909bad19109a8b188097f42550979a5d3095806c9093090f108e3b35808c04d1d0895d519082a1dbb07b7fb560750f5920749dc20071e8afe06dc1cba06d1977a0694c2350620bd3c05b8ad5a050cdc2203c61cd003a7a7ad034547c702ef67e502d338cd02c4fbd3028e48480229321f01ace7900183aeef00bd628100aa571900a8eff1
  | 7, 0, 1 => 0x24e82e8e24946f0f23efb98523e4b78223baaf5423aa133923450ca42284b333223769d321f40ce021ea349621cdfa682195a69b216cd56f216845b42112506520e11eae20dc7ec92070a08e2014b8841ff0e4ee1f46511d1f3e23d61ee037e11e99e7201e73f7591e4ab73e1d201f441d0839f91cb356241c3444581c014a391bb8628c1bb028501ba9074c1b8f4bc21b13bb7c1a57e9971929eff61915a6ab18d23d5e18ac6e2518917f9417ec8ed517bc20f017b10efc17aaac961747ce40174309b4173ca74e16ed244d159e41e5157f2c9b152b3c71151f94c71515e261149a4ea1140ddc3213fda563138bc72e1332ca01131fe96f1288b046126f0f31
  | 7, 0, 2 => 0x3a75cc8338c12eb93899b8e13865c14c382d8f7737f2c06537c82cde36fc90e836727dff35d968a5358231293535d36d34c7ce25344e166f342fd35d33df7b7b33b2c29e33b0f4e3338b145732c2068732be679b31bdaf9d3107d3ae30dd2abe308b8d4b304cf6a4303247ff302f8f992fd90f922f244e602ee6a1a12ee11b4d2ed106232e2cb24b2d7eac952d4d2e3b2d0065ab2cfd4cb22cdf28f32cbfb75d2c13df762b33ca0b2ad101ba2aafe6892aa75ad22a71985b2a20277c29e09a2c29cef945290c466229095e4728b7dffc2807443f27c003a926b7a5be25d1e1fb25836aef2579079a256a2da72565128125613c15255eaa502525ce5d24f1d90e
  | 7, 0, 3 => 0x4ce69ba94c74d9df4c38c8d04c24813e4bcac3884bc432324b766c804b6d7f204b685d854b0721694a07ce47499f41ff4926b51048b7e81148b14f3c4861424c483a13a9483280b84804f0f947ef23c547a969a6473a6d9246f5e808469151e1464f4da14646e00c46373f9e461fe42345eb319d45e428f445c9387e459ded534561370c44b0b53e43f8662a43d0d33c42f9159c42e485104266f78e424c63d0423f8f0e42084761419fa155413bc90740ffb32940587af6404296163fd9664c3e9bf4f73e6edb873e209aba3e098a5f3da55a963ce410fd3cdef75a3cc98e253cc208833c5fea2a3c54033b3c43a1fe3c3c2a323bd23dc43bd1ee373bbb8b30
  | 7, 0, 4 => 0x623567bb6205d88361c76273617b54216178d6cc60dd8b76609fe7025fdec53c5fa624535f83829a5f20052e5f16df6a5e1f89135d97f1e35d5e8ac95d03b9ec5c4850ef5bf22aa55b791fcb5b3983f85aca5d735ab8a9c85a9cf1fb5a757c235a1d1ad159d8d2e559a1e079598f6cca5922ec465916f36a58c2ef5958bcfd2358acce97578a7e975710d06856f73cc156d3c25556590b955618a06b557784d6555672e15522f61055073dee54b21510548e179a5431b23f53ed427d534c3a7b52fe54375271f78f52368d0150fece0850fcb6f250a374335047ce895008758d4f87c10a4f5a6fd74eabf50f4e8393474e10be834defa2b84da171e74d8edfa4
  | 7, 0, 5 => 0x72d87a3472ab5f4f727f3775725ce89b718e49e471686d2e71045df270f3945670e0f81a70ac39d170a7275b7098f8c1704b1802703978876ff10c326fef05cc6f658ee36f2eb18f6f21cbf56ef35a186ed3404e6e7696f56dc766ec6dc5812b6d1b550a6d043ea96ca5bfe46c76c0d66b9ca6a46a5e2e496a55e1356a38ec4f69cae707697c5b606977216c69658b7468bee2ec689eda766814c4b167fcab5667d44f0c6722ad0066f87fdc667312616624a083661766a565df9c0165dd7ad3655c4e5a64ef0a7e64ce772864a6aa8e64818a9364809651644d15206412729763a5592a635f225d634e7c64632d205c62bc2e5c628c736e6287a97662415fa3
  | 7, 0, 6 => 0x85839d3f8574e5528515b8cd84582d5584252ff584135e95840206a983f73f8a83e19bc583a7f6e483324e8f8320ada88311930b82b2a8608277192482641cb98209a61281975c238103242c80c510098080ab1d806943d18050a21c7fefa5537fe457a97f64161b7f18940b7ec9c7b37eb814087e9642097e2fc5837e151cff7dcdede77d908acf7d6e825a7d4a419d7ca027e27c9f7e7c7c91203a7c7e1f537c3f68397ba3efb57b28e4477b11ecbf7b103aa87b07922d7a9eb29b7a8d2c777976ef16790df74a78ed702f786b20207862d689782718a177cfa30e76e301307669dadc758c243d74fb6bb7747a456a739605b4736f7e657348088d732cb951
  | 7, 0, 7 => 0x9a06f6719996391b99232e86986710679858d15b984429e79811ba8397e3684197956ff4974a5a399724c77e96d72ef996ac7d519677bd2a964c72dd95ef59af95dd264195cdd5a695c3b1989553881e9530276095225003951eb3b894e87956939c8143936a0d2693384e8a9274a528917a56a590eb9e8f9081cf04901c386b900d98039004c28d8f0950aa8ef9880b8e26e5f78e1d627c8dd424298d9ceb668d9225708d7869e68c127d8a8c0b847c8bfbe3e68be3e6828b793b1c8b66e6008b3227778b277e8b8b0ab19f8af4dc708aa2abe88a88182a8a7a9db88a555217887b0991882c96a287f329e786de1e4486bb989c865a602686453eb986412037
  | 7, 0, 8 => 0xabea86aeab4606c5ab33e817aaf7e2b6aa98f8b4aa0f9412a9744f92a9688716a944cd73a8fc3611a8d0e661a8ca0453a8a83ea4a8579795a84a90f6a84315e6a82101fba7c8dcf2a76b4f4da7070867a6768364a6375980a5fc6fe3a5eabc38a5d302cca53f8738a42ac53aa398ac2ea3731f65a317fe4ba2dee76ea2abd7d4a214873fa2066a62a1c22db6a1b6164aa101dc92a0daeb40a0ba2447a093d74aa072054b9f67cab99f1dec7a9ed42a8b9e7b41be9e68ddc59e4ff7719d8e14769d3f16bb9d2176fd9cd5fbe69cd157399c6d66999c69df519c26f80f9c0945a09bd7494f9b751e6d9b6f9ad19b52b2589ab180269a8d7d6a9a78a26b9a470735
  | 7, 0, 9 => 0xbf6dea7dbf52f044be4929dbbe31cb13be302c54be04ba19bd63b217bd569d44bd012136bcb5f9c4bc5ae0bebc4e049dbc29ef1dbbdea910bb9554cdbb6bf353bb49c479bac6ac71ba2fc850ba22d3edba084ee9b9fb3ed2b9e99debb9cd3fe6b9ca7d3ab97b98a3b9238bb6b8afb66ab86683b3b8610c11b7c51bbdb737b8cab72f4b60b6b24b4fb6967739b62871f1b60a28a2b5e1844eb57ac8adb574c2ceb4d870c0b4826f84b403b48eb3686ebfb274a0a9b21cccbcb2069b61b1b80fbab1918fb0b177d426b0f7f7a1b0e9a2f8b085131bb03a9b5baf78aea8af6a54ceaf2498e4ae7a07f8adee40ccadcd7a96adbb0c5bad9e7681acbd3eedac3c9990
  | 7, 0, 10 => 0xd2b65212d2a6e32cd243bfa0d21ac315d1cce4d6d1c6eaa5d1bac628d1ba769bd1566dadd10ff778d0f46623d02ede41d01d5aded008a737d000bef7cef74cf6ceb75128ce9bbdfbce5b4dcccdef810bcd813366cd4ee83fcce6e03ecc5e9a47cc3dbb03cbaa415bcb7a0fdfcaca8817cabe2c2bc9fb379ac9f8ee7ac99fcd9ec9901028c8f8b2c0c8e2cba9c89d7b8fc88c5676c87d6749c85246a6c77e063ac76c6475c7049024c6d60225c631c44cc609a241c5c197f6c53b428bc4cf2a05c4c8c1fac4bff0edc4bc0901c45b15b3c44c184fc406c3f6c3f04a81c35bf766c3583e79c2d474bfc2742114c22fd643c1fec366c1a1f633c1438dfbc0222c96
  | 7, 0, 11 => 0xe6b6f618e6334511e5e1b3ece56e18dee54e6e14e542f83be5419b8be53126b1e50845f1e3b83e5ce341463fe305e741e2f73a11e2dcb27ae244b55ee1d5d790e1560784e150e5e9e0e0bbd7e0d17bb7e04d6edde01f1c9be00de424e00dbdb6df99d6a4df140ce9ded551a2deb0d72fde91cd35de8ede08de2d6931ddea6151dd44ebefdd22f5f6dcc2d6ebdc79da45dc56f92cdc0b8b92dba90328dba5c180dba270bddb6fd9b3dad14fd0da9b71c7da5c102cd9e0ee8ed9b59298d959f241d8f816a5d8c624d8d8b63777d89c90c3d7a0e62ad719f753d6d828a2d6b7954cd6683848d5b41e40d5484081d5443201d4847d5bd3f88ffed39eec29d388e184
  | 7, 0, 12 => 0xf94b341ff947aac1f82e5cddf781aefbf7712f20f739e369f72ec109f6e37eaff6b5bc52f670f085f660409df629f526f5e05daef57ec026f574dc78f52b5c6af48e01d5f48a3216f4857ffdf4081177f3ee0630f3a8a818f3733036f311585ef241b39af17526c4f1411580f0d31038f0857a5ff0799319f05e0487f04df3e5efa703a7ef335fc1ef0cfe70eede5f57ee36c9a5ee33f0d4ee28865dee04b134ee0296c1edd76c01ecf958ccecf44026ece05157eccb1c68ecb91f5fec99ef6dec4ffe10ec1e12d4ebaed3bfeba52384eb1a9bc8ead47602e9eb6b25e9d791d3e9d0ea74e93d90ece8e13f4fe8cf8ba4e86cf0ede85a7ff3e71705cde6e489db
  | 7, 0, 13 => 0xffbcfeaeffb3ea6bff86098aff844943ff837588fdaefc54fcd69e68fc02cecffbec75b6fba0aebcfb84f944fb6d2ecffb48b5a4fadab05cfad792e2facfb439fabf1a11fab6ff8cfa33b007fa2bdd19f9f779d9f9b38880f9a363a4f9611aa0
  | 8, 0, 0 => 0x27928aca2572009524f1d90e248349f222f2b39022b3913a21f40ce021a9023c216845b420bd10b4204508b51f505e561f28e87e1eb180c41c7f660e1c1160c61b9b06e31b96e8611ae554351a51558f19b15e68196926bf194d07b418ed5c0818b98c20180356601703b38d16ed244d169f5cd91658ec56161ad833155b070714f312d4147be17a1439cce4141f8fdd140ddc3213ec0a33128177ed11f546a611c9fc59111d5c6110af5719108cbea2106602d20f1c517e0eccb7400d2c2e290cf6d6570bedd9ed0b8bbf6b0b5d6d290a5133e109703723093db6800907828d0801277907a389060790ca2a0769545206e4120e0544cdf6025a06d300f26ece
  | 8, 0, 1 => 0x5514da2a53d9433552c6dafb5164663950c1bb7d50ba5f8b509f8ca3509cfade4f85907a4f2308104f1c75a54d2885244cd3f7294c8d80f44c50a0f349d837ae48be36e9477294e646e757da46cd9c50455fb1d0449d41de43ee7c4343cfd02243cb0728434d74413fd89f2f3fd242ec3f643da43f521ef63eca17bc3eb72f933e51fe3b3dad5fbf3ce83b323cc117773c5cd0913bcc4b8e3a1aa6c2386dc67537a1d1e4376a4f69375c328c36209e153578c84e3567276734f9221f34bd92e334bca48e31c32ec3315f0dca30797d6f30452eee2f1583e82ee5f83b2d6782ad2d2b64b72ceb381e2c9d909e2ac299d12aa950482a339e2928f2496d27a4a978
  | 8, 0, 2 => 0x84013fe7836a9b7e82fc9636824f20f681127705801c3ae37f2d59fd7db0481d7c3a52057ac3e1087a98c065770282c076abcfae76a6ae13764d3db575a337077596bf2d749a204b745985b3742c1b0372f58c2c7278be2071cfa26f70e422b06f36b6b86d42739e6cd46e566bd02c766b3d020a6af4746f6a866f276a20792e69da45856952e2d968f8c50e684ad96a679e3ab86722ad0067108e5267103ec5664b1a33664a2e4d64bb1a68644d152063ff7f4763d8096f620d6f8d61b0ce8d619f6a4560c081b76013f4555e4e7aea5c6c86d75bf8a09c5b8b47325b8a9b545b1760205a910ab55a24f22f5a0f56b1595bb8d458bcfd2356713ef9555e780a
  | 8, 0, 3 => 0xa9536d8da92e1f67a906a98fa8fc3611a888922ba7de7870a77db8c7a64e8b36a5ef21d7a5dd0329a57263d1a3ac4ce7a38fee89a07a6a93a039bc459f574e1a9eadcef39e86591b9deb9d439dc6e8679ca6bdbc9c31e4e49bea8a5f9b0e75849a8d182a9a31aaa698fd6fd798e639c897e4107297de4ccf964fc4fc95feb81b94dbd1b49353153f911bcb6190761323902d5b0c900cc7b68f8b65ae8f0950aa8e9d72eb8dbf9f568d8425078d4f66ca8c8fab938c5ba5cf8c0b847c8b3625d88b1d15ca8ae474e18ac1d328895dd9a18911bc2488c8f86088a3b6dc87abe572877f470c85db428985cf5b4385b3ccb185a3bc0f84fccbd184613cd484135e95
  | 8, 0, 4 => 0xe2760958e1f09bdde0b0bd65e042b81dddb2f137dd44ebefdcf66048dab6ff36da70651bda067d68da025fd3d7fb8f7bd6363344d43a869fd35f5289d358ca24d277431ed175aa0ed111535ad0ab1f49ce16f6e3cdef810bcd52d7cdcb884e68cb694c08cb41d630cad7f953c98e47ffc88323f1c7abb727c74aa3c2c6dc9e7ac58557c3c5742e9cc5164b1ec3827a75c2d474bfc2157f87c18ac36bc169a7a0c11b76cfc060a091c026c9e4bf75efa6be769f18be620e8cbe2c3e52bd541193bbc01f92bab4727aba47a138b9653685b8db3bf4b806c79fb749d50ab6c414e4b5e0fc76b5c668b8b1838f47af359018af1d0a4eae6ff2a8aba7945faa6baa8b
  | 8, 0, 5 => 0xffb3f673febb539efe96364ffdf4a2a0fc4e4806fb8cf931fb6d2ecffab21684fa359d84f92dd199f77c0b91f75ba0adf4c886ecf42e45c1f3caa704f147f2cfef2e9b0fee18b783ee12c54dece124ddece046c1eb8687baeb7d2b56eb6b0ca8eaac3b0bea5d0618ea36d74ae9e3dfc4e9877a69e9430aa7e8a202a5e7f44a52e78c552be76e1fb8e6527f1ce604fcffe5f93c5de4ee680b
  | 9, 0, 0 => 0xfe971ab2f9554771f92dd199f61649e1ee12c54deab44034e5f2c308d43a869fc43bc065ba47a138b749d50ab40748eeb03b1c5fa0e187959437159c8ff96af68f8b65ae77cbd18269904ec962a89ff75d017f514e31041e46d9577144efaef6448b58423e51fe3b3d084ce73ba45360358f846f196926bf19570811
  | 10, 0, 0 => 0x69904ec9
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xcccccccccccccccc00ff00ff00ff00ffa5a5a5a5a5a5a5a53333333333333333ffffffff88888888fafa0000fafa0000eeeeeeeeeeeeeeeef0f0f0f0f0f0f0f00000ffff0000ffff99999999999999990f0f0f0f0f0f0f0fffffffff00000000ffff0000ffff0000ff00ff00ff00ff00c3c3c3c3c3c3c3c35555555555555555
  | 1 => 0x5555555500000000f5f5f5f5f5f5f5f55050505050505050dddddddddddddddd44444444444444440505ffff0505ffffaaaaaaaaaaaaaaaaffaaff00ffaaff00fff0fff0fff0fff0ffaa0000ffaa0000fafaaaaafafaaaaaffffffffcccccccceeeeeeeeaaaaaaaaffffffffaaaaaaaaeeeeeeeecccccccc00000000ffffffff
  | 2 => 0x1313131313131313fffa0000fffa0000ffee0000ffee0000fefe0000fefe0000cccc0000cccc0000ffccffccffccffcceeeeeeee00000000fffffffff0f0f0f0f0f0f0f000000000fffffffff0f00000cccccccc00000000003f003f003f003ffcfcfcfcfcfcfcfcc0c0c0c0c0c0c0c00303030303030303ffffffff55555555
  | 3 => 0xa8a8a8a8a8a8a8a8a0a0a0a0a0a0a0a0eeeeeeee88888888ffaaffaaffaaffaafafafafafafafafaf8f88888f8f88888ffe0ffe0ffe0ffe0888888888888888811111111111111111111111133333333fafaf0f0fafaf0f0f0f00000f0f00000ffffffffa0a0a0a0005f005f005f005fffa0ffa0ffa0ffa0ecececececececec
  | 4 => 0xaaaaaaaa00000000fffafffa00000000ccc8ccc8ccc8ccc8fefefefe00000000fefefefefefefefec8c8c8c8c8c8c8c80505050505050505fefeeeeef0f00000eeee0000eeee0000fefef0f0fefef0f00011ffff0011ffff0f0e0f0e0f0e0f0e0101ffff0101ffffaaaaaaaa88888888eee0eee0eee0eee0aa88aa88aa88aa88
  | 5 => 0xfffffffffafa0000fafa000000000000ccccccccc8c80000ffffffffc8c80000ffc8ff00ffc8ff00f8f8f0f0f8f8f0f0fefecccc00000000fefeccccfefeccccc8c80000c8c800000005ffff0005ffff000f000f000f000ffefe0000fafa0000fcfcf0f0fcfcf0f0eeeeaaaaeeeeaaaafac8fac8fac8fac8aaa0aaa0aaa0aaa0
  | 6 => 0xfff00000fff00000fcfc0000fcfc00005555ffff5555fffffffaf0f0fffaf0f0fff0ff00fff0ff00f0a0f0a0f0a0f0a00055005500550055ffccff00ffccff00f0e0f0e0f0e0f0e0cc88cc88cc88cc88ffea0000ffea0000fca8fca8fca8fca8ffecffecffecffeccc80cc80cc80cc80ccccccccc8c8c8c8fafaf0f0f0f0f0f0
  | 7 => 0xeeeceeeceeeceeeceeeeeeeeeecceeccffff0000cccc00001111111155555555fafa0000f8f80000ffc0ffc0ffc0ffc0ffeaffeaffeaffeaaa80aa80aa80aa800505555505055555fffaaaaafffaaaaaffeeaaaaffeeaaaafefeaaaafefeaaaaaaaa0000aaaa0000ffcc0000ffcc0000fffafff0fffafff005050f0f05050f0f
  | 8 => 0xffccffccff00ff00fcfcfcfcf0f0f0f000330033003300335544554455445544fffcfffcfffcfffc5454545454545454ffff000000000000333300003333000030303030303030305555000055550000ff55ff55ff55ff55ff50ff50ff50ff50dcdcdcdcdcdcdcdcff44ff44ff44ff44f4f4f4f4f4f4f4f4eeeeeeeeecececec
  | 9 => 0xeaeaeaeaeaeaeaea2222222222222222ffaaffaaff00ff00fafafafaf0f0f0f0eeeecccceeeeccccfffafffafffafffaff88ff88ff88ff88f8f8f8f8f8f8f8f8ffeeffeeffeeffeefff0fff0ff00ff00fcfcfcfcccccccccfcfcccccfcfccccc5550555055505550ffffffffff00ff000f0f0f0f000000000c0c0c0c0c0c0c0c
  | 10 => 0xaaaaaaaaa0a0a0a0fefefefefafafafafefefafafefefafafafafafa00000000ff880000ff8800000077007700770077f8f80000f8f80000fff8fff8fff8fff807070707070707070e0e0e0e0e0e0e0effeeff00ffeeff001111ffff1111fffff1f1f1f1f1f1f1f1e0e0e0e0e0e0e0e0fafafafaaaaaaaaa0a0a0a0a0a0a0a0a
  | 11 => 0xfffafffaffaaffaaffaaffaaf0a0f0a0fffaffaafffaffaa0f0a0f0a0f0a0f0affeeffeeffaaffaaffeeffaaffeeffaaffeeffee00000000ececececa0a0a0a0ffa0ffa000000000ffff0000fafa0000fffffffffafafafafffaff00fffaff0000050005000500050505000005050000ffff0505ffff0505ff05ff05ff05ff05
  | 12 => 0xf2f2f2f2f2f2f2f2fafaaaaaf0f00000fafa0000f0f00000fffafffafff0fff0050505050f0f0f0ffff0fff0aaa0aaa0ffff0000aaaa00000f0f0f0f0a0a0a0aeeeeccccaaaa0000005500ff005500ffeeeecccc00000000ffffffffffaaffaaffaaffaa000000000055ffff0055ffff0055000000550000f0f5f0f5f0f5f0f5
  | 13 => 0xfffcf0f0fffcf0f0f0f3f0f3f0f3f0f3aabbaabbaabbaabbf0c0f0c0f0c0f0c0ccc0ccc0ccc0ccc00f0c0f0c0f0c0f0cfaf8faf8faf8faf81515151515151515fffcff00fffcff000303ffff0303fffffffc0000fffc0000ababababababababffa8ffa8ffa8ffa8fffff0f0f0f0f0f0ffffaaaaaaaaaaaababababababababa
  | 14 => 0xaeaeaeaeaeaeaeaeff0aff0aff0aff0acecececececececefcfcccccf0f00000fcfc0000f0f00000fffcfffcfff0fff0030303030f0f0f0feeee0000aaaa00000f0f0f0f0c0c0c0cffaaffaaff88ff88fafafafaf8f8f8f8003300ff003300fffffcfff0fffcfff003030f0f03030f0f11115555111155550033ffff0033ffff
  | 15 => 0xf00ff000f00fffffffffffff0fff0fff0fff000000000000fffff000fffff000f0000000f0000aaafaaafaaafaaafffffffffaaa0aaa0ffffff00ff00ff00ffffccccccccccccffff0000ff000000aaaaaaaaaa00aa000f0f0f0f0f000f00ff0fff0fff00ff00cfcfcfcfccccccccafafafafaaaaaaaaff0cff0cff0cff0c
  | 16 => 0xfafafafafaf0faf00505050555555555ffff0000f0f00000ffaaffaaffa0ffa0
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x2008100603a850040a0404d408020503c1aa040183c1a0e50200c040100280c040f06841408170b0541ea04018081a0c50205c301507a82c040a0402540803010180aa120102810115
  | 6, 0, 0 => 0x100623110001cc0002008580f0c815800040102810000630000803011a89a1960001004530503c32c000205c5a08078658000401808123f02b00050031383c000e6000105c020406418c000580c04090c81580004010201e733bb000240301020323660000c100f0c8c820c0004064180e03841800022c828100f0cb0000629078640a0e600010043407864e0c00000100602008654000a0403c320e0830000817010541e73600010623b0503c32c00020086a34078018000401808100017b000086b0b0201e1960001006020c8d80ac000200c040f069258000401824700507300008020403c3256600010040a0404c1ec002700814080786580004018c41e1924b00008030103c32446
  | 6, 0, 1 => 0x100400060140ec000200cc6083106580004010281e0002b00008030107036056000980608078001cc00018081029000318000b01820121907300008023d8201e1960001006021d9347cc00020b8040f0c81580004378086a0f0cb00028031e00810136000100602078641ac000200c04220008580004168081e1902b0000619060141c10600010ec020403ce6c0001020520f0001d8000401808220002b00008021d83c7c1a60001006021d94018c000200c2e3c0a83d800030103c00050830001e19028380e10600010ca020403c32c000180812291c01580017010281e190830000803011f8320560001006023208832c00018087629078f980004010201e190d30002802050204a196
  | 6, 0, 2 => 0x100602400640ac000216c1408078658005c01028100f0cb01006020a820260f70000810000601c20c00018a804290c815800040116010570cb00008021d8287c0c60000c0429078000ac0001028100f0004180004019e4100f3c300008030119ccc196000100608088001cc003e80810341286580004018ec7c0c0730005c020403c321060000c0408048f432c000200c043e061258000401180140f0cb0000803040c0000e600010040a0406418c00021c83008078658000401808124202b00006021d8f81810600010063b0786464c000580c040f00015800040102810610cb0000802040e06e0760001004150403cdac000a0084a190281d800260b008100f0cb00006171502052196
  | 6, 0, 3 => 0x100408078648ac000900814080793d808030b8a810130cb80006081483c000e6000102e020503c00c002f808bc080786580002078000a070830000602240201e1960001004540403c32c0002008760a07941800040180810001b3000080205020ba1960001004080c83034c0001130140807865800031c820520f0cb000080205020a40f60000c62081483c32c000200c040f281258000b018201e000730000817150281e1960001006021c0dc0ac000200c7208048e18000401054104707b0000602148ac320560001006080780064c0002020000c0701d80004050201e00073000080304070360e600048063c0102022c000205c040a07941800000200c040f06a80066030403c000e6
  | 6, 0, 4 => 0x201e000701c20c000200c041e0e831800041d8281e3e07300008170c0d01e19600010040a078f892c000200c04080c8198000318820320c0830000802078640a1a600008760a078f820c00020b8040826865800040c0082a0807b00040030103c3e05600010042c0403c00c000200c1e3e248398001401808760809b00008031e020a00c60005006250c8141cc00018ec1e3e070418000417008100f28300008030b9441e196000100600060141cc000200814080886580004010281e192ab0000602078f8921060001004351a06418c000200c047f0c81580002050201e190830000803010ec1e0d60000c9c021d83c7cc00021c404340786580004078000a0e03b0000602000300a106
  | 6, 0, 5 => 0x106a34078641cc00021b00434078658000401024700503b00008030403ca069600010040a0413432c000183c000507041800021a8d01e190830001602078640a076000102e3c0503c32c0002008e808079cd8000401028100f28300000040180810065000100415041cc18c00020081419060158001201808760808b000080807864340e60008006080787c1cc000a00c04130c8158000205020520f0cb0000408078643410600010063c079400ac000580c7802040258000401044320503b00008020502012386000105c020403c00c00020088c34078658000416808100f0030000608000301c106000100602049000ac000580c04080c8dd8000b01028100f0cb00024020793c0a076
  | 6, 0, 6 => 0x1006110c8141cc00021d40408079cd8000404024700e03b00008170b0d01e1960001004080786486c000200c620800031800120183c9e050730001608078641c07600010046e1a83c32c000205804150403d8000401820320c193000082e010ec1e3e60001006080780048c000202810190603980004018781e1d0730009c2e010201e19600010d0160403c32c000200814080780180014018084a0002b0000602040a456006000480602088640ac00018085219060158000205020320c08300028030404c320e60001006021d02012c00010a41e190281d800040b8081e190d3000280301020327c60001006311d86418c000200c54082086580004010b0760f1f3000062a0102052006
  | 6, 0, 7 => 0x200c044b250f98000401028b40f0cb0001603078640a0e60000cfa02128640ac000580c043b0402580004010201e000d30000803010001805600010320c028380ec0002054100f39839800040503c3205073000280304094000e6000480608088641cc00021bc300807865800040b80814190630000419060140e10600010ca7a0403c32c0001054100f39841800020503c32050830000602260ec1e3e6
  | 7, 0, 0 => 0x102e02050201e197000000408078000e10600000080318820320c6000100602048ac32057000100602118243205700008103407864e6107000480808078641c0770000c040f0c8000a1070000008021d8281e3e60001006020403c32a470001006020883c3205700010061e0403c320e7000100617010281e1970001006024e03c32057000f00408078640e1070001006020c93c180570001054020403c0007700010060207865ea05700010040807864d2077000100602118d41e197000100602079cc00057000100602678201e1970000008030403c322460000008031d83c7c0e60000c044c1d8201e197000100602078640a21700010060807894000e7000100699010201e0070000c040814a881e1970001006020403c32a770001006021d820a40f700011a2030103c32057
  | 7, 0, 1 => 0x100608078650c0e70001006c90403c320e7000100602078646e057000100639040241e197000000808078001c0760001006170403c326970001006020411c320c700010103407864e60e700010060f0c8000a0e70000006020400018106000100689078640a0e70001006020403c32da70001006be010201e1970004806024e0201e197000100617012381e1970000c04080c8300a1070001006020c8300aa07000500802078640a0770000c780204064181070001006e3010201e19700010062a01020000c7000480602040d01e4f7000100631040241e1970004806021d8201e4f7000102e020406418077000100616010201e00700010060204064186970001006080e03c000e700010060207864da057000100602370201e007000100617010d01e007000100617010ec1e007
  | 7, 0, 2 => 0x100602160201e1970001006ee010201e19700010060211820000c70001006080483c000e700010069a010209a19700010040a0403c321a70001006020403da81970004806890403c320e7000100602670201e197000100676010201e19700000080304000180e6000100602258209419700010100f0c8e01c077000100602040d0221970001006021a03c325570001006080c8300a0e70001006021d820221970001006021d83c325570001006020403c324970000cde020403c3210700000080301020fe19600010069a010201e5070002c0617010201e1970001006020e03c320570001004230403c000770000c043b0403c3210700010040f0c8300a0770000c04080483c0010700010068b0103c320570000c2e3c0403c321070001006020c83110057000100617150201e007
  | 7, 0, 3 => 0x10062a01020261970000c2e02040a41e19700010043b04064180770001006020404c1e00700010061701020fe1970001006021d83c7c4970001006ca010201e19700011a2030403c320e70000008020403c321a600000080301064180560001006024a0201e007000100602043a01e1970001006020a8201e00700010066b150201e19700010043b050201e1970001006020409c000c700010063c0119c1e197000100602258ec1e3e70001006022903c32057000004003010201e1f600010062a0403c325570001006315b8201e1970001006df010201e197000480602078640a91700010068f010201e00700010fa02040d01e19700010067a0403c327870001006020431c1e197000100617010201238700000280304094320e60001006024c0201e007000100602042e01e197
  | 7, 0, 4 => 0x1006020403c005570001006022383c32057000000602078000a1060002c0602040d01e19700010060807864da0e70000024020403c9e0760002c06021d8201e197000480803078640a0e7000480602078649e057000100608048ac320e70000c7802078640a1070001006021a820320c70001006020403c32e070000c100f0c8001c10700010062a0103c0005700010046e0403c32737000102e021a03c32737000100602078640a6970001006310403cc419700010069c0403c320e70001006020403c3302700010068501020000c70001006084f83c320e70001006d7010201e197000100608079cc000e70001006021d83c943e70001006020403c328c70001006020403dba197000100697010201e007000a008030103c00057000100671010201e1970001006020483c32057
  | 7, 0, 5 => 0x8031e0201e506000100602078ac000570001006021183c0005700010067201020320c700010060f0c815220e70000008020404432076000100617010209a19700010061801020320c7000100602050201e00700010100f0c8301c077000000803078000a0e6000100602040d0123870001006021d820123870000008021a8d01e196000100631010ec1e1970001006020403c32cb7000100602040647e0c700000080301020322f6000100408078651a0770001006020403c32c1700010040a0403c4a19700010062e010201e19700010040807800360770001006021d8201e3f7000000803010201240600010066b010201e007000500808078641c077000100617010641805700010069a010201e007002d40602560201e1970001006020403c0088700010062d010201e197
  | 7, 0, 6 => 0x10060f0c93c0a0e70001006850103c000570000c54020403c0010700010063c01054100f70005c0408078640e1070000c040807864d210700010060f0c815200e70001006082903c320e70001006021d8201eaf70000c9c3c010201e197000100617012701e1970001004150403c327370000c04081483c323e7000100602668201e1970000006310403c321060001006170403c328d7000100602470201e00700000280301020261960031006c3010201e19700010060f0c8141c107000100617390201e19700010062a188201e197000100602758201e19700010060211888323f70000c04081a0a41e19700010060204000188770000c043b040a41e1970001006681e0201e1970001006170c0201e19700010068901020000c70000c0408048a41e00700010060f0c8e00a0e7
  | 7, 0, 7 => 0x80311888320e600010060204064a00c70001006171e0d01e19700010040a040241e1970001006171e0ec1e197000100631010201e0070000c0408048a45619700010060204000189e700010062a010204a0070001006027903c320570000c2e0204064181070001006021d8201e50700000080205020320c60001006f00103c320570001006171e0201e50700010063c010ec1e3e7000100602230201e19700010043b0403c321a70000c04082383c321070001006021d86418057000000803010781e1d6000a008030403c000e7000100602568201e19700010069d010201e00700010060204340320c70001006b0010201e1970001006020403c3232700010063c01020260f70000050031383c320e6002480802050201e197000119202040d01e1970000c040f0c81540107
  | 7, 0, 8 => 0x100602078640ac87000100602078640a8d70001078020403c0007700011a40301020320c70001006026f0201e197000100602078000a49700010040a0403c3273700000080204024700760001006720103c3205700010069701020cc19700010060207800360570001006020420c1e0070001006020486470057000500803078640a0e70001006180103c320570001006024d83c3205700010068501020320c70000c04230403c0010700010040f128640a07700010060267820320c70000024030103c9e056000100602078647e0570001006020c8300a2170001006082383c320e70001006021d8209a197000000608078001c106000100408048641807700010069a011a81e1970000c100f0c8141c107000480608078649e0e700010060f0c815400e70000016020403c32076
  | 7, 0, 9 => 0xc04081a06418107000100602078655e0570000c043b04064181070000d344e010201e1970000c04350403c32107000102c020403c561970001004081a03c326d70001006081383c000e7000100696010201e007000100602040001805700010061715021b6197000000803010883221600010063c01020000c700010040807864920770200c2e020404c1e1980000004081483c32076000100602320201e1970000008030104432056000100602518201e197000100602048640a90700010044b0403c32077000087608078640e107000100608078ac000e70001006230403c000e7003e40617010201e19700010060f0c8300a0e70001006020403c32bc70001006ab010201e1970001004081a03ce600700010060250820320c70001006890103c00057000000602078640a106
  | 7, 0, 10 => 0x10063b04064180e70001006350403c320e700010066c010201e19700010060207864a0057000100602040248e3870000008020c8300a076000100602040c01e0070001006020403c32a6700010069a010ec1e3e700010060204064000c70000c2e02078640a1070000c04080c8f8181070000008020a8201e7360000008020503c320560001006020403df419700010066f010201e007002480802078640a077000002803010204a00600010062a01020120070001006020406418497000004c030403c320e600000240301020221960001006021d8201e007000000602040a4320c600050060204094320570001006171e0201e0070001006b4010201e197000116c021d8201e197000107608078641c077000100602078640ae770001006020403c32aa700050063c010204a197
  | 7, 0, 11 => 0x24030403c9e0e60001006020486418057000100608078647e0e700010066b1e0201e1970000016030103c32056000100602040441e0070000c04081483c327370001006024e0201e00700010063c0403c325570001006020413c000c70001006020403c32d870001006020403c008a70000c04081491c1e19700010060211888320070000c04086283c327370001006850103c320570001006021d83c7c0c70000ce4020403c3210700010043b05020320c70001006020427c1e007000100435050201e1970001006080c8f8180e70001006020403c32e470000c30020403c321070001006020403c32fb700050080301024320570001006020403c00217000000602040c032106000100409078640a07700011ee030103c320570001006bd010201e1970001006081a064180e7
  | 7, 0, 12 => 0x80304044320e60001006020403c32e170001006020403c32e2700010068b010201e00700010060204000188870001006020c9cc18057000105402050201e1970001006020403c32c670001006020403c00377000102e021d83c32077000100602078640ada70001162020403c3249700010063c0103c000570001006ba010201e1970001006890403c000e70001006020403c32d6700000080301024700560001004ac050201e197000000803188ec1e196000100617340201e197000100602040003e0c7000100602570201e197000a00802050201e19700010060807800360e700010060804864700e70200c04081a04c1e1980004808030103c00057000000803040c0320e60001132020403c32077000100602040245600700010060211820120070001006d5010201e197
  | 7, 0, 13 => 0x10de020403c32737000081009078640e10700010061601020320c7000102e2a0403c320770200c04150403c4a19800010060207864000570000066030403c320e6000100602078e000057000100608078655e0e70001004081a11c1e19700010060237020320c7000100617010d0320c7000100617153701e197000100617010ec320c70000004080c8300e106000100617010d41e1970001006171e1a81e197000100602078640a4970000006021483c320560001006f60103c320570001006020403c32fc7000100602078000a9170001006530403c320e700000040a0403c321060001006174c8201e19700010067a0403c3224700010540204064180770001006022583c320570000c043b078640a10700010060207864840570000c9c17010201e1970001004080780018077
  | 7, 0, 14 => 0x1006020403c32c270001006720102012197000100602040241e0070001004351a03c327370000050030109c1e0060001004980403c3207700010063c188201e1970001006020793c000570001004230406418077000101009078641c07700010043b0503c3205700000080301020000c60001006bf010201e197000100602040ac32377000a0063c0109c1e19700010061715020320c700010040a0403c56197000100700010201e197000100423050201e1970000008030403c32326000100602078000a907000100602041481e0070000008080c8301c0760001006170b0201e1970001006020403c321a70001006a5010201e19700000080a0403c320e6000100663188201e19700010063b078640a0e70001006ee0103c32057000100602078000a10700011f0030103c32057
  | 7, 0, 15 => 0x1006021d820260f7000100684010201e00700010060229820121970001006310403c323270200c2e2a0403c327380001006020411c1e00700010060f128640a0e70001006a10403c320e70001006990103c32057000112e020403c32077000100602818201e1970004808030403c000e70000c0408048a4323870000c04080c9cc181070000c0408078000a1070000c9c021d8201e197000100602078000aa070001004080983c3207700011a4030403c320e7000100602078003e0570001006020403c32ff70000008030108c440060001006ea010201e1970000c78020403c00107000100602078653c0570000016030403c320e6000102e020403c0007700010063c0108c4419700000067d010204a1960001006020403c00937000000803188201e0060001006680103c32057
  | 7, 1, 0 => 0x10060207800180570001006160103c320570001134020403c320770001006961e0201e1970000c1034078641c107000000817010281e19600010040807864aa0770000c7608078641c10700010060807864840e700000040f0c8140e1060001006021d8647c0c70001006850403c326970001006080c9cc180e7000500617010204a197000100608078000a0e7000105c3c010201e1970001006020f020000c70000008030102032366000100602040003a0c7000100617478201e1970005008030103c000570001006023a0201e197002d40802050201e197000105402078640a0770001006020403c328a70001006d3010201e1970000c0408078649210700000080304024700e6000105a3c010201e1970001006020a820320c7000100602288201e19700010061701020000c7
  | 7, 1, 1 => 0x100602041041e19700010040a0403c32007000111202050201e19700010043b0403c0007700010040a0403c9419700098063c010201e1970000c0409078640a107000103002040d01e19700010066b01020320c70000008030103c0005600010069a01020320c700010040a0403c32497000100602728201e1970001006171503c32057000100602040010c0c70001006020403c32b27000100608078001c107000100602040641855700000080f0c8141c0760008008030103c000570000006020c8300a10600010060807888000e700010044b050201e19700008760a0403c32107000100608078e0000e70000c100f0c8f81c1070001006020406418a070001006174b8201e19700010060807864920e700010062a01064180570000006081483c320e600010060207bbc32057
  | 7, 1, 2 => 0x100608078003e0e7000100602040f8000c7000500602040d04a1970005006021d8204a1970001006020403c32707000a80408078640e107000100602600201e197000000802160201e1960001006310403c320c700010068f0103c3205700010060204064800c70000c040f0c9cc0a107000100602040d0000c70001006024c03c320570001006021d820000c70001006021a8201e0070001006021186418057000100609078640a0e7000100602298ec1e197000100602078640af4700010048e0403c3207700000080301020123f60001006080793c000e700010060205020320c700010062a0c0201e1970000008030c8300a0e600010760a0403c320e70001004080c800180770000810091483c320770001006021d83c4a3e7000004c03010201e0060000016030102012196
  | 7, 1, 3 => 0x100672010201e0070001006020f03c324970005008030403c000e70001006020403c322470001006027683c32057000100618010201e0070001006020426c1e0070001004080c8313c07700011342e010201e19700000080301020600060001006170103c3249700010040807894000770001006020403c329370000c2c020403c32107000000602040245238600010060f0c9cc0a0e70001006970103c3205700010067a010201e0070001006020f03c0005700000080301020fc19600010063c01020601970000c046e0403c321070000c2e021a03c321070001006020983c320570004806020403c9e0570000c2e021d83c32107000a00808078641c077000100602760201e19700048063c010201e4f70001006793d0201e1970001006a8010201e1970001006170103c00057
  | 7, 1, 4 => 0xcc063c010201e19700010067d0103c320570008008030403c000e700000082d010201e196000100602298201e0070001006020f020320c70000006080c8301c1060017c0802050201e197000480802050201e1970001006021d8241e3e7000102e021d8281e1970000c04081483c32007000000803010202200600010069a0103c32057000100602078010c05700010060207865100570001006174e8201e197000100602040443205700010063101020320c7000084608078640e107000100602078640abc7000000803010ec7c0c600010060807800180e700010063c0102022197003f806fd010201e1970000006020403c001060001006020a820120f70000c2e2a0403c3210700010066e0403c320e70001006020403c008d700000100f0c8380e10600010062a01020001b7
  | 7, 1, 5 => 0x8020400018076000100602078640aa6700010069901020121970001004081a064e60c70001006020c800180570001006020403c32e9700010068901064180570000c04091483c320570000c04150403c321070000c2e020403c001070001006020786480057000000802050201e006000100682010201e007000107802040641807700000080301020381b60001006021d83c000570001006020404c1e73700010060211820001b7000100602548201e197000100602118201e007000107802050201e197000100675010201e19700010060204070000c7000104608078641c077000006603010201e0060000d723c010201e19700000082e010201e196000100668010201219700010040f0c8000a07700010068b01021b61970001006020400018377000100617150204a197
  | 7, 1, 6 => 0x1006021d820320c7000a00803078640a0e700010060204024000c700010069d0103c320570001006171e020320c700010061e0403c000e70001006080983c320e7000001603010201e006000100608078003a0e700010042c1d8201e197000100602370201219700010067a0403c320070002c06020403c320570000c5402078640a107000105c17010201e1970001006150403c320e70002c063c010201e197000100602078647c49700010040a0403c321070001006021d820c21970001006020403c327c700010060204064703770000028020409432076000105402040243207700010040a0403c323870001004080483c00077000102e3c0403c320770000c100f0c9cc1c1070001006024703c320570001006980403c320e70000c0408078003a107000100602040650c0c7
  | 7, 1, 7 => 0x100602041cc000c70000c040a0403c321070001007010403c320e70001006020f03c320570001006024a8201e00700000060f0c8141c1060001006bb010201e197000100423040243207700048069d010201e19700011a20301020320c700010043b0503c323e7000100617150201219700010060807865400e700010049c0403c3207700010060204024700570001006020403c32b370001006020c8313c05700010062a010943205700010063c0102012387000000803010ec1e5060001006020789400057000100602508201e00700010040a0403c324f70000cd6020403c321070000d34020403c3210700010e4020403c3273700010066f01020320c7000100415050201e1970000c040807864aa1070001004080786442077000000803010201242600010063b078647c0e7
  | 7, 1, 8 => 0x802078000a0760001116020403c32077000100617010ec1e507000500802050201e19700010060a0403c320e700010060204064da0c7000100408078646e0770001006cc010201e1970001006020403c32c870000008030102100196000107802078640a077000113402050201e197000100617012601e1970001006024c020121970001006f30103c3205700010100f0c8001c077000100602408201e00700000062a01020521960001006020403c004970000c04080c80018107000000602040a41e00600010067d0403c320e70001006024e020320c70001006020e03c000570000c04081483c320570000c04081a03c00107000100602258201e0070000c043b0403c001070000c7802040a41e1970000c0423078640a107000100608078010c0e7000480802078640a077
  | 7, 1, 9 => 0x10040a2f0201e1970001006171e03c3205700010040f0c8140e107000102c02040d01e19700010062a010ec1e3e70004806890103c32057000100679010201e1970001006026c8201e197000000803010001805600010060207bc43205700010068e0403c320e700010043b050201e00700010040f0c8e00a077000100608078f8000e700010040a0403cae197000116802050201e197000480617010201e4f70001006170103c001d700010040a0403c320c700010063c01064180570001006021dab01e3e70001006080c800180e70024808030103c000570001006310403c4a197000100617010541e197000105c021d8201e1970001006081a03c000e700010063b0403c000e700010060f158640a0e7000100602078650c057000100623078640a0e70001006c90103c32057
  | 7, 1, 10 => 0x1006021d0201e197000100458050201e19700010040f0c93c0a0770000008033d0201e00600010061701020221970000008030103c7c49600010067a1e0201e19700000080301020703760001006020403c3277700010063c010209a1970000c62020403c32107000000802050201e196000100617150d01e197000100617150ec1e19700000280301094320560000006021d83c7c106000000602040a45619600010062a0102432057000100668010201e0070001006020403c008c700010060204025443870001006020483c000570001006e6010201e1970001006020c8300a917
  | 8, 0, 0 => 0x200c04080483c327380000c04081a03c321070200c04080491c1e198000100602258201e1970000c043b0403c321070001006020403c324270200c040807864000c800010060204064e60c70001006020403c000570200c5402040d01e1980200c54021d8201e1980001006024a8201e19700010063c010201e0070200c78020403c3205800000080301020123860200c043b560201e1980200c2e020403c325081401006021d8201e1980001006020789432057000100602508201e197000480803010201e0070200c7816010201e19800011a403010201e1970901006020403c3205800010060204024320c709010063c010201e1980200c2e020403c561980200c2e02118201e198000001603010201e196000100685010201e19700050080301020121970001004080483c32077
  | 8, 0, 1 => 0x200d1217010201e198000100668010201e1970001006020483c320570200c78c3010201e1980001006020403c9e0070200d2e3c010201e19800000080301064180560200c0408078649e05800010043b050201e197000100608078647c0e70200c78020403c324f80200c043b0403c561980200c04231d8201e1980024808030103c320570001006081a03c320e700010063b0403c320e70001006020403c0010700011f003010201e197000000802078640a0760200c0408078640a1080001006020403c440070001006020403c320070001006020403c700070200c78020403c321080000c0408078647c1070200c040807864700580200c78020403c441980001006020403c324970200c78020403c32388000000602040a41e1960001006f6010201e1970200c54020403c323e8
  | 8, 0, 2 => 0x803010201e006000100617150201e1970200c043b0403c32498000000808078641c076000800803010201e00700000060204064181060200c044b1d8201e19800010062a01020320c70200c04350403c327380001006020403c000c7000100616010201e1970200c04080786418058000100602370201e197000100617010d01e197000100617010ec1e197000000408078640e1060200c78020403c320c8000500803010201e0070001054020403c320770a01006020403c320585a81006021d8201e1980a010063c010201e19800010060207864e605700010060807894320e70200d343c010201e198000100699010201e197000a008020403c320770000008033d0201e1960001006020403c001f70200c040807864001d80001006020403c329e70200c2e020403c32008
  | 8, 0, 3 => 0x200c2e020403c321080200c04230403c327380200c2e020403c323880001006021d83c323e700010060807864e60e70200c04080789432008000100697010201e197000a008030103c320570001006020f0201e0070001006020404c1e1970001006020403c001d70001006024a0201e1970001006020a8201e197000100617010201e0070001006020409c320c700010068f010201e1970000c040807864e61070001006024c0201e19700010060211820320c70001006080483c320e70200c54020403c327380200c2e020403db61980200c30020403c3273800000080304064180e6090100617010201e1980200c04084d83c327380001004230403c320770200c04081a03c320080200c043b0403c320080200d12021d8201e1980000c04080483c321070200c043b0403c94198
  | 8, 0, 4 => 0x100602470201e1970200d3417010201e1980001006020403c7c0070200c2e020403c32558000100602040641887700010060204064000c700010068901020320c70000c0408048a41e1970200c78020403c323e80001006020403c32407000100602040d01e0070001006021d8201e007000100602078ac320570001006021183c320570200c7802040d01e198000100602050201e1970200c78021d8201e198000000803078640a0e6000100408078640007700010067d010201e1970200c2e020403c324f8090100602040d01e19800010066b010201e1970901006021d8201e19800010069a010201e1970001006020403c008670001006020403c328870001006020403c32557000100701010201e197000000602078640a1060001006020403c32a0700010062a0103c32057
  | 8, 0, 5 => 0x1006890103c320570a0100602040d01e1980a01006021d8201e1980001078020403c320770200d34021d8201e19862010063c010201e198000100602040701e0070000c04230403c321070004808020403c320770001006020f0201e197000000608078641c106000100631010201e19700010060204064189e700010062a010204a197000000803010ec1e3e60001006020403c4a0070200c04230403c323f80200c04081a03c324f80200c040807894320580200c043b0403c324f80200c78020403c4a198000a008030403c320e700010069d010201e1970200c2e020403c320c80000c54020403c321070200c04081a03c321080200c043b0403c321080200c5472010201e1980a0100617010201e1980200c04081a03c323880200c043b0403c323880200c04080483c32008
  | 8, 0, 6 => 0x100408078649e077000100602040c01e19700010066f010201e1970200c78020403c32698000002803010204a19600010062a01020121970001006021d8201e197000100602040241e0070001006171e0201e1970200c04080483c32058000100408078640e1070200c0408078647c0c8000480689010201e1970200c7802040241e19800000080301020000c600010040807864700770001006081383c320e7000100696010201e197000100602040641805700010063c01020320c70200c04081a03c320c8002480803010201e0070200c043b0403c320c80200c043b050201e1984901006020403c32058000100608078ac320e70001006020403c328670001006230403c320e70001006c9010201e1970000008020403c000760001004081a03c327370001006020786400057
  | 8, 0, 7 => 0x10040807864180770200c0408078ac320080200c04230403c320080000008030103c0005600010068b010201e19700010060204064188870001006020403c3237700010063c0103c3205700010060807864000e70001006890403c320e70200c040804a881e1980005008020403c320777f0100617010201e1980001006020403c326d70004808030103c320570200c2e6f010201e198000100602040245619700010060211820121970000c040807864001070200c2e021d8201e198000100602040441e1970001006024e0201e197000100602040649e0c70001006020403c32f570200c54020403c320080001006020427c1e1970001006020403ce60070200c5402043701e1980001006020403c322170200c7802041a81e1980200c78020403c3273800011a203010201e197
  | 8, 0, 8 => 0x10061701020320c70200c040807864001b80200c0423370201e1980001006020411c1e1970000006020403c001060004808030403c320e70000c0408078640a1070004806020403c324f7000100602078640aa070000008030108c441960000c78020403c3210700010062a010201e007000102e020403c320770001006020403c326970200c54020403c320580200c040807864e60c8000000803188201e196000a00803010201e007000100602040241e1970000050030109c1e196000100602078649e05714010063c010201e19800000080301020320c60200d1617010201e198000100602078640a907000100602041481e197000100602078640a10700010060207864700570200c2e020403c4a1980200c04081383c32008000100602078640a917000100602040701e197
  | 8, 0, 9 => 0x1006170103c32057000100602040647c0c70200c04081a0241e1980200c043b040241e198000100602040d0320c70001006021d820320c70001006021a8201e197000100608078649e0e7490100602040d01e198000100685010201e0074901006021d8201e198000004c03010201e19600010043b0403c320770000008030103c32056000100608078641c1070001006020409c1e0070200c2e020403c3273800010060807888320e700010060807864700e70200c78020409c1e1980001006020403c56007000100602118201e00700010060207864180570200c040807894323e80200c78020403c561980200c7802118201e1980000008030403c000e6000100608078640a0e70200c2e02040241e1980005008030103c320570200c04081a03c4a1980200c043b0403c4a198
  | 8, 0, 10 => 0x802050201e1960024808020403c320770001006021d83c32057000100602118201e197000006603010201e1960001006020403c32af70200c04080788832008140100617010201e198000100602298201e197000000803010202219600010060807864180e7000100689010201e0070000006020403c321060200c040807864000580001006020403c328d70200c78020403ccc1980200c78020403c320080200d123c010201e198000100672010201e1970001006020403c001b70200c043b0403c3273800010060204024323870005008030403c320e7000100618010201e1970001006020426c1e197000000803010206019600010040807894320770200c54020403c32408000002403010201e4f600010067a010201e1970001006020403c323f70200c04080483c323e8
  | 8, 0, 11 => 0x11ee03010201e1970001006020403c325070200c2efd010201e19800000080204064180760000c2e020403c321070200c04080789432738
  | 9, 0, 0 => 0x401808102707865c0803010201e2b0cb8100602118201e197000100608078641cc0001808100f0c8418080315008100f0cb8a00803010201e197000100602078640ac0401808100f0c9cdc080301020120f0cb800080301020320c64901006020403c32e0002008100f0c81d80803010201e250cb81006020403c323e70200c04081a03c32e0401808760807865c08030b808100f0cb8000803010201e1960200c04080786418e140200c040807865c0803010201e1927b81006020403c321070200c04080788832e0401808100f0c8e1c000401808100f00301006020403c320570200c78020403c32e120200c040807865c0803010201e190038100689010201e197
  | 10, 0, 0 => 0x803010201e196
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 49
  | 6 => 67
  | 7 => 76
  | 8 => 76
  | 9 => 67
  | 10 => 58
  | _ => 0
def stateM : Nat → Nat
  | 5 => 0x1ffffffffffff
  | 6 => 0x7ffffffffffffffff
  | 7 => 0xfffffffffffffffffff
  | 8 => 0xfffffffffffffffffff
  | 9 => 0x7ffffffffffffffff
  | 10 => 0x3ffffffffffffff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x3807c7061cddc001fc1ff83fe01ff00e3c60c7c600e0000fc7f838f9e322300ffffff8000001c001c0000039e00000003807ff07fcddf001c39800381f1e000003fff8001ffff00fc7ff00f80323c00e3c67ffc7e0e1f00ffffff8000000000ffc0007ffe000000e03e007c01fe0000e046038c1fc3c300ffff8c7fe1ffe0
  | 1 => 0xffff8c0000000000ffff8c7fe1ffe0001c39800381f1e000fffffc7fe1fffc0003800c7061cdc000e3fffffc61ffff00000073801e001f00e03e007c1ffe0000fc3f807f81ffe000e000007c1e0000001c0073839e001f00fffffff061cddc0003807f801e001f00ffffff801e001f0003807ff061cddc000000007fffffff
  | 2 => 0xfc7f838f9e322300fc00007f9e000000e380007c7e0000001f800073fe0000000380007060000000e3be7c7c61ffdc0003807f8000000000ffffff8381f1e0001c39800000000000ffffff838000000003807c00000000001fc1ff83fe003f001fb9fc73e1fdfc000000000001c1c000e046038c1e020300ffffffffe1ffe0
  | 3 => 0x700000001c00000000000000000003807f8000001c00e03e73fc1ffe1f001c39f3839ff1ff001c00700380001c00e03e007c01ffc0000000700000001c00fc7f800f80322000fc7f800f9e3223001c3980039ff1e0001c00000380000000ffffff80000000001fc1ff83fe01ff00e03e007c01fe000003807c7061cddc
  | 4 => 0x738000000000fc3ff380000000000000707001cddc001fb9ff80000000001fb9fff3fffdff000000700001c1dc00e3c60c7c600e00001f807f8380000000038000707e0000001fb98073fff1e0001c7fff8381ffff00e3867ffc7e0e1f00e07fff8c01ffff000000738000001c000000007001cdc0000000700000001c
  | 5 => 0xffffff839e0000001c0000000000000003807c0000000000ffffff8000000000e03e007c01fe00001c39800381f1e0001f807c00000000001f807c73ffcddc00000000000000000003ffff8061ffff0003c07f807e001f001f8000039e0000001fb98073e1f1e000038073f07e001f000038700001f1dc0000000000000000
  | 6 => 0xfc00007f800000001f800073e0000000ffffffffe1ffff00fc39807f9ff1e000fc3e007f81fe00000038000001f000001fc18c03e001e000e3be007c61fe00000038000001f1c0000000707001cc1c00e000007c1e0000000038707001fc1c00e3be7c7c61ffdc000000007001cc000003807c0001c1dc001c39800381f1e0
  | 7 => 0x3807c7061cddc0003807ff061cddc00ffc0007060000000fc7f807fe1ffe0001c00000380000000e03e007c01ffc000e03e73fc1fffdf000000000000000000e3ff8c7c61ffe000fc0073ff9e001f00e38073fc7e001f001f8073f3fe001f00000000001e000000e380007c60000000fc3f807f9fffe000e3c67ffc600e1f
  | 8 => 0xe3be7c7c01fe00001fb9fc0381f1e0001c4183839e002300e3be0c7c61ffc000ffbffc7fe1fffc001fb98c73e1fde000ffc0000000000000fc40000f9e0000001c39800380302000ffc0007fe0000000ffff8c7fe1ffe000fc3f807f81ffe0001fb9fc73e1fdfc00e3be0c7c61ffc0001fb98c73e1fde00003807ff061cddc
  | 9 => 0x73801fc1df00000003801e000300e03e73fc01fe00001c39f38381f1e00003807c707fcddc00fc3ff3ff9fffff00e03e707c01fe1c001c39f00381f1fc00e3be7ffc7fffdf00fc3f807c01fe00001fb9fc7061cddc001f807c73e1cddc00fc3f807f81ffe000fffffffc01fe0000e3c67f800000000003807c70600c1c
  | 10 => 0x7380000000001fb9ff839ff1ff001fb9f3f3fff1ff001c39f38000000000e000007c000000001fc18f83fe01e3001c00000380000000fc3ff07f81fffc00e3c60ffc7e0e030003807ff07e0c1f00e3be007c7ffe0000fc7fff8f81ffff00fc7f800f81f3e0000000000001c1c0001c39f3801e001f00000073801e001f
  | 11 => 0xfc3ff3fc1ffe1f00e03e738001f00000fc3e73ff9ffe1f00e00673fc1e0e1f00e3be7ffc1ffe1f00e3be73fc7ffe1f00e3be7f800000000003807c0000000000e03e000000000000ffc000039e000000ffffff839ff1ff00fc3e007f9ffe000003c00c0060000000e3c0007c60000000ffc60c7ffe0e0000e3fe0c7c61fe00
  | 12 => 0x1c3983839ff1e3001c007383800000001c00000380000000fc3ff3ff81ffe000e3c60c7c7e0e1f00fc3f800000000000ffc000001e000000e3c67f801e001f0003807c001e0000001fc1ff83e001ff0003807c0000000000fffffffc1ffe1f00e03e7380000000001fffff83e1ffff001fc00003e00000001ff98c03e1f1e0
  | 13 => 0xffb9807fe1f1e0001c7983839ff1e3001c41f3839e003f000038000001f1c0000000007001cdc000e3867c7c600e1c001c39f00381f1fc00ffff8c7fe03e2000ffbe007fe1fe0000e07fff8c1fffff00ff80007fe0000000e046738c1e021f00e03e707c01fe1c00fff9800381f1e000ffc073801e001f001c39f3839e303f
  | 14 => 0x3807ff07e0c1f00e03e73fc1ffe1f0003807ff07fcddf001f807c03800000001f80000380000000ffbffc7f81ffe000e04603fc7e0e1f00038000001e000000e3c67ff0600c1c00e03e73fc01fe1c001c39f38381f1fc001c41ff839e01ff00ffbf807fe1ffe000e0467f8c1e0e1f00fc7f8c0f81ffe0001c7fff839fffff
  | 15 => 0x3c1ff807e01ff00ffffffff81ffe000fc3f80000000000003ffff807fffff0003c000007e00000003c07f807e001f00ffffff8000000000fffe007c01fe0000ffc07c7061cddc00ffc0007c000000000000738000000000e3c67ffc000e0000e3fe7ffc01fe0000e3c67ff061cddc00e3c67f801e001f00e3be7c7c61fe1c
  | 16 => 0x1c39f38381f1e000e3c60c7fe1ffe000ffc0000380000000e03e73fc01fe00
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x4b957c7163cddc000dc1d681f601f500460c98c084586500b46a838e9c322300ffffffd0334d5c00bde0423ffea090006fdffff5ffdfff009d3994abc5f1e500001fbd80015f6f0090a0701a22645c0062c66b543a0e1a00ffffffc011090000ffe0427ffea09000f23e297e09fe0a002953172559c3c600db350c6b41a980
  | 1 => 0xdb350c4001090000df3d9cebc5f9e5009931042b41a18000dbb57c7b63eddc004b150c6141898000421fbdc0015f6f0024caf394be567f00f6fe6b7ebffe1a00ff3fbdffcdffef00f6e0427ebea01000bdeaf3bffef6ff00fffffff173cddc006fdfffd4bf5f7f00ffffffd4bf5f7f006fdffff173cddc000000003feef6ff
  | 2 => 0xb062030e18220200ffe0427ffea09000ffe0427ffea09000ffe0427ffea090004b80407162809000fbbf7d7f6bffde006fdfffc011090000ffffffebd5f9e5009d39948001010000ffffffebd5a980004b957c400109000004c0c280b6003100dfbdfcfbe7fdfd000911142141c1c4002042030418020200ffffffeb51a980
  | 3 => 0x488f090a6547d0004089080845065006fdfffd0334d5c00f6fefbfebffe7f00bdfbf7bffff7ff009da0703be6e4dc00ff3fbdffcdffef000080701022445c009020000a002000009020000e8c322300bdf9d6bffff1f5009d20002bc4a08000ffffffc09559650009c1460172019000f63eb9fe8dfe6f004f9dfcf1e7ddfd
  | 4 => 0x24caf38010000000ffffffc0110900004b957c7163cddc00ffffffc011090000ffffffffffffff000991743163c5dc004204084000080000ffffffebd5a980006fc04275fe809000fff9d6fffff1f500001fbd80015f6f0062c66b543a0e1a00001fbd80015f6f0024caf39032445c006f1fbdf5cddfef00208a71142a565e
  | 5 => 0xffffffffffa99000bde04200100000004b957c7163899000fffffff173899000fbbe697f6bfe9a009db9d4bbe7f1f500fff57e4011090000fff57e7fffeddc000980403162809000001fbd80015f6f0000c0420032001000ffe0427ffea09000dfb9d4fbe7f1f5006fcaf3f5fed6ff00b9bb753f6bf7de00240ab1948c566f
  | 6 => 0xff20007fcca08000dfa0407be6a09000db3fbdeb41ffef00fff9d6fffff1f500ff3e297fcdfe8a00943890aa85f065000901040140018000fbbe697f6bfe9a009d3994abc5f1e5004294787023cc5c00ffe0427ffea09000d6bcf8faa7fc7d00ffbffdffefffff004214387001cc4c004b957c7163cddc00bdf9d6abd5f1e5
  | 7 => 0x6f9ffdf5efdfff006fdffff57bdfde00ffe04271728090009020002b40a08000bde0423bf6a09000fb3f3d7f49ffce00ffffffffffffff00200a311408564e0042150c4001090000ffeaf3fffef6ff00ffeaf3fffef6ff00ffeaf3fffef6ff0024c04214be001000fba0407f6aa09000ffffffffffffff0042062940000e0a
  | 8 => 0xfbbf7d7e09ff0a00dfbdfcebc5f9e5000440828094002100db350c6b41a98000ffbffdffefffff00db350c6b41a98000ffe0424010000000b460020e9c2000009428808a84302100db20006b40a08000fb3f2d7f49ff8a00fb3f2d7f49ff8a00dbb57c7b63eddc00fb3f2d7f49ff8a00df3d9cebc5f9e5006fdffff1f7ddfd
  | 9 => 0x2ddbf7b5ffd7ff00244a83849c122300f6fefbfe19fe0a00bdfbf7abd5f1e5006fd57e75ffcddc00ffffffffffffff00f2be797e2bfe5e009db9f4bbe7f5fd00ffffffffffffff00ff3fbdfe09ff0a00dfbdfcf163cddc00dfb57c7be7eddc00db350c6b41a98000fffffffe19ff0a0062c66b401008000042846850220c18
  | 10 => 0x24caf38094506500ffffffffffffff00fffbf7fffff7ff00bdfbf78011010000f2a0407e2aa010000d418681d401a1009da0403be6a09000ffbffdffefffff0062460b44180a020062c66b543a0e1a00fffe6b7ffffe9a00903fbd8a017f6f009d3994abc5f1e5000d1994a1c5d1e500bdfbf794bf577f0020c263143a061a
  | 11 => 0xfffffffebfff7f00f6fefbea95f86500fffefbfffffeff0062c66b543a0e1a00fffffffebfff7f00fffefbfffffeff00ffffffc0110900004f9dfcc085596500f63eb9c001080000ffe0427ffea09000ffffffffffffff00fffe6b7ffffe9a0000000000000000004200004000000000ffe44a7ffea89000f23e297e09fe0a
  | 12 => 0xbd7b97afddf3e700bdeaf3abd4a08000bde0422bd4a08000ffffffffddffef00420408542a0e1a00ff3fbdd48d5f6f00ffe04254be00100062c66b543a0e1a006fd57e54bf091000090194814001e5006fd57e4011090000fffffffebfff7f00f6fefbc011080000091fbd81415fef0009000001400080009d3994abc5f1e5
  | 13 => 0xffb9d4ffeff1f5009d7996abd5f1e50024caf394be567f009939142b41f1c4004b153c7141cdcc00628669542a0e1a00bdbbf5bfeff7ff00d224084a00280000ffbe697feffe9a00205fbf84195f6f00ffa0407feea0900024caf394be567f00f6bef9feaffe7f00fff9d6ebd5f1e500ffeaf3d4be567f00b4eaf39ebe767f
  | 14 => 0x66cefbd4be5e7f00f2fe6b7e3bfe1a006bd77f757bcfde00dfb57c6bc5a98000dfa0406bc4a08000ffbffdffcdffef00204203143a061a006fc04254be00100062c66b50320c1800f6fefbfe3bfe5e00bdfbf7bbf7f5fd000441968094016500ffbffdffefffff0020462b04180e0a0090350c0a01290000045fbf80955f6f
  | 15 => 0xc1d68032017500ffffffffddffef00ff3fbdc00109000000dfff80335f7f0000c042003200100024caf394be567f00ffffffd49d5f6f00fffe6b7e19fe0a00fff57e7173cddc00ffe0427e18a0000024caf39418560a0062c66b54180e0a00f2fe6b7e19fe0a006bd77f7173cddc0066cefbd4be5e7f00f2be697e2bfe1a
  | 16 => 0xbdfbf7bfddf7ef004204086b40a88000ffe0426bd4a08000f6fefbfe9dfe6f
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 260 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem wd_0 : ∀ i, 0 ≤ i → i < 128 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem wd_128 : ∀ i, 128 ≤ i → i < 256 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 128 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem wd_256 : ∀ i, 256 ≤ i → i < 260 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 4 256 = true)
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 260 → wireDOK i = true := (range_split wd_0 (range_split wd_128 wd_256))
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 260 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 260 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0x1ff) :: stateWiresD n (ids >>> 9)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0x1ff) :: stateWiresS n (ids >>> 9)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 11 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 5 => 8
  | 6 => 594
  | 7 => 2042
  | 8 => 344
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xbe040037a954f45da08a055b91262c62534e837451851abb4305642938b6d6a1
  | 6, 0, 0 => 0x20a6edd120492a721fd528dc1f2901191e5d01b71e51e19a1dca59811db7f4151d4a39ee1c0316c31b6e9d7c1ae554351a97ec0a1a25eb4e19f7414419a4c68718917f9417ba9f93177c24c6176776c316d6d09316cab25b16b7bd0716612fb91658ec56163694bf1615b491158d7e83157f2c9b15671ce815459a9614baca8d12e88899129fea2910de1144109911fc108dfb000fb71aff0f2081030eccb7400e9fc0db0e9214770e2146200db36e6d0d20fe830ab1918c09fa4f09097f42550979a5d308bac832082a1dbb07198c0706e4120e03f8295d03d201c103ac249f0360c75a02e58f2b026aed280250646b01864c9500c78cfd00bf18a70046e4ed
  | 6, 0, 1 => 0x3bf6b9653bf368d73bcc4b8e3abd65e23a7cd14d3a75cc833a151ed139fb5db839b9eed639249b5a38c2cc7738a6759d38938049387e8026386dcd19385f4f1136e7f2d936d19d763582312934ed624534bd92e334ab5128347817ff34702ab8344e166f33fd04f033c52937332ff082324f851831ad60fd30ce194d308b8d4b2fd2dc832efbabc92ee5b6912ece18e22e9f17e82e9162f92d7859662d60e6582d5b776f2d286d6d2ca7cc942bf9805c2b125d972ac299d12a968b74298caa25295f47c128fc70ce28f54f49288899a127ab8edf2760319a25a631e724df4e522402d8e5238ec9892374b28423620fd723440ec021f40ce021a3ed8120c2b356
  | 6, 0, 2 => 0x4fdecd1d4faa861b4fa727e14fa0aef64f5a6fd74ecd1a174ec31ab64e8a104e4e838fd64e1594024e09ec584d947f0c4d3dcf844d2a1ffc4cff85024ca8e9834c9e6ed44be198184b4d31944b42168b4a8c18c5499a357b497e0663495e6d1f48facd0148deb89248986f3648766c384802432547a7018747741cc446a8cf054690d0534674d0c1462f16d945b84e38451a7cea44b5f23c4459c9ea43cfd02243aebfc643a6031e42c49e344293091941c7dbb3417ecd76417ae7e7417a81cf4169e7a741437c4240cfa2874042961640410a5a3fa9ee9a3f25fd303ea54a713e51fe3b3e1d34483e0dbefd3d2128443ce2c1c13cc117773ca9f1eb3c288264
  | 6, 0, 3 => 0x6dce3ec56d999fbb6d5776cf6d08e4c86c8913746ba2e3c56b85ca486aba7bd46a903a936a2e811969b7b878689eda7668211f4c67d59b0167bb5db467ae2a0667734ea96624a083661766a5657e37b6653d59ad64b8667564818a936440749a62afdfb561d3c4c661a85c2561100f8360c081b760a95c2b5fb333815f2174ff5d7ec6a05d0aa0ec5d03b9ec5ca506e55c6b9e195c59311a5c10f0005bff29cf5bf22aa55b18ec795a59ee845a3b1253599a622a58bcfd2358706dc258000af756549b0b55f2918a55e20adb555c98fb55249632552376a75483357b5321809253108902523d809752378dbf51f280be50e4481950a8ee26509a0cc150247369
  | 6, 0, 4 => 0x8759faf88743bbbd86ed63ac868e1944867018248649735784fccbd184b750ed8485fe988464003e8406bfc7840206a982f225d8828ebe06813734568103242c80854553807ff1427fefd26c7eb988177eb28c4e7e33a2117e32fd247dcdede77dca2b207c38b94a7c12f7dd7be36d2d7b812c767b7902c07abfddae7ab6d2f37a98c0657a5bc2797976ef16796447717933afc278c7d28f78a40dec780c6c857720ead2764d3db5759ba13574b26f2c747a456a7423dda972d23fce72bc591a72b0ab21729c6145728580e37259e285718e49e4716d676771382528713103a370c44dfb70b2846f709dd914703777bb701232276ff442ca6eff599c6df72d03
  | 6, 0, 5 => 0xa2b95721a276c6ada20527b3a1db0767a0f3d190a0daeb40a058fa6d9feeb2fd9f67cab99f37cc0b9eb63d339e5b2cb99dda28589d8a0a049d6958ea9b4865e5999b1e5999569214978f500b96b015619615da839577e7ad956cd1a795521fb295225003944258589436e1fb93d3912f93acbee993a4b7de9391693f936a0d269307726292a96043923926aa921a26f791c3067b90f9298090bef59590b220929081cf04902d5b0c8fa1088c8f53ba7f8f346e288f2f69968e9116618e54373c8e4591378c95ff338c810a2e8c6bfdd58c0b847c8bd505418b9ab91c8b8de4ab8af066f98a19a66b89ea70d58989ed488863e0d78825b57d87f329e78771de69
  | 6, 0, 6 => 0xbd118863bcdf6492bcbc907cbcb5f9c4bc7536e9bbc01f92bbbc7503bb8eba4bbb251300ba170c41b9e8170fb9653685b788427ab749d50ab748acb8b71a1d14b69f1060b68bcfeeb57273e1b4d3eb4ab4b4f0b8b4458a1bb43521b9b433f8c4b3f69aeeb3df9486b3d88913b3c41c7cb3b8f06fb39d4d71b3218e6cb2f6302eb2b1c5a5b242d147b23b10d4b219bac1b18b9460b0354d20b02ed5acaf451055aecbdfe5ae7a07f8ae0f20a9ade9db15ade53914acf41acfac251fbdaba30cfaab4572abab2c5829aaeccdecaaeb2ea7a8fc3611a79c9d6da747bb54a6768364a65948dca63fc380a5c1ad00a4edb26fa49448e9a409ce84a3f9f809a2dee76e
  | 6, 0, 7 => 0xdeddbc76de167681dc51fe70dbe06c38dbcd1d99dab550b0da9e7aa0da720627d9f9fb5ad9a47bd8d94aedbed8b45af8d83bcf6bd825243bd7fb8f7bd7533556d72c9c9ad720f8acd6af5112d5ab293bd566f8f9d4d1b38dd43a869fd41e9489d3cf3014d3315ec6d2b65212d2555ac5d1c5a1a2d1bb8cead19faa06d19c6ca2d169122dd0ced859cfa2773acf54d149cf2bc269ce57ec36cd5d8b38cc22a61bcc10aa7ecb7a0fdfcad7f953cac0d3c7caacd43fca58b31cc91589c7c89d7b8fc84ba573c7df3805c5fd5e6bc52120bcc448c592c406c3f6c2d474bfc25f196dc1f9021ac1397415c0eb8503c0920075c060a091bf47d025bde2bd91bdadc90b
  | 6, 0, 8 => 0xfa2bb521fa275381f9963cc4f94acfaef8766b53f86a8a06f805289ff790e489f77c0b91f6a06f11f69881caf67e384df5ec7cddf5dedc51f59f1446f477dc2af3680c83f2cb481bf2856546f276ac1af1bfa95ef17e3a7cf147f2cfefdcb04fefa703a7eeac3e7fee12c54decb1adebec4582deec1e12d4eb1a9bc8eb0d1e96ea43bbc7ea074a08e9bc24cae9306a07e92f85eae80a176fe803160be7f44a52e7e8f3aee7772d12e6ef03d2e6527f1ce5d0dcfee55a38fee542f83be4d4de3fe4bb5df2e4ae2957e49fb121e4959b00e43126cfe412ca1de39955eee31a21c7e1239367e0d17bb7e0b33483e074a129e06e8c87dfe04b27df817c55df247d40
  | 6, 0, 9 => 0xfff239c3ff844943ff414a26fe4e5997fdf9659afdf4a2a0fdaf27bcfdaefc54fc813e75fc697111fc42960afb8694d5fb6d2ecffb2c06dafacfb439fabf1a11fa901e3afa76c52e
  | 7, 0, 0 => 0x95537f9093db680090422d80889983b0883b66b086df8bb083591010828fed708028ac807a1618d07983db607852a5a073325e0072330e406e0c14b06d133fa0674bcee0626d89105f6b71805d2cb9505b2eac505ab6a7705a7c7630583d1110567fa5105640497055450540544cdf60532d23705032bb404d064d104b1bc0e047e8d15041cbc31039a82b703887dd8036514f10335143e032ca92b0303e9c302f5fddb02a4c08f02a36d9d0280d1440263fddc025a06d302463e4701dfe0b301c0cf2f019b811a019520ef017d5a38016d7b820166af5f012d94cb0129179e01271ba701189fc600f26ece00d64fc300bcc8890025265100251438001528ba
  | 7, 0, 1 => 0x11cdb06811c9fc591194d57e1158bc8d10faeb3210f5763010ee709e10c79138109879331082e40b107e292e106602d21056c74b104dd56b10391595101cf3100fcf05c80fb89c5c0fb19ba80f9f8c4e0f8f22d10f747f2a0f713d840f5e8c8c0f27162b0ed51c0e0ecd7e060e86711a0e68f5ce0e68bc0a0e4ce4f90e4468b30e41de8b0de1f81f0db8a9780daeef0b0d4b6ee40cfdf2310cd3e9650c76b2fc0c7515ce0bab8a350b8bbf6b0b70e1e80b619aaf0b53118e0b2837460b236e970b0d46330af1588d0aba57dc0a9cd3050a75aa570a61674a0a5db90d0a5133e10a49c2db0a2d480b0a0eeb570a01adfb09d69a7109c81ff709baeccb09b67f10
  | 7, 0, 2 => 0x19b45c2419b15e681972931919728323196c97d4196926bf19689e57195e483819570811194d07b4194a9f681938a66f19324a89191c880718f4e10a18ce2c7618baa09918b98c2018b26e22189eabce184e84e31843d43e182077a417d900ce17c2485d1783d36c176a6ff91769b970176707ad1702826616e4f06916c4ecbb168319a41682538b161b6076161ad83315ef008615e3d4b915bf0bfb1593013315653d6815613a26155737d0154ef37814df93dc14c25be714c1c47914b7c4bd147be17a144456111425a5261405c61e13b478a213ac2e7a138eec7e1383ce791357233a12ed65f812e4a74a12e220cf12d9123b128e86e2125842a711f546a6
  | 7, 0, 3 => 0x214d3e8521234ed22118d8ca210940e420fb4f1320e5768320d1d0a420814bc4206d00e32056771b204cfb9c202b40b21ff874121fcef5c61fc3edc11fc1b3651fa9b9161f2f304f1ecad99b1ec8714f1eb180c41ea65d111e85d81f1e56cbc31e30bcd41dd9276e1daf8ff81da1c6791d8c9d641d64beba1d57bc371d1ff9bc1d1a31a91ca711891c9476741c9375ba1c92c2ce1c92106b1c8242da1c54452b1c1160c61c0377111c02e4e51bf4b44a1bd07d241bb5a1481b9b06e31b96e8611b67bfdb1b5aa7ce1b23c71b1af7262a1af0de741ae777391ae554351adb9ef91ad576b71a939d131a76b50e1a23412a1a0397ba19f944a419ed676819b9c868
  | 7, 0, 4 => 0x290449ee28e13c0c28c3a7c328a5bcb4289b69732889e91d285eafc82841347c283f1c4d2838fb10282ec36b27caf5c827bf8f032794709c27872db92773e4862730f4cd2726dd4726d06c1026c74c0626c65b7f26a6631e26385dd626144d362613f5a225f87f7325f197ff25cd4ba525c5d19325c57f8825c5372925b758692597e2692572009525044d2724d5ba0324cde72424bc32c92461748c245dbecd242a74e023dff6a623a5583523a12dde2371f15e2363757d233bab092304dae022f2b39022b12ef022b0f35f22a39c5a228741b922272e9b222383cc220099e721f5914321d6d25821d64afc21c06e8b218a64562185dc3721701c6821677a51
  | 7, 0, 5 => 0x30c2219f30b123c53044b910302c87ea302a0ae32ff39f242fedd83d2fcb51632fbca8982f9ebac62f775b232f4cd03b2f3679eb2f27a1862f2664432f1482242ef590472ee5f83b2ee0625e2e93b2902e28a2bd2e1f778a2e1add622ded15fc2ddbe4da2dd5e4112dba570b2dab107d2d4ca52a2d3564552d1a98902d189d522ceb381e2cd48a3e2c9c92ba2c35d6762c0d41422bdaea362b6d142c2b5379482b3e9fc02b351a482b3290202b08aee72aff1c0f2afbe5a92ae3339f2ada82fe2abf74ef2aa950482a9e670e2a8854e22a7f6c962a71ab6e2a6bb0532a5f79ad2a5af2ea29e3d32f29c95011297cc0d4297400f8296764912935e746292d555f
  | 7, 0, 6 => 0x3600263635db239335d7765e35ccf2f835ac22d8359ae37e35937adb358f846f358ad93f3578c84e3574f68835747c4035672767355ab1d0355a85df354c0f9d3545db6c353ffe89353f3678353cf1b335389f973532e67c350e8d4334f9221f34f6108234ea9d8534c730bd34c3851934bde41134bd92e334b3dda734aeaf24348ee9a334824e4b346c53a43457b94234206ca6341c5d5033b8069c33addc9633ac4949338c9ad2337098c0332b6cf03326806b33036e7132d4864e32c69f3432ac8e8132a7011732a1551e327951d1326f6bb332344619320f02f831eb022d31c32ec331b30d7c318eb2df316e3c87315708a1314ce6a1311656bb30e763cc
  | 7, 0, 7 => 0x3e19f81b3e1439d73e0301fa3dccbcab3d9991003d71fd593d6b71c53d5db2783d35d18c3d287a803d1bf2473d1bc8603d084ce73ceaa2313cd921923cb7623b3ca51e343c83af333c7bdb083c6977bf3c5cd0913c4e2a8a3c2cf4da3c1fe1e43b6671ed3b22fa393b1fa0fa3b1437703b02a7df3af3c39b3aefec363ae45aa93aca73853aa0418d3a9e17353a99cd023a810fb93a7a6f103a75749a3a6372fa3a39bf7f3a1fbb533a046aa1395f96ae39105115390a721138f9f1d038f267cf3887ec9c387cf53238168c5937808de0376d9978376a4f69375c328c374100aa371be0213705812c36936f6836817d763661bf25366071743622fc1e3620a030
  | 7, 0, 8 => 0x45a4de7d459a7aba456cd12f4566e491452bb7f64508ab2444efaef644eecb5944e4a4f844aae862448b5842446609b64434fede443331984430796e4421a80f43ff470e43e12dec43d4b83643cfd02243c11da543bdd24743a70ae543a00a7f437f917b43662798434d0023433fa33f43358d1542fc4e1d42f8136942a809fe4222f01b4183d824417ae7e741770975417604ab41588a4440e7045440ba3bb340b04b794092dffa40811af0407b21bb4053abe33fd89f2f3fc6f07c3fbcee743f5f549d3f5b35893f4469d73f36e8fe3f0d3cfb3efbbcfe3ef2c9303eadf8b13e8c6d673e51fe3b3e4848ff3e4191e33e2a98cc3e294fff3e2424c43e22f7d8
  | 7, 0, 9 => 0x4df9f4364daa25224d5415874d2885244d1a63024d10dd8a4ce12a5a4cd3f7294cb7f0c94cacc4fc4ca9aba14c9ad3b34c8d80f44c89535d4c7de44c4c50a0f34c36b62c4c2e2dab4c1e31e94bfbeabe4bb6a0f34bafb81c4b4480574b0d46544afc9a304aee95694ae809a44ae58e0c4ac781234a97a0934a632e214a4cbebc49f1948249b03c2b499b52454988577f495faea748be36e94887d501486b9cc54860e5784860daab485d290d47e015e447989971478a6e5d47730c8646da15bd46d9577146cd9c5046ba482546b676c446b17d4546b0993046a5aa934697f60b465ec409462ee210462698db45f4fb8345e12de845d63c9845d1eda145bd00e6
  | 7, 0, 10 => 0x553dfa355539a68b550f9dbf550d9549550243ad54bb755d547d82545478803b54768c9854617bf9545e03ba54132bd553dc75bd53c3f8a4539e25065385ac35535d66b75359b3fb53561912533d603a532862f05321ec17530dd69552f219fd52dfc42352bc8da352996d6752862178528577355270ec6c526f455b520b52db52084b2c520551e45200f47051db4f1a51d54e51513f899f510364c850f4e59f50ebe3bd509f8ca3503e3f224ffb3acc4fe884164fb750c94f961a4d4f1c75a54ee29ddf4ee201a54edbdb8e4ed160d14ec079ac4ebdb7684eac70544e94fe3a4e8225634e5d1adb4e5aaf8b4e4273d64e3c11704e31041e4e2ff7f04e142ea6
  | 7, 0, 11 => 0x5d4631575d017f515cd1d3785cc5a5c95cc01deb5c8704475c8048ac5c7c04cf5c47f1045c46243c5be7e2d45bcd8fcd5b8b47325b7034a45b6d297d5b60eb4b5b4c7f215b26af105b212d615b1b4a615b1760205b10def85b04eb6c5aef23a75a910ab55a5fdbb45a24f22f5a1eb2ec5a0964c259e37c0159dd40be59cb15b4599470e75992e51b5979ab67597460c8595bb8d4594545ac58e5b5ac58d6963f58c7437a58a0143c5874c9ef5867afd6580aba2258039e4a57db40a857c46348572f6f4b57106ce85702d8b156f51c3656c28bb956abf8c156951586565e118d560409b255f8209255eaa36555d916225593c9de556da6c7555e780a553eb09b
  | 7, 0, 12 => 0x657bce9e656b230a6564da55655e0be16555e60365559138655258d66539ae4665039c1564bb1a6864b7656c6438425e63ff7f4763de9315639d7a8163965c286376351f633cbe4b632a33a462fec6b962e9c1c962adb27b62a89ff762a0e515628be68f626ea33c6241b5f7622d0e0961f7222a61b0ce8d616dfee361597ca760d6c19560c081b7609ba710608f820d608f0109607ce25b605c2bfe602ebcf1602bde88601d50b9601407686013f4555ffed7895fef18d95fecffb25fe54eea5fae7b465faa2c4f5f6bdcae5f66e6445f6459b65f3975ba5f13a1b05f084a655eba33625e6d15f35e4e7aea5e214a9c5dfd04b75db7a25f5d7c35235d470a60
  | 7, 0, 13 => 0x6c42b8326c3ef1636c3d6c836c1cce2b6c0ecbaf6bc738476ba8875c6ba0ff156b7e56f36b78b4ba6b408f3a6b3017626ae95ce96ad9b6196ad97ffd6ac5e7666ac4e77d6a161b4269de091c69d4566969c1909169bc6b26698f8f7769548d2468ff83c268f8c50e68ddca6368c3f13e68badc8d68ae8ce6688509b668571614684c91f468377a746821124f67e20fe067d6a2c867d0bec567c0882367bd3c8767adb0e3677efbbb67796d5c676ca753676ae4a96767de4a67539f086742a7d3673d759c67108e5267068df5670425a966f41fba66e46e6666c18c79668c7880667cc29c6678e4496658320f6653a3d9664bccff664a2e4d65ff6a2e65f15376
  | 7, 0, 14 => 0x7590c5d1758859847579e848753c1a0574f44fdf74cc57067480d2477440f11773ff5c9c73b7125c73b111937366785c73536d5d734c9f767334bc72729b2e07728af817722f623071fe46de71ece1b871ebea7c71e3fb2171d3a02871cfa26f71afb552715adeae7124adf070f7e40370e8ab9670e3dc6970db175f70cd5ae470cbec1270be61217050cc06704a65906fec830e6fdc58a56fd9346f6fc2e2136f43ea976f36b6b86f309df76efc04706ee55b736edf7c9c6e9f61156e9604b16e83e6036e74d7686e65169f6e3433cd6e09f0ed6e02eec26df0fec26deaba066d71deff6d4f0de56cf10f6b6cee2f236cdf4af96c873f416c6b07056c453e1d
  | 7, 0, 15 => 0x7eee8de77eeda02d7e7ba7e07e5eb0787e0700227dd7bdf57dc7732a7db6488a7d87996f7d6e9ad67d4f5f387d0c8cbb7cf9986b7cf70da37cb55eb97c85f1297c2e85b57c2395e47c1ebfe47c11f4fd7bac4d1a7b6ea85d7b5f89e47b3164647b2108ee7afac6a87aac77f87a98c0657a831aff7a5716df79ef6f1079c53e6079b4a8397999a798796641d97941415e79227995790cff8978ebe05e78e4f5a278de9bf378db4aa8789e7b0c789de8b6788c2ff57860e639785ddb12785978f078204d0577dbdffd77c666a777496a09773d6e7877323623771e7005770282c076bbf7e3768d3e1e765f42f5765a45a97623de9a75c905bf75a337077592aa55
  | 7, 1, 0 => 0x865fd91e8626c9b8861a5c81860fc652860c2be685fefde185cf5b4385c3ded685b3ccb185a4cbd185a3bc0f857f37778577d8858575445085721f6a84fccbd184f3169584e9fccf84cdc56e84a52c198467a9d1845b963e8428a1a9841cbaf9841371a884013fe783cbd3c083b31a7d8394a9d4836650848363c3f683490ab0833c7e948315c73282c9e5be82b6236a82b0af5c824ebd768236f38f81db8c7a81a9776c819c32b2819b4b0881704eb8815abce6812d517a8128f3f38119fa0280b8c97c806c43f780458e7c8032d812803070bd80231ba08015343d7ffd68267fda735e7f7cb5047f6c93bd7f34c9357f348d087f2619507f21f4997f1dbf9e
  | 7, 1, 1 => 0x8ed3aa658ec7b0ec8ec451bd8eb6e2ca8e902fad8e6302838e3d634f8e3270a98e032ec18dff31bb8da850658d8425078d7aed198ce6acb38cd297818cbb13f68cb5433f8ca552fe8c8dbcb08c89107e8c8473f68c6c2dc88c3afb688c096b588bd6858c8bd60d088bb2b8e58bb1328c8ba1dbf28b67488a8b414eb68b34a47b8b33bd8c8b1b39fd8b04dcb88aeaa6c08ac1d3288abc62618a323b078a1656d289fc41b18998ffc9895dfe56895dd9a18952d794894e9e1a88ed27e288d4431e88c8f86088b6d63c88a972778869664f885bec338844fe92883b20ae8833f5518826a03487bd1ad887b698fb873c288b8738119c8737715887299de486dc7d57
  | 7, 1, 2 => 0x95feb81b95c7433b959ee858957a19a9956af0e49556de689556175c95546bd095522fc3954d6df6954c91e4954a07bc94f20c5594ea215094e2b7a694ad7817949a11839493f2d89492ddb294726a869466b5f39437159c93d352ba93a98caf938b73e2937ec4bf9350940a934ff48a9340ec709323bdfe92fb6e8992f9ae429295b59292646ea3923924e7923619c092352ad9922628d2920b519791f26bdb91ecb7d991ea244691d7069f91cac90e91b813ea912299f9911fadd9911bcb6190dec3a290a6310190a4b5609073fab89061903f900e35ef900cc7b68ff96af68ff3586c8fbfa2c28f8b65ae8f69047f8f2f8aec8f295bc48f088a868ed4acb6
  | 7, 1, 3 => 0x9e33d4ec9e0665df9dfc23f69df4f9a79dcf7e389d3e8f329d3df8079d1bdcb79d14bd429cf729b79cee05e09cebfdea9ce83a339ce503cd9c926e6c9c44bee19c26fc249c14133a9c0a3ca09c0635639c029e899bea8a5f9bd4a9df9bca85189b65def89b4c7f429b3cd8b89b2dce579b0e75849b0132a19ab8455a9a9a44729a91b62d9a8bf7aa9a67f3379a43ff869a1dcd2a9a1c8ce899b8363499b7a33f99a91c42993f19229937be1a991a12f1990ffb6b98fd6fd798f5fe4c98c6cc9598a9b59598a41970989a6e7d9897bb259836ef2697fd6b5a97d1cea79781008d976c89139765e29c9752bd69971d87a9971c539996d01321965c958996088129
  | 7, 1, 4 => 0xa61de4fea5ef34eaa5ef21d7a5cc6a95a59a240ca5904268a57de989a56dc7a2a54714f0a54213c6a5329562a51841d6a4fbd245a4f94880a4f18a74a4b7b929a497a2f7a46a78e5a4626ff5a427599ba406231da3b74bbea3a12717a39c9fa5a35de210a333f748a30914bca304b735a2a0d34ba28e7069a27497a3a241a4fda23d3a6aa23614c8a22151bea1b636a0a18ed7a9a13bd84ba13530fba10bf6fba0eca533a0e18795a0cfbfc5a0855b69a06bbb55a03a73baa039bc45a028cb9ca01eb416a006866a9fd634209fa3366c9f5c29a69f56ae149f210c3d9f0c24059eb1c3c19eadcef39eab00239e99c5e79e8fb9389e6f30de9e56811f9e366023
  | 7, 1, 5 => 0xae603738ae49084eae45eeb5ae43e66cae08364caddc392fadd89541adbb5be8adb0dd5dada685f3ad5e09e2acebc603acbf819aacb391a9aca5b365ac584a90ac3bcc57ac203c81ac125034abe218e6ab7128a0ab65e7feab49c28aab377bdcaaf36980aaaa5796aaaa4cddaa4f8b80aa452991a9ce7a41a9c34916a9b19c58a99fc019a99d0106a9925c3da98165a6a9536d8da927f774a917ebcda8cd2faea8aceb64a89c906ba888922ba86f31f2a85b9c23a82e2574a8255610a81ce379a7de7870a79c234da78974f5a7752a14a76199bca7352dc1a73369e3a715035ca6b0199ca6ae84b7a697cd48a66aaf8fa65571c8a64e8b36a6365dcfa61f1203
  | 7, 1, 6 => 0xb60754e6b5e0fc76b5ca4c10b5c668b8b5b77e2ab5b461f1b5902909b554a760b4f848e5b47aa5bdb3d27f62b3c24a54b390f841b34d471eb33dffa7b3156a73b3129c5ab30f35e5b2a50143b2a359d7b299699db28f99edb26a3914b23ccd8fb22e5d43b21631a8b20248e0b1f7fbadb1ea3e9eb1e9f931b1b90588b1838f47b165fce9b165918ab1200722b11cca9ab0e12fb9b0e0351cb0c810ccb0772feeb0443e12b03e1077b03b1c5fb00c731fafedb434afe9653dafdef203afd5efccafb5dacfafa392a4af957413af7e5c2daf552038af359018af3327ccaf2bc6ccaf2022c0aee9412baedd696eaed822e5aec114e0aeb8f7e5aea8cd7caea402e0
  | 7, 1, 7 => 0xbde508e2bdcd0c10bdb59ca2bd5c6ceabd56c4b9bd481cb7bd2dda18bd197d31bd189bfabce0ee17bcd904bbbc8cd216bc7ca571bc7607b4bc6f13e9bbfcd59abbf2c6b6bbecc5edbbe6e79bbbdba126bbc7133abbbb2494bbb4f983bb806acdbb2895d7bb151e4fbae435a9bade97aebab4727aba6ddb7aba506113ba47a138ba3a7919ba1aaad3b9f8020cb9cec865b9c6ad7bb9bb368db9b21282b9713336b941a5deb91f90c3b8fa157bb8f867cbb8db78a7b8db3bf4b8997bc3b8572b6cb7d57de9b7a8f6efb758a4ccb749d50ab73008afb6fad8c9b6e2d1dcb6c4937ab6a0caf9b6837379b66db2f5b645a547b63ea31cb63e8ff7b6358400b6187b80
  | 7, 1, 8 => 0xc6aa6d36c69e7be3c5f87b2fc5ca4838c58557c3c532c1fdc52a3a92c51c6308c4f3c18dc4b98e87c4775350c46d232dc43bc065c3e22da4c3d59e60c3aa5cb7c38bd864c3827a75c3753fb4c35cbd48c35a0575c34759aac319e2a8c317b5fbc2df77a7c2daf057c26e9b1ec22b236ac1fd94bec1ed227fc1de7afec18ac36bc17f1d37c17e3825c158b17ac14db770c1489010c124aa0ac11a504dc10c93d2c10593c9c0e7a473c0e46e0dc0df4715c0c3705dc0aa5d7fc0a7fd53c091d8acc088584ac085c7cac0324461c02871dec026c9e4c0178e5dc00f909ebfcca165bf851e63bf75efa6bf309476bf1361a9befb92b4be9f0fa5be54e56bbe159bfb
  | 7, 1, 9 => 0xcdfbffc3cdd100f8cda6d537cd8357a1cd6d5593cd66305ecd52d7cdcd43454dcd359d45cd2585cccd18a10acd083060ccde85f8ccc52a17cca35e2bcc86101fcc7a28d9cc684041cc67d89bcc4e89a5cc4309eccc2a050dcb9f0c58cb8b3933cb7d8f0bcb7d4e04cb76685acb50d9e6cb349801cad7f953cac05273caac0d7dca54dc08ca546425ca537f57ca04774eca011952c9f3d846c9e8e892c9c45eccc98e47ffc972257ac966dd57c93615f1c92b194cc90dcec6c8da031cc8c1c799c861da35c81b12f1c8144c74c8122111c7e4a5b2c7c6f986c7b9162ac7b58e37c7abb727c7a82444c775e74ec75da8f3c758fffbc72a8082c71fc81ac6d90c65
  | 7, 1, 10 => 0xd5d51448d5a576d8d547dd01d532849fd52c7513d51f7162d4f0f799d4468e80d43a869fd41890d1d3ff0dd7d3f580b8d3d3e2c2d3c82579d3c5c492d3b5450fd3a2fce4d394c8cad379eceed35f5289d358ca24d33a7929d338bdb8d3265b1ad31e59f0d2d79b92d2d4b27bd28c47b6d271ba71d257e8b9d248728ed24558f5d23c8d64d23889ebd22df939d21dd0abd210ee89d1d4b423d1c7e360d19e99b9d1967357d16ca0bed130e37ad10eeb0ed0f3126dd0eed897d0d31777d0cfa936d0bc3a17d0b92cb0d0b2fbe9d06fa9abd062548ed00843b7cfffa44ecfb93b24cf65523ecee52cedcee27a34cedaf033cec333d3ce87419dce16f6e3ce07748e
  | 7, 1, 11 => 0xdd2587bbdd193586dcf66048dced4dafdcc898cddca985b1dc8e32f7dc7a461adc46d9ccdc468c75dc15be7adc14de50dbff3966dbaaaeb5db3dab48db00be62daf1b18fdae3a970dabcacbbda9544d8da803c01da61dd2cda067d68d9fa4268d9d3059ed9c9b650d9c6cb2fd98f9349d984ba31d95b6233d95402cdd93d87e6d93cbd2cd9137c0cd8efac19d8ed43cdd8d6d0a8d8961c4ad8785702d841a5abd823951fd808765ed7fb8f7bd7f5b952d7f0e012d7e5e446d7c698f7d7bcbfb8d7b10725d75e8d0fd74112a8d73f0427d734ab98d6e7a459d6e2b88bd6cc8efcd6b13ff8d69eb6ddd698d3ddd6827ea1d65e32c6d6363344d61a4d78d5e404bf
  | 7, 1, 12 => 0xe811424ae80761dfe7deeac6e7bd6f55e79d5b38e78ddb80e77177a8e75cc097e73ba6c9e72b167be7253829e6ed781be6c57e21e69551c9e669c3c7e626c786e5f2c308e5b161a2e5aec729e55cbfe8e5589c89e54ed277e52648e8e4b843a0e4a9c7bfe4a63fcce46f7636e41a242ee38f2d78e37f5dabe3247725e3106e12e30df211e2d32023e2c0314fe2b96760e2b50a36e2a3a791e283c095e2785dd5e27552aee26d9beee1f74cd8e1f35799e1f09bdde1e47322e1410c7ae0e569efe0d36f7fe07f22d5dfb96348dfa83d6ddf382235df130c3cdf0bc77bdeeb28edde9849e3de4dbcd2de49630fde3e9d1bddb2f137dd5c2e0fdd580b4fdd29ad5e
  | 7, 1, 13 => 0xf0a4ef4bf07b02c5f05ab396f04f03a7f041e202f0296f4deff1ed26efae6c75ef3e65bdef2e9b0fef201bafef10c5a5ef0b74aaeeea3911eea663e9ee894606ee459ecdee343295ee2ae944ee18b783ee12c54dedf34286edc3c90cedacebaced8d83bded7dc820ed2d3eceed27dc13ed105b43ecde4c59ec87d0bfec83f7cfec6e369fec663512ec41d777ec309f4aec0e5b5debbb66bdeb9304d6eb7e1f2aeb44c916eb406b8feb222eefeb0a72d0eac36ef1eaac3b0beaa78c21ea8b3a97ea6a2fdcea5d0618ea40e8c9e9f1eafae9e08265e9942c9ce9840b59e963f38ee9430aa7e935373ae9060583e8cb3923e8bab8e2e8b32ee1e8a202a5e881f5cb
  | 7, 1, 14 => 0xf8dbc959f874971ff848f742f8456696f82ca004f821a1bdf81aa65df8037aa5f7f54a0af7813a1af7717167f768559bf760f6a9f7568747f713d73ff6fb34a4f6f4ac3ff6e481d6f69beb92f68e4a3df66671a5f65316f9f60e6587f5ed84a4f5c74da0f5b82fb1f5b4f1e4f542c7dcf4fa1d32f4d0f0ecf4c930adf4b303e2f4a423e9f42bd9dcf4211c37f3f82decf3caa704f3b02e20f367d1f7f32a4c71f3031826f2d02965f2cc7d86f2c6f385f280ddebf27b317ef276b0dbf21bf636f1dccc71f1ce1097f1b84c83f195bf85f1784439f16df488f165d328f153f5cff153a027f136cbbdf1350785f12036a8f1195156f0c49457f0be3d76f0b6b375
  | 7, 1, 15 => 0xffff0634fffea3a6ffc4e429ffb3f673ffaa18f5ff945926ff640b3dff57afedff3d1588ff123350ff0402b5fedd3cb7febb539efe971ab2fe82066dfe7e7e7afe770e46fe6faf54fe69f639fe64aba8fe559d87fe24198cfdf4a2a0fdf0164bfdeaed64fd9d02e8fd8afa16fd676c26fd536d0dfd43650bfd3c276cfcef1659fcecae0dfcc3aa8ffcbd4b15fc71364efc4e4806fc20dd5afc019be2fbc7748afbc1bc8dfbbcb1d0fbadfa39fba57992fb88fb78fb3e6e67fb292497faf397f8fa9321d7fa7457defa25ad8bfa11d0d1f9554771f9552142f93a5051f92dd199f9208f7cf8ec2452
  | 8, 0, 0 => 0x33c0c90032db8bcc32c96d1e3265f7993263f9b831b30d7c313507a62dbb214e2c33b3742b5379482b384c952ad2a9b428a5bcb426c74c0624c639ab24ba3ed623937e8521b447422136416c2085ba6f1d42c60e1c8d2d2f1c3bd1d81c02e4e51b54b30e1a52295d1a44266019edd2a918097fbf17c02815179ba5681742223f1723715414c25be71444561113b478a212c7ac7e12a036a6126ac74e116093e11106cdc710dfc44d10bcd6ce0f970d4b0ecd7e060e62c7b30de1f81f0db3a33c0d359d660cd4669f0c041eab0b15b6280af1fed60aeb16150a9f6c0309efeca509d69a7108cb2a3507852a5a07540f0806940e5504e56c62020fff7e01737d88
  | 8, 0, 1 => 0x61318505611f665760f5b64260965ffb604bbc7e5f938c875e6214035dfdbd4f5c0fa18f5b919bb95b7badac57c4634856cdce4e56a65876567ab1f4564fc878562852a055b00d5b552f3dc753fc1e265123e019506e3a1a5046c4424fc5f4ae4f01e97c4ef5be6c4ed13bb34dcff4e94d2e4be94cae6cf64bba97004b8b4c2a4b0d46544a258bc548a30f48465f78f845d1eda1452bb7f644aae86244333198436b49e54307780a42ed440f42a809fe424b4c7341e4c453417604ab414c6349412582f0411da5b740f62fdf409f8ab43e0da1cd3d9f9c853d41059b3d0bb5b13c8ae61d3c79d3023a97ffb8392a1219387f886f380b1a5e36fa74a835db2393
  | 8, 0, 2 => 0x93a06ffc93080b4c92e1305c928a0576923c767590dec3a28faa1b9f8f95124e8ef8c9ee8ed4acb68ea1b5b78e3118c78cb80d3c8cac4f718ca877188c53b6888c27a7848969c35588c3fb85881c49d6861a5c81857f37778513d73f84d0ab2d824ebd76816c4ed88128f3f37f82a65d7f1e4fa97e67abc27d57e2b57c1b05047a5bb7ea79fc07f67937382478e4f5a2779b444e76e1ad9c76cf8eee7673e45e7663a7c676518918764401fc74e1c74f73e927a1735a86ea72675a3b724ff73c71e3fb2170821968706ffaba70227bd6700149d46ee55b736ea16f056d6ed5cb6bf5ec2669999003685bd80f67a3692b67360e8c655e0be164ede0156438425e
  | 8, 0, 3 => 0xb9c192a0b940c30cb93140c9b800f691b7ba7b55b535655eb41a71fab3c7f7b0b399a266b0b06ff8af8e44b8ae9fb3e9ada97aa9acab5189aba98afbab858806ab75d046ab2b8525aa70fe3da99d0106a96bd003a8fdcabba8aceb64a7697e48a7420870a70cc526a61c3eeda54e664ba549f6c7a4c9dd97a4c92733a451de4ea3d3d878a304b735a26835d3a203df1fa1ea2ffda185d949a0bdc985a08ce91f9df24a1a9d717a869d3b975e9cf9c3bc9c26fc249c08a19f9bca85189ba44aeb9b87d20b9b4c7f429b237b579b0132a19a80d3c49a02cdee99661cd897a2ad88979476b8977c745d97181da995f96264956af0e494ea215094213f909406f9df
  | 8, 0, 4 => 0xf29f8f19f1de1c4af1dccc71f1af9c79f179c596f13196a3f029aa86eecba126edacebaced71f1d3ed03ec8becf3ebfdec85e6b5ec663512eb500845eb406b8feb1c83beeacf38b1e9f6ba3be8a9e5dbe892c0b4e7125d9fe6c3db03e6a45857e62388c3e3a3bb46e27df1c3e2182b15dfb8f64bddae2572dbff73e2db747efcd7c1c93cd753c3f4d519e096d5053b33d4034cd6d3f99519d3ba0645d271ba71d0c3bd27d0bc3a17cf7791e2ceca0d03ce904c00ce63f497cb78c448cab0ad57ca5896e9ca1e5d15c9ad816cc77d5d96c76b3ee8c6579413c634e73dc3753fb4c02126d4c016ba9bbfa320febdb79b24bb553d6fba7a062eba53eca2b9fc0058
  | 8, 0, 5 => 0xff89d50dff652815ff257e59ff123350fe87aae0fe5a0e72fddc089cfdb187fafc453af5fbadfa39fb1f7172f9d0f0ddf8ec2452f8037aa5f7fa7a3ef7a272fef779aaaaf63e7977f4ed8e48f4da989ff3f2f90df3c7c4c5f36e4cfcf303e5cd
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x84140000002105000000084140000006101000000184144125440303000000084040000002101
  | 6, 0, 0 => 0x841400350812070000001841000000021000000000840400018122030011410481c00104402070004110080c00425082070000203880c000004110b0000202880c00000061050000204881c000081220300000018410000000a10800000300410000000a10b0011510081c00008062030000201881c000000e107000000084140021484207000d520080c000000e1080000002842c00000021070000003842c0020480207
  | 6, 0, 1 => 0xd420481c00000061000000002840400450412030000203880c00000c0104000d410481c00000121070000002842c000000e10b0000001840c000280e2070000202881c00001001000000000840400000021010000201881c000180e2030000a04881c00000021040000003841000000061000000002842c00000061070011410481c00000061040000003840000214842070005520081c000000a1030011410480c0035041207
  | 6, 0, 2 => 0x5420481c0035081207000d520080c00000121040005520080c00000021070010140081c00350812070000010442c00454c82070000a04880c0000012100000d420481c000008410700000038420001508120700000008400000000e10b0000003842c00038122030000002841c000000210400000008400000000e1000000603881c000000210400000048420000000e10b00000400400000180a20700000018420000080a207
  | 6, 0, 3 => 0x8521081c00000061040000604881c00000c51080000002842000000801070000001840000008062030000000842000000c01040008120081c000000a1000000003842c00000021040005540081c000000a10300000008410000000a1040000202881c00000021030000e04881c000280e2030000004841000008122070000020440c000000a1000000010442c00405002070000004841c00000021040000010442c0010440207
  | 6, 0, 4 => 0x48420001550020700000008414000001210b0000603881c00000021080000000841400000061070000004842c00000021010000203880c00350812070000010442c000000e1000000000841c000000e1050011410480c0000006107000d420481c00000121040000004842000350812070000003842c000004110b0000000841c00415042030000003842000154802070000202881c000000e1070000003841c00000c0104
  | 6, 0, 5 => 0x8410000000a1040000001841000001001000000204881c00250412070011410481c00354842030000e04880c00204802070011510081c00000121040000000840000000121070000004841000454802070000004842c00454802070000001841000000c010400000008420000000a1050000002841400001041080000000842c000000610000000038410000000a1040000a01881c0000012104000000284200015500207
  | 6, 0, 6 => 0x11410481c00000061030011410480c00154802070000002842000411052070011510081c00000c010400000028420004150420300000300410000000e103000000084200002812207204d5200c0c00350812070000000840000104402070009510080c001004120700000008400003504120700000008404000180e2070000002840000000c01040000004840c000000610400000008400000000a100000d420481c0000006105
  | 6, 0, 7 => 0x8404000000a1040008120081c00350812070009510080c000000a1030011410481c000000a1000000002842000000021040000002842c000180a2030010140081c000001210b0000202881c000000a10b0000201880c00000811030000030041000000061000000602880c000000e10b0011532081c000000a1080000010442c00000021050000201880c000004110b0000002841c000000a1070000010442c0000100100
  | 6, 0, 8 => 0x4841c000000610500000018400004240e20300000048410000080e2030011410481c00000121070000602881c00204802070000000841000354842030005520081c00000061040000000842000000121040000003841c003544020300000410420000004110b0000001840000354842030000000842c000000210b0000204880c00150812070000002842c000000e1000000a03881c00450812070000021041c0000002107
  | 6, 0, 9 => 0x2840000254402030000003841400000c01040000004841000000021080000203881c000000210400000008410000080a2030000000840400454802070000604881c000000210700000028410000000a1080000000840400415042030000002842000150812070000020041c00000841070000002842000155002070000030041000000021000000000841000038122070000010442c000000a10700000028410000000e101
  | 6, 0, 10 => 0x11520081c00000021080000002841000350812070000000841c0001812207000000284100000002104000000084100041504207000d510080c00350812070000600881c00000021000000001842000000021050011410480c000000a1050000a03881c000000e1080000201881c000000a10b00000008410000000e1010005420481c000000a1040000e04881c000000e10b00000008420000080e207000d420481c000000a101
  | 6, 0, 11 => 0x30041000000021030005520081c00415042030000002841000350812070009540080c000000610b0000a04880c00155002030000001840400000061040000002842c000000a1080000000841c000000e1000000001842c000000210000000038400000000a10700000300410000000e104000000184000000806203000000084000040500203000000184000000012103000d420481c000000a101000000284140045440207
  | 6, 0, 12 => 0x18420000080a2030000002840400008062070000000842000000c01040000002840000000121000000a03881c000180a2070000004840000028122070000001840c000000210b0000a00881c00000121080000010442c004240e20300000048410000000a1070000202881c00001001000001521080c00000061010000e04881c000080e20300000018414000000210400000008420000280e2030009410481c0045041207
  | 6, 0, 13 => 0x4110081c000000a10b0004110080c00000021040000004842000000801070000603880c00000061000000002841400000121080000000841c00425082070009540080c00000061070008020481c004508120700000048420000000a10b00000008400004544020300000048420000280e2030000010442c00000061040000031442000001001000000002841c00150812070000604880c0000002101000000384140000002100
  | 6, 0, 14 => 0x2840400000c010400000028420000080620300000028410000000210800000038420000080e2070008120081c00350812070000000841c00000021070000002841400028122070000002842000350412070000000841c00255002030000204881c00450812070011410480c00000061040000204881c00000061000011420481c00405002070005432481c000000a1010008521081c0000006100000d420481c0000006108
  | 6, 0, 15 => 0x841c000000a10800000008400000000210100000008414000000210b00000028420002048020300000038404000280e207410d4414c1c000000a1080004110081c00415042030011532081c00415042070000000841400000121040000000841000000c51080000004840000000021050000002841c000080e2030000000842c00008062070000201880c00000021040000000842c000000a101000000284140020480207
  | 6, 1, 0 => 0x11410480c00000021080000604880c00450412030000000841000000021000000001840000154802070008120081c00000021040000001841c00405002070010541080c00415042070000a04881c0025041207000000484200000012103000d420481c000000610b00000028410000000210300000018404000001210b0000002840000204802070000602881c000000a10800000300410000000e10700000430400000000a104
  | 6, 1, 1 => 0x11420481c000000a10b0011410481c000001210b0000001840c000000210000000018410000180a2030011520081c000000e1040000203881c00000021010000000842c000180a20300000028410000000e1070010900880c000000e1000000e04880c000004110b0000603880c000000e1080005540081c00350812070000202880c000000a1040000004841c000000e1030000202880c0045041207000000084200000006100
  | 6, 1, 2 => 0x38420000000210000000018420000000210000000018404000180e2070000001841000000021040000202880c00050c92070010942081c0000006107000d420481c0000002104000000484100045041203000000384200000002101
  | 7, 0, 0 => 0x2841c000000a1030000001840000000801070000000842000001011070000041041c00001091030000030041c00001041070010541081c00000c51080000043440c000004110b0000004840c00000061030000001841c00000021030000032041c00000021080000010441c00154802070010942081c00000061000000020441c000000a1070000010440c000000e1000000004842c000000e103000d521080c000080a207
  | 7, 0, 1 => 0x4841000001091030000002841c000000a1070000002842000000021010000003841400214842070000003840c00000021040000002842c00000121070000004842000000c51030000002841000028122070000202881c00000c41070000202881c00000801070000001840c00028122030000002840c000000210b0000003841c00000061040000000840000000021070000001842c000004110b0000004840c0000002103
  | 7, 0, 2 => 0x1842000000061030000010441c000280e2030000000842c000000e1030000003840c00000061070000003841000000c010700000018400000000a10b0000030041c00350412070000003840400000021000000004841c00001051030005540081c000081220700000018400000010c10700000028404000000210b0000003840c00000411030000001840000008122070000001840c00000851030000004842000000c8107
  | 7, 0, 3 => 0x2840000000021040000002840c000000a1040005520080c00000021040011520081c00000021080000001840c000001210b0010942081c000000210700000008410000000210000000028414000000e10100000028404000000e1010000000842c000000e1080000030440c000004110700000400400000000210300000048420000000e1070000002841c000000a1070000002840c000010c107000d520080c0000006108
  | 7, 0, 4 => 0x41440c000001210300000018400000010c1070000001841000000061070000000842000001011030000001840400008122030010942080c0000002107000d420481c00000061070000000840c00000061080000004840c00000061070000001840c00001001070000000840c000000a1040000000841c00000061040000a04880c00214842030000000840000000061000000020041c0000109103000d520080c0000006103
  | 7, 0, 5 => 0x2841c00000021000000004842c00000401070000204880c00000021070000030041c00000121080000043041c00000021000000000840000000801070000603880c00038122070000204880c00001041030000020041c00000121040000002842c000000a1030000001841c00000c41070000002841400000411030000021041c000000a1030000042041c000080a2070000603881c000000a1080000004842c0000012100
  | 7, 0, 6 => 0x3842c00000021070000001841400000121080000010441c00000021070000000840c00000021080000020441c00000121030000002841c000000a10700000008400000000210400000008420000010c1070000002841c000280e2030000000841000000801070000004841c00000021010000002840c000000a1030011410480c000080a2030000000840c00001011030000000841400000021000000204881c0000002103
  | 7, 0, 7 => 0x8400000008110300000028404000000e1000000030440c00405002030000000842c000000610b0000001842000454402070000204881c00018122070000000840000008122070011532081c000000e1070000000841c000000a10000000028400000000a1000000002841c00001091030000003840c00000121070000020041c00214842070000001840c00000c81070000032440c000080e203000003144200000006100
  | 7, 0, 8 => 0x842000000c41070000000842c00000061000000001840c000000a10b0008120081c00000061030000030441c00000c81070000030440c00000811030000020441c000000a1070008120080c000000a10000000008420000000e1070000000841c000000a1030005520080c000000e1070000002842c000008510700000048420000000e10700000300410000000210800000028420000000e1080000203880c000001210b
  | 7, 0, 9 => 0x18420000000610300000018400000001210700000018414000000e1000000004841c00000121030004110081c00000c81070000004842c00000811070000002840c00001001070000e04880c00000021030000000842000000021040000001841c000000a1030008521080c00000c81070000020441c000000210700000300410000000e1030000000841c0000085103000000384100000006107000000284000000006107
  | 7, 0, 10 => 0x10041c00000061040000042041c00000061070000001840c00155002030000004840c000000a10700000018400000000a10800000028420000000e1040000000841c00000021000000003840000000021040000000840c00000021080000000840c00001091030000002841000000121070000002842c000000e1080000002840c00415042070008120080c00000021040000003842c000000a1070000001841c0000105107
  | 7, 0, 11 => 0x42440c00000021000000003840c000000a1030000002842000000121000000030440c00450412070005520081c00000121080000000841000000411030000001840c00000061010000000840000454c82070000004841c000000a1030000000840c00001091030010942080c00028122030010140081c000000210b00000048420000000e1010000002842000001091030000003842c00155002070000042041c0000109107
  | 7, 0, 12 => 0x8420000000a10b0000000842c000280e2070000001841000000121040000001840400000021070000001842c00000121070000003840c002148420700000028420000000e1000000002841c00000061070000003841c00001091030000010440c00000021000000000840400000411030011520080c000000a1070000000842c000000a1070000021440c000001210b0000031440c00000811030000002840c0020480203
  | 7, 0, 13 => 0x20440c00000121070000030041c00000121070000021440c00000851030000003840000001011070011520081c00000851030000003841c00000061040000032041c00000411030000000840c000000210b0000003840000000121070000002841c00254402030000004841c00038122030000021441c00000811070011532081c00000061080000004841c00000021030000002840000000121030000004840c0000002104
  | 7, 0, 14 => 0x841c000000a1030000000842c00000061070005520080c000000e1030000021440c00000061010000002840c00008062070000001840c000000e1030005540081c00000021030000201880c00000021050011510081c000000610b0000000840000001081070000032440c00000021000000030041c000000a1010000004842000000121080000001840c000000210b0000021041c000000e1070000a03880c0000012104
  | 7, 0, 15 => 0x20041c00000061080000000841000000021070000030440c000000a10b0010140081c000000a1080000000840c00000811030000a04881c00415042030000002841c004050020300000430400000000e1030000000841c00000061070000004840c000000a1040000000842c000000610b00000048410000000a1040000602881c00000061030000042441c000000e1070000000841000454802030000040440c000000a10b
  | 7, 1, 0 => 0x1841c00000c41070000000841c00454402030000000840c0000002107000d420481c000000210700000008420000000a1080000000840000000c41070000021441c00000851030000040440c00000021030000000841c000000a1070011520081c000000210b0005520081c000000a1000000031441c00000121000005520080c00000021070000000840c004150420700000018420000000a108000000284100000104107
  | 7, 1, 1 => 0x42440c00214842070005520081c000000a10b0000004841c00000061000000021041c00154802070000031442000000121030000010041c00000021070000021041c000001210300000028410000000e1070000003842c00000021080005540080c00000061070000002841c000000e1000000201881c00000021070000003841c000000e1080010140081c0000012107000d420481c00000061040000020041c000000a107
  | 7, 1, 2 => 0x3841c00001091030000003840c00000021080004110080c00000121030000004842c000000e1010005540081c00000021030000001841000155002030000000840c00001011070000030041c000000e1000000004841c00000411070000000842c000004110700000028400000000a1070000201880c000000e10b0000041440c00001091030000002841c000000a1080000020041c000000a1070000002840c000180e207
  | 7, 1, 3 => 0x20440c00001001000000041440c000008510300000028400000000e1080000002841c00000811030000004841000000121070010942081c00000061040000000841c00000061000000002841c00000061040000003840c000000a10b0000001841000000021070000032440c00204802030000003840400000121070000003841c00000121030000000841c00000021030010541080c00001051030010902880c0000012104
  | 7, 1, 4 => 0x3840c00000811030000020441c000000a10800000018404000000a10700000028404000001210b0011410480c00000411070000000840c00038122030000042440c000000a10700000038420000000210400000018400000000a1080000001841000001041030005540081c000080e2070011510081c00454802070000031041c00000c81070000021441c00155002070000002841c00001001070000e04881c0045480203
  | 7, 1, 5 => 0xd521080c00000021030000000840c000180e20700000038420000000a1040008120080c00000121030011520081c000000e1070000042440c000010c1000000003840000001081070000002842000001041080000003841400000061030000042441c00000021070000032440c000010910300000008400000000e1030000000840c000001210b0000000840400350812070000000840c00000021070000040041c0000006107
  | 7, 1, 6 => 0x841000000061000000002841c000000a1070000042440c0000006100000d420481c00000121080000032041c000000610300000008414003508120700000008404000000610b00000008420000000210700000430400000080a20700000018400000000a10300000008420000000a1070004110081c000000e10b0000032041c000000a1010000202880c00405002070000002840400000121040000002841c0001812207
  | 7, 1, 7 => 0x1840000001051070000010442c000010d1030000003842c000180a2030000004841c000000e1030000031041c000000e10000000008410000010c1070000032041c00000061070000603881c000000a1050000000841c00000121030000000842c000000a1080000020441c000000210000000028420000180e2070000000840c000000a1070000001840c00000021030000000840000000021040000001841000000c5103
  | 7, 1, 8 => 0x1840c000000a10700000018400000000e1040000000841c000010c10700000008414000000e1070000000840c000000e1000000004842c00000021030000004841c00000021070000002841c00000061080000004841c00000121030005520081c000000e10000000038414000000e1080000002841c00000c010700000314420000000e1040000041440c00450412070011510081c00000061070011510080c0000040107
  | 7, 1, 9 => 0x1841000000c81070004110080c00000061070000000842c00354842030000000840c00000061030000001842000000021030000003841c00000061030000002840c004544020700000048410000080a2030000020440c000000e1000000003840c00000121070000001840c000280e2070000001841c00000c510300000028420000000e1080000043440c00000061030000043440c00000811030000201880c0010440203
  | 7, 1, 10 => 0x30041c00000411030000002841c00000061040000003841c000000e1080000042440c00000061000000003840c000000a1070010942081c00000c910300000008400000000a10500000008404000000e10b0000001841c000000610300000008400000000210000000400400000000a1000000000840c00000021070000000841000000411030000602880c00425082030000001840c00000401070000004840c0000002107
  | 7, 1, 11 => 0x1840c004240e2030000004841000000c51030000004842000104402070004110080c000000a10400000048410000000610300000008400000000210700000048410000000e1030000001840000000061030000003841c000000210b0000002841c000008010700000008420000180a2070000004841c00000021010000002840c00000021040000003841000405002070000004840000354802030000001840c0000104107
  | 7, 1, 12 => 0x8410000000a1000000002840c000000a1030000001841000000061040000003841000008122030000001840400000121070000010442c000000a1070000001841c00000021010000010041c00000021070000043041c00214842070000002840000000021030000003842c000000e1030000002841c000001210b0011410481c00214842030011410480c000000210300000018410000000a10b000000184040010440207
  | 7, 1, 13 => 0x2840c000000210b0000003842000000021030000002842c00001041030000602880c000000a1040010942080c000000e1080000002840400000121080011410481c00000121070011410480c00000021080000021041c00028122070000a03881c00001011030000004840c00000061030000001841c00001001070000000842c00000021070000000842000000c01040000204881c000000a104000000484000000012103
  | 7, 1, 14 => 0x1521080c00001091030000001841c00000c91030008521080c000180a2070000004841c00000021070000002840000000021080000004840c00000021070000602880c000000a1070000a03881c00000061070000010442c00000061000000203880c000000e10b0000003840000000c41070000004840000000801070000002842c00000841070000604880c00354802030000000840c00000c010700000008400000004110b
  | 7, 1, 15 => 0x602881c00000c11030000001842c000080a2030000030440c00000121030000002840c00001081070000021041c0000812203000d521080c000000e10000000008400000000e1080000040441c00038122070000000842000000851030000000840c00000c91030000000840c000000a1000000000840000001001000000002840000214842030000040041c00000121070000001842c000000e1010000003840c0000012104
  | 7, 2, 0 => 0x2840c000000a10b0000000842c000000210300000048420000000a1070000003840000000841070000000842000000061000000000840c00000c9103000d521080c000000a10b0000002840c00000021080004110081c00000061000000001840000000021000000604880c00000121000000010442c00000021030000002840c00000021010000602881c00000021070000004842c000001210400000028400000000a103
  | 7, 2, 1 => 0x841000000811030000000841c00454c82070000000841c00000061030000000840c00000121080000021441c00000121040000040440c00000021070000000841c00001041030000203880c00000021030000000840c00001091030000003840000000021040000003842000000021040000001840c00000061000000002842c000000a1030000000841c000000a1030000604881c000000610000000048410000000610b
  | 7, 2, 2 => 0x3840000000401070000000841c000000a1040000001841000001011070000002842000000021010009540080c000000a1000000021041c00000061070000a03881c00000061040000040040000000121070000000841c00000061070000001842c000000a1030000001841000450412070000021041c000180e2030000002840000000841070000002840c00000061000000003841c000000210000000028410000004110b
  | 7, 2, 3 => 0x842c00425082030000002841c00000061080000003841c000000e10b0000004842000000411030000002840c00000121070000002841000000121030000000841c00000061030000001842000000021030000002840000000c51080000030041000000c01070000001840000000021040000000842c00001001000000e04881c000000a1070000030440c000004010700000008420000000a1040000020041c0000006103
  | 7, 2, 4 => 0x42440c00018122030000004841c00038122070000002841c000000e1030000040041c00405002030000604880c000000a10b0000000840c00000021070000e04881c00354802030000002840400000c81070000000840c00000121040000000840c00000c01040000602881c000000a1080000010441c00000c81070000002842c00204802070000020441c00000121030000201880c00000c11030000040041c000000a103
  | 7, 2, 5 => 0x40440c00000021050000001841c00000061030000000841c00001001070000000840000001091070000001842000000021030000000842000000021080004110081c00000021030005520080c00000061040000003841c00001041070000001842000000021030010140081c00000801070000021440c00000121080000602880c00000811030000001841c00028122030010140080c000000210700000018414000000a107
  | 7, 2, 6 => 0x20440c00000021040000603880c00000021030000004840000000841070000010041c000000a1000000041041c00000021010000042440c00000121080000003841000000021030000004840c00018122070000002841000000c51030000001841c000000e10b0000204880c000000e1070000000842000000121030000003840c000000a1080000040441c00000121040000041440c000000e10b0000603880c0015480207
  | 7, 2, 7 => 0x840400000121070000001842c00000121000000000840400000121000000000842000000c01040000004840c00000021040000004840c00000021070000003841c000000e1000000004842000000121040000004841c000000610b0000042041c00000121070000004840c00000061080000031440c00000021070000003841000000021070000001840000000021030000040041c000001210300000018420000000a103
  | 7, 2, 8 => 0x20441c00000c910300000028400000000e1030000004840c00000021030000002841c00000061000010140080c00001041070000001840c00028122070000001840c000080e2030000002842c00000061080000001841000001091030000004842c000000e1030005540081c000000210700000028410000000610700000038420000004110300000048410000000210b00000018420000080e207000000184040015500203
  | 7, 2, 9 => 0x40040000000121070000000841c00000411070000002842c00454802070000201881c004500a2030000002840c000000a1000000032041c000000e1030000000842c00001051030000003842c00000021030000021440c00454802030000003840000001051070000003840c00000061030000001842000000021050000040041c000000a10b0000003842c000000e1070000043041c0015480203000000184100000012103
  | 7, 2, 10 => 0x10541081c000000a1030000003840c00350812070000001840c000000e1070000002840000000061000000004840c00000121070000021441c00000061040000020440c00454c82070000002840c000010c1070000001840c00001001070000000842c000000210800000008400000001210b0000204881c004150420300000028420000000a10400000038410000000a1040000004842c000000a107000000184000035105207
  | 7, 2, 11 => 0x2840000000061050000004842c000000610b0000040441c00000021030000000841c00000061030000004841000000061040000042440c000000e1040000000841c000000e1070000001841c0000104107000d510080c000080a2030000030041000155002030000001841c00000021030000a04880c000000a1070000000840000000021080000002840c00000021000000003840c0000006107000000284200000104103
  | 7, 2, 12 => 0x21440c00000121040000004842c00000021070000020440c00204802030000000841c00000021040000020441c00000021070000003841c00000021080000000841c00000021030000003840c00028122070000003841c00000021050000000842c000000210b0000a04880c00000061000000001840000000021080000000840000000811030000a04880c000000e1030010942081c000000a10400000028410000000a107
  | 7, 2, 13 => 0x20440c00000061000000004842000000411030000a04881c000000a1040000603881c000000610b0011510081c00424022030011510080c00000061070000030440c000280e2030000000841c00000021030000000841c00000411070000041440c000000e10700000048420000000a10700000038400000000a1080000041441c00454802030000001840c00000c410700000018414000000e10800000018400000000a108
  | 7, 2, 14 => 0x30440c00000411030000040040c00000021070000000841000000401070000001841c00000401070000003842000000021040000000840000000c910300000018410000000a1080000002841c00000061070000001841c000000a1080000a03880c00000061070008120081c00000061040000000840c00000061070000000840000000021080000043440c000000210b0000000840c00000061030000a04881c0000002107
  | 7, 2, 15 => 0x3841c000010c10700000008420000000a1030005520080c000000e10b0000030440c000000a10800000028400001044020700000018420000004110300000008410000000e1030000002840c000000a1070000000842000000021010000000840c000004110b0008120081c00104402030010140080c000000a1080000000841000000c910300000048400000000610b0000000842c00000061030000001841c0000041107
  | 7, 3, 0 => 0x20441c00454402030000001840c00000061030000031041c000001210000000008400000000210300000038410000000a10700000018400000000210b0000000841c000000e1070000002840c000000a1080000004841c00000841070000002840400000c91070000004841c00000121040010541080c00000061000000000842c00000021070000020441c000000210b0000031041c00000c51030000010041c0020480207
  | 7, 3, 1 => 0x5540080c00008062030000204880c00000801070000001841c00000021080011510080c00000021080000001841c000000a1070000000841c00450412070000030041c00000c01070000002842c00000021000000000841c00000411030000004840c00000021000000000841c00450412030000020441c00000411030005540080c000000a10b0000202881c00000021030000004840c00000c81070000001841c0000012104
  | 7, 3, 2 => 0x2842c00028122030000000841000000021040000003840c000000e1010000001841000000121080000002841c00000121000004110080c00000061030000000841c00000121000008120080c000004010700000018400000000a10400000018410000000a1000000001841000001091030000001841c000180e2070000002842c00000c41070000003842c00000021000000000840c00028122070000001841c0000109103
  | 7, 3, 3 => 0x203880c000000e10400000314420000000e1080000041440c00204802070000001840000000061070000003841c00038122030000021440c00000411030011520080c000080e20700000008420000000e1030000000840c00000811030000004841c00001011030000004840c000080e2070000003842000354802030000003841000000061030000004841000000c91030000002842c00000021070010541080c000000a103
  | 7, 3, 4 => 0x42041c00000021070000010040c000000610400000018410000000210000000028414000004110b0000000841c00000061050000e04880c000000a1000011410480c000000a1070000001842000000811030000001841c00038122030000002841c000080620300000008400000180a2070000040041c00000121000000000841000000c01040000602880c000000a1030000000840000000021070000000840c0000006103
  | 7, 3, 5 => 0x4841c000000a1030000002841c00000801070004110080c000000a10b00000008400000000e1030000002841c000000e1080000002841c00000021070000201881c00000811070008120081c000000a10700000008410000000a1000000002841000000121070000000841000001011030000201881c00000021040000002840c00425082070000020440c00000061040000004841c000280e20300000018410000000a10b
  | 7, 3, 6 => 0x38404000000210700000038400000000e1000000021041c000000e10b0000000841c00000c81070000000842c00000021070000042440c00415042070000004841000000401070000032440c000000a100000d521080c000000a1030000002841c000001210b0000004840c00000121040000000842c00000c01040000020441c000000210b0000002842000000021010000041041c00000811030000020440c0000002104
  | 7, 3, 7 => 0x10441c000000e1070000020440c00000021040000003842c00001011030000602880c00001091070000204881c00454402030000203881c00000c01070000004842c00000121080000003840400000c51030000000841c00000021000000004840000000061030000004840c00000021030000000841c00001011030008521081c000000a1080000041040c000180a207000000384200000002101000000384000000012104
  | 7, 3, 8 => 0x1842c00000021000000002840000000061080000003841000008062030000003840c00000021070000203881c000000e1080000203881c000000210000000018410000000a1070000002841000000021040000000842c000000e1070000001840c00000021030000004841000000061070000000842c000000a1040000201880c000000610b0000002840c000010c1000000001840c000000e1080000001841c000000e100
  | 7, 3, 9 => 0x32041c00001041070000000840c00405002030000020441c00000061070000004842c00000021040000002841000000121000000000840c00000021080010541080c000000a1070000020441c000000a1030000042441c000000e10b0000041041c00354842030000010440c00000811070000032041c00000811070000002841c000280e2070000004841000001051030000202880c00001011030000201881c0000081103
  | 7, 3, 10 => 0x841000000021070000000840c000000e10b0000041041c004504120300000018420000000a1030000000842c00000021030000002840c00450412070000004841000000c41070000001842c00000121070000043041c00000021000000041042000000021030000604881c00000c11030000201881c00000801070000030041c00000021030000201881c00000121030000604880c000000e1050000010440c0000006101
  | 7, 3, 11 => 0x4841000000121070000042041c000001210400000048400000080a2070000001840000000851070000000841000000061070000004841c00000c81070000030041000000021040000000841000000061030000000841c00000021000000000842c00000021030000004841c000000610100000048410000000a1070000004841c00000021000000000842c00415042070000003842c00001091030000003840c0000002104
  | 7, 3, 12 => 0x1840c00000411070000003842c00425082030000021440c00000811030000604881c000000610300000048420000004010700000300410000000a1040000000840c000004010300000400400000000e1000000001841c00000021030000040040000000061070000001840c00454c82070000003840400001001000000000840000000121030000002841c00355002030000004841c000080a2070000603880c000000a105
  | 7, 3, 13 => 0x841c000000e10800000038410000000a1000000001841c00000121030000000840c000000e1070000003841c000000e1030000000840c000000e1070000003841c000180a2030000000840c000000e10b00000008410000000210400000008400000000e1040000604880c00354802030000041041c00000021070000002841000000801070000003841c000000a1070000003840c00000021030000004840c000001210b
  | 7, 3, 14 => 0x4842000008122030000001840000000c81070000001840400000061000000001840000000061070000000841c00000411030000004841c00001001030000000842c000000a1070000001842c00000121070000001840c000000e1080000202880c000000a10b0000031442000214842030000001840c00350812070000000842000000061080000031041c00000021000000003840c0000085107000000384000000002103
  | 7, 3, 15 => 0x4840c000000a10b0010140081c000010510300000028420000080a2030000003841c00000061040000001840400000061070000001841c00000121040000020041c00001081070000004841c00038122070000001841c00000061070000603880c00001091030000040041c000001210b0000001840c00000021040000001840c0000006104
  | 8, 0, 0 => 0x10440c00000061070000001841c00000021030000031041c00000851070000002840c00000411070000030440c00000411030000001841c00000061030000002840c00000061070000001840c000000e1070000003841c00000411030000030041c00001051070000040440c00000401030000043440c00001051030000001840c00001001030000004841c000000e1070000043440c00000c81070000010441c0000012103
  | 8, 0, 1 => 0x21440c00000021070000043041c00000c91030000041440c000000a1070000002841c00001091070000010441c000000a1070000004841c000000a1030000004840c000000a1030000030440c00000c91030000040040c00000c01070000030041c00001091030000001840c00000021030000004840c000000a1070000030041c00000841030000001841c00000401030000042041c00000411070000041440c0000041107
  | 8, 0, 2 => 0x4841c00000811030000003840c00001081070000002840c00000121070000004840c00000121030000042441c00000811030000042441c000000a1070000020041c00001091030000000840c00000c51030000020040c00000c41070000021441c00000121030000032041c00000811070000031440c00001091070000042440c00000811030000041041c00001081030000042440c00000061030000040440c0000012107
  | 8, 0, 3 => 0x841c000010c1070000043440c00000021070000004841c00000851030000021041c00000401070000042041c00001081070000041040c00000021070000031041c00000851070000002841c00000c41070000021441c00001081070000042040c00000021030000042040c00000c41070000021441c00000851030000040441c00001041070000020040c00001041030000032440c000000e1030000021440c0000012107
  | 8, 0, 4 => 0x43041c000000e1070000042441c00000021030000002840c00000021070000043041c00001051070000000841c000010c1070000041040c00000411030000041440c00001081030000020040c00000c01070000001840c00000021070000043041c00001011030000000840c00000061070000043440c00000c51030000000840c00000801030000010441c00001001070000010440c00000061070000020440c0000006103
  | 8, 0, 5 => 0x2840c00001011070000042440c00001011070000030440c00000021030000010440c000000a1030000031041c000000a1030000004841c00000c11030000021041c00000061030000040441c00000401070000040440c000010d1030000040040c00001011030000000841c00000021070000043440c000000a1070000002841c00000121030000002840c00000841030000010040c00000851070000040441c0000006107
  | 8, 0, 6 => 0x4841c000000e1030000021041c00000401070000021041c00000401070000040040c00001091030000004841c00000121030000001840c00000121030000004841c00000841070000000841c00000401070000021040c00000021070000010040c00000121030000002841c000000a1070000004840c00000c51030000041440c00000841030000010040c00001001070000000841c00000021030000002841c0000109107
  | 8, 0, 7 => 0x1841c00000061030000042040c00001011070000021041c00000061030000041441c00000851030000041440c000000e1030000041440c000000a1030000020041c00001081070000040041c00001081030000002841c00001001070000001841c000000a1030000032041c00000811070000004840c00000c41070000021441c00000061030000021440c00000c51030000040041c00001051070000040040c0000012107
  | 8, 0, 8 => 0x32041c00000811070000020041c00000811070000000840c00001081030000010441c00000121070000041040c00000061070000041441c00000801030000021440c00000c91030000003840c00000401070000032440c00000811030000003841c00000021070000043041c00000021030000032440c00000121030000001841c00000c51030000001841c00001001070000042440c00001051070000041041c0000105107
  | 8, 0, 9 => 0x10041c00000841030000001840c00000801070000010040c00000801070000040440c00000021030000002841c00000c81070000020441c00000c81070000020441c00000021070000020041c00000021030000002841c00000801030000002840c00001041070000030440c00000c81070000020040c00000811070000020440c00001011070000040440c00000811030000042440c00000c01070000020041c0000104103
  | 8, 0, 10 => 0x21040c00001091070000010040c00000061070000030041c00001041070000041041c00000841030000040041c00000061030000040040c00001001030000000840c000000e1070000041041c000000a1030000041040c00000c11030000004841c00000411030000042041c00000121030000041040c0000084107
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 12 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_x1_0 roots_x1_0 7 s ws hint
  | 1 => checkCutEntry dom_x1_0_x5_1 roots_x1_0_x5_1 6 s ws hint
  | 2 => checkCutEntry dom_x1_1_x3_0 roots_x1_1_x3_0 5 s ws hint
  | 3 => checkCutEntry dom_x4_1 roots_x4_1 8 s ws hint
  | 4 => checkCutEntry dom_x2_0 roots_x2_0 7 s ws hint
  | 5 => checkCutEntry dom_x2_0_x4_1 roots_x2_0_x4_1 6 s ws hint
  | 6 => checkCutEntry dom_x1_0_x5_0 roots_x1_0_x5_0 5 s ws hint
  | 7 => checkCutEntry dom_x3_0 roots_x3_0 8 s ws hint
  | 8 => checkCutEntry dom_x5_0 roots_x5_0 7 s ws hint
  | 9 => checkCutEntry dom_x0_0_x4_1 roots_x0_0_x4_1 5 s ws hint
  | 10 => checkCutEntry dom_x0_0_x5_1 roots_x0_0_x5_1 5 s ws hint
  | 11 => checkCutEntry dom_x5_1 roots_x5_1 7 s ws hint
  | 12 => checkCutEntry dom_x0_0_x4_1_x5_1 roots_x0_0_x4_1_x5_1 4 s ws hint
  | 13 => checkCutEntry dom_x1_1 roots_x1_1 6 s ws hint
  | 14 => checkCutEntry dom_x1_0_x4_1_x5_0 roots_x1_0_x4_1_x5_0 4 s ws hint
  | 15 => checkCutEntry dom_x0_0 roots_x0_0 6 s ws hint
  | 16 => checkCutEntry dom_x3_0_x4_1_x5_0 roots_x3_0_x4_1_x5_0 4 s ws hint
  | 17 => checkCutEntry dom_x1_1_x5_0 roots_x1_1_x5_0 5 s ws hint
  | 18 => checkCutEntry dom_x1_1_x3_0_x5_0 roots_x1_1_x3_0_x5_0 4 s ws hint
  | 19 => checkCutEntry dom_x4_1_x5_1 roots_x4_1_x5_1 5 s ws hint
  | 20 => checkCutEntry dom_x3_0_x5_0 roots_x3_0_x5_0 5 s ws hint
  | 21 => checkCutEntry dom_x1_0_x4_1 roots_x1_0_x4_1 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_63 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_1_x3_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x4_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x4_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_1_x3_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x4_1 _ hc
  · contradiction
def p0Subs : List Nat := [4, 0, 8, 7, 11, 3, 15, 1, 13, 10, 5, 9, 2, 17, 12, 19, 6, 16, 18, 20, 21, 14]
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)) ||
  p0Subs.any (fun k => checkCutByIdx s ws k)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_63 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq, Bool.or_eq_true] at h; rcases h with h1 | h0
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2
  · obtain ⟨k, _, hk⟩ := List.any_eq_true.1 h0; exact checkCutByIdx_sound hk
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_63 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_63 goalM u ys) : RunD dom_63 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_63 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 12 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 64 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 64 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6_64 : ∀ i, 64 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 64 64 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6_128 : ∀ i, 128 ≤ i → i < 192 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 64 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6_192 : ∀ i, 192 ≤ i → i < 243 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 51 192 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 243 → Z 6 i = true := (range_split (range_split z6_0 z6_64) (range_split z6_128 z6_192))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_0 : ∀ i, 0 ≤ i → i < 64 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_64 : ∀ i, 64 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 64 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_128 : ∀ i, 128 ≤ i → i < 192 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_192 : ∀ i, 192 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 192 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_256 : ∀ i, 256 ≤ i → i < 320 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 256 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_320 : ∀ i, 320 ≤ i → i < 384 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 320 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_384 : ∀ i, 384 ≤ i → i < 448 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 384 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_448 : ∀ i, 448 ≤ i → i < 512 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 448 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_512 : ∀ i, 512 ≤ i → i < 576 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 512 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_576 : ∀ i, 576 ≤ i → i < 640 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 576 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_640 : ∀ i, 640 ≤ i → i < 704 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 640 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_704 : ∀ i, 704 ≤ i → i < 768 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 704 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_768 : ∀ i, 768 ≤ i → i < 832 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 768 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_832 : ∀ i, 832 ≤ i → i < 856 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 24 832 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 856 → Z 7 i = true := (range_split (range_split (range_split z7_0 (range_split z7_64 z7_128)) (range_split (range_split z7_192 z7_256) (range_split z7_320 z7_384))) (range_split (range_split z7_448 (range_split z7_512 z7_576)) (range_split (range_split z7_640 z7_704) (range_split z7_768 z7_832))))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_0 : ∀ i, 0 ≤ i → i < 64 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_64 : ∀ i, 64 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 64 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_128 : ∀ i, 128 ≤ i → i < 192 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_192 : ∀ i, 192 ≤ i → i < 256 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 192 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_256 : ∀ i, 256 ≤ i → i < 320 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 256 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_320 : ∀ i, 320 ≤ i → i < 358 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 38 320 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 358 → Z 8 i = true := (range_split (range_split z8_0 (range_split z8_64 z8_128)) (range_split z8_192 (range_split z8_256 z8_320)))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 31 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 31 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
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
def RootG (s : Nat) : Bool := scr dom_63 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 6 5 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : RunD dom_63 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_63 roots_63 goal_all 11 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_63 goal_all := by
    have h0 : isConstB dom_63 goal_all = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub; have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq; rw [hcov] at hbad; contradiction
end S_63
theorem low_63 : Lower dom_63 roots_63 goal_all 11 := S_63.noCircuit

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

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 13]⟩], 16⟩
theorem wit_mono : PEqualNP.MetaComplexity.Monotone2 wit := by simp [wit, PEqualNP.MetaComplexity.Monotone2]
theorem wit_size : wit.size ≤ 11 := by decide
theorem wit_eval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = ((fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4209552032) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0))) x := by decide +kernel
theorem hT6 : ∀ r : Fin 64, goal_all.testBit r.val = ((fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4209552032) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0))) (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4209552032) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) t → 11 ≤ t :=
  lower_to_circuit6 (fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4209552032) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) goal_all 11 hT6 (by unfold IsConst; decide) low_63

end PEqualNP.Outside.L_meta_40345_aux

theorem PEqualNP.Outside.L_meta_40345 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4209552032) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809440 * 2 ^ 32 + 4209552032) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s hs
  have hlb : 11 ≤ s := PEqualNP.Outside.L_meta_40345_aux.lower s hs
  exact ⟨PEqualNP.Outside.L_meta_40345_aux.wit, PEqualNP.Outside.L_meta_40345_aux.wit_mono, le_trans PEqualNP.Outside.L_meta_40345_aux.wit_size hlb, PEqualNP.Outside.L_meta_40345_aux.wit_eval⟩
