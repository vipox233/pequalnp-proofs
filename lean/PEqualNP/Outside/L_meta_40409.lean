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

namespace PEqualNP.Outside.L_meta_40409_aux

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
def goal_all : Nat := 0xfeeaeee8faeaa0a0
def dom_63 : Nat := 0xffffffffffffffff
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]
def dom_x1_0_x5_1 : Nat := 0x3333333300000000
def roots_x1_0_x5_1 : List Nat := [0x2222222200000000, 0x3030303000000000, 0x3300330000000000, 0x3333000000000000]
def dom_x0_0_x4_1_x5_1 : Nat := 0x5555000000000000
def roots_x0_0_x4_1_x5_1 : List Nat := [0x4444000000000000, 0x5050000000000000, 0x5500000000000000]
def dom_x0_0_x5_1 : Nat := 0x5555555500000000
def roots_x0_0_x5_1 : List Nat := [0x4444444400000000, 0x5050505000000000, 0x5500550000000000, 0x5555000000000000]
def dom_x2_0_x4_0_x5_1 : Nat := 0xf0f00000000
def roots_x2_0_x4_0_x5_1 : List Nat := [0xa0a00000000, 0xc0c00000000, 0xf0000000000]
def dom_x4_0_x5_1 : Nat := 0xffff00000000
def roots_x4_0_x5_1 : List Nat := [0xaaaa00000000, 0xcccc00000000, 0xf0f000000000, 0xff0000000000]
def dom_x2_0_x5_1 : Nat := 0xf0f0f0f00000000
def roots_x2_0_x5_1 : List Nat := [0xa0a0a0a00000000, 0xc0c0c0c00000000, 0xf000f0000000000, 0xf0f000000000000]
def dom_x3_0_x4_0_x5_1 : Nat := 0xff00000000
def roots_x3_0_x4_0_x5_1 : List Nat := [0xaa00000000, 0xcc00000000, 0xf000000000]
def dom_x4_1_x5_1 : Nat := 0xffff000000000000
def roots_x4_1_x5_1 : List Nat := [0xaaaa000000000000, 0xcccc000000000000, 0xf0f0000000000000, 0xff00000000000000]
def dom_x3_0_x5_1 : Nat := 0xff00ff00000000
def roots_x3_0_x5_1 : List Nat := [0xaa00aa00000000, 0xcc00cc00000000, 0xf000f000000000, 0xff000000000000]
def dom_x5_1 : Nat := 0xffffffff00000000
def roots_x5_1 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]
def dom_x2_0_x4_0 : Nat := 0xf0f00000f0f
def roots_x2_0_x4_0 : List Nat := [0xa0a00000a0a, 0xc0c00000c0c, 0xf0000000f00, 0xf0f00000000]
def dom_x2_0 : Nat := 0xf0f0f0f0f0f0f0f
def roots_x2_0 : List Nat := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]
def dom_x1_1_x3_0_x4_0 : Nat := 0xcc000000cc
def roots_x1_1_x3_0_x4_0 : List Nat := [0x8800000088, 0xc0000000c0, 0xcc00000000]
def dom_x1_1_x4_0 : Nat := 0xcccc0000cccc
def roots_x1_1_x4_0 : List Nat := [0x888800008888, 0xc0c00000c0c0, 0xcc000000cc00, 0xcccc00000000]
def dom_x3_0_x4_0 : Nat := 0xff000000ff
def roots_x3_0_x4_0 : List Nat := [0xaa000000aa, 0xcc000000cc, 0xf0000000f0, 0xff00000000]
def dom_x4_0 : Nat := 0xffff0000ffff
def roots_x4_0 : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]
def dom_x1_1_x3_0 : Nat := 0xcc00cc00cc00cc
def roots_x1_1_x3_0 : List Nat := [0x88008800880088, 0xc000c000c000c0, 0xcc000000cc0000, 0xcc00cc00000000]
def dom_x1_1_x3_0_x5_0 : Nat := 0xcc00cc
def roots_x1_1_x3_0_x5_0 : List Nat := [0x880088, 0xc000c0, 0xcc0000]
def dom_x3_0_x5_0 : Nat := 0xff00ff
def roots_x3_0_x5_0 : List Nat := [0xaa00aa, 0xcc00cc, 0xf000f0, 0xff0000]
def dom_x3_0 : Nat := 0xff00ff00ff00ff
def roots_x3_0 : List Nat := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]
def dom_x0_0_x4_1 : Nat := 0x5555000055550000
def roots_x0_0_x4_1 : List Nat := [0x4444000044440000, 0x5050000050500000, 0x5500000055000000, 0x5555000000000000]
def dom_x4_1 : Nat := 0xffff0000ffff0000
def roots_x4_1 : List Nat := [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000]
def dom_x1_0 : Nat := 0x3333333333333333
def roots_x1_0 : List Nat := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]
def dom_x1_1_x3_1_x5_0 : Nat := 0xcc00cc00
def roots_x1_1_x3_1_x5_0 : List Nat := [0x88008800, 0xc000c000, 0xcc000000]
def dom_x1_1_x3_1 : Nat := 0xcc00cc00cc00cc00
def roots_x1_1_x3_1 : List Nat := [0x8800880088008800, 0xc000c000c000c000, 0xcc000000cc000000, 0xcc00cc0000000000]
def dom_x1_1 : Nat := 0xcccccccccccccccc
def roots_x1_1 : List Nat := [0x8888888888888888, 0xc0c0c0c0c0c0c0c0, 0xcc00cc00cc00cc00, 0xcccc0000cccc0000, 0xcccccccc00000000]
def dom_x1_0_x3_1_x5_0 : Nat := 0x33003300
def roots_x1_0_x3_1_x5_0 : List Nat := [0x22002200, 0x30003000, 0x33000000]
def dom_x1_0_x3_1 : Nat := 0x3300330033003300
def roots_x1_0_x3_1 : List Nat := [0x2200220022002200, 0x3000300030003000, 0x3300000033000000, 0x3300330000000000]
def dom_x3_1 : Nat := 0xff00ff00ff00ff00
def roots_x3_1 : List Nat := [0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000]
def dom_x0_0 : Nat := 0x5555555555555555
def roots_x0_0 : List Nat := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]
def dom_x1_0_x5_0 : Nat := 0x33333333
def roots_x1_0_x5_0 : List Nat := [0x22222222, 0x30303030, 0x33003300, 0x33330000]
def dom_x5_0 : Nat := 0xffffffff
def roots_x5_0 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

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

theorem low_x0_0_x5_1 : Lower dom_x0_0_x5_1 roots_x0_0_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555000000000000, 44, 60)] (by decide +kernel) (by decide +kernel) low_x0_0_x4_1_x5_1

namespace S_x2_0_x4_0_x5_1
def pairsG : List (Nat × Nat) := [(33, 35), (33, 41), (34, 35), (34, 42), (40, 41), (40, 42)]
def r1sG : List Nat := [33, 33, 34, 34, 40, 40]
def r2sG : List Nat := [35, 41, 35, 42, 41, 42]
def mpG : Nat := 0x3f
def pool6G : List Nat := [37525803116835]
def xsM : List Nat := roots_x2_0_x4_0_x5_1.map (· &&& dom_x2_0_x4_0_x5_1)
def goalM : Nat := goal_all &&& dom_x2_0_x4_0_x5_1
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x2977382d
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xf000000000000000c0c0000000000000a0a00000000
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x2_0_x4_0_x5_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x2_0_x4_0_x5_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x2_0_x4_0_x5_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x2_0_x4_0_x5_1 goalM u ys) : RunD dom_x2_0_x4_0_x5_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x2_0_x4_0_x5_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x2_0_x4_0_x5_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x2_0_x4_0_x5_1 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x2_0_x4_0_x5_1 roots_x2_0_x4_0_x5_1 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x2_0_x4_0_x5_1 goal_all := by
    have h0 : isConstB dom_x2_0_x4_0_x5_1 goal_all = false := by decide +kernel
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
end S_x2_0_x4_0_x5_1
theorem low_x2_0_x4_0_x5_1 : Lower dom_x2_0_x4_0_x5_1 roots_x2_0_x4_0_x5_1 goal_all 4 := S_x2_0_x4_0_x5_1.noCircuit

theorem low_x4_0_x5_1 : Lower dom_x4_0_x5_1 roots_x4_0_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f000000000, 33, 37)] (by decide +kernel) (by decide +kernel) low_x2_0_x4_0_x5_1

theorem low_x2_0_x5_1 : Lower dom_x2_0_x5_1 roots_x2_0_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f000000000000, 33, 49)] (by decide +kernel) (by decide +kernel) low_x2_0_x4_0_x5_1

namespace S_x3_0_x4_0_x5_1
def pairsG : List (Nat × Nat) := [(33, 35), (33, 37), (34, 35), (34, 38), (36, 37), (36, 38)]
def r1sG : List Nat := [33, 33, 34, 34, 36, 36]
def r2sG : List Nat := [35, 37, 35, 38, 37, 38]
def mpG : Nat := 0x3f
def pool6G : List Nat := [37525735744803]
def xsM : List Nat := roots_x3_0_x4_0_x5_1.map (· &&& dom_x3_0_x4_0_x5_1)
def goalM : Nat := goal_all &&& dom_x3_0_x4_0_x5_1
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xd942fcfb
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xf000000000000000cc00000000000000aa00000000
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x3_0_x4_0_x5_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x3_0_x4_0_x5_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x3_0_x4_0_x5_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x3_0_x4_0_x5_1 goalM u ys) : RunD dom_x3_0_x4_0_x5_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x3_0_x4_0_x5_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x3_0_x4_0_x5_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x3_0_x4_0_x5_1 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x3_0_x4_0_x5_1 roots_x3_0_x4_0_x5_1 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x3_0_x4_0_x5_1 goal_all := by
    have h0 : isConstB dom_x3_0_x4_0_x5_1 goal_all = false := by decide +kernel
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
end S_x3_0_x4_0_x5_1
theorem low_x3_0_x4_0_x5_1 : Lower dom_x3_0_x4_0_x5_1 roots_x3_0_x4_0_x5_1 goal_all 4 := S_x3_0_x4_0_x5_1.noCircuit

theorem low_x4_1_x5_1 : Lower dom_x4_1_x5_1 roots_x4_1_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa000000000000, 48, 49)] (by decide +kernel) (by decide +kernel) low_x0_0_x4_1_x5_1

theorem low_x3_0_x5_1 : Lower dom_x3_0_x5_1 roots_x3_0_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff000000000000, 33, 49)] (by decide +kernel) (by decide +kernel) low_x3_0_x4_0_x5_1

namespace S_x5_1
def pairsG : List (Nat × Nat) := [(33, 35), (33, 37), (33, 41), (33, 49), (34, 35), (34, 38), (34, 42), (36, 37), (36, 38), (40, 41), (40, 42), (44, 45), (44, 46), (44, 60), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [33, 33, 33, 33, 34, 34, 34, 36, 36, 40, 40, 44, 44, 44, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [35, 37, 41, 49, 35, 38, 42, 37, 38, 41, 42, 45, 46, 60, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0xffffff
def pool6G : List Nat := [61715127215409, 48521121899817, 55118056006947, 57317080704305, 55118258776614, 48521189009701, 55118190945827]
def xsM : List Nat := roots_x5_1.map (· &&& dom_x5_1)
def goalM : Nat := goal_all &&& dom_x5_1
def NN : Nat → Nat
  | 5 => 3
  | 6 => 7
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xd129852f9679e0100854d8be
  | 6, 0, 0 => 0xc5ee96e7b433ea05a716f0c18ec3435845025efc3bd8c2aa009e3c06
  | 7, 0, 0 => 0xbe37fa2f
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xffff00000000fff0fff000000000ffaaffaa00000000fafafafa00000000aaaaaaaa00000000f0f0f0f00000000000ff00ff00000000ffff000000000000ff00ff0000000000cccccccc0000000055555555000000000f0f0f0f00000000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x427055462155432105
  | 6, 0, 0 => 0x43621503627b5493627604627554a3627643862760432705
  | 7, 0, 0 => 0x436275
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
  | 0 => 0x3fff0000000000fc3f800000000000e03e0f00000000001c398f000000000000000f00000000001c398000000000001fc1ff0000000000ffc0000000000000e03e0000000000000380700000000000fffff00000000000e3c67f
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x1ff70000000000ff3fe60000000000f6fedf0000000000bdfbbf000000000024ca9f00000000009d39a200000000000dc1bb0000000000ffe0080000000000f23e4400000000004b95710000000000db3560000000000062c65d
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
  | 5, 0, 0 => 0xdbed3bd2cf2b795aca328ef0a4c1e84379885aa941067208169ce0f10656cce9
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x8400000000a10000000038400000000a100000000384000000006100000000184000000002100
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 4 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_x1_0_x5_1 roots_x1_0_x5_1 6 s ws hint
  | 1 => checkCutEntry dom_x0_0_x4_1_x5_1 roots_x0_0_x4_1_x5_1 4 s ws hint
  | 2 => checkCutEntry dom_x0_0_x5_1 roots_x0_0_x5_1 5 s ws hint
  | 3 => checkCutEntry dom_x4_0_x5_1 roots_x4_0_x5_1 5 s ws hint
  | 4 => checkCutEntry dom_x2_0_x4_0_x5_1 roots_x2_0_x4_0_x5_1 4 s ws hint
  | 5 => checkCutEntry dom_x2_0_x5_1 roots_x2_0_x5_1 5 s ws hint
  | 6 => checkCutEntry dom_x3_0_x4_0_x5_1 roots_x3_0_x4_0_x5_1 4 s ws hint
  | 7 => checkCutEntry dom_x4_1_x5_1 roots_x4_1_x5_1 5 s ws hint
  | 8 => checkCutEntry dom_x3_0_x5_1 roots_x3_0_x5_1 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x5_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x4_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x4_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x5_1 _ hc
  · contradiction
def p0Subs : List Nat := [0, 2, 5, 3, 7, 8, 1, 4, 6]
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)) ||
  p0Subs.any (fun k => checkCutByIdx s ws k)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x5_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq, Bool.or_eq_true] at h; rcases h with h1 | h0
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2
  · obtain ⟨k, _, hk⟩ := List.any_eq_true.1 h0; exact checkCutByIdx_sound hk
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x5_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x5_1 goalM u ys) : RunD dom_x5_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x5_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x5_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_x5_1 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x5_1 roots_x5_1 goal_all 8 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x5_1 goal_all := by
    have h0 : isConstB dom_x5_1 goal_all = false := by decide +kernel
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
end S_x5_1
theorem low_x5_1 : Lower dom_x5_1 roots_x5_1 goal_all 8 := S_x5_1.noCircuit

theorem low_x2_0_x4_0 : Lower dom_x2_0_x4_0 roots_x2_0_x4_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f00000000, 3, 35)] (by decide +kernel) (by decide +kernel) low_x2_0_x4_0_x5_1

namespace S_x2_0
def pairsG : List (Nat × Nat) := [(1, 17), (3, 19), (3, 35), (9, 25), (9, 41), (10, 42), (11, 27), (11, 43), (16, 17), (18, 19), (24, 25), (26, 27), (26, 58), (33, 35), (33, 41), (33, 49), (34, 35), (34, 42), (40, 41), (40, 42), (48, 49), (50, 51), (50, 58), (56, 57), (56, 58)]
def r1sG : List Nat := [1, 3, 3, 9, 9, 10, 11, 11, 16, 18, 24, 26, 26, 33, 33, 33, 34, 34, 40, 40, 48, 50, 50, 56, 56]
def r2sG : List Nat := [17, 19, 35, 25, 41, 42, 27, 43, 17, 19, 25, 27, 58, 35, 41, 49, 35, 42, 41, 42, 49, 51, 58, 57, 58]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [55023264993571, 61620334760233, 55118257596707, 61787955864362, 61715226693929]
def xsM : List Nat := roots_x2_0.map (· &&& dom_x2_0)
def goalM : Nat := goal_all &&& dom_x2_0
def NN : Nat → Nat
  | 5 => 3
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xcf7e460e9113e5435bafac8c
  | 6, 0, 0 => 0xf0260ba
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xf000f000f000f0a0a0a0a0a0a0a0a03030303030303030f0f0f0f000000000f0f00000f0f00000f000f000f000f000c0c0c0c0c0c0c0c0505050505050505
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x11a21633bac6b55
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
  | 0 => 0x73e307000000000000e0df00000000019ce5190000000001ffe0000000000001f01f0000000000018c1cf80000000000631ae60000000001ff1f20
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x31a3070000000000b5efdf000000000094c5190000000001fff0b40000000001f09f4b0000000001ce5cf800000000016b3ae600000000014a1020
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 3 0 (NN s)
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
  | 0 => checkCutEntry dom_x2_0_x4_0 roots_x2_0_x4_0 5 s ws hint
  | 1 => checkCutEntry dom_x2_0_x5_1 roots_x2_0_x5_1 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x2_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x5_1 _ hc
  · contradiction
def p0Subs : List Nat := [0, 1]
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)) ||
  p0Subs.any (fun k => checkCutByIdx s ws k)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x2_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq, Bool.or_eq_true] at h; rcases h with h1 | h0
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2
  · obtain ⟨k, _, hk⟩ := List.any_eq_true.1 h0; exact checkCutByIdx_sound hk
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x2_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x2_0 goalM u ys) : RunD dom_x2_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x2_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
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
def RootG (s : Nat) : Bool := scr dom_x2_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_x2_0 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x2_0 roots_x2_0 goal_all 7 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x2_0 goal_all := by
    have h0 : isConstB dom_x2_0 goal_all = false := by decide +kernel
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
end S_x2_0
theorem low_x2_0 : Lower dom_x2_0 roots_x2_0 goal_all 7 := S_x2_0.noCircuit

namespace S_x1_1_x3_0_x4_0
def pairsG : List (Nat × Nat) := [(3, 7), (3, 35), (6, 7), (6, 38), (34, 35), (34, 38)]
def r1sG : List Nat := [3, 3, 6, 6, 34, 34]
def r2sG : List Nat := [7, 35, 7, 38, 35, 38]
def mpG : Nat := 0x3f
def pool6G : List Nat := [6610527593223]
def xsM : List Nat := roots_x1_1_x3_0_x4_0.map (· &&& dom_x1_1_x3_0_x4_0)
def goalM : Nat := goal_all &&& dom_x1_1_x3_0_x4_0
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xb1abef80
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xcc00000000000000c0000000c00000008800000088
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x1_1_x3_0_x4_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x1_1_x3_0_x4_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x1_1_x3_0_x4_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x1_1_x3_0_x4_0 goalM u ys) : RunD dom_x1_1_x3_0_x4_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x1_1_x3_0_x4_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x1_1_x3_0_x4_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x1_1_x3_0_x4_0 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x1_1_x3_0_x4_0 roots_x1_1_x3_0_x4_0 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x1_1_x3_0_x4_0 goal_all := by
    have h0 : isConstB dom_x1_1_x3_0_x4_0 goal_all = false := by decide +kernel
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
end S_x1_1_x3_0_x4_0
theorem low_x1_1_x3_0_x4_0 : Lower dom_x1_1_x3_0_x4_0 roots_x1_1_x3_0_x4_0 goal_all 4 := S_x1_1_x3_0_x4_0.noCircuit

theorem low_x1_1_x4_0 : Lower dom_x1_1_x4_0 roots_x1_1_x4_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc000000cc00, 34, 42)] (by decide +kernel) (by decide +kernel) low_x1_1_x3_0_x4_0

theorem low_x3_0_x4_0 : Lower dom_x3_0_x4_0 roots_x3_0_x4_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc000000cc, 33, 35)] (by decide +kernel) (by decide +kernel) low_x1_1_x3_0_x4_0

namespace S_x4_0
def pairsG : List (Nat × Nat) := [(1, 5), (3, 7), (3, 35), (4, 5), (6, 7), (6, 38), (9, 13), (9, 41), (10, 42), (11, 15), (11, 43), (12, 13), (14, 15), (14, 46), (33, 35), (33, 37), (33, 41), (34, 35), (34, 38), (34, 42), (36, 37), (36, 38), (40, 41), (40, 42), (44, 45), (44, 46)]
def r1sG : List Nat := [1, 3, 3, 4, 6, 6, 9, 9, 10, 11, 11, 12, 14, 14, 33, 33, 33, 34, 34, 34, 36, 36, 40, 40, 44, 44]
def r2sG : List Nat := [5, 7, 35, 5, 7, 38, 13, 41, 42, 15, 43, 13, 15, 46, 35, 37, 41, 35, 38, 42, 37, 38, 41, 42, 45, 46]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [37443711730982, 37525870225699, 15440980353797, 48425993635113, 48525096453414]
def xsM : List Nat := roots_x4_0.map (· &&& dom_x4_0)
def goalM : Nat := goal_all &&& dom_x4_0
def NN : Nat → Nat
  | 5 => 1
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x58fe465
  | 6, 0, 0 => 0x3b576e79
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xaaaa0000aaaa0000ffff000000000000ff000000ff000000f0f00000f0f00000cccc0000cccc0000555500005555
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x46885
  | 6, 0, 0 => 0x468d5
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
  | 0 => 0x1c6c70000000003ffc0000000000003c03fc0000000000330383800000000000e37360000000003fe3938
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x153dedf0000000003ffe5a40000000003c93fc0000000000334ba7b0000000002ae77360000000002ac2120
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 6 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 6 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 6 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 6 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 6 then wireAt i else 0
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
  | 0 => checkCutEntry dom_x1_1_x4_0 roots_x1_1_x4_0 5 s ws hint
  | 1 => checkCutEntry dom_x4_0_x5_1 roots_x4_0_x5_1 5 s ws hint
  | 2 => checkCutEntry dom_x2_0_x4_0 roots_x2_0_x4_0 5 s ws hint
  | 3 => checkCutEntry dom_x3_0_x4_0 roots_x3_0_x4_0 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x4_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_1_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x4_0 _ hc
  · contradiction
def p0Subs : List Nat := [0, 1, 2, 3]
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)) ||
  p0Subs.any (fun k => checkCutByIdx s ws k)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x4_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq, Bool.or_eq_true] at h; rcases h with h1 | h0
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2
  · obtain ⟨k, _, hk⟩ := List.any_eq_true.1 h0; exact checkCutByIdx_sound hk
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x4_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x4_0 goalM u ys) : RunD dom_x4_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x4_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
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
def RootG (s : Nat) : Bool := scr dom_x4_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_x4_0 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x4_0 roots_x4_0 goal_all 7 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x4_0 goal_all := by
    have h0 : isConstB dom_x4_0 goal_all = false := by decide +kernel
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
end S_x4_0
theorem low_x4_0 : Lower dom_x4_0 roots_x4_0 goal_all 7 := S_x4_0.noCircuit

theorem low_x1_1_x3_0 : Lower dom_x1_1_x3_0 roots_x1_1_x3_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc000000cc0000, 3, 19)] (by decide +kernel) (by decide +kernel) low_x1_1_x3_0_x4_0

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

theorem low_x3_0_x5_0 : Lower dom_x3_0_x5_0 roots_x3_0_x5_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc00cc, 20, 22)] (by decide +kernel) (by decide +kernel) low_x1_1_x3_0_x5_0

namespace S_x3_0
def pairsG : List (Nat × Nat) := [(1, 5), (1, 17), (3, 7), (3, 19), (3, 35), (4, 5), (6, 7), (6, 22), (6, 38), (16, 17), (18, 19), (18, 22), (20, 21), (20, 22), (33, 35), (33, 37), (33, 49), (34, 35), (34, 38), (36, 37), (36, 38), (48, 49), (50, 51), (50, 54), (52, 53), (52, 54)]
def r1sG : List Nat := [1, 1, 3, 3, 3, 4, 6, 6, 6, 16, 18, 18, 20, 20, 33, 33, 33, 34, 34, 36, 36, 48, 50, 50, 52, 52]
def r2sG : List Nat := [5, 17, 7, 19, 35, 5, 7, 22, 38, 17, 19, 22, 21, 22, 35, 37, 49, 35, 38, 37, 38, 49, 51, 54, 53, 54]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [6610794975493, 55118189167907, 57187591652625, 57200930394390, 6610796028677]
def xsM : List Nat := roots_x3_0.map (· &&& dom_x3_0)
def goalM : Nat := goal_all &&& dom_x3_0
def NN : Nat → Nat
  | 5 => 2
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xfc6186b5236d2b7b
  | 6, 0, 0 => 0xa5e2e6eb
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xaa00aa00aa00aa000f000f000f000f00ff00ff0000000000ff000000ff000000f000f000f000f000cc00cc00cc00cc0055005500550055
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x23442c6755
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
  | 0 => 0x1c01f0000000000e7ce1f0000000003ffc0000000000003e03e0000000000031831e00000000000c60ddc0000000003fe3fe0
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x16bd67f000000000063461a0000000003ffc1100000000003e13e8a00000000039cb9e50000000002d66ddc0000000002942980
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
  | 0 => checkCutEntry dom_x1_1_x3_0 roots_x1_1_x3_0 5 s ws hint
  | 1 => checkCutEntry dom_x3_0_x4_0 roots_x3_0_x4_0 5 s ws hint
  | 2 => checkCutEntry dom_x3_0_x5_0 roots_x3_0_x5_0 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x3_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_1_x3_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x5_0 _ hc
  · contradiction
def p0Subs : List Nat := [0, 1, 2]
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
def RootG (s : Nat) : Bool := scr dom_x3_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_x3_0 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x3_0 roots_x3_0 goal_all 7 := by
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
theorem low_x3_0 : Lower dom_x3_0 roots_x3_0 goal_all 7 := S_x3_0.noCircuit

theorem low_x0_0_x4_1 : Lower dom_x0_0_x4_1 roots_x0_0_x4_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555000000000000, 26, 58)] (by decide +kernel) (by decide +kernel) low_x0_0_x4_1_x5_1

theorem low_x4_1 : Lower dom_x4_1 roots_x4_1 goal_all 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa0000aaaa0000, 16, 17)] (by decide +kernel) (by decide +kernel) low_x0_0_x4_1

theorem low_x1_0 : Lower dom_x1_0 roots_x1_0 goal_all 7 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3333333300000000, 9, 41)] (by decide +kernel) (by decide +kernel) low_x1_0_x5_1

namespace S_x1_1_x3_1_x5_0
def pairsG : List (Nat × Nat) := [(11, 15), (11, 27), (14, 15), (14, 30), (26, 27), (26, 30)]
def r1sG : List Nat := [11, 11, 14, 14, 26, 26]
def r2sG : List Nat := [15, 27, 15, 30, 27, 30]
def mpG : Nat := 0x3f
def pool6G : List Nat := [15440845609743]
def xsM : List Nat := roots_x1_1_x3_1_x5_0.map (· &&& dom_x1_1_x3_1_x5_0)
def goalM : Nat := goal_all &&& dom_x1_1_x3_1_x5_0
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x3b3c5b9c
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xcc00000000000000c000c0000000000088008800
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x1_1_x3_1_x5_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x1_1_x3_1_x5_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x1_1_x3_1_x5_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x1_1_x3_1_x5_0 goalM u ys) : RunD dom_x1_1_x3_1_x5_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x1_1_x3_1_x5_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x1_1_x3_1_x5_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x1_1_x3_1_x5_0 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x1_1_x3_1_x5_0 roots_x1_1_x3_1_x5_0 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x1_1_x3_1_x5_0 goal_all := by
    have h0 : isConstB dom_x1_1_x3_1_x5_0 goal_all = false := by decide +kernel
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
end S_x1_1_x3_1_x5_0
theorem low_x1_1_x3_1_x5_0 : Lower dom_x1_1_x3_1_x5_0 roots_x1_1_x3_1_x5_0 goal_all 4 := S_x1_1_x3_1_x5_0.noCircuit

theorem low_x1_1_x3_1 : Lower dom_x1_1_x3_1 roots_x1_1_x3_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcc00cc0000000000, 10, 42)] (by decide +kernel) (by decide +kernel) low_x1_1_x3_1_x5_0

namespace S_x1_1
def pairsG : List (Nat × Nat) := [(3, 7), (3, 19), (3, 35), (6, 7), (6, 22), (6, 38), (10, 42), (11, 15), (11, 27), (11, 43), (14, 15), (14, 30), (14, 46), (18, 19), (18, 22), (26, 27), (26, 30), (26, 58), (34, 35), (34, 38), (34, 42), (50, 51), (50, 54), (50, 58)]
def r1sG : List Nat := [3, 3, 3, 6, 6, 6, 10, 11, 11, 11, 14, 14, 14, 18, 18, 26, 26, 26, 34, 34, 34, 50, 50, 50]
def r2sG : List Nat := [7, 19, 35, 7, 22, 38, 42, 15, 27, 43, 15, 30, 46, 19, 22, 27, 30, 58, 35, 38, 42, 51, 54, 58]
def mpG : Nat := 0xffffff
def pool6G : List Nat := [15440845083399, 55023264994083, 15441248789255, 28647617660694, 28634783287059]
def xsM : List Nat := roots_x1_1.map (· &&& dom_x1_1)
def goalM : Nat := goal_all &&& dom_x1_1
def NN : Nat → Nat
  | 5 => 3
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xdad0a36da5998c2783b557a8
  | 6, 0, 0 => 0xd4898dc3
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xc0c0c0c0c0c0c0cc8c8c8c8c8c8c8c88888888888888888cccccccc00000000cccc0000cccc0000cc00cc00cc00cc00c0c0c0c0c0c0c0c04444444444444444
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x46af511a216358d6
  | 6, 0, 0 => 0x468d5
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 22
  | 6 => 19
  | _ => 0
def stateM : Nat → Nat
  | 5 => 0x3fffff
  | 6 => 0x7ffff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0xffe3c70000000000001fbf00000000000003870000000000fc00000000000000e3e0000000000000039fc00000000000001c380000000000fffc78
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0xb6a34600000000006dffbf000000000024a78f0000000000fe12640000000000e3e9120000000000939fc00000000000495cb90000000000db5870
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 3 0 (NN s)
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
  | 1 => checkCutEntry dom_x1_1_x3_1 roots_x1_1_x3_1 5 s ws hint
  | 2 => checkCutEntry dom_x1_1_x4_0 roots_x1_1_x4_0 5 s ws hint
  | 3 => checkCutEntry dom_x1_1_x3_0_x5_0 roots_x1_1_x3_0_x5_0 4 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x1_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_1_x3_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_1_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_1_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_1_x3_0_x5_0 _ hc
  · contradiction
def p0Subs : List Nat := [0, 1, 3, 2]
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)) ||
  p0Subs.any (fun k => checkCutByIdx s ws k)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x1_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq, Bool.or_eq_true] at h; rcases h with h1 | h0
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2
  · obtain ⟨k, _, hk⟩ := List.any_eq_true.1 h0; exact checkCutByIdx_sound hk
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x1_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x1_1 goalM u ys) : RunD dom_x1_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x1_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
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
def RootG (s : Nat) : Bool := scr dom_x1_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_x1_1 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x1_1 roots_x1_1 goal_all 7 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x1_1 goal_all := by
    have h0 : isConstB dom_x1_1 goal_all = false := by decide +kernel
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
end S_x1_1
theorem low_x1_1 : Lower dom_x1_1 roots_x1_1 goal_all 7 := S_x1_1.noCircuit

namespace S_x1_0_x3_1_x5_0
def pairsG : List (Nat × Nat) := [(9, 13), (9, 25), (12, 13), (12, 28), (24, 25), (24, 28)]
def r1sG : List Nat := [9, 9, 12, 12, 24, 24]
def r2sG : List Nat := [13, 25, 13, 28, 25, 28]
def mpG : Nat := 0x3f
def pool6G : List Nat := [13233198733581]
def xsM : List Nat := roots_x1_0_x3_1_x5_0.map (· &&& dom_x1_0_x3_1_x5_0)
def goalM : Nat := goal_all &&& dom_x1_0_x3_1_x5_0
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xa3e95fe9
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x3300000000000000300030000000000022002200
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x1_0_x3_1_x5_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x1_0_x3_1_x5_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x1_0_x3_1_x5_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x1_0_x3_1_x5_0 goalM u ys) : RunD dom_x1_0_x3_1_x5_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x1_0_x3_1_x5_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x1_0_x3_1_x5_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x1_0_x3_1_x5_0 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x1_0_x3_1_x5_0 roots_x1_0_x3_1_x5_0 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x1_0_x3_1_x5_0 goal_all := by
    have h0 : isConstB dom_x1_0_x3_1_x5_0 goal_all = false := by decide +kernel
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
end S_x1_0_x3_1_x5_0
theorem low_x1_0_x3_1_x5_0 : Lower dom_x1_0_x3_1_x5_0 roots_x1_0_x3_1_x5_0 goal_all 4 := S_x1_0_x3_1_x5_0.noCircuit

theorem low_x1_0_x3_1 : Lower dom_x1_0_x3_1 roots_x1_0_x3_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3300330000000000, 9, 41)] (by decide +kernel) (by decide +kernel) low_x1_0_x3_1_x5_0

namespace S_x3_1
def pairsG : List (Nat × Nat) := [(9, 13), (9, 25), (9, 41), (10, 42), (11, 15), (11, 27), (11, 43), (12, 13), (12, 28), (14, 15), (14, 30), (14, 46), (24, 25), (24, 28), (26, 27), (26, 30), (26, 58), (40, 41), (40, 42), (44, 45), (44, 46), (44, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [9, 9, 9, 10, 11, 11, 11, 12, 12, 14, 14, 14, 24, 24, 26, 26, 26, 40, 40, 44, 44, 44, 56, 56, 56]
def r2sG : List Nat := [13, 25, 41, 42, 15, 27, 43, 13, 28, 15, 30, 46, 25, 28, 27, 30, 58, 41, 42, 45, 46, 60, 57, 58, 60]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [15440845478157, 48425993899305, 28635287854105, 61620334762281, 48426697627917]
def xsM : List Nat := roots_x3_1.map (· &&& dom_x3_1)
def goalM : Nat := goal_all &&& dom_x3_1
def NN : Nat → Nat
  | 5 => 3
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xf4bf4b31ea8598c906cd6aa0
  | 6, 0, 0 => 0xd9129671
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xff000000ff00aa00aa00aa00aa000f000f000f000f00ff00ff0000000000ff000000ff000000f000f000f000f000cc00cc00cc00cc005500550055005500
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x111dd633aac6885
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
  | 0 => 0x3e0fff00000000000000770000000001c7f07f0000000001fe00000000000001c1f0000000000000380f80000000000001ce780000000001ffff88
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x1e0add00000000004a52f70000000000c7506e0000000001ff084c0000000001e1f522000000000138af91000000000095ce780000000001b5ad08
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 3 0 (NN s)
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
  | 0 => checkCutEntry dom_x1_0_x3_1 roots_x1_0_x3_1 5 s ws hint
  | 1 => checkCutEntry dom_x1_1_x3_1 roots_x1_1_x3_1 5 s ws hint
  | 2 => checkCutEntry dom_x1_0_x3_1_x5_0 roots_x1_0_x3_1_x5_0 4 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x3_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_1_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x3_1_x5_0 _ hc
  · contradiction
def p0Subs : List Nat := [0, 1, 2]
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)) ||
  p0Subs.any (fun k => checkCutByIdx s ws k)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x3_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq, Bool.or_eq_true] at h; rcases h with h1 | h0
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2
  · obtain ⟨k, _, hk⟩ := List.any_eq_true.1 h0; exact checkCutByIdx_sound hk
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x3_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x3_1 goalM u ys) : RunD dom_x3_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x3_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
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
def RootG (s : Nat) : Bool := scr dom_x3_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_x3_1 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x3_1 roots_x3_1 goal_all 7 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x3_1 goal_all := by
    have h0 : isConstB dom_x3_1 goal_all = false := by decide +kernel
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
end S_x3_1
theorem low_x3_1 : Lower dom_x3_1 roots_x3_1 goal_all 7 := S_x3_1.noCircuit

theorem low_x0_0 : Lower dom_x0_0 roots_x0_0 goal_all 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555000055550000, 6, 22)] (by decide +kernel) (by decide +kernel) low_x0_0_x4_1

theorem low_x1_0_x5_0 : Lower dom_x1_0_x5_0 roots_x1_0_x5_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x33003300, 20, 28)] (by decide +kernel) (by decide +kernel) low_x1_0_x3_1_x5_0

theorem low_x5_0 : Lower dom_x5_0 roots_x5_0 goal_all 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccccccc, 20, 22)] (by decide +kernel) (by decide +kernel) low_x1_0_x5_0

namespace S_63
def pairsG : List (Nat × Nat) := [(1, 5), (1, 17), (3, 7), (3, 19), (3, 35), (4, 5), (6, 7), (6, 22), (6, 38), (9, 13), (9, 25), (9, 41), (10, 42), (11, 15), (11, 27), (11, 43), (12, 13), (12, 28), (14, 15), (14, 30), (14, 46), (16, 17), (18, 19), (18, 22), (20, 21), (20, 22), (20, 28), (24, 25), (24, 28), (26, 27), (26, 30), (26, 58), (33, 35), (33, 37), (33, 41), (33, 49), (34, 35), (34, 38), (34, 42), (36, 37), (36, 38), (40, 41), (40, 42), (44, 45), (44, 46), (44, 60), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 1, 3, 3, 3, 4, 6, 6, 6, 9, 9, 9, 10, 11, 11, 11, 12, 12, 14, 14, 14, 16, 18, 18, 20, 20, 20, 24, 24, 26, 26, 26, 33, 33, 33, 33, 34, 34, 34, 36, 36, 40, 40, 44, 44, 44, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [5, 17, 7, 19, 35, 5, 7, 22, 38, 13, 25, 41, 42, 15, 27, 43, 13, 28, 15, 30, 46, 17, 19, 22, 21, 22, 28, 25, 28, 27, 30, 58, 35, 37, 41, 49, 35, 38, 42, 37, 38, 41, 42, 45, 46, 60, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0xffffffffffffff
def pool6G : List Nat := [57235474881558, 57287115413020, 57222085608721, 55165116293930, 55035897775398, 48521119797545, 61762184480028, 55023264993571, 15441248789253, 28634783286545, 55118189167907, 57222590176273, 48425993635113, 57235290525980, 57286829737238, 61788273776170, 48426195226921, 55023063401763, 28647617529110, 15441248784645, 57317178872069, 57287216077846, 55165434205738, 28647617529116, 55165502232102, 57317078598929, 55036149896742, 15440845082885, 57286830130460, 55118056201233, 36344854418949, 36396292900113]
def xsM : List Nat := roots_63.map (· &&& dom_63)
def goalM : Nat := goal_all &&& dom_63
def NN : Nat → Nat
  | 5 => 12
  | 6 => 209
  | 7 => 810
  | 8 => 388
  | 9 => 37
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xf6874ecaf0b89d84ebbc17cbe66532ddde61ae49d4ab8b88be040037b7bad9f3a954f45da798be06a08a055b2f85125b
  | 6, 0, 0 => 0x48893a7a47aa69384690d053466496c5462f16d945aa23ee4459c9ea4331a3f542c49e343e7d30483d6089e83ad916173aaaf6cd39fb5db839b9eed638c2cc77385f4f11364999113582312934f6604934ab512834736aa632fc7e7c31c5695e2fd2dc832bedc5d12b303f5f2ac077742a5f178b28ffa4ce260c02e62315db4222fdda5c22143a7921fe11cc21a84b1b20c2b3561e5d01b71e06cafd1de864821c7f980f1c4214131b6e9d7c1a97ec0a18917f9417c2160a1638a69a144a6e321182c6e9117ea3200fb71aff0efd143c0d891f440d20fe830ca288c80ab1918c09fa4f09073c0d4905fcea2e04e6bdd803f8295d03d201c10385b4f601d122d0
  | 6, 0, 1 => 0x8f8bdc5a8f78e0ca8e4591378e2b32378c810a2e8af066f98a34f76c8863e0d78755af518676de0f86497357837332c5833bb76a83051936823172d881ab94487fda4eaa7cb131b67caf1f007c2cfebf7b3832d678c7d28f77a096e07720ead274297a2b729acbe572685f3070ce3025701d6163701232276efe35746e565c756d6c8ec16a903a936a0153b269a98e2e689eda76661467a161d3c4c660e0af50604ea7585f3c4d2a5cb4d9595c86ba0f5a3b12535a17d80859df37c5574f87ec5738c89655e3a3fc55c4d39e55051b7154b154c55450d488532cafce5318a9a350ac6bf3508cbf0e507bdd2c502473694de6e3834b688295497e0663493bf4dc
  | 6, 0, 2 => 0xea32f8e8ea296bdae9bc24cae986d3dae9153832e7e8f3aee6646590df3a5626de3b5545dbcd1d99d9c25d72d6c67342d570448ad42f64bed41e9489d3c105cad3315ec6d2b65212cfa2773acda92b94cc22a61bcc10aa7ecb7e5d4dcb57904bcad5eaa9c7adf1c2c021bcacbf7bfc6cbbbc7503bb698a2bba04a7adb4458a1bb43e3decb3d0ece6b3c41c7cb3b8f06fb242d147b22a9c77b114bc38b081337cae7a07f8ade9db15ade53914ac2e0563aba30cfaa76b4f4da4e0dc78a2ff1743a28b112ca192e8b39e8ae2429d13f6189ce207249af5e89b96a3cfb396053d6d95a7205a9562efe795521fb294d7ef1094b018d394768f2792fd9fb490deee38
  | 6, 0, 3 => 0xfeae66dcfe177252fc813e75fc6d3e51f8a23684f6b5bc52f69881caf5dedc51f524d58ef29d61bdf2856546efa703a7ef4da853ed2150faecb1adebec63ca88eb53615d
  | 7, 0, 0 => 0x103915950f8f22d10f4449ac0f32cd070f32a2810ed4fd100e2bde830de1f81f0daeef0b0d37803a0c76b2fc0c3025590c2225300bb355150a9cd3050a4b0a760a01adfb09dbbd9309a8b188097f42550979a5d3090b2c300895d5190889983b082a1dbb08028ac807f0940f07c644650749dc20070b6e2706dc1cba06d1977a06a6e2bb06974e470694c2350674bcee0620bd3c05d2cb9505a7c7630573298d0567fa5104b7811a047e8d15041cbc3103f5a31803ac249f03a7a7ad0389aaa7036a906202f2e5b202d338cd02c4fbd302c256eb026aed280229321f01bf50c3019b811a017d5a3801271ba700bd628100ae951800aa571900a8eff1001528ba
  | 7, 0, 1 => 0x2730f4cd2709b68a2707962226b7a5be25f87f7325836aef2579079a256a2da724e82e8e248544a523efb98523e4b78223aa13392331768c2284b33321f40ce021d6d2582195a69b21701c68216845b42161cccc2112506520dc7ec92070a08e1fcef5c61d714dfe1d201f441c9476741c3444581c1160c61c014a391bf318101b8f4bc21b5aa7ce1b3609e11afbbe891ae554351ad576b71a0397ba18d23d5e18ce2c7618917f94185ae160182077a417ec8ed517bc20f01769b9701747ce401702826617015c7216ed244d15bf0bfb149a4ea113fda563138bc72e1357233a1204e72a1182c6e910b47c75109959ad108dfb0010873aff107eac71103db424
  | 7, 0, 2 => 0x3f5f549d3f3c83753ef57a873e9bf4f73cc117773c54033b3bd23dc43bbb8b303b6671ed3b22fa393a1fbb53393fefff38f9f1d038c12eb93899b8e13895e653382d8f7737e0d956375cfd243705812c368845d53622fc1e3582312935389f973532e67c34c7ce2534886c253457b94233df7b7b33c6beda32be679b3234461931c427d731b52cbf314ce6a13107d3ae31003e0330dd2abe302f8f992fbe19942f3679eb2e9f17e82e1f778a2ddbe4da2d7eac952d6c76452cd9d1a82c0d41422c0090eb2ad101ba2aafe6892a71985b2a20277c29676491294551f02920d6ee28b7dffc289b6973285367de284126582807443f27c003a927bf8f0327ab8edf
  | 7, 0, 3 => 0x5271f78f52368d0152083abf5200f47051f858f951db4f1a50b5442c50a374334fa4e9104f87c10a4f5a6fd74ee201a54ed160d14e1ca4aa4e10be834deb64974da171e74d3c625a4ce69ba94cc3be474cae6cf64c74d9df4bb6a0f34b685d854b60c5b44a64fe6e49a68b81499f41ff499b52454926b51048ea49724884aee54861424c483280b847ef23c547a969a647989971478064a146f5e80846a5aa93466a8462463c9e9745f4fb8345d63c98459ded534561370c4520d30e4517335244b0b53e43f8662a43e12dec43d0d33c43cfd022433fa33f42f9159c42b870d042a5c7fd4266f78e424c63d04183cd8d40ffb32940e06b1a40d7902040429616
  | 7, 0, 4 => 0x66731261664bccff661766a565ff6a2e65a37f6d6539ae4664f83f6464a6aa8e6494341264545b1d644d152063965c286376351f633e4e9d62e9c1c962c7ad3b62bc2e5c62adb27b62a0e51562387e78623567bb61c7627361ac135560c081b7608f0109605c2bfe602bb2d35fdec53c5f83829a5e86d97f5e1f89135d97f1e35d45a2725d03b9ec5c8704475b99bffc5b60eb4b5b3983f85b04eb6c5ab8a9c85a9cf1fb5a757c2359d8d2e559a1e079599800ca5979ab675929fb825916f36a58c2ef595874c9ef57e59be05710d06857106ce856f73cc156ac910056590b9555eaa36555784b9c557784d655073dee548e179a548cc5b553fbbe5e539fb7ea
  | 7, 0, 5 => 0x7b11ecbf7b103aa87afac6a87abc8b8c7a9eb29b7a552bc079ef6f1079b4a839798ccf517976ef16790df74a788c2ff57862d689785ddb12782718a177c666a776e301307669dadc758c243d74cc5706747a456a7412504373a86ee77366785c727f3775722f623071fe46de71e3fb2171c5b78b716d676770f3945670e8ab9670ac39d170a7275b7098f8c1703978876f658ee36f21cbf56ef35a186e9fdaee6e7696f56e02eec26da035b16cf10f6b6c76c0d66c24c4ee6c1c3b6c6b9ca6a46b504f2a6ad9b6196ac5e76669cae70769c1909169bc6b2669b46fdc697c5b60696e78c469658b74689eda7667fcab5667d44f0c6767de4a6722ad0066f87fdc
  | 7, 0, 6 => 0x91d7069f91c3067b9180cfe590eb9e8f9081cf04907955279061903f902c96a18f2f8aec8ed4acb68e1d627c8d9ceb668ce4dcad8c127d8a8c0b847c8bc200e88b90331e8b34a47b8b04dcb88aa2abe88a88182a8a7a9db88a323b078952d79487f329e787e29fff87b698fb877e346f86bb989c8626c9b88577d8858574e55285721f6a84fccbd184252ff584135e9583f73f8a8342e145833c7e94828b485b8277192482641cb981975c2381450cb28119fa028103242c806943d1805153838050a21c7fefa5537fda735e7f8e9d3a7f6c93bd7f29300d7eb814087e6b005c7e5eb0787e387f3f7e151cff7d908acf7c9f7e7c7c34289a7bba2dba7b28e447
  | 7, 0, 7 => 0xa3731f65a2f38e3ea2dee76ea2abd7d4a214873fa1b636a0a138fd27a104f34fa093d74aa0855b69a03a73baa03392da9f7bf9f09f67cab99f1dec7a9eaa44479e6365479e58602e9e4ff7719dd91c739d3f16bb9cd5fbe69c0945a09c029e899bd7494f9b6f9ad19b5bb1f19b52b2589b1d4b609a9a44729a8d7d6a9a78a26b9a67f3379a4707359a3c86029a23b0e59a06f671991a12f198aadf4f9811f11d9811ba8397e3684197a7d92797a3ebd59765e29c9677bd2a964c72dd95ef59af95dd264195cdd5a695c7433b95c62ad995c3b198957a19a99553881e9522500394e8795694b28afb93593a8c934ff48a93384e8a92fb6e8992646ea392352ad9
  | 7, 0, 8 => 0xb8572b6cb853a286b758a4ccb737b8cab72f4b60b6b24b4fb63ea31cb6187b80b5e1844eb5ca4c10b533f09fb3971adbb390f841b29c2681b2831dfdb274a0a9b21cccbcb2069b61b1b80fbab187c3e5b177d426b0f7f7a1b0e446edb0b06ff8b085131bafedb434af78aea8aee9412baed822e5aea402e0ae7a07f8adee40ccadcd7a96ad9e7681ac203c81ab79d2ccab4606c5aaf7e2b6aa98f8b4aa82d705aa29db81a9925c3da9744f92a8fc3611a8ca0453a84a90f6a8255610a7ed6f8ea76b4f4da6d0c780a6789671a6768364a6375980a5ef21d7a5eabc38a5d302cca57de989a53f8738a51841d6a42ac53aa4232d48a406231da3b74bbea39c9fa5
  | 7, 0, 9 => 0xcd66305eccc52a17cc2a050dcb0f48bccad7f953cabe2c2bca7074eeca011952c9c932d0c93615f1c928a34fc91fbe5dc88c5676c87f2059c87d6749c85246a6c72a8082c7147b79c7049024c6af14d6c69e7be3c677c7a3c65854a2c631c44cc53b428bc51c6308c46975e9c45b15b3c44c184fc406c3f6c3f04a81c26e9b1ec1fd94bec1e22041c1c5ae3cc157bd32c1438dfbc091d8acc0222c96c0163f9ec005c2cebfb4dfb5bf52f044be652655be3bf042be29aebcbe159bfbbd7d1a02bd517ba9bd197d31bcf80b4bbcb5f9c4bc7607b4bc6f13e9bc4e049dbc29ef1dbbf2c6b6bbc7133abb6bf353ba6ddb7aba2fc850b9cd3fe6b8afb66ab88ec8b7
  | 7, 0, 10 => 0xde49630fddea6151dd44ebefdc8e32f7dc530cc6dc15be7adc0b8b92dbaaaeb5dba90328dba270bddb6fd9b3db5796e8dafd2b41da9b71c7da9544d8d9e0ee8ed9c9b650d959f241d8c624d8d8876c1fd8785702d801ed6ad7fb9027d7bd6d5dd7a0e62ad75e8d0fd6683848d6363344d616616dd5b41e40d57f7a4cd4847d5bd45ab438d4468e80d3f88ffed3d3e2c2d3d2f872d3c5c492d39eec29d338bdb8d2b65212d2a6e32cd1cce4d6d1c7e360d1c6eaa5d1bac628d16ca0bed1566dadd130e37ad10ff778d0f46623d0f3126dd02ede41d008a737d00843b7d000bef7cef74cf6cee27a34ce9bbdfbce8dcdf0ce6b0b63cdfbffc3cdb5173bcd813366
  | 7, 0, 11 => 0xf22dc195f17526c4f1411580f0d31038f0c49457f0857a5ff05e0487f047ce9cf0296f4defa703a7ee60f2f9ecf958ccecf44026eccb1c68ec99ef6dec4ffe10ec41d777ec14f7caec01a134ebc90001ebaed3bfeba52384eb5c844eeb1a9bc8e9eb6b25e9d791d3e9d0ea74e9942c9ce9840b59e93d90ece9060583e8d36004e8cf8ba4e8bab8e2e85a7ff3e78ddb80e71705cde6b6f618e626c786e56e18dee55cbfe8e54ed277e542f83be4b843a0e4a63fcce4052d0ee3b83e5ce38f2d78e341463fe3106e12e2fc6deee2f73a11e2dcb27ae2a3a791e29557f5e27ebb7ee27552aee244b55ee1f74cd8e150e5e9e0dc783ce04d6edde01f1c9be00de424
  | 7, 0, 12 => 0xffe602bdffbcfeaeffaa18f5ff945926ff86098aff844943ff570128feff5658fe6faf54fe69f639fdf4a2a0fdaefc54fc8bca0cfc24ab7bfbec75b6fbeba59dfb6ae941facfb439fa2bdd19f9f0e2f7f9b38880f9611aa0f93a5051f8ab1084f7949bb9f7712f20f760f6a9f75b3d8ef6e37eaff6b5bc52f66671a5f660409df629f526f5e05daef57ec026f563e839f4081177f3ee0630f3bae230f3b02e20f3a8a818f3031826
  | 8, 0, 0 => 0x25029ba324f1d90e24ba3ed6242a74e022f2b390225227cd21f40ce021a9023c216845b420bd10b41f505e561f28e87e1da0f8bb1d42c60e1d0c61251c7f660e1c1160c61c02e4e51ae5543519b15e68196926bf194d07b418b98c20189246be18035660178028051741648716ed244d169ad4dc1658ec56155b070715303b8814c25be7147ef837147be17a14445611140ddc3213b478a2128177ed126ac74e11f546a611c9fc5910dfc44d10af5719106602d20f52f7e70f1c517e0ecd7e060eccb7400de1f81f0db3a33c0d359d660d2c2e290b8bbf6b0b5d6d29093db68007f0d02407852a5a07540f0806d33f74046cf47e02fbbdeb02f5fddb00f26ece
  | 8, 0, 1 => 0x4f2308104f1c75a54dcff4e94cd3f7294cae6cf64c8d80f44c50a0f34b0d46544a258bc548be36e947c09368477294e646cd9c50463a0f174541e84844aae86243cfd0224307780a42a809fe417604ab414c634940fd5c893fd89f2f3fd242ec3f643da43f521ef63eca17bc3eb72f933e51fe3b3d9f9c853d7b1e3a3d4337b83ce83b323cc117773c79d3023bcc4b8e3a2919be3a1aa6c238495668376a4f6936209e1535db239335895b0434d1c21a34bd92e333549545332ee49d3265f79931b30d7c315f0dca30b17a1b2ff00c9c2ee5f83b2e00a7792d6782ad2cfda1512cbbaac62b5379482ad2a9b42ac299d12aa950482a339e2928a5bcb427a4a978
  | 8, 0, 2 => 0x779b444e76e1ad9c76a6ae137663a7c6764d3db575a3370774e1c74f749a204b745985b3742c1b0374289a00739f2b3971e3fb2171a8d4f0708219686f36b6b86f1f7e7a6cb455396bf2d3266af4746f6ad542766a9da52b6a866f276a20792e69da458568f8c50e6722ad0067108e52664b1a33664a2e4d655e0be164ede01564bb1a68644d15206438425e63ff7f4763d8096f620d6f8d619f6a456131850560c081b760965ffb6013f4555e6214035bcd8fcd5b7badac5a910ab559bf3e1358bcfd2357c46348567ab1f456713ef955fdc57d55e7a0d6555e780a5391b86c537f76e652d41b94526f455b5164663950c1bb7d50ba5f8b4fc5f4ae4f85907a
  | 8, 0, 3 => 0x9c31e4e49c26fc249bea8a5f9bca85189b4c7f429b0132a19a8d182a9a80d3c49a31aaa699d4553f9972845b98fd6fd7964fc4fc95feb81b956af0e494ffe11f94ea215094dbd1b494acc95294213f90923c76758f8b65ae8f0950aa8ed4acb68dbf9f568d4f66ca8cea63e38c0b847c8b9a7c8c8b3625d88b1d15ca8ac1d328895dd9a188a3b6dc87abe572878389bf861a5c8185db428985b3ccb1859d96c6857f377784fccbd184d0ab2d84135e9584013fe783b31a7d824f20f6824ebd7681a2fbbd8128f3f38124f5e78112770580d29a3980b185227f2d59fd7db0481d7d55c27b7b7c8fb07b4367897ac3e1087a98c06579fc07f6795af53878e4f5a2
  | 8, 0, 4 => 0xd111535ad0bc3a17cedaf033ce63f497ce16f6e3cdef810bcd52d7cdcb884e68cb78c448cad7f953ca1e5d15c9ad816cc98e47ffc77d5d96c74aa3c2c6dc9e7ac58557c3c5742e9cc3753fb4c2d474bfc18ac36bc11b76cfc060a091c02871dec026c9e4bf75efa6bebd2cbbbe769f18be2c3e52bd15572dbd015709bbc01f92b981579cb940c30cb93140c9b8db3bf4b749d50ab5e0fc76b5c668b8b3c7f7b0b0b62913b0b06ff8b03b1c5faf359018ae6ff2a8ac584a90aba7945fa99d0106a9536d8da92e1f67a906a98fa8fdcabba8fc3611a8aceb64a64e8b36a5ef21d7a5dd0329a5937c4ea54e664ba304b735a185d9499e60f45a9deb9d439dc6e867
  | 8, 0, 5 => 0xfdf4a2a0fc4e4806fb8cf931fb6d2ecffa359d84f8ec2452f8037aa5f7a272fef779aaaaf63e7977f61649e1f4c886ecf3caa704f29f8f19f1dccc71f1af9c79f05ab396ef2e9b0fee18b783edacebaced6973f8ed03ec8bece124ddec663512eb7d2b56eb500845eb406b8feace13c6ea5d0618ea36d74ae9e3dfc4e9a376e3e892c0b4e7f44a52e78c552be7311744e6a45857e62388c3e5f93c5de4ee680be3412cc1e2760958e1f09bdde17cf3aae042b81dde53bb01ddda770fddb2f137dd44ebefdcf66048dbff73e2db4ac3addb2c04c2dae1e332dab6ff36da067d68d80e38fad753c3f4d6363344d5053b33d43a869fd358ca24d277431ed175aa0e
  | 8, 0, 6 => 0xff89d50dff123350ff0a3806febb539e
  | 9, 0, 0 => 0xfe971ab2f9554771f92dd199f61649e1ee12c54deab44034d43a869fc708d5a6c68acfd0c43bc065c0a94172c02871deba47a138b749d50ab158ad0fb03b1c5fa4234630a0e187959437159c8ff96af68f8b65ae8302b3d677cbd18269904ec962a89ff74e31041e44efaef6448b58423ef2c9303e51fe3b3d084ce73ba45360242a74e0196926bf1957081117a485a0167ebc1d
  | 10, 0, 0 => 0x69904ec9
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xaaaaaaaaaaaaaaaa0f0f0f0f0f0f0f0ff0f0f0f0f0f0f0f0aaaa5555aaaa5555fafa0000fafa0000ffff0505ffff050500000000ffffffff0000ffff0000ffff00ff00ff00ff00ffffffa5a5ffffa5a5ccccccccccccccccffffffff00000000ffff0000ffff0000ff00ff00ff00ff00a5a5a5a5a5a5a5a53333333333333333
  | 1 => 0xff000000ff000000fffff0f0fffff0f0f0f00000f0f00000fff0fff0fff0fff0f000f000f000f000ffff5555ffff55555555000055550000ff55ff55ff55ff555500550055005500f5f5f5f5f5f5f5f55050505050505050ffccffcc00000000dddddddddddddddd44444444444444445555555555555555f0f00f0ff0f00f0f
  | 2 => 0xff88ff88ff88ff88eeeeeeee0000000011111111fffffffff0f00000ffffffffffffccccffff0000ffffccccffffcccccccc0000cccc000000330033ffffffffff00ff0000000000cccccccc00000000ffccffccffccffcccc00cc00cc00cc00ffc0ffc0ffc0ffc0fcfcfcfcfcfcfcfcc0c0c0c0c0c0c0c0ffffff00ffffff00
  | 3 => 0xfefefefefefefefec8c8c8c8c8c8c8c80505050505050505a0a0a0a0a0a0a0a0fafafafafafafafaeeeeeeeeeeeeeeee8888888888888888eeaaeeaaeeaaeeaaffaaff00ffaaff0005050f0f05050f0ffafaf0f0fafaf0f0eeeecccceeeecccceecceecceecceeccffffa0a0ffffa0a0ffa0ffa0ffa0ffa0ecececececececec
  | 4 => 0x5f5f00005f5ffefeccccfafa0000fafac8c8fafa0000fac8fac8fac8fac80000fafa0000fafaaaaaa0a0aaaaa0a0fafaa0a0fafaa0a0ffaaffaaffaaffaafffafffa00000000fffafffafffafffafa00fa00fa00fa00ccc8ccc8ccc8ccc8ececececa0a0a0a0ffc8ffc8ffc8ffc8fefefefe00000000fe00fe00fe00fe00
  | 5 => 0x505555505055555000033330000ffff0f0f0f0f00000000fff0fff0f0f0f0f0ff00fff0ff00fff000000f0f00000f0faaaaaaaa000000001111111155555555fafafafaf0f0f0f0eeeeeeeeaaaaaaaa0000555500005555aaaa0000aaaa0000fafaaaaafafaaaaaffffaaaaffffaaaaaa00aa00aa00aa00ffecffeca0a0a0a0
  | 6 => 0xfff0fff00000000055505550555055500f0f00000f0f00000f000f000f000f000c0c0c0c0c0c0c0cfcfcfcfcf0f0f0f0fcfcf0f0fcfcf0f0fcf0fcf0fcf0fcf05544554455445544fcfcfcfc000000005454545454545454ffff000000000000f0f0f0f0000000005555555500000000f5f0f5f0f5f0f5f0f4f4f4f4f4f4f4f4
  | 7 => 0x7070707070707070e0e0e0e0e0e0e0effffeeeeffff0000fefefefef0f0f0f0ffaaffaaaaaaaaaaffaaaaaaffaaaaaafafafafaaaaaaaaafaaafaaafaaafaaa0a0a0a0a0a0a0a0aeeeeaaaaeeeeaaaaeaeaeaeaeaeaeaeafaf0faf0faf0faf0ffaaffaa00000000fafafafa00000000f8f8f8f8f8f8f8f8fff0f0f0fff0f0f0
  | 8 => 0xfffafffafafafafafffafafafffafafafffffffffafa00000505ffff0505fffffffa0000fffa0000aaa0aaa0aaa0aaa0fefefefefafafafafefefafafefefafafafac8c8fafac8c8fefe0000fefe0000a8a8a8a8a8a8a8a8fffffafafffffafaff888888ff888888f8f88888f8f88888f888f888f888f888ffff8888ffff8888
  | 9 => 0xeeeeccccaaaa0000fffafff0fffafff0f0f0f5f5f0f0f5f5fff0aaa0fff0aaa0ffffaaaa000000000f0f0a0a0f0f0a0affccaa88ffccaa88fcfca8a8fcfca8a8cccc8888cccc8888eac0eac0eac0eac0ffffaa00ffffaa00050f050f050f050ffffafffaf0f0f0f00f0a0f0a0f0a0f0aa0a0a0a0ffffffffffa0ffa0a0a0a0a0
  | 10 => 0xfaf8faf8faf8faf8ffffc0c0ffffc0c01515151515151515fefefefeaaaaaaaafffff0f0f0f0f0f0ffffaaaaaaaaaaaa0000ffff000000000000f0f00000f0f00000aaaa0000aaaafffff0f0ffff0000fafaaaaaf0f000000a0a0a0a00000000ffffaaaaffff0000050505050f0f0f0f55555555ffffffffaaaa0000ffffffff
  | 11 => 0xaeaeaeaeaeaeaeaeffff0a0affff0a0afcfcccccf0f00000f0f0c0c0f0f00000030303030f0f0f0f1111555511115555ffffcccc000000000f0f0c0c0f0f0c0caaaa8888aaaa8888fafaf8f8fafaf8f8ffffcc00ffffcc00ffffffccffff0000fffcfffcf0f0f0f0ffeeffeeaaaaaaaa0f0c0f0c0f0c0f0caa88aa88aa88aa88
  | 12 => 0x550055555555550055555500555555fafafaf0fafafaf005050505555555550555055505550555fffafffaaaaaaaaa0000ff000000ff000000cccc0000ccccffffff00ffff0000ffffff0000000000aaaaaa00aaaaaa000f0f0f000f0f0f00afafaaaaafafaaaaffff0f00ffff0f00afaaafaaafaaafaaffff0c0cffff0c0c
  | 13 => 0xfffff0f000000000fffff000fffff000ff00aa00ff00aa00f0f0a0a0f0f0a0a0f0f0fff0f0f0fff0f0f0fafaf0f0fafa000f000f0f0f0f0f
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x40d050c0750402100f00504020b0501504030501075030205010950402050c0e5040a020501504020d0c0050406020501504030201005040205010850410050f075
  | 6, 0, 0 => 0x42f050f0e08600041e02530f0060004030205113660004032221110760004031805170e600042a0d291107600041d050f075a60004020b0d11006002b02050f0e5d6000403250d3811600040a020d0f0060004032524110e60004030d1100076000403423b053c600045202350f006000432023b3a05600040d0511070860004024e0d050f60052020d5400096000d0f00070809600032e050f0e07600040a0205110e6002b02270d051160004023b3c0008600031c1b05110960004030205013d60004033a390e076001402050f0e086000432020d11006000403180d1700600042f0b0d050f60047020b0d050f6
  | 6, 0, 1 => 0x3023b3c00096000452020d4a00600020d560559086000302350f000960004230d051108600020d050f28086000402053c3d08600042b023a0f0e60004320d051107600040348330f0e600040211000e0860004020b05110e60004030213120e600041e021d110060003020d05112d6000403403b053c600040a02050f0e6000403023b443c600040305110e07600040302050f01600045205540e076000403340f0e07600030f000e0709600020d2e0511086000403400d3e0f600050f0e07080960004323b050f07600032527260f0e600042b050f0e076000314020d1112600043202050f3d60003023b2e053c6
  | 6, 0, 2 => 0x4033705110e60003025605590e6000004020d050c5000302050f0e2860004020f000e0860004020d540055600040a02053c3d600041e53050f076000314023b053c600040d11000708600040b0d05110760004030d131207600040a0d050f0760004024d0d050f6000004030205015040302530d5605700020d1100080960004023b0b3c0060003022e05110e600045235050f07600020b0d051109600045b0d0f000860004201f0d11006000432250d240f60004020d0f004f60004033b3c00076000403370d110060004310d0f00086000302570d56056000403023c003d600043b053c070860004030d3011076
  | 6, 0, 3 => 0x4020b053c3d600040d050f074f60032020d2e050f60004250d380f086000425240f0e0860004034c0d240f6000403053c3d0760003020d055958600033b053c070960004520d054a0760003020d2c0511600041e02050f5f600040311000e07600040205540e556000302053c3d0960004032f3a0f0e6000403023b05016000347023b053c60004030234110e6000405110e0708600030211000e09600041e1d051107600030d2e05110760004034851000e6000205110e0809600042b0205110e600035c250d260f60002270d050f5e60004201f05110e600044805510e0860014020d0511086000402330f0e086
  | 6, 0, 4 => 0x3140d05111760004020b0f000e6000403450d440f60032020d0f0009600041a0205190e600040325380f0e60004032f05110e6000403023b4a0060004030f000e07600034805510e0960004020d0f004b6000302330f0e09600020d050f2d0860004050f0e0708600040d0554075560000040210050f5002b0227050f0e600045202050f3660004030d341107600030d1100070960004420b0d050f6000403020f00366000403023511006000d0511070809600043248023b05600040302161500600041a020d19006000325270d2611600043b0b053c07600042b0d05110760003140205110e60004023b49050f6
  | 6, 0, 5 => 0x2b5c020d050f600040302054a3d6001e021d0f00096000302413b053c60004201f0f000e6000403253b243c6000403370f000e60004021d0f005a6000403310d11006000402222111086000403050f36076000402050f0e5e600040335051107600040316051507600041a0d05190760003020d05112860004031c1b110060004020d1100086000302050f2d0e600020b0d0f0009600041c1b05110860004034645053c6003214020d050f600041e480253056000402050f0e4b600022e050f0e0860004023a390e0860004524802350560004320d0f000760004020b0d440f6000305110e0709600042a290f0e076
  | 6, 0, 6 => 0x403023f3e3c6000403023b4305600042a0229110e60004030233110e600040d050f075e60004030211000e60004250d24110860004520254000e600040f000e0708600040b050f0e07600320d050f0709600040205110e0860004033b054a07600020f000e0809600040d050f074b6000432023b0f006000350020d050f6
  | 7, 0, 0 => 0x42b020d050f0e70000045b0d050f086000403020f59000e7000403022705110e7000425020d0511087000403250d240f3c70004c00302050f0e7000004201f0d05116000004480d055108600041e0302050f3d700040348050f510e700042b0302050f0e7000403020d050fb87000004020d330f086000403020554110e700040390020d050f7000314020d050f117000004020d050f4f6000004033b053c076000302413b0d050f700000403370d05116000004310d050f0860004030d052611077000403020d380511700041a020d1d051170003020d052659117000403253b0d240f7000403020d050f7f70000040335050f076000403023b0d760570004aa0302050f0e7000403020524110e7
  | 7, 0, 1 => 0x40d050f0e0708700045248020d055470003020d0f000e097000403026a0d3a0f700041e023b0b050f7000403020f000e77700520314020d050f700041e03020d0f007000403050f0e070870004030d050f4a07700000403480d5100600041c020d0f000870004030205c10f0e70004030d1305110770003020d0511070970004037b020d051170003020d05111709700041e033b050f07700041c020b0d050f70000020d05110809600000403310d0f0060004c70302050f0e7000302050f110e09700040325050f0e6c7000004023b0b053c600040d050f0708a770000042b020d05116000402050f0e77087000403160d050f0770000040222210f0860004030257050f0e70048020d050f08097
  | 7, 0, 2 => 0x4030d3a051107700045203050f0e0770004c20302050f0e7000403020d3a2611700000402050f0e086007d03020d2e050f70004020d63051108700040302a50d050f7000432020d05260f7000004030d1100076000004020d055455600040d05210f07087000403023f0d3e0f700040d050f39070870004030205110e6c70004030d0f000e0770004031402050f0e7000004032f0d3a0f6000403020d050f3d7000403020d05115d7000402220d0511087000402050f000e0870003020d3a051109700520302050f0e09700000403020d341160000040d051107086000403027c0d050f7000403050f110e077000003020d110009600040364050f0e077000403020d050fb170003022705260f0e7
  | 7, 0, 3 => 0x40373020d05117000314020d050f0e7000403026a3b050f70004030d75050f07700042b030d050f0770004030d055411077000403023b053e3c7000403020d050f67700040325020d560f7000448270d050f0870004023b0d0f00087000403020d5605117000403023b053c3d700045202050f0e6d70004aa030d050f07700000403020f000e6000004250d240f08600040302530d0511700041e030d05110770004023b0b0d050f700040d050f5907087000403020d6311007000403023f3b053c70004030276050f0e70003020d1b0511097000403020d050fd07000403020d9f050f7000403020f000e6d700040302710d051170004033b0d050f077000403020d43050f700040302980d050f7
  | 7, 0, 4 => 0x41e03250d240f70004038f020d050f700045202350d050f70004020d051112087000403423b0d050f7000403023b0d058570004031c020f000e70004039e0235050f700000432020d0f006000004020d300f086002a0302050f0e097000402720d050f0870000030205110e09600040348740d050f700041a020d1d050f70004a603020d0f0070004023b350b050f700034802050f0e09700040302350d0f00700030d050f1107097000403250205110e7000004034805510e6000432020d050f07700041c02050f0e087000403570d050f0770004020d0f3c0008700000314020d051160004037a020d05117000403020d050fcc700040318020d110070000042a02290f0e60000040302330f0e6
  | 7, 0, 5 => 0x4031c1f0d051170004035c250d050f700043202270d050f7000403026a0d051170000040d050f070860003023b0d2e050f700040364020d11007000403050f390e077000403020f51000e70004020d0f0008a87000403021f0d1100700040302050f0ec47000403020d1100087000403020529110e7000403022205110e7000432020d05240f7000403050f0e5d07700002b02270d050f600040370020d0f00700046f020d050f0870004035c023b050f700042a03050f0e0770000040305110e0760000031c1b050f0960052030d050f07097000403023b0d3a39700020d05260f08a97000402050f510e087000403020d050fa27000003020d050fa060004020b0d05260f7000432020d3a050f7
  | 7, 0, 6 => 0x40348023b053c70004023b0d050f8c7000403023b0f000e7000004030216051560000041a020d0519600000403250d380f600040302880d050f700045203020d11007000004032f0d05116000403480235050f700040302050fa10e70000040325240f0e6000302050f0e77097000403050f590e0770004032f0d050f0e700040302d10d050f7000403180205110e7000325020d0511097000403020d2e051170004034802530d057000004030d0f00076000003480d0551096001c020d050f0809700040302050fb70e700040302050f0e9a7000403050f0e6b0770004030d76050f077000003020d330f0960003020d2e050f3c70004023b050f0e087000003020d050f916000003310d050f096
  | 7, 0, 7 => 0x302220d051109700040205260f0e087000402790d050f087000403403b0d050f700040302810d050f70004030272050f0e700040302780d0f00700040302050f850e70003b314020d050f7000403023b0d440f70000030d05110709600040302050f0ea4700041e021d05260f70004035c020d0511700030d050f0e0709700049b0302050f0e7000403050f0e770770000040302050f3660000040322210f076000403020d0f0055700041e030d050f077000403020d0f8a0070004521c020d0554700040325020d26117000403250d0511177000403020d96050f7000402780d050f087000403023b0d058a70000042a0d290f076000004020b0d0f006000004030235051160004034827050f0e7
  | 7, 0, 8 => 0x402740d050f0870000020d2e050f08600042003020f000e700040383020d050f7000403050f0e6d077000403023a0f0e6b70004036f02050f0e700023b0d050f080970004030d052911077000403220d0511077000403050f000e077000403020d050f92700042b020d1d050f700040348050f0e6c700042b023b0d050f700040302790d0f007000403640205110e70004020d05110e08700035c020d05260f7000448020d0511087000403021f05110e70004ab03020d0f0070004201f3b0d050f70004030205110e3d70004030205110e08700042002050f0e087000004020d3a39086000403020511120e7000403023a0f390e700041e020d0f00087000403373b0d050f700040399020d050f7
  | 7, 0, 9 => 0x3020d0f3c00097000452020d0f54007000004020b050f0e6000032020d050f096000403b3020d050f70000041e021d0f006000003020d050f2d6000403020d0f003d70004030d050fb707700040302740d0f007000403023b0d05117000452030205110e7000452023b0d05547000403023b0d340f70004a303020d0f00700000403023b054a600043b0d050f07087000402050f0e0708700043225020d050f700041e52020d0f0070003020d1d0f000970003023b0d0f0009700040325270d0511700000403050f0e0760004031c1b050f1170004020d052111087000004020d050f4b60004030d630511077000403020d11000e7000403020d050fcf700040348020d110070004020d050f3d087
  | 7, 0, 10 => 0x403020d5911007000403020d050fad7000403020d05116570004030222210f117000403023b053c0070004023b0b0d0f007000403020d750511700040302050f0eb870004030d0f3c00077000004320d050f07600040302050fc50e7001e03020d2e050f7000003020d300f096000452020d0597547000004020d050f5e60004023a050f0e087000452031c1b050f70004a6030d050f07700048403020d0f0070004033b0d0f0007700040302660d05117000403020f000e07700040302050f0e557000403350d050f07700040302680d0511700040302050f8a0e7000004020f000e086000403020d050f7e700040346023b053c700040d050f3c07087000403020d0f1100700031c02050f0e097
  | 7, 0, 11 => 0x40a020d050f3d7000403480205110e7000452030222210f7000302570d05260f7000403640d0511077000302270d052611700040d050f0708a8700045203020d75057000314023b0d050f700000403023a390e6000402720b0d050f700041e03020f000e7000403020d116200700040227050f0e08700040302890d050f70004030d0511070870004030d0511120770004030d3a0f390770403020d1d56050f8000452020d0526547000004030d300f07600040d05260f070870004020d38050f08700020d05260f590870004030d050f85077000302050f510e09700040205240f0e08700045203020d0f00700040302b60d050f7000004230d050f08600040302570d051170003021f0d0511097
  | 7, 0, 12 => 0x452030d0511077000004020d0511086040302530d05260f800040302050f110e7000403020539110e70004037b020d0f00700045202050f540e7000403020d0f00a770000020d0f00080960004031c0235050f700040302050f0e3d70004030274050f0e700040314020d05117000003022e050f0e60004030205110e5d700b40314020d050f7000403690d050f0770000020b0d050f0960004a30302050f0e700040393020d050f700040302270f000e700041e5202050f0e70003023b050f0e097000004201f0d0f00600042a030205110e7000314020d050f3c70004020d051100087000403020d050fba7000403020f54000e700047b020d050f08700000403370d0f00600040302050f0eb17
  | 7, 0, 13 => 0x42a020d2911600000403020d33116000004021d050f5a6000403020d05116e700000403310d05116000403020d330f0e7000403020f000e6c70004035c480d050f700041a03020d110070004520302050f0e7000402710d050f087000403020559110e70004020d3a260f0870004023b0b050f0e700000403020d11006000402d10d050f0870004030d050f0755700000452020d54006000403250d240f1170004030205110e6b7000403020d76051170000040d0f000708600030205260f0e5d7000402050f0e6c0870000040b0d050f076000403020d0f005a70004840302050f0e7000302780d050f0970004033b050f0e0770004023b0d050f4b7000004031c1b0511600020d3a050f08097
  | 7, 0, 14 => 0x41e030d0f000770004031c020d11007000014020d050f086000403023b35050f7000403023b0d56057000473020d050f0870000040337050f0e60004032f0d1d050f700040305260f0e077000403790d050f0770004030238050f0e70004032f3b0d050f700030205260f590e70003020d0f54000970003020d05110e097000347023b0d050f70004030205110e7770004020d56050f0870004020d05111508700045203250d240f70004ab030d050f07700043203020d0f007000403020511620e700000403022221116000348020d0511097008d023b0b0d050f700041e0d050f0708700200302050f0e09700041c020d05110870004020d630f00087001e03020d0f00097000403480d05510e7
  | 7, 0, 15 => 0x4030d050f3d0770004950302050f0e70000030d2e050f0760004030205bf0f0e7000403020511000e70004a3030d050f0770004037a020d0f00700041e520d050f07700033b0d050f07097000302050f0e0709700042a030d05110770004037b02050f0e700040302050f0ea77000002050f0e08096000403023b0f3c00700000432023b050f60004037a023b0d0570004030205c30f0e70004030d05110e0770000042b02050f0e600040302160d11007000403020d111500700042502050f0e08700001e021d050f096000403020d050f6570003020d050f3d097000004201f050f0e6000004030d3a39076000302740d050f0970004800302050f0e700040302530d0f007000403024c0d050f7
  | 7, 1, 0 => 0x4020d0f1100087000403023b05263c700041a030205110e7000403023505260f70004020b0d050f1170004023b0d05110870004020b0d053e0f700040222050f0e087001e0314020d050f7000484030d050f0770003023a050f0e097000004030205110e60004020b0d050f3d7000403020d1119007000004520205540e60000040302340f0e6000004050f0e0708600040370023b050f70004031c7a0d050f7000003020f000e0960004030d0521110770004030d050f1107700023b0b0d050f0970004030d053911077000403020d511100700030d050f3c070970004520d050f54077000403020d0f007770004038e020d050f70000041e1d050f0760004020d0f0008a970004030205110e6d7
  | 7, 1, 1 => 0x4031c1f0d0f0070000042f0d050f08600041e03050f0e0770004031c0205110e70004030d051162077000403020d3c1100700000432020d0511600000403180d051760025020d050f080970004020d2e050f0870000201f0d050f096000403020d050f94700043248020d050f700040348270d05117000003370d050f096000403020d1d110070004030271050f0e7000403023b0d1100700040302350d05117000003020d2c050f60004033a050f0e07700040302693b050f7000403023a260f0e7000452030d050f0770004026a0d050f08700000403250d241160004030d055911077000484020b0d050f70004ae030d050f077000403250d240f0e7000004030f000e07600043b0b0d050f077
  | 7, 1, 2 => 0x52020d05540960000040302350f006000003020d340f0960004030d050f07a7700000d050f070809600040302050f620e700040325020d1112700000325270d260f600045c020d050f0870000042b0d050f0760004030216050f3d700040370020d051170000031402050f0e60004037a02050f0e7000403023b053c0770003027c0d2e050f7000425020d260f0870004037302050f0e7000004023b053c08600000403020d30116000480030d050f0770004be0302050f0e70004020d052611087000403020d050f6e700040302720d05117000403023b45053c7000403050f540e07700041a03020d0f007000403021605110e70004030256050f0e700040302bd0d050f7000452020d0f00087
  | 7, 1, 3 => 0x403023b05243c70004020d0511070870004020d05111708700041e03023b0f007000004030d0511076000402050f110e0870004039c020d050f7000004520d0554076000004030d340f0760004020d0f0008a77000403029d0d050f7000403ca020d050f700040302690d05117000004520235050f600040302160d0f0070000030d0f0007096000302050f0e6c0970004035c020d0f007000403023b3a053c70004030d050f075a700042003020d110070004c60302050f0e700040302ac0d050f70003020d2e050f117000403020511190e70004036f020d051170004b90302050f0e70002220d050f0809700040302050f0e92700000403023b3c0060004030d051100077000403020551110e7
  | 7, 1, 4 => 0x41e0253050f6000432030d050f077000403710d050f077000403020d110007700000403480d330f600040302273b053c70003020d051115097000403020d1117007000004020d110008600040302050f0e7e7000403020f11000e700040d63050f07087000403020d050fbb700040364020f000e70004020d0f000e087000302530d050f097001e030d050f0709700031c020d051109700040302050fb00e7005203020d2e050f7000004020b0d05116000448020d0f00087000403021f0f000e700000403020d13126000403023b05110e7000403020f000e08700040302220d11127000403020d050fcb7000403020d0f4a00700041a030d05110770000040a020d050f6000448020b0d050f7
  | 7, 1, 5 => 0x402050f0e08c870004033b050f3c077000403023b0d0f00700045203020f000e7000004032f050f0e60004020d052411087000403160d0511077000402660d050f0870004030d56050f0770004030d051115077000402863b0d050f7000402680d050f0870003020d56050f597000403230d050f117000432020d050f00700032502050f0e097000403022e050f0e7000403530d050f07700040302050f3c3d70000042b020d3a0f60004031c0d051117700037a020d050f097000403020d050f9a700040302780d05117000403020d050f58700041a0302050f0e70004020b0d050f3970004023b0d050f0870003b214020d050f70004020d3a051108700045202050f0e087000403026a050f0e7
  | 7, 1, 6 => 0x3023b0d05110970003020d0f000809700030222050f0e097000403480d0f510070004030d051119077000403020d5411007000402050f0e08a770004030216050f0e700045203230d050f700040346450d050f7000003050f0e07096000403483b0d05517000402050f0e08c970004035c02050f0e70004aa03020d0f007000420030205110e70004023b0b050f3c700042a023b0d290f7000403023b0d330f70004030d050f77077000402570d050f08700041e03020d110070004020d0f59000870004520302780d057000402270d0511087000403020d3a390e70004020d1b05110870004032502260f0e70004020d75050f087000403020526110e700040302790d051170004020b0d050f597
  | 7, 1, 7 => 0x4b50302050f0e700048b023b0d050f70004030d1d05110770004033b0d05110770004030205110e07700040305290f0e07700040322050f0e07700042a02050f0e087000403020511170e70000040205110e08600040302870d050f700044802050f0e087000446020b0d050f700040302710d3a0f700040d050f110708700040302600d051170000041e021d05116000403b2020d050f700040302cd0d050f700042b020dbc050f7000403020d05113d70003020d0f110009700040302740d05117000003020d2e0511600040302570d0f007000403021305110e70003020d2e050f0e700041e48021d050f700040302270d110070003020d1d0511097000403020d1b11007000402d20d050f087
  | 7, 1, 8 => 0x4020d0f000860000040302053c3d6000402050f0e6b087000403020d050fce7000403020d050f5f70003020d562e050f7000403257b0d050f7000003023b053c096000403020d051167700000452020d054a6000403023a05110e7000403020f000e5d700041a030d050f0770000030235050f0960004032527050f0e700040325023b053c70000041c1b050f0860004520d050f0708700040302af0d050f7000004030211000e6005203020d0f000970004036a0d050f0770004023b0b0d05117000402050f390e0870004030d053c1107700040302610d0511700040348020f000e7000403023b72053c700a303020d05260f700040a023b0d050f70004030d0f1100077000414020d050f087
  | 7, 1, 9 => 0x3020d560559600040302820d050f70004030266050f0e700041e030205110e7000402050f590e08700000403230d051160004030268050f0e7000003020d050f286000004031c1b0f006000452030d0f00077
  | 8, 0, 0 => 0x40302270d0f00700041e52020d050f70003020d1d050f097000403020d1b0f0070003023b0d050f09700042a03020d051170403020d050f11008042a03020d050f0e8000403020d0f54007000403020d05110e7041e03020d3a050f8040325023b0d050f800040348020d05117000403020d050fa97040348020d050f0e80004200302050f0e700000403020d3a39600041e03020d0f007000402270d050f0870004020d1b050f0870403023b720d050f80004030205260f0e700040302790d050f70004ab03020d050f7041e03020d050f0780003020d050f510970004020d05240f08700041e020d050f0870004d503020d050f700040302780d050f7000403020d050fc570004020d3a050f087
  | 8, 0, 1 => 0x4d603020d050f7000403023a050f0e704031c020d050f08800045203020d050f7000403020d05591170004ae03020d050f700000403020f000e60403020d050f590e80004023b0b0d050f70004030d050f3c0770403023b0d05290f8040302223b0d050f8041e0302270d050f8045203020d050f00800048403020d050f70004030d1d050f0770004033b0d050f07700040302050f0e07700000402050f0e086000403020d0521117000403020d050f117000403020d05391170003020d050f3c097000452020d050f5470403020d050f390e80000041e021d050f6041e03020d05240f8000403020d050f3d700040302740d050f7000003020d2e050f6040325020d050f3c80004a303020d050f7
  | 8, 0, 2 => 0x403023b0d050f3d80000040d050f070860403023b0d050f088000003020d0f00096000403020d050f5a70403023f3b0d050f800049503020d050f7000403020d05110070403020d050f000e80003020d050f070970004037b020d050f7000403020d050fa770000020d050f08096045203020dd3050f80000042b020d050f60452031c020d050f80004030227050f0e7000425020d050f087000004201f0d050f600048003020d050f700040302050f540e700000403370d050f60004030d05260f077000403020d38050f70003020d05260f5970004030205240f0e700041e0302050f0e700000403230d050f6000403020d05116270403020d050f11158002003020d050f09704031c020d050f118
  | 8, 0, 3 => 0x403020d56050f7000403020d05111570403020d05260f08800040302530d050f700041e030d050f0770004031c020d05117000403020d630f0070003020d1b050f097045203023b0d050f80003020d050f5409700043203020d050f700040302710d050f70004030d3a050f077000403020d3a260f70004020d63050f087001e03020d050f097000004030d0f00076048403023b0d050f800040302050f0e6c700041a03020d05117041e0325020d050f8000403020d050f5d7000402220d050f0870403020d1d050f1180403023b0d050f118040364023b0d050f80003020d3a050f0970403023b0d053e0f800000403020d051160403021f3b0d050f800000452020d0554600000403020d340f6
  | 8, 0, 4 => 0x403020d1d05117000403023b0d05117000403020d0f000870004030205290f0e70004030222050f0e7040348020d1d050f8040348023b0d050f80403020d050f1107800000403050f0e0760403020d050f111780004020d050f110870403020d05210f5180004c603020d050f7045203020d05260f8000403020d05111970004b903020d050f700000302050f0e096000403020d05511170403020d050f510e8000403020d050f7770004020d050f08a97000403020d050f6270004032502050f0e700000314020d050f60004037a020d050f7045203020d05970f800040373020d050f7000403023b050f3c70004030d050f540770403020d05260f118041e0302220d050f800040302160d05117
  | 8, 0, 5 => 0x42003020d050f0e8040302270d050f11800040325020d260f70403020d1b050f11800000403023b053c6000403020d0526117045203020d3a050f80403020d1d050f5980403020d05260f0e80403023b0d050f598000004030235050f60004020d050f08c8700045203020d0f007000004032f0d050f60403020d05240f118000325020d050f097000403020d2e050f700041a03020d050f7045203020d050f0780403020d1d050f398000452020d050f0870004031c1f0d050f70403023b0d050f3980403020d3a050f118000403026a0d050f7000403020d053c117000403020d0f1100700040364020d0f007040348020d050f3c8000403020d050fb07000403021f0d0f007042a03023b0d050f8
  | 8, 0, 6 => 0x40348020d0f0070403023b0d050f0080403023b0b0d050f80004b503020d050f7000403020d05110770004030d05290f077000403220d050f07700042a020d050f087000403020d0511177000004020d05110860403020d050f0e07800040302050f110e70004036402050f0e70004020d050f0e087000448020d050f087000403021f050f0e704520302270d050f800040302050f0e087045203020d1b050f8040346023b0d050f8040302570d050f598000403020d050f4a7000403020d1305117000302220d050f09700041e03023b050f70004020d050f08a77045203020d05240f800040302160d050f70000030d050f070960004020d050f08c970004035c020d050f700042003020d05117
  | 8, 0, 7 => 0x40302570d050f70003021f0d050f097000403020d0f5900700040302270d05117000403020d1b051170003020d050f08097040325020d050f118040302270d050f0e8000403020d75050f7000403480d050f51700042b03020d050f7000403020d0554117040348020d050f5480004aa03020d050f7000403020d052411700040302660d050f700041e03020d051170004020d050f5908700040302680d050f70403020d05240f0e8041e0348020d050f8000403023b0d050f7000403020d3a051170004520302050f0e70403020d3a050f0e80403020d050f3c00800040325270d050f700000403020d110060004020d05210f0870004020d050f390870004030d63050f077000403020d0f000e7
  | 8, 0, 8 => 0x4520302d40d050f8041e03020d050f008045203020d63050f800040302050f590e700000403020d0f00600040302050f0e6b7000403020d76050f704520302220d050f8000004031c1b050f6000452030d050f077000004020d050f08600040302050f390e70403020d63050f11800040314020d050f700040302050f0e5d700042a0302050f0e70004020d050f000870403020d05290f118040302220d050f1180403023b0d050f518000004030205110e6005203020d050f0970004034802050f0e70004030d050f11077000403640d050f077000302270d05260f704520325020d050f80004030d050f070870403020d1b050f3980004c703020d050f70003020d050f1109704031c023b0d050f8
  | 8, 0, 9 => 0x4030d050f39077000403020d0f5100700040302050f0e6d7041e031c020d050f8000403020d052911700040302220d0511700040302050f000e70403020d05260f3c800042a030d050f077000004030d0511076042003023b0d050f80004020d050f510870004030d050f0e0770403021f0d050f1180403020d1d05260f80403023b0d05260f80004031c020d0f0070403020d050f11128002a03020d050f097000003020d05110960003020d050f0e09700040302050f0e777000004030222210f600041e03020d050f7000348020d050f09700040325020d0511700000403480d0551600041c020d050f087040325020d050f0e80000042a020d290f600000403020d330f600000403310d050f6
  | 8, 0, 10 => 0x40348020d050f08800000403020d300f60004020d05260f08700040302720d050f70403023b0d05240f8041e03023b0d050f8000403020d050f8570403020d3a050f3c800049b03020d050f70004031c02050f0e7000403020d0f3c00700000432020d050f60403023b0d3a050f80004a603020d050f700040348270d050f7000403020d1d0f007000403023b0d0f00700040302350d050f70403020d050f3c078000403020d050fa1700000403250d240f60004020d050f3c0870004030d050f5907700040318020d05117000403020d050fb770403023b0d050f0780004023b0d050f0870403023b450d050f80000040302050f0e6000403020d630511704031c020d050f5480004030d05210f077
  | 8, 0, 11 => 0x4020d0f0008600031c020d050f0970403020d05260f548000004020b0d050f6000403023b050f0e700045203020d051170004020d050f07087045203020d050f0e8041e03020d05260f804520348020d050f8000004030d050f0760403020d05210f11800040302690d050f70403021f0d050f39800042003020d0f007040302270d050f3c80004036f020d050f70004030d050f0007700040364020d0511700040302050f510e70004020d050f08a87040302273b0d050f80403020d050f110e8000403021f0d05117040348020d050f1180403020d05240f3c8000403020d0511087000420020d050f087000403020d05111270403023b0d050f548000403020d3a0f39700040370020d050f7
  | 8, 0, 12 => 0x45203020d05210f8000403020d0f00077000403020d050f557000403020d050f8a7
  | 9, 0, 0 => 0x40325020d050f700040302050f0e6040302270d050f70403020d1b050f70403020d050f5470403020d05240f7041e03020d050f70403020d3a050f7000403020d0f0060403020d050f0770004020d050f086042003020d050f70403020d05260f70403020d050f3c70403020d1d050f70403023b0d050f70403020d050f51704031c020d050f7000403020d050f60403020d050f0070403020d050f5970403020d05210f70403020d050f397042a03020d050f7000403020d051160403020d050f0e7040348020d050f7045203020d050f70403020d050f117040364020d050f70403021f0d050f70403020d050f087
  | 9, 0, 1 => 0x403020d63050f70403020d05290f7040302220d050f70004030d050f0760003020d050f096
  | 10, 0, 0 => 0x403020d050f6
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 44
  | 6 => 60
  | 7 => 68
  | 8 => 68
  | 9 => 60
  | 10 => 52
  | _ => 0
def stateM : Nat → Nat
  | 5 => 0xfffffffffff
  | 6 => 0xfffffffffffffff
  | 7 => 0xfffffffffffffffff
  | 8 => 0xfffffffffffffffff
  | 9 => 0xfffffffffffffff
  | 10 => 0xfffffffffffff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0xf0000ee1f00e3c67ff8e0fe1f001c3980071f01e000003ff0001f11e0001c00000700000000ffc670ffe0100000000000ffffffff00003fff001fffff001fc1ff07e001ff00ffc670ffe0100000038070e0dcf1dc00ffffff0000000000ffc000ffe0000000e03e00f81ffe0000e3c670f8e0100000fc7f8f1f230e23
  | 1 => 0xe00000f800000000fff980ffff01e0001c00000700000000fc3f80ff1fffe000003800001f000000fffff0ffff11e000ffc000ffe0000000fffff0ffffffe000e03e00f81f100000fffff0ffff11e0001c3980071f01e000e3be700000000000fffff0fffff1fc00038070e0dc11c000fffff0ffff11e0001c067f0700fe1f
  | 2 => 0xe03e00f81ffe1c0003807f0000000000fc7f80ffffffff001c0000ffffffff00ffc070ffe0000000ffc070fffcf1dc00038000e0c00000001c418fffffffff00e03e0000000000000380700000000000e3be70f8dfffdc00000000e01cf00000e03e00f81fffc0001fb9f0e7dff1fc00000000001c01c000fffe00fffffe00
  | 3 => 0x1fb9ffe7dfffff00000000001ce1dc00e3c670f8e010000000000000000000001c398f071fefff0003807fe0dcffdf000000000000e01c0000000fe01cfe1f00e03e00f81ffe0000e3c67ff8e0fe1f001c3980071f01e000038070e0dcf1dc00038070e0dcffdc00ffc000ffe0000000e03e00f81ffe0000038070e0dcf1dc
  | 4 => 0x3fff001fffff001f807007000000001c00000700000000003800001fefdc0000398f001fefff0000000000000000001c00000700000000e03e0ff81ffe1f00fc3f8f0000000000fc3f8fff1fffff00003800001fee0000000000e01cf1dc000380700000000000e03e00f81fffdc001fb9ff0000000000003800e01ffe00
  | 5 => 0xe3fff0f8ff11e000003f8f001fffff00e3c67f0000000000fc3f80071f01e000e03f80f81fffe00000067f0000fe1f0000000f0000000000fc7f80ffff11e0001c398f071f01e00003807f0000ee1f00003ff0001f11e00000000000000000001c000f0700ee1f00ffc00fffe0ee1f000000000000ee0000e3be7000000000
  | 6 => 0xfc3f800000000000fc3f80ff1f11e000e3c000f8e0000000e00600f800fe0000038070e0c0f01c001fb9f0071f01e0001fb980e7df01e0001c3980e71ff1e000e3be70f8df11c0001fb9f000000000001fb9f0e7df11e000ffc00000000000001c39800000000000fffff00000000000fc3f80ff1f11e0001fb9f0e7df11e0
  | 7 => 0xe3c67ff8e01e030003807fe0c0fe1f00ffc07fffe00000001fb9ff071f01e000e03e0f0000ee1f00e0000ff800ee1f001c398f0000ee1f0000380f001fee1f0000000f0000ee1f0003800fe0c0ee1f0000000f001cefdf001c3980071fefe000e03e0f00000000001c398f00000000001c3980071fe1fc00fc3980ff1f01e0
  | 8 => 0xfc3f8f071fefff00fc398fff1fefff00ffffff0700000000e3fffff8ffffff00fc0000ff000000000000000000ee00001fb9ff071fefff001fb98fe7dfefff001c0000071ce1dc001f8000e7c00000000000000000e01c00fff98fffffefff00e00000f800e01c001c00000700e01c00003800001fe01c00ffc000ffe0e01c
  | 9 => 0x380700000000000fc3f80ff1fffe0001c3ff0071f11e000fc0000ff00ee0000ffc00f0000000000e3c00ff8e0ee1f00e38000f8c0ee1c001f8000e7c0e01c00038000e0c0e01c00000000001cefc000ffc000ffe0ee0000e3c67ff8e0101f00fc3f8f071f01e000e0060ff800fe1f00000000ffffffff00e03e0000000000
  | 10 => 0x1c3980071feffc00ffc000fffc01c000fffff0ffe31020001fb9ff0000ee1f00fff980071f01e000ffc00f0000ee1f00003fff0000000000003980001f01e00000000f0000ee1f00fff980ffe00000001c000f070000000000000f0000000000ffc00fffe0000000e3c670f8e0fe1f00fffff0ffffffff00000000ffffffff
  | 11 => 0x3807fe0c0fe1f00ffc00fffe0ee1f001f807007000000001c00000700000000e0460ff8e0fe1f00fc7ff01f3f11e000ffc0700000000000e3c070f8e0f01c000000000000e01c001c3980071fe1fc00ffc000fffcf00000fffe70ffe0000000ffbff0071f01e000e3be7f0000ee1f00e38670f8c0fe1c000000000000ee1c
  | 12 => 0x1fc1f0ffff11e0001ffff007ff11e0001c3980071fefe000e3c670ffff11e000ffc7f0ffe011e000fc3f8f0000ee1f00003e00001ffe0000000070001cf1dc00fffe00ffe0000000fffe0000000000000000000000ee0000e3c600f8e0fe0000e3c00ff8e0ee1f00ffc600ffe0fe0000e0060ff800fe1f00ffc070ffe0f01c
  | 13 => 0xfff9800000000000fff800ffff000000e00000f800ee00001c000007000000001c3f80071fffe0001c398f071fefff0003c07ff8e0fe1f
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x24ca9f2965ee7f0062c65da860dc1a009d39a2579f23e50024d5682970550a00bde0087fea448a00ffe448ffea548a000000007fef66ef00001ff70015bb75000dc1bb03e001ff00ffeccaffef76ef004b9571e2dcf1dc00ffffff8010991000ffe008ffea448a00f23e44fc1ffe0000460cc28105326500b46a8e1d230e23
  | 1 => 0xf22000fc0a440000fff9aaffff67ef009d2000578a008000ff3fe6ff9fffe500903800541f220000fff568fffa558a00db2000d68a008000fb3f64fe9fff8000d23440d41a100000df3de2d79f33e500993120569a018000fbbf758010991000dbb571f6def1dc004b1560c298118000db3560d69a1180009d2655578a9890
  | 2 => 0xf2be55fc5ffe5c006fdfff80109910009020007fef66ef009d20007fef66ef00fff579fffad59a00fff579fffef5de004b8000e2c840880004408a7fef66ef00f23e4480109800004b95718010911000fbbf75fedfffdc00421440e01cf00000fb3f64fe9fffc400dfbdf3f7dff3fd00091120429c21c400fffe4cfffffe8a
  | 3 => 0xffffffffffffff0009913162dce1dc0042044080001000000408820105226500bdfbbf7fffefff006fdfffebfdffff000080112044e05c0066dedfe97dfe7f00f6fe4cfd7ffe0a004206558000981000bdf9aa7fff67ef006fd579ebfcf5de006b9f75eaddffdc00ffe88affef66ef00f63ec6fd1ffe65004f9df3e3ddf3fd
  | 4 => 0x17750010991000fff579fffad59a00bdf1397ffac59a00b9bb357edfefdc00001bb70015ab750024c88a2965666f00bde88a7fef66ef00f6fedffd7ffe7f00ffffff8010991000ffffffffffffff00b03a047c1fee00004b9571e2dcf1dc004f9df38115b37500fbbf75fedfffdc00ffffff8010991000f23e44fc1ffe00
  | 5 => 0x4215608010110000000a8600052a650062c65d8000981000ff3fe6d79fbbe500f23fe6fc1fff6500000655000098100024ca9f0000881000902000568a008000bdfbbf579fabf5006fdfffa975ff7f00001560001011000024c0082960440a00bdea9f7fefeeff00ffea9fffefeeff00200a042805ee0000ffbff78115bb75
  | 6 => 0xff3fe68010990000db3560d69a11800062c008a860440a00620644a800dc0000428451a040d01800dfbdf3d79fb3f500dfb9a2f7df63ed00df3de2f79ff3e500db3560d69a118000dfbdf38010911000db3560d69a118000ffe00880000000009d39a20010010000db35608010110000df3de2d79f33e500df3de2d79f33e5
  | 7 => 0x62464c88201c020062c65da860dc1a00fffffffffadd9a00ffffffd79fbbf500f6fedfa975fe7f00f6ea9ffd6fee7f00bdfbbf2975ef7f00b4fa9f7d7fee7f0020c21d2860cc1a006fca9febedeeff002ddbbf6bfdefff00bd3ba67f9fefe500f6fedf8010981000bdfbbf00108910009db9b377dfe3fd00ff39a2ff9f67e5
  | 8 => 0xffffffffffffff00fffbbfffffefff00fffffffffadd9a00421ff78015bb7500ffe008ffea448a00240a862905ee6500ffffffffffffff00fffbbfffffefff00bdf1397ffee5de00ffe008ffea448a000488932145e27d00fffbbfffffefff00f2a011fc4ee45c009da01177cee0dc0090b811745fe25c00ffe019ffeee4de
  | 9 => 0x6fd579a970d51a00ffffeeffffffef009d3de2579f33e500ff2a86ff8feee500ffea9f800088100062c21da860cc1a00fbaa15fecfeedc00dfa893f7cfe2fd004b8011e2cce0dc00291b246a9defc400ffea0cffefee8a0042c4598060101a00ffffffd79fbbf50062c65da860dc1a000408827fef66ef00f63ec68115ba65
  | 10 => 0xbdbbb77fdfeffd00fff128fffe65ce00d224409402100000ffffffa975ff7f00fff9aad79f23e500ffea9fa965ee7f00001ff700109910000019a20015236500000a970005aa7500fff9aafffa458a00bdea9f578a88900020c21d0000881000ffea9fffeacc9a00420440a860540a00db3560ffff77ef0024c0087fef66ef
  | 11 => 0x66cedfa965fe7f00ffe21dffeacc9a00dfb571d79a9190009d3120579a01800020420c28604c0a009035601412110000fff579801091100062c459a860d41a0024c0192964e45e00bdf9bb7fffe7ff00fff448fffef48a00ffff7dfffadd9a00ffbff7d79fbbf500ffffffa975ff7f00628655a840dc1800208a152845ee5c
  | 12 => 0x90120568a0180000915600290118000bdfbae7fffefef00420440d68a1080004b05608280118000ffffffa975ff7f00001e440015ba00000015710014b15400fffe4cfffadc8a00fffe4c801098000024ca0c2965ee0a0062c64ca860dc0a0066ca9fa965ee7f00ffe64cffeadc8a0066cedfa965fe7f00ffe459ffead49a
  | 13 => 0xfff9aa8010010000fff808ffff668a00f22a04fc0fee00009d2882578f22e5009d3fe6579fbbe5009d3bb7579fabf50000c0192860441a
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 215 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem wd_0 : ∀ i, 0 ≤ i → i < 128 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 128 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem wd_128 : ∀ i, 128 ≤ i → i < 215 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 87 128 = true)
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 215 → wireDOK i = true := (range_split wd_0 wd_128)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 215 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 215 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0xff) :: stateWiresD n (ids >>> 8)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0xff) :: stateWiresS n (ids >>> 8)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 11 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 5 => 5
  | 6 => 626
  | 7 => 2160
  | 8 => 211
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xed6345c9d2a69730b26a646736a8a111231d5079
  | 6, 0, 0 => 0x1658ec5616541029163694bf15ff171615e6266715d0f7c1153dc90f153d1f1014b3ba6d1461d13713fddd5613f2ead7127163cf11ef7e1e10de1144108dfb00107400660f7752f40f27dc140f2081030f09fad50ef542660eccb7400e9b7ac70e2146200e1d654e0da501c20d6e65f60cf9cfce0cf7765c0caedf080c6bf2bb0bf576830bd83bfb0b4d1db00a33c96509cf5899097f42550979a5d3090fc5e1090ca4c6089cd0ff088cedd708770ba60872a45508707bd2086ba10a082a1dbb0819ffed07e9699407b18e4b072b8745060d28c705cec3ef04a48fc5043774010436cf8903cdafc4037cc55602d338cd02402263019a0d4d00ae95180046e4ed
  | 6, 0, 1 => 0x33d88edc332ee49d32c8e06a31ad60fd3181ce44310fca6430b17a1b2fd7a63b2f3679eb2f1607bd2ed593102ece18e22e00a7792d7eac952c6b0b4a2bf9805c2be5f3fb2bd135332b93ca5a2b8c762a2b4fd7bb2ae868082ac299d12a0c9307285367de27ab8edf2760319a26c2811a26c1d593263f8ca326018c0d2402d8e522f32c97225b92f7224f4a5422228024220a3b1221f40ce02195415a20e8daf220be61591ff2102c1fd528dc1eaf028e1e4901931dd8228d1daddc891d0f1aa71ccc29191c31fbbb1bca6d001ae554351ae4d3311aace10f1a25eb4e19f7414419a4c68718e357811841966d183d5a6b17802805177c24c6167d670d16597d23
  | 6, 0, 2 => 0x4ac1eb5a49ac6b2e499a357b496d24814926b510481b4fe54802432547a701874789a6fd475962ae4716c152464349f845f7fc1c45be32a945b84e384437563943cfd022437923884371049c42ad9c65429a249b4293091941826078417ecd7641437c424126cadd40d876e940745b4f3f950d843f8e322a3f55de1a3f2509473eb752293e51fe3b3e1d34483d7b1e3a3d4337b83ce2c1c13cd6190a3cc2b2363cc117773cc096733c2882643bf6b9653bf368d73bcc4b8e3b5c06d43abd65e23a7cd14d3a34c39739f7af7a39433a0538d4220938a41372386871c337fd47963747122336f111dd36d19d7636948cac34bd92e334b49b2d34702ab833fd04f0
  | 6, 0, 3 => 0x6539ae46647457d264182a7d639477c4635e23ba60d5834a60c081b760a2a7735fb68be25f779d215e3b543e5e177c725dea9a3c5d900afd5d09e2a35d03b9ec5b18a40e5aad18295a59ee8459e43a0358d9029158c3b61b58bcfd2358afb4c057ec096e56c84aaa5690b39e565ba58f56549b0b564852af55aa1a505483357b54703f9a543df55c543154da53bf00475391b86c530f3cf3529e822851f280be50e4481950c74ff0504483b24fdecd1d4faa861b4fa4fd2b4f767a5f4f5a6fd74f3869254dfab27e4dc98a5c4d9f88fe4d947f0c4d4c66a74d3dcf844cff85024cb8dc994c9dcdca4bd446dd4b7caab04b4d31944b2b0a7d4ae3c8134adcf315
  | 6, 0, 4 => 0x82771924823f4a2e82079cb081ea047c818f753d813734568103242c80d6d68b802964717ff33fb47fefa5537f5540ab7e32fd247cd86cd17c38b94a7c12f7dd7c06f5ba7bd83eff7abfddae7ab6d2f37a98c0657a718c707a5bc2797933afc278f34f3e7830bf1a782f5f22782415f1780c6c8577b7e213770eedf8764d3db5760cee1f75bd86b4759ba13575637f5a747a456a74289a007423dda972bc591a722046f471a8d4f07141861d6ff0f0146e02eec26dce3ec56d9d1d886d1524fe6cb2f77d6c95aec06a53a82a6a2e811969b7b87869231ba16917c18a680978ab67bb5db467734ea966ad06a56644a9d46624a083658e4a6a657e37b6653d59ad
  | 6, 0, 5 => 0x98f9b99d98aadf4f97a78488978295b196b0ab7f9694e7ea968282e69615da8395fd6b9795ccefb295b07dad9599601b94b1cd8f9496c2d1947f766c94240aa393e72ff0933cb471928b751e90f3eca990cff37190bef59590321fb78fb81d878f9517088f4be6f88f346e288d59a8068ceac1a68ce1a1a98cc727558ca585d08c95ff338c730a938c0b847c8be05f688b9ab91c8b8de4ab8b8551708b76b7228b34a47b8abef05a8a87f08a8a19a66b89b4d5728888c9e78873c2128863d693883d2e4d882f52c48825b57d87f329e7875d8dfa8759faf88706fc3b868e1944866ded6e864aef5b859a5f97855009ac84fccbd18485fe988464003e8406bfc7
  | 6, 0, 6 => 0xb4d962f6b4978af2b433f8c4b43189f7b3de26c4b3b45fa4b2b1c5a5b219bac1b184c531b10e276bb0b62913b08bf0a2b03ee8f2b03b1c5fb02ed5acaecbdfe5aebd64ebae57b51aac9ab39cac420587ac3c988dac251fbdab99d814ab81c7f6aaeccdecaabd402da95aae96a8fc3611a87daad0a8255610a7ed6f8ea7c43dcca6b9e057a6768364a65948dca63fc380a5c1ad00a5200459a49448e9a457dddaa41b0d70a409ce84a406231da2dee76ea2aa842aa214bf32a19a254fa0f3d1909f7abb759f67cab99eb63d339e3c3eec9dd91c739db402419cea49f89bbbe39e9b35c5219ac5a6439aaf15399a8d182999ef1dd799e0b1c199a3c81d99494fbe
  | 6, 0, 7 => 0xce09c8a5cdabef60cd2f9a87cca39874cc95dff5cc8a7a44cc7d1510cbb7367dcb71faa7caecfae6cad7f953cab7206bcaacd43fca9d2391ca58b31cca011952c9c932d0c9683370c85246a6c84ba573c83db92fc5fd5e6bc5bd83aec5ac483fc4bb0594c4acc54ec466d46ec4229849c406c3f6c3c9f9ffc3b3b1e9c2d474bfc28ba3fdc264fb50c242462bc1e22041c174fe8ec1438dfbc0dfc246c0d41187c060a091c05fca4bc036effbc00e3a75bf26eda8bebd2cbbbe3bf042bd930f95bd15572dbd015709bcf80b4bbc70fa57bbc01f92ba5bfb4eb9e8170fb9d5c1adb98347cab95e58f3b931e345b88608f9b8336b67b749d50ab65b39aeb5da9890
  | 6, 0, 8 => 0xeaa71707ea176e26e92f85eae8f80c1ce7f60c43e7f44a52e7772d12e707d935e5c53e3ee542f83be477a166e424b129e350c1d0e24836b6e17cf3aae0b33483e0addab3e06e8c87e01415a2df7c8e7adf55ace5df247d40deddbc76de167681dd82b20add3960d8dccb3a10dc530cc6dc179f3ddbe06c38db7868cbdb2c04c2dac72978d9f9fb5ad9a47bd8d998f72fd961abecd9598d00d8ae62b1d8ad2698d89274ddd7b11757d720f8acd50d91abd4d1b38dd4996489d43a869fd3cf3014d3b19d9bd3abfbb9d3a4eef8d2ab3a9ad2555ac5d1bb8cead19faa06d169122dd0a9a204d05c2170d02ede41cf994254cf55be21cf54d149cebcaa6dce1dc8c9
  | 6, 0, 9 => 0xfffed30affec1097ffe602bdfee5b62efe96ee08fdf9659afdf4a2a0fdf2010ffdc26793fdaefc54fd5fd546fc234e3afb6d2ecffb3d6f2efb2c06dafa76c52ef92deb93f8f01a5ff86a8a06f84d177af832917bf805289ff7527dd0f6f91945f61649e1f5efddebf575af72f4998b8ef486fddcf3803ce8f2aa9b9bf28b39aef1750596f0f66ff4f09eb1f0f0986dafee983d24ee58d852ee21d76eedf013deed2447c7ec532b31ec4582deec0dca4fec017c18eb9cda82eb92a2b4eb865a11eb1a9bc8eaee4e27
  | 7, 0, 0 => 0x7942f90078c51520778512e07540f080750f592074a9e19073f3580073325e0071ebcc606e0c14b0682030e0672c3e8065b88aa0644efc805f6b71805c6c8a205b329cf05b2eac50583d111056af0ba05640497055450540551f2ae05406a46050cdc2204e70ca904e13ce004d064d104a878240499b2c103af1625039a82b70342ee7a0335143e0331cac6032ca92b0303e9c302e42d5302d5aaf50298e12a028e4848024965c902463e47023e56a502232361020a349501fd268701ef9d1c01dfe0b301c0cf2f01be086c01b60d1501ace79001a5ef43019fb52f019f51af0188bf72015f40100129179e01189fc600f26ece00d64fc3002f48270010041b
  | 7, 0, 1 => 0xe61175a0e5684bd0e4ce4f90e499dbe0e4468b30e41de8b0dfa82c30db6ae630db3a33c0d359d660d2f75e70d2e8f990d16ec7b0cfdf2310cd494d50cd3e9650cbb9b490c9f1b370c7515ce0c4d96010c2d1daa0c1de1fe0c1b94cd0c0ce0890b8bbf6b0b7770420b5d6d290b51b6a80b49b0210b2837460b24a2690b236e970b0d46330af1588d0ad79ab60accf95f0acc9fe20a668a080a5db90d0a51d1c70a5133e10a49c2db0a3a77c009d69a7109ca1cde097a53e0095537f909426d5e093db680093090f1090422d808e3b35808c04d1d08ae6dda08915f040883b66b087d4564086df8bb082470f7081475360812e9d2080ba27907a1618d07983db6
  | 7, 0, 2 => 0x14c25be714c1c479148f3e3a147387c814445611140ddc3213f695b113b478a21383ce79135fcdb11345c7c5133bd6551332ca01131fe96f12ed65f812e220cf1288b046128628ed126f0f311255565b1227f09d1205328f11f546a611cdb06811c9fc5911967b201194d57e116cda671158bc8d1149f222112ec5f51121d881111b7f22110fc78210f5763010e737ec108cbea21077ed45106602d21056c74b104dd56b101cf3100fcf05c80fb89c5c0fb19ba80f9f8c4e0f8e1c700f88b3880f7d0cdf0f713d840f6a88660f5e8c8c0f52f7e70f232de10ee047db0edabba70ed51c0e0ed4b88e0ecd7e060eb3ce750e9b4d760e888f2a0e86711a0e68f5ce
  | 7, 0, 3 => 0x1c02e4e51bf4b44a1bd07d241bb5a1481ba9074c1b9b06e31b96e8611b8240731b77905d1b67bfdb1b60776d1b50f3c41b23c71b1b1313111af0de741ae777391adb9ef91ac426e21a939d131a8c40601a812e9f1a0a201f19f944a419ed676819b45c2419b15e68198257a319729319196926bf195e4838194d07b4194a9f6819324a89191c880718f4e10a18f4153718dcd1c218b26e22189eabce184e84e317d58bc317cf99f217bee38a17a485a0178cea6b1783d36c1772d462170706f516c4ecbb16a0d74d1682538b167ebc1d161b60761609134215ef008615e3d4b9159e41e51585bdc915653d68154ef37815303b881515e261150cd70b14e6f9fa
  | 7, 0, 4 => 0x223fc74c22272e9b222383cc21f0ebfc21ea349621d64afc21d2836121c06e8b218a64562171d80121677a5121658ddb2164fee0214d3e852118d8ca210940e420fb4f1320d1d0a420bd10b420b871ce20b6d82820b45b68206d00e3204cfb9c202d9691202b40b22016bee32014b8841ff874121fd910571fc1b3651fa9b9161f90ee121f2f304f1ee037e11ecad99b1ec8cee61ec8714f1eb180c41ea89fbe1e99e7201e85d81f1e33ca591e30bcd41e2098c81df4fadf1de5ae731dbf2e791d64beba1d57bc371d1ff9bc1d1e89ac1d1a31a91cbc6c011cb356241ca711891ca1fc5c1c8d91dd1c7f660e1c711fd81c6686f61c54452b1c3932451c037711
  | 7, 0, 5 => 0x290c466228e13c0c28c3a7c328acf73c2898a3ce285eafc8285080302841347c281da14c27d6d48b27d27a5a27b55b262773e486273c4f3c272db5f02726dd4726d06c1026c74c0626bbad5026b85e4826a0152526144d362613f5a226099ed525f197ff25c5d19325b7586925b515bc259f1f6f2597e26925613c15255eaa502543e48c25044d2725029ba324fce11724f4abb424f1d90e24d5ba0324bff09524a4de9024927c112485e17f2484e1252474a46c246f838b246a0b8a245dbecd242a74e02422aaa3241a19e723e95a4623b0b5072379a87f2371f15e2363757d235dd3e7232fdfb72308cf9f2305e8be2304dae022f2b39022e36ade22a39c5a
  | 7, 0, 6 => 0x2faa7f832f9ebac62f775b232f76da822f4f8e472f2d333f2f27a1862f2664432f244e602ef94f442ef590472ef118992eee210f2ee6a1a12ee5f83b2ed106232e8cc1e52e65c3952e2cb24b2de3d37c2dd5e4112dca65fb2db8ca292d6782ad2d48cd4d2d2059702d11b3fb2d0b08af2d0065ab2cfd4cb22cd48a3e2cc710002cbfb75d2cafca952c9d909e2c60eef42c35d6762c13df762c002f4b2bf3edcf2bb7e6892b7940bf2b5379482b411ce62b3e9fc02b351a482b3290202b0c54332aff1c0f2af61e482ae3339f2ada82fe2ac5b9242aa950482a88612a2a71ab6e2a6bb0532a5f79ad2a3e98622a2f82d32a1fbbbc297cc0d4297400f8292cb8d4
  | 7, 0, 7 => 0x35895b043579dda73576bc213574f68835747c40354c0f9d3545db6c353ffe89353f36783509393735017f8434c730bd34c3851934bde41134bd92e334b3dda734aeaf24348ee9a3346c53a4346473883434cfff34206ca6341c5d50340c055d3409b9113403b3df33b8069c33addc9633ac4949338c9ad2338b1457337098c03344a17a332ee49d331102a833036e7132f5b1f632eeda0232d4864e32c69f3432b01489327951d1326b44773242eb653219776631eb022d31c32ec331b30d7c316e3c87315f0dca3146060b311656bb30ec4ec230dac11430d3ff1530b123c5304cf6a43044b910303247ff302c87ea302a0ae32ff39f242fe2e0532fd90f92
  | 7, 0, 8 => 0x3e0301fa3dccbcab3da80a963d90978b3d82a2f13d71fd593d5db2783d4d45463d35d18c3d21d1683d1bf2473d1bc8603d084ce73cf4fcd73cb7623b3ca51e343c7bdb083c6977bf3c5fea2a3c5cd0913c4b2c0a3c2cf4da3c1fe1e43bed95723bd1ee373bcc4b8e3ba453603b8c54ab3b1fa0fa3b1437703aca73853ac38fcc3aa0418d3a9e17353a810fb93a7a6f103a6372fa3a39bf7f39ae918a39ad638a3977cb6c3963cb48395f96ae38f267cf387cf5323872f208382293d138168c5937f723b8376a4f69374100aa37373b89371be02136fc90e836f914db36f1a5a336d40a5d36817d7636727dff366071743620a03035db239335ac22d835937adb
  | 7, 0, 9 => 0x458c1b08457ce1024566e4914541e848453591d24508ab2444efaef644aae862448b5842446609b644637b7c4430796e442d00d14421a80f441fad5c43ff470e43c5a5e043c11da543a70ae543a00a7f4398b1694366279842fc4e1d42e48510429bb6704258c7cf424c735b423d3c4e4222f01b41be98b94183d82441588a44411df3ec40fd5c8940d7019140ba3bb340a1669c40811af04027cfa6400633024000425a3fe1dd833fe0c39e3fd89f2f3fbcee743f775e1d3f5fe1ad3f5b35893f4469d73f41ccdb3f12e7d53efbbcfe3ef2c9303ee60e733eadf8b13e51fe3b3e4848ff3e2a98cc3e294fff3e26d9273e256bce3e2424c43e19f81b3e098a5f
  | 7, 0, 10 => 0x4d1a63024d10dd8a4d0e53624cd391e84cd1a6274cccc7944cb7f0c94cacc4fc4caa099a4ca0b7c64c9ad3b34c8d80f44c50a0f34c35789e4c1e31e94c1de4d44bfbeabe4bef9b8c4bc432324b6d7f204b4480574b3060ba4b0721694afc9a304aee95694ac781234abb17904aacdde34aac3dc34a4cbebc49f1948249d837ae494f193048e93b5348b7e81148a30f48489e7dbe486b9cc5485e935b485d290d48335e004830af334804f0f947e5621747cd22e347c2ddf3474b9a27473a9da3473a6d92470552fe4702e8f446f8474e46da15bd46cfadf846cd9c5046ba482546b17d45469151e1462698db460863bc45eb319d45e428f445d5b36a4591ff1b
  | 7, 0, 11 => 0x550f9dbf550d954954bb755d54b2151054920a805478803b54617bf95431b23f540efd8e53ed427d539e25065396465d538571565359b3fb53568220534c3a7b532862f0530dd69552fe543752f219fd52afc25752996d67528577355270ec6c526f455b52652dd5524b30b6520b52db52084b2c51d54e5151bb968e5171a2a8515d0726513f899f510364c850fcb6f250fc017750f4e59f50c1bb7d508168075047ce895013ea855008758d4fc4d3114fb750c94fadd4194f74e8544f2308104f1c75a54ef8dc934ef588884ef1dd984ee29ddf4edbdb8e4eabf50f4e9f63764e94fe3a4e8a2c674e83672f4e4532634defa2b84daa25224d7df7ce4d7c1ea0
  | 7, 0, 12 => 0x5cbc40065c8048ac5c7c04cf5c46243c5bcd8fcd5b96d7675b7034a45b5a06b45b4c7f215b26af105b212d615b1b4a615b10def85b0742dd5af6329a5aca5d735a910ab55a79a54a5a69bac65a5fdbb45a55be6c5a0964c259dd40be59bf3e13599470e75992e51b597460c85945debb594545ac5943b1655922ec4658d6963f58c7437a58bcfd2358ac94e158a0143c5867afd65813abce580aba2258039e4a57db40a857c46348578e7901578a7e9757378c385718f8f75702d8b156f51c3656cd3b8556cac6b8569e151f5679d043565a3d7756337c8455fdc57d55f8209255f262bd55e7a0d65593c9de5593c310556da6c7555e780a555672e15539a68b
  | 7, 0, 13 => 0x655c4e5a6555e603651a057864ef0a7e64ce772864bb1a6864b7656c6493563e64818a936456be916438425e642996a763ff7f4763fe5a4f63a5592a63a078c8639d7a81639a5bfb635f225d633cbe4b632a33a462fec6b962ddcc1362d6318562a89ff7625ced936245d47962407623622d0e09621cd3f661f7222a616dfee361597ca76151516d610788a560fd5a8260dd91ac60d6c19560d3573560cfe67b609ba710608f820d602ebcf1602bde88601d50b95ffed7895fe54eea5fcd3a315faa2c4f5fa624535f66e6445f3975ba5f13a1b05ef7b5895eb355125e6d15f35e053f7f5ddf67e95dadfbca5d6dc8875d6817ed5d4631575d42352f5cff8ca1
  | 7, 0, 14 => 0x6bb38dc86ba0ff156b7e56f36b78b4ba6b750a8b6b6f4ef26b408f3a6b3017626ae95ce96ad97ffd6ac4e77d6ac0491a6a801d696a698cb76a5e2e496a161b426a08220869de091c69da458569d5f13269be6e3d6991695b698f8f776954d60169548d2469506ea2693e0e7b690b0d3968ff83c268f8c50e68e5b1bd68ddca6368cdc73668cd9ffa68badc8d688509b66821124f6814c4b1680102c468006be767f8c41b67e20fe067d6a2c867c3a34567adb0e36799ca88676ca753676ae4a96742a7d3673d759c67108e5267068df5670425a966e46e6666c18c79668c7880667cc29c6678e44966704cbc6658320f66484c30662141df65dd7ad3655e0be1
  | 7, 0, 15 => 0x739605b4737229507371dd96736c3eab734c9f767348088d7321287b72d87a3472beea2b72ba3b1172ab5f4f729b2e07727e079d7278be2071d3a02871cfa26f71afb55271a437ce7178456271686d2e7162bd45715adeae70f7e40370db175f70d8105170d14bca70d1106770cd5ae470be6121707653cd706ce156704a65906fef05cc6fec830e6fdc58a56fd9346f6f9d17036f696a4a6f43ea976f3212226f2eb18f6f1f7e7a6efc04706edf7c9c6eaf552a6eac48236e73d1506e0d8dc26df0fec26dc5812b6d72199c6d71deff6d60d6bf6d2479296d22410c6d041d796cfba4ef6cb058c66ca5bfe46c6b07056c55ce416c3019736c0ecbaf6bb6c94b
  | 7, 1, 0 => 0x7c2e85b57c1ebfe47bac4d1a7b8055d47b6ea85d7b5f89e47b58a2cc7b38ee6a7b3164647b2108ee7ac2d0767a98c0657a7531077a6bf5b27a5716df7a32e6c479fc07f679c53e607999a798798382f1796641d9795af538790cff8978ec302a78ebe05e78e4f5a278de9bf378db4aa8789ffcfc789e7b0c789de8b6786dfc597860e63977dfd53c77cfa30e77cbd18277540ede77496a09773d6e78771e700576ebcd8676b692d376a6eed2769ea8ea768d3e1e76883f0f764f73f775a337077590c5d17579e848753c1a057527fdbd74fb6bb774f44fdf74e4177e74dd2a1a7480d2477440f1177440dbf174381a6273ff5c9c73ccaf6873b11193739f2b39
  | 7, 1, 1 => 0x8515b8cd84f3169584a52c19848eec4d845b963e84582d55841cbaf9840206a984013fe783cbd3c083b647ca83b31a7d8369a809836650848363c3f683490ab083079e278302b3d682c9e5be82b6236a828b9b69824f20f6824ebd768236f38f81c8c2f4819c32b2819b4b088147aab0812d517a8128f3f3810ac0a1808d6ce0806c43f780458e7c8032d812803070bd80231ba07f89bf0c7f7cb5047f34c9357f31c35f7f2d59fd7f2619507f21f4997f1dbf9e7f18940b7eee8de77ec9c7b37e9e811e7e7ba7e07e62c7897dc7732a7da5dec27d5b202e7d4f5f387d4a419d7d4847ff7d0c8cbb7cf9986b7cf70da37cb55eb97ca027e27c3f68397c3a5205
  | 7, 1, 2 => 0x8c6c2dc88c5fd6378c3afb688c39f18b8c096b588bd6858c8bd60d088ba1dbf28b9a7c8c8b67488a8b3625d88b33bd8c8b2f2b7f8b1d15ca8b19b7c88aeaa6c08ae474e18ae2f1388addff2e8ac1d3288abc62618aa94f158a8e51ef8a1656d289f9aa0989c7447a89c21aea895dd9a1894e9e1a89148cd389008caf88d4431e88c8f86088a97277888486d18869664f8868df0a8856635b8833f5518826a03487f2185f87d4677187bf553887ba31dd873c288b8738119c8737715887299de486b097268669e687865fd91e865a602686453eb986412037861a5c81860c2be68608582185db428985c3ded685bbaa0485b6fcdc85b3ccb185a4cbd1857f3777
  | 7, 1, 3 => 0x93c41c0193a98caf939c8143938b73e2934eabff9323bdfe92bb609592baeec8923924e7923619c0922628d29212d16f91ecb7d991e19236916040ff911fadd990dec3a290a76b7a90a63101908305449073fab89033b52490211671901c386b900e35ef8ff96af68ff3586c8fdfe3ad8fd5231c8fcffd1f8fc4eb5e8fb6970b8f8b65ae8f6eb9328f69047f8f4ddcde8f166a708f0950aa8ed0cc8d8ec614628ec451bd8e9c58c18e902fad8e7230768e68f6f78e46ca478e3d634f8e26e5f78e032ec18dff31bb8dc02d048da850658d9ebf6c8d9225708d8425078d7aed198d784f7c8ce25eba8cd297818cbb13f68cb5433f8c8473f68c839dfd8c7cbb37
  | 7, 1, 4 => 0x9b2dce579b0132a19aeb76b19ab8455a9a8bf7aa9a5e5fd59a4a5fb19a43ff869a42902e9a399e549a1dcd2a99bb987e99b2b20c99a91c429996391b998e521e9972845b995d02aa9944d26b993f1922990ffb6b990e95b29909283a98fd6fd798f5fe4c98a9b59598a2066198654ff79863be119851bf22984429e797fd6b5a979e957997956ff49778eb8b977147d6976c8913974a5a399747c874971d87a996ed6b4b96d72ef996d01321965c958996134b2695feb81b95e626af95dce18f95d6492b959ee8589590b85b956af0e49556175c954c91e4954a07bc94ffe11f94dbd1b49493f2d89492ddb2948722919437159c940b257293da0a2093d56e6b
  | 7, 1, 5 => 0xa2e072faa2b50c6da28a69a4a26ac316a241a4fda22151bea219d787a2066a62a1c22db6a14a8c27a14856ffa13bd84ba10bf6fba0f982e0a0ca5129a0ba2447a0a58af5a06bbb55a039bc45a0230024a01eb4169fbed9729fa3366c9f8844ec9f56ae149f210c3d9f0c24059eb1c3c19eab00239e8fb9389e60f45a9e56811f9e33d4ec9e08b2919e0665df9dfc23f69dfb72369df4f9a79deb9d439dcf7e389da9a9399d3e8f329d3df8079d1bdcb79d12b9ba9cf729b79cebfdea9ce83a339caed7489ca6bdbc9c6d66999c44bee19c31e4e49c26f80f9c14133a9c0635639bea8a5f9bd4a9df9bca85189b65def89b5a16b29b53791e9b4c7f429b3cd8b8
  | 7, 1, 6 => 0xaa452991aa0f9412a9faaec3a9c34916a9b19c58a99d0106a9851227a9775949a9536d8da944cd73a927f774a917ebcda8d0e661a8bd2881a8aceb64a894d850a86f31f2a8579795a8417749a84135a5a82101fba7db6d6fa7c8dcf2a78974f5a77f0384a7752a14a7352dc1a73369e3a72b3a68a7250e10a70c7473a7070867a6ea9da8a6ae84b7a697cd48a66aaf8fa65571c8a64e8b36a640a41ca6365dcfa61e7dd3a61de4fea5dd0329a5a3cc47a59a240ca596fabaa593fad9a56dc7a2a54714f0a54213c6a4b7b929a498c4b8a4626ff5a427599ba4234630a3f6f2dea3bd8ff3a3b4b63ca3ac4ce7a395bb0ea32d150fa317fe4ba30914bca304b735
  | 7, 1, 7 => 0xb1908a5bb1838f47b176d427b158ad0fb14a7c74b14872c1b146c193b11cca9ab10a3f49b08c3973b0772feeb03e1077b03b1c5fb00c731fafec201eafe9653dafdef203afd5efccafcbe12cafb5dacfaf9158dcaf7e5c2daf6bc115af6a54ceaf359018af3327ccaf31501aaf2bc6ccaf2022c0af0aef8caedd696eaeb8f7e5aea8cd7cae8e3c58ae603738ae49084eae45eeb5ae44786dadf95653addc392fadd89541adbb5be8adbb0c5badb0dd5dada685f3ad7c2950ad4fb26fad13ee5aacbf819aacbd3eedacb391a9aca5b365ac5efcdbac08d977abd61055aba7945fab65e7feab377bdcab356b88aab8de38aaaaab15aaaa4cddaa631bb8aa4f8b80
  | 7, 1, 8 => 0xb839de42b8110090b7d97460b7d3b0e4b7c1e9f1b7bed18eb7b15b21b7a8f6efb7a18c77b74e163fb749d50ab7401fceb6fad8c9b6eb0984b6e2d1dcb6c4937ab6af85aab6a9ab77b6967739b67a79c0b63e8ff7b6358400b6355c70b62871f1b607de9bb5ff4747b5e0fc76b5b77e2ab5b461f1b59cf503b5902909b5784485b554a760b52fe6ddb52bb7ccb4d28f2cb4ae3bd5b4826f84b43d5ea9b436000bb4265a72b3f37ff8b3ef1ffcb3c24a54b35a2bf3b34d471eb345a3a5b341a868b33dffa7b320141eb3129c5ab30f35e5b2f698f4b2a359d7b28f99edb26a3914b23ccd8fb22e5d43b1ea3e9eb1e9f931b1b90588b1a60c98b19e29acb1918fb0
  | 7, 1, 9 => 0xbf8928b0bf851e63bf75efa6bf6dea7dbf653cc4bf1361a9becd8a39bec5fc52be9f9425be769f18be54e56bbe4929dbbe390894be302c54be04ba19bdfcbc5bbde508e2bdbb02bebdb59ca2bdb3ec25bdad5056bd6b7298bd63b217bd5c6ceabd569d44bd481cb7bd189bfabd16353ebd0e6676bcf03cf9bc885194bc7ca571bbfcd59abbecc5edbbe6e79bbbdea910bb806acdbb49c479bb2895d7bae435a9bad421dfbac6ac71bab4727aba506113ba47a138ba0bd188b9fb3ed2b9f86c0cb9dd9279b9cec865b9ca7d3ab9c6ad7bb9b21282b9a5abf7b985498cb97a58bbb9238bb6b90d0024b8fa157bb8db3bf4b8b4c543b89bc33ab87a7005b8750d6a
  | 7, 1, 10 => 0xc8e2cba9c8da031cc86aea85c861da35c835b086c81b12f1c8144c74c8122111c7db80e1c7c57366c7b9162ac7abb727c77e063ac775e74ec76c6475c75da8f3c722c4afc71fc81ac6b55f67c68acfd0c673f56fc5c197f6c5a7e8ddc58557c3c57fd30dc577f454c53d52fac532c1fdc500765fc4cf2a05c4bc0901c4b98e87c4828b8bc4775350c43bc065c4359a57c3aa5cb7c38bd864c35cbd48c35a0575c33155b1c2daf057c2d474bfc22fd643c2157f87c1fec366c1de7afec1d9b175c1a1f633c18ac36bc158b17ac124aa0ac11a504dc10c93d2c10593c9c0e7a473c0c437dac0b58cbbc0aa5d7fc0a94172c085c7cac0324461c02871debfcca165
  | 7, 1, 11 => 0xd111535ad10eeb0ed10ba971d0eed897d0d31777d0bc3a17d0b92cb0d0b2fbe9d06fa9abd062548ed01d5adecff42cabcfed907acfd785f5cfb93b24cf73c5f6cf65523ecf5eaabbcf2e0516cee52cedce87419dce44a282ce16f6e3ce07748ecdef810bcd52d7cdcd43454dcd359d45cce6e03eccbc92c1cc86101fcc6e980bcc67d89bcc5b0663cc3dbb03cc32d0cfcbf282e6cb9f0c58cb7d8f0bcb7d4e04cb78c448cb76685acb69ce5ecb349801caea07e8cabc859bcaac0d7dca990205ca54dc08ca546425ca537f57ca04774ec9f8ee7ac9f3d846c9c45eccc9ad816cc99fcd9ec9901028c98e47ffc95ac6c6c93668ffc92b194cc900de10c8f98b0c
  | 7, 1, 12 => 0xd793416cd7899138d759f9b3d74112a8d73f0427d734ab98d6f1bbdfd6e2b88bd6d828a2d6cc8efcd6b7954cd698d3ddd6827ea1d6659f56d647910fd5fede1cd5e404bfd5d51448d5a576d8d594118ed558a97bd5484081d52a553fd5220327d4f0f799d4ee2432d475a5e5d43a869fd430d163d41890d1d3ff0dd7d3fcff7dd3f580b8d3b5450fd3a8e0f7d3a57e94d3a2fce4d394c8cad388e184d379eceed36d52f2d36b2b55d35f5289d358ca24d3571d07d3265b1ad31e59f0d30a59ccd2d4b27bd28da698d28c47b6d257e8b9d248728ed24558f5d243bfa0d23c8d64d23889ebd21dd0abd21ac315d1ba769bd1b1b30ed1aafba8d18f4277d175aa0e
  | 7, 1, 13 => 0xdf382235df0bc77bdeeb28eddee4c313ded551a2deb1fadbde9849e3de91cd35de8ede08de808106de53bb01de4dbcd2de41b497de3eec65ddb2f137dd5c2e0fdd29ad5edd22f5f6dd193586dd09945fdd076004dced4dafdcc898cddcc2d6ebdc7a461adc79da45dc56f92cdbff3966db3dab48daf1b18fdae88803dae3a970dae1e332dacbece6dab6ff36daa3ea24da868036da803c01da6a175ada61dd2cda067d68d9fde2d5d9ae803cd992563bd98f9349d984ba31d95b6233d95402cdd93d87e6d9137c0cd8efac19d8ed43cdd8c3bfbfd8b63777d89dfb22d8961c4ad8316a54d825c4b2d823951fd808765ed7f0e012d7db0a89d7bcbfb8d7a0aa52
  | 7, 1, 14 => 0xead8cca8eab44034eaa78c21ea8b3a97ea5d0618ea20e6d9e9877a69e935373ae8e13f4fe8b32ee1e89fb0f7e881f5cbe8764198e7e40de4e7deeac6e78c552be75cc097e73ba6c9e7311744e72b167be6ed781be6e489dbe6cd35a2e6c57e21e6aaed47e694d16fe6334511e54e6e14e54da510e53126b1e4aea01ae4a9c7bfe46f7636e44a5e60e3af3956e398d376e38d55f2e3866ba8e37f5dabe356b114e3518b52e3412cc1e3247725e30df211e2f59de5e2d32023e2d1c9bae2785dd5e25821fce20b1b97e1f09bdde1e47322e1560784e152886ee1410c7ae0e569efe0ad7f41e0500651e00dbdb6dfb96348dfa83d6ddf99d6a4df739b43df4022ff
  | 7, 1, 15 => 0xf153a027f1350785f11de759f1195156f1167821f0d81ed1f0b6b375f0945cbff08b0e3ff07b02c5f0799319f064dccbf05ab396f05897d3f04f03a7f041e202eff1ed26efae69a2ef3e65bdef335fc1ef30bf30ef2e9b0feeea3911eee2b68feede5f57eea663e9eea09446ee894606ee5cbc09ee459ecdee36c9a5ee343295ee33f0d4ee28865dee18b783ee0b492fee091011edf34286edacebaced8d83bded7dc820ed6973f8ed41d198ed105b43ecf6989eeceb1d3bece2987aecc5cb2aecb91f5fec87d0bfec83f7cfec72facaec6e369fec663512ec65e546ec489e51ec309f4aec20b13cec15bfe8ebdaeb21eb9304d6eb44c916eb406b8feb222eef
  | 7, 2, 0 => 0xfa25ad8bfa0187f4f9ffdd1ff98630cef9554771f947aac1f92dd199f9208f7cf8dbc959f8806e93f848f742f8456696f82e5cddf82ca004f821a1bdf81aa65df8037aa5f7f54a0af7c46fa3f7813a1af768559bf7568747f721c153f7061881f6f4ac3ff6e481d6f6c1cf77f69beb92f68e4a3df65a409af644b462f61649e1f60c94a5f5ed84a4f5c74da0f5b4f1e4f4fa1d32f4c930adf4b303e2f4a423e9f49f418ef4782ca3f469dc77f42435d0f4211c37f3e6b4a2f3a1f4fef39aa1fef39639ddf3733036f367d1f7f35650ebf34d028ff2d5b052f280ddebf21bf636f1fe0360f1e406f9f1dccc71f1b84c83f195bf85f1784439f165d328f153f5cf
  | 7, 2, 1 => 0xfffea3a6fffd9e4bffb3f673ff640b3dff57afedff3d1588ff2e1a43ff123350ff0402b5fedd3cb7fea4321afe82066dfe770e46fe554becfe24198cfdf0164bfdeaed64fddd6bbcfdb3f8dffd9d02e8fd93ab53fd8afa16fd536d0dfd3ce5b2fcef1659fcecae0dfcc3aa8ffcb0afc1fcaa14ddfc30d494fbc60337fbc1bc8dfbbcb1d0fb9c1d90fb88fb78fb84f944fb77b89bfb6b568bfb3e6e67fb2e4632fb292497fb26bad0fad792e2fab6ff8cfab21684fa9321d7fa4e962dfa33b007
  | 8, 0, 0 => 0x408d44063ff1a89f3d41059b3d0bb5b13c8ae61d3c5cd0913aa5adab3860df7e37fc88ca36aa1577352b3a5933ac49493263f9b831c32ec330797d6f30452eee2f1583e82ea7d59d2dbb214e2c9d909e2b3beed9276f815f26c74c06259565192238b79e21d460ea2085ba6f1eb180c41c3bd1d81c1a73291b9b06e31a51558f1917953718ed5c08179ba5681773f91516c885cc133606d912b537451101c9f510eee49c109989db108a8de80eb2ba8a0d2e3d660cda57470cd4669f0c5bdf350bedd9ed0b203b970b15b6280af1fed60a9f6c030a5133e109efeca509d69a710907828d07a3890604be9b5d03e5727602c7e1c601c0cf2f01737d88002f4827
  | 8, 0, 1 => 0x8f87e3d58f66a91b8f0252678ea1b5b78e3118c78d8425078ca877188c27a7848969c35588c8f86087a84624877f470c8646d6de861b4d85836a9b7e83490ab082fc9636816c4ed8801c3ae37dcefbd27d57e2b57c3a52057ae9648876b73a477673e45e75b7bbb0759045d8752fd4817278be2071801e4470227bd66ea16f056d42739e6cd46e566c8cdfa26bf5ec266b3d020a6a314b07690b81846716b47363e020e4621b7fc560f5b642604bbc7e60364b425bf8a09c5b8a9b54572b3dcc5619d07f55da71805514da2a53ebb6ee52652dd5509cfade4f01e97c4be20cd84bba970048a30f484716cec643cc419643cb072843a4cbbe42ed440f409e34a4
  | 8, 0, 2 => 0xdf0b1436deae0fc1de2570bcda70651bda025fd3d69e5019d676da41d58f793dd35f5289ce0e84ffcd79adfbca5896e9c7fd48dcc7abb727c5547d17c52d073fc242cba7c2157f87c1522335c0edcc81bb67486ebb553d6fbb32f41dbab4727ab9fc0058b96ac126b806c79fb7acf0edb6b375dab535655eb41a71fab399a266b1838f47b14a7c74b141b29aadb8d1c0ad1f9a1cab8e1314aabb0592a6ea9da8a648124ca4c9dd97a3d3d878a3ac4ce7a38fee89a184c90da08ce91fa039bc459df24a1a9d717a86979476b89790a9e0977c745d97181da995cb9afe959b5dd29492ddb29406f9df92e1305c928a0576917f8e9790dec3a2903af60b8f95124e
  | 8, 0, 3 => 0xff652815fbcfa734fab21684f6b22f67f6b00b97f4ed8e48f42e45c1f3c7c4c5f029aa86ee9a4055ecc677f9ec9f0221e9877a69e6c3db03e5685c65e3a3bb46e286305de27df1c3e2182b15
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x8115480300000d52108000000105100001084108040035504204
  | 6, 0, 0 => 0x1842c000000e10b00055200800002048020000000038404000081220000000018404000000210200000028400000000210800000018408000000a1040000000842c00000121020000003842c00000c010100115200800413544030000000048408000000610200000038420000000210800002018800000008110b00000300404000000610200000420404000000a1010000003842c000000210200000038408000000a101
  | 6, 0, 1 => 0x104400000000210000000018404000000610c00081200800000001210c0000002841000000021020000001840400000021010000003842c000000210100000028404000000a10c00000018404000080620000000038408000001210c00000038404004504120c00000028430000000610c00041100800000004110000002038800000010810800000038404000000a1080000001842c000000a104000000284300015500200
  | 6, 0, 2 => 0x8408004140a20000000048410004140e20000114204800000180a20000002028800000000210100000028408000080620000000028424000000210400000008410000000e1020000000841000000c01010000041041000000121010000003841000028122000000001842c000080e2000000040042000008062000000000842400008122000000001842c000548420000109420800000001210c0000003842c0000002109
  | 6, 0, 3 => 0x842c00001051000000003842c00000021010000020442c000000610b0010d430800000000610b0000001840400000121040000002842c0000012101000d5400800000080a2000000001842c000001210800000028430000000e10400000314400004140220000000008408000000e100000d521080000000061080000000842c000000610b00000008404000000e10c00000018408000000610b0000042042c000000e10b
  | 6, 0, 4 => 0x28408000000210000109420800004050020000055400800000080a2000000003842400414022000000e048800000000a10b00000300404000000a10800000018404000000610000000038404000001210b0000001842c000000e104000d5200800000080e2000000000842c000008110b31415310c00000000610b00000008430000000610200000028404000000210000000048400000000210b00000008424000000a108
  | 6, 0, 5 => 0x28430000008110b00000038430000000210200000018408000000a10b0000001842c000001210100000028420000000e10200000008420000001210b00000038408000001210c00000048400004140e20000006038800000000210200002038800000000e10b0000003840800000c01010000a048800000000e1080000001841000000061020000041040400000021080000003842c000000210100000048408000000210c
  | 6, 0, 6 => 0x18404000010810800000038420000000610200000314400000008110b0000001842c000000610100000008420000000610400000018420000000210100000028404000000610200000048408000080e20000000300404000000610100006048800000010010800000048404000000a1000000000842000000121010000004842c000004110c00000314400000001210100006028800000004110000000038404000000a10c
  | 6, 0, 7 => 0x18404000000e10800101400800000000610b0000e04880000000061090000a038800000550420c00000008430000001210100000008404000000a10200000048400000000e10800105104800000000e10b00000038404000000210100000300404000000e10b00000038410000080e20000000028400000000210200105028800000000610b00000104430000000a10400000008420000000610b000000084200000002109
  | 6, 0, 8 => 0x842c000000e1020000000840400454802000000002842c002550020000000018404000001210100000028420003544020000000038404000000610200000028404000080620000000038404000000e10100000414400000000a10200000038420000000210100000028400000008110b000c5310800000000210c0000000843000000061020000001842c000000610800000300404000000e10200000018420000180a200
  | 6, 0, 9 => 0x6048800000000610800000018408000000a10000000018420000000a1010000001842c00000061080000001842c000000e1020011420480000000021040000001842c000000a10400000008420000000210100000008430000000a1020000002840400018122000000003840000000121020000003842c000001210100055200800000000610800114204800000000a10b00000048410000000e108000000084100020480200
  | 6, 0, 10 => 0xe048800004140220000002018800000181220000000008404000000e10900000048430000000210800000018408000080a20000000048408000280e20000000420420000000a10b0000001842000000c510000000048400000000610c00000038430000000e1020000a038800000000a1080000000841000000c010100000048408000000e10100000420420000010d10b000020488000000002101000000284080000002109
  | 6, 0, 11 => 0x18420000000a10c0000a048800000000a10200000048410000000e10c0000000842c00000c010100000008430000000610200000048408000000a1040000604880000355042040000001842c000000210800000028408000000a10100000038408000000210200000410410000000a10100000038410000590520000000008408000000610000000018430000000610100000018404000000a102000000284040000006100
  | 6, 0, 12 => 0x48408000180a20000000038424000000e1020000003842c000000a10c0000000842c000001210b00000028420000280e20000000028404000000a10b00000008404000000210b00000414400000000a101000d5210800000281220000006028800000001210200105028800000000e1020008120080000000021010000001842c002550020000000048420000180a2000000000842c000000610100000400420000000e101
  | 6, 0, 13 => 0x8430000000a10400000018404000000a1040000001840800355042040000004842c000000210b00000420404000000e10c000c9320800000004110000000018430000001210000000028420000281220000000038408000001210b00002038800000000610900000028400000000a10c00002048800000001210100000048404000000e10b00000028430000080a20000000048400000000a1020000001842c000000a104
  | 6, 0, 14 => 0x3842c00000061020000042042c00000061020010502880000038122000000000842c000000e10200085210800000000210b0000002842c00431042020000003842000304c02000000001842c000000a1080010541080000154c0200000000384040000006102000d5200800000000210800000008410000000e1080000e048800000000e1020000003840400000061010000004842c00000061000000002842c000180a200
  | 6, 0, 15 => 0x48410000000210b0000002843000000c51000000004840800154c020000000028400000000a1010000003840000000021090000203880000254c02000000e048800000000610b00000018424000000e1020000002842c000000e10100006038800000000210400000038420000001210c0000043442c000550820b30455300c000000002102000d5410810000001210100000018404000008110b000000484040000002100
  | 6, 1, 0 => 0x8408000000e10900000038430003550420400000028408000280e20000000018430000000a1010000020442c000000210c00000048404000000a10c00002048800000000e10200000028400000000210000000300404003548020000000018404004140a20000002028800000180e20000000038430000000a10900000048404000000210800000008408000080a2000000002842c00008062000000001842c000000a109
  | 6, 1, 1 => 0x48408000000610200000008404000000e1040000003842c001548020000000008404000001210c00000038404000280e20000000038410000008110b00105038800000000210800115200800000000610c0000002840800000c0101000d5100800000010410400000028408000000a10100000008410000080a2000000a03880000000c91120000000840800000061080000003840400008062000000000840400314c4200
  | 6, 1, 2 => 0x8420000000610400000048408000000610100000028404000000210200000038400000000e1090000020442c000000210200105038800000000a10200000038408000000210800002038800000000e10100016414800000000a10b00000028408000000e10000000038420000000e10c00108410804002544020000002028800000000210200000008400000000a10b0000001842000000061040000000842c0000002108
  | 6, 1, 3 => 0x18410000000e1010000010440000000021020000000842c000000610900006048800000000a10c00000420420000000210100000038420004144120000114204800000000e10200000008404000080620000000048408000000e104
  | 7, 0, 0 => 0xc932080000304c02000000002842c000010410c00000424400000000610800000204400000000a1020000001842c000010410400000048408000000a10c00000420404000000e10b0005530080000001091000000003842c00000061000010d430800000000210800000008430000010410400000038430000000a1020000000842c000081220000000018420000000a1040000003842c000000e108000000184000000012100
  | 7, 0, 1 => 0x18410004150420000055300800000000e1080000001842c000000e10b00000038420000001210000000018400000000a10100000038410000000610000000048400000001210000000008404001044020000000048420000000610c00000008400000000210c00000018404000000210800000028400000000a101000000384300010440200000000184000000012101000004044000000006100000000384040000006108
  | 7, 0, 2 => 0x48420004250820000085210800000008110000000028410000000210b00000028424000001210200000008400000000e10200000008408000000610000000104400004050020000000048404001550020000000424400000000610b0000002841000000121020000e048800000000610c00000414400000000a10000000304400000080620000000204400000001210000000008410003548420000000008404000000a100
  | 7, 0, 3 => 0x4144000002812200000d520080000214842000000001840800000061000010d430800000000a10800000048400000000e1010000000842c00000121020000003842c000000e10000000038420000000a10100000420400000000a10000000038404000008110000000048400000000210200000018430000010510000000028400000000e104000002044000000108108000d54008000000012100000000284080000002108
  | 7, 0, 4 => 0x42042c000010010000000008404000000e10200000214400000010510000000008430000000210100000008400000000e10900006038800000000e10900000008400000000e10000055300800000000a1000000002842c000010010800000204400000000210000000048400000000610000000038404004050020000000038430000000a10400000028430000000210000115210800000000610000000028410000000a102
  | 7, 0, 5 => 0x1840000000021020000004842c000000e10c00000018404000008110000000324400000000210b0000001840400001051000000032440000000061000000001842c000001210c0008521080000000061080000001842c000000610400000008430000000e1020000001842c000000210400000018408000000a1080000000840400000021020000a04880000000c51000000002840400304c02000000004842c0000100108
  | 7, 0, 6 => 0x2842c000001210000000008400000008110000000314400000000a1000000001842000000061040000004842c000010510000000038410000010c10000000038420000000a10000000434400002048020000000048420000000e10b00000048408000001210000000018420000001210400000018404000000610c00000048408000000a10200006028800000080e20000000404400000000610b000000184100000081100
  | 7, 0, 7 => 0x28410000280e20000000008420000000210b0000000842c000000210000000434400000000610c00000048408000000a1040000003842c000000e10b000000084040000108101000000484100000002100000000284080040500200000000084040015500200000004044000003812200000000084200000002109000000284100000002108000002144000000012100000000084000000012100000000084200000002108
  | 7, 0, 8 => 0x314400000000a10800000028400000000a10800000424400000000a10800000028400000000e10400000008430000000e102000d5210800000000a10100000200400000010510000015310800000000e10b0000203880000000c510000000028400000000e1040000003840000000121080000003840000000021040000003843000000061020000002840400000121020000004842c0000002100001151008000000012100
  | 7, 0, 9 => 0x38404000000e1040000002840000000021040000000842c00000c01010000003840400000021000000001842c00355002000000004840000000021080000004842c000000210800006038800000000e10800000038430000000210000000028404002550020000000314400000008110000000018400000000210000000038410000000610000000008408000000210000000008420000000a10b00000038410000000210c
  | 7, 0, 10 => 0x21442c000000210000000424400000001210200115200800000000610b00000018420000000a1080000004841000454c02000000000842c000000a1040000003840800000021000000002842c000000610200000404400004350c20000000038400000000210200000018430000000e10100000204400000000a10000000414400000000e1010000004842c000000e10800000028420000000210000000434400000000a10c
  | 7, 0, 11 => 0x28430000000610100000018420000001210400000038404000001210400000008410000001210200000200400000010910000000008410000000210400000008430000000610400000038400000080a20000000018410000000a10000000038410000000e10b00000414400000000210400000300404000000610b00000008420000000e1010000001841000000061000000002843000000021020000000842c000080a200
  | 7, 0, 12 => 0xa038800000000e10c00000048400000001210b00000018404000000a1000000004842c004548020000000038430000000a10000000018420000001210100000018420000000a10200000028400000000a10b00000008400000000e10b00000038420000000210100000008404000000210000000018404000000e10000000028400000000e1000000001840400254c0200000d5400800000000210100000038400000000a10b
  | 7, 0, 13 => 0x214400000001210000000008404000000a1040000030440000000061000000002840000000021080000020440000000811000000004840400001081080000004842c000000210b00000028408000000210c00000420420000001210000000028408000000e10b000000384240000006104000c5310800000000e10000000008430003548420000000038404000001210b0000003840800000121000000001840400000c5100
  | 7, 0, 14 => 0x28404000010510000000008408000000e1080000003842c000001210000000028430000000610c00000038430000000210800055200800000010810b00000410410000000a10400000008400000000a10000000048400000000e10b00000038410000000610b0010140080000000c510000000018420000000210800000008430000000e1020000e048800000000a10000000028400000001210800000018400000000210c
  | 7, 0, 15 => 0x304400000000a10400000424400000000e10400000018400000000210000000038420000001210400000028410000008510000000008400000000e10000000008408000000a10800000048400000001210200000008404000000210000000008400000000a10b00000038420000000610100000048404000000610000115200800000000a10b0000001842400000021010000001840000000121040000003842c0003812200
  | 7, 1, 0 => 0x1842c000000210000055200800000000a1080000001842400000c01010000003842000000061040010541080000154c020000000038400000000210200000018400000000a10c000d5200800000000210800000028420000000210800006038800000010010800000048400000000610c00000028404000000a10b00000008410000000210000000008408000000e10800000048404000000e1000000003842c000000e108
  | 7, 1, 1 => 0x8404000000210c000d5100800000010410100000008410000000a10000000028400000000a10b00000008420000000210b00000028400000001210000000028400000000610b00000038408000000210c00000048430000000a1010000000842c000000210000000028410000001210100000028404000000e1010000000842c0000006100000003044000000006108000c1300800000000e10c00000008410000000a100
  | 7, 1, 2 => 0x28410000000a10000000300404000000210400000028430000000210800095400800000000210000000104400000001210b00000038430000000e10b00000008400000001210c0000001842c000000610800000038400000000210800000304400000000e10000000414400004050020000000048420000000210000000008408000000610000000028408000001210000000410408000000a10100000028404000280e200
  | 7, 1, 3 => 0x38404000000e101000000284000000012100000000184000000006108000002104000000109100000001004000000002101000c5310800000000a10100000028410000001210000000304400000000e10000000038404000000a1040000000842c00000021040000020442c000000a10b00000018404000001210c0000001842c000000e10800081200800000000210b00000018430000000610b000000284200000002104
  | 7, 1, 4 => 0x48410000004110000000028430000000e10000000424400000181220000000038420000000610100000104400000000e10c00000048408000000a10b00000038404000000e10b00000410410000010c1000000203880000000061080000031440000000121000000604880000000021000000002842c000000210000000028420000000210c00000028410000010510000000038400004508120000000008400000000e104
  | 7, 1, 5 => 0x28420000000e10200000038400000000a10000000038420000000e10800000048404000001210c00000420420000000610400000018404000000210c0000001840000000c110000000018404000000a10000000008430000000e10c00000008430000000210b0000003842c00000061000000001842c000000e10c0000004842c000010110000000028410000000e1040000004842000000121010000003842000000c5100
  | 7, 1, 6 => 0x324400000000a10c00000038400000000a1000000204880000000121000000003840800018122000000001842c000000e1010000003840800000411000000002843000000021000000041040800000411000000000840400000021020000001842c00354402000000001842000000061010000003842c000010c102000003104000000104104000000084000000002100000000384000000100108000004344000000002101
  | 7, 1, 7 => 0x8404000000e10800000028404000000210b00000028400000001210b00000038430000280e20000000424400000000a10c00000028400002048020000000414400000000610000000048408000000610b00000038430000000210800000018430000000a10b00000028420000000210900000008408000000210400000304400000000a10000000048430000000610c000000384000000006109000000184100025500200
  | 7, 1, 8 => 0x28404000000a10000000104400000000610200000300404000000e101000020188000000006100000000084000000002104000c5310800000000610b0000003842c000000e10400000018420000000610b0000004842c000010510000000028410000010110000000028400000000e10400000048400000000a10900000008420000000210000000028424000010d10000000028400000000610b000000284080000002100
  | 7, 1, 9 => 0x40042000000121040000002842c000000e10800000434400000001210b00000028420000000e10200000008420000001210200000008400000000a10000000008420002544020000000048410000000e10b00000008408000001210c00000204400000000610800000008404000000210800000018404000010510000000008404000000610800000028410000000e101000000184200010440200000000084080000012100
  | 7, 1, 10 => 0x41100800000001210100000048404000000e10800000048420000000610000000038404000004110000000018420000000e10b00000038404000000210c00000038420000001210400000018400000000210000000048404000000210c00000038420000000e10000000028430000000e10000000404400000000e101000000484100045480200000000184200000002102000000284200000006108000000184100020480200
  | 7, 1, 11 => 0xa0488000000002100000d510080000000021000000000842c000000210100000038410000001210400000038400001548020000000018408000000e1080000001842000000c010000000028400000008510000000048404000000a10b00000008430000000e1080000003840800000121010000001842c00001091000000001840000000c11000000204880000000c810000000018408000008510000109420800000000210b
  | 7, 1, 12 => 0x4842c000000e10100000048420000000e10800000028400000000210b0000041440000001081010000040440000000061010000003842c000010110000000028404002550020000000038430000000210800000038400000000610100000018400000000210800000008420000000a10800000008408000000210c00000008404000000e10b00000048404000000610800000008410000000e10c000000084080000006104
  | 7, 1, 13 => 0x204400000000a10100000048404000000e10b00000420420000001210000000008420000000210400000048404000180a20000000038430000000610b00000414400000000e1040000001842c000000210000105410800000000610800000214400000004110000081200800000000a10400000048430000000a10100002018800000000610c00000008400000000a101000000384040000002101000001044000000012100
  | 7, 1, 14 => 0x28430000000610000000018404000000e1010000003842c00000021000000001842c000010810800000048408000004110000000028430000000210900000038400000000a10400000028404000000610b00000018420000001210c0000a048800000010010800000048400000001210b0000030040400001041040000000842000000021020000000842c000180a20000000008430000000a10c000000484000000002102
  | 7, 1, 15 => 0x3843000425082000000003842c000000210000000048410000000210b00000324400000000e10000000104400000000a10b0000001842c000000210000000018400000000e1000000001843000000c110000000008400000000210b00000018410000000210b0000004842c000000210400000300404000001210800000018408000000a10b00000018420000001210b00000028420000001210400000314400000000a100
  | 7, 2, 0 => 0x28430000000e1010011420480000000c910000000038430000000e1000000003842000000121080000042042c00000021000000000842c000010410200000028420000010d10000000008420000000210000000028408000000e10000000008408000000a10b00002028800000000a1000000000841000000c910000006028800000000e1000000000843000000121080000040440000454c420000000028424000000e108
  | 7, 2, 1 => 0x8408000000210000002048800000000210100000028420000000210800000410410000001210000000400420000000a10800000400420000000e10000000400420000000e10100006048800000000a1040000003841000000121010000004840000000021000000002842c00000c910000000018420000000210400000048430000000210c000000284200000002100000003144000000012100000000084100000812200
  | 7, 2, 2 => 0x18420000000610800000008420000001210800000048420000000a1080000201880000000021010000020442c000000210b00000048404000000a10800000028408000000e10b00000018404000000610b00000008408000000610000000018430000000a100000004144000000105100000d5210800000000210b00000028420000000e10800000008420000000e100000c9320800000000210b0000000842c0000012100
  | 7, 2, 3 => 0x18408000000210200000008404000000610b00000008404000000e10c00000018420000000e10000000028400000000210400000048420000000e1010000004841000000061080000004840400000061000000204880000000c010000000008400000000210800000048400000000e10c00000028410000001210000000028404000000610800000008400000001210000000028400000000a102000000184100035500200
  | 7, 2, 4 => 0x8400000000610000000048410000000a10200000404400000000610000000028420000000a108001014008000000002100000d5200800001550020000000018420000381220000000008400000000a1010000031440000000c510000000008404000000a10c00002028800000000a10c00000008410000080e20000000048430000000a1080000004840000001051000000020442c000000a10b000000284000000002104
  | 7, 2, 5 => 0x8404002148420000000008400000000a10b00000018400000000e1090000001842c000000210b00000038420000000a10100000038420000000e10800041100800000000e10000015210800000000a101000003244000000108108000000484000000006101000c1300800000001210800000018408000080620000000420420000001210c00000038420000000610c00000018404004150420000055300800000001210c
  | 7, 2, 6 => 0x204400000000a1000000004840800038122000000042042c000000210b00000420400000008510000000028430000000210400000038410000001210200000028410000180e2000000004840000000021000000002840800324c820000000424400000000a1010000003842c000000e10b00000048400000000210000000410430000010c10200000018400000000210c0000603880000000061080000004842c000000e101
  | 7, 2, 7 => 0x3843000000121000000001842c000000610100000038420000000210c00000104400000001210000000048430000001210000000038400000010810100000018400000000e10800000028400000000a10b00000008400000010510000000048404000000e10c00000300404000000a10c0000000842c000000a10c00000028400000010810000000028400000008110000000038400001550020000000404400000000210c
  | 7, 2, 8 => 0x18420000000a10c00000420404000000610b00000038408000000e10b0000a048800000001210100000048400000080e20000000038400000180e20000000214400000010110000105028800000000610b00000008420000000a10b00000008400000000210800000008420000000210200000008400000008510000000048400000000a10800000018400000000a10b000002004000000012104000000384100000012100
  | 7, 2, 9 => 0x842c000001210000000008420000000610000000008404004150420000055300800000000210000000314400000000e10400000048420000000e10400000404400000000a10800000008430000000210400000414400000000e10c0000001840000000021000000a0488000000006102000d5200800000000210200000048408000000a1010000004842c00001041040000031440000314c420000000008408000000e104
  | 7, 2, 10 => 0x842400000c51000000004840400000061000000002841000000121080000000840000000021090008521080000000121080000000840000000c01010000002842c00000021010000000843000000121000000003840400000411000000202880000000121010000020440000450812000000001840000304c020000000018400000000e10b00000008400000000e10100000410410000000a10c000000084040000006108
  | 7, 2, 11 => 0x85210800000000210000000008430000000a10200000048408000000a10800000048400000000a10200000038430000000e10100000018410000000210200000018420000000e10c00000018410000000e10c0000002842c000000610c00000028400000000a10200006028800000001210000000038400000010110000000008410000000a10100000018410000000e10000000048404000000610200000434400000180a200
  | 7, 2, 12 => 0x48400000000a10100000038404000000a10b00000048400000000a10c00000018430000000a10000000314400000010010800000038400000000210800000028400000000e10100000324400000000a10000000028400000000a1080000000842c000000e1020000003842000324c820000000434400000000610000000018404000010410100000048400000000210200000008430000000610b00000038400000000e102
  | 7, 2, 13 => 0x3840800000c11000000001842c000000a10000000410408000000610b00000424400000000210b00000038420000000610c00000038430000000a10800000018430000000e10400000404400004350c20000000018404000000a10c00095310800000000e100000020388000000012102000000184300000002100000000284080000002100000000484000000002100000c531080000354842000000000842c000080a200
  | 7, 2, 14 => 0x28404000000e10c00000028420000000e10b0000004840000000021040000001840000000021020000000841000000061020000003842c000001210100000018404004548020000000008400004350c2000000000841000000021000000003841000000061010005540080000000061020000000842c000000a10000000008408000280e20000000008410000000210c00000420420000000a102000d54008000000002108
  | 7, 2, 15 => 0x8404000000a10000000048420000000e1000000003840000000c910200000008404000000210800000410410000010410400000008404000000210400000048400000000210000000038404000000210100000038408000000610900000018410000000e10c000004144000000002100000000384100000006102000000184200000006108000d5200800000000210000000008420000000e10b00000028400000000e100
  | 7, 3, 0 => 0x18400003544020000000048430000000210400000008408000000a10c00000304400000000a1000000003842c001548020000000320400000000610400000430400000280e20000000008408000000e10400000008404000000a10200000008410000004110c00000100400000000e10400000028410000000e1080000002840000304c020000000018408000000e1000000001842000000121000000001842c000000610b
  | 7, 3, 1 => 0xc9320800000010110000000028410000001210400105038800000001210000000414400000000a1000000041041000000061080000001840000000061020000001840400000021000000000842c000000610c00000008404000010c10200000420400000000610400000038420000000a1000000000840000000811000000010442c000000a10200000018420000001210100000028404000000610c0000003842c000000a10b
  | 7, 3, 2 => 0x28410000000210900000008408000001210200000028408000000610b00000008404000001210800000200400000000210c0000000840000000061040000010440000000c110000000048408000010810100101400800000000210c00000028400000000210100000018410001550020000000424400000000a1080000e048800000000210b00000008420000000a1000000001840000000851000000003843000314c4200
  | 7, 3, 3 => 0x1843000000021000000000842c000000210200000038404000000210000000018400004548020000095400800000000e10c00000028420000080e20000000028410000000610b00000008430000000210400000038430000000a1010000000840000154802000000003843000001041040000000842c000000a10c0000003842c000000e10000000028420000004110000000414400000001210b000002044000000002100
  | 7, 3, 4 => 0x48408000000210800000400400003544020000000008420000000210400000008420000000210400000028430000000a10000000008400000001210c00000038400000000e1020000021442c000000e10c0000000842c000000a10000000038420000000610000000008420000000210b00000038404000000a1000008120080000000021040000003841000000c410000000028420000180e200000004244000000006108
  | 7, 3, 5 => 0x2038800002048020000000204400000000610800000414400000000a10100000018404000000e10000000038420000000210800000018410000000a10000114204800000000e10000114204800000000210800000048400000000a10b0009540080000000c810000000018404000000a10c00000304400000000610c00000028400000000a10200055200800000000210000000410404000000610b00000018430000000a10c
  | 7, 3, 6 => 0x48410000000a10200000008400000000210000000038420000000e1000000003840400000061020000002842c000001210b0000004842c000000a1000000002840000000411000000002840800001081080000002840000000121010000000840400000021010000000842c000181220000000048400000000e1040000041043000000c110000000028404000000e10200000048400000000210c0000000842c000000a102
  | 7, 3, 7 => 0x28420000000a10800000028400000000a10000000018400000000610400000038400000000a1040000000842000000021080000000843000000c51000000000840000000121020000004842000008122000000000840400001051000000002841000000c01010000000841000001051000000000842000000061010000000842c000000610800000028420000000e1080000000842c000000a10400000038408000000e108
  | 7, 3, 8 => 0x8420000000a10100000008410000004110000000008404000000a10800000018408000000a10b0000002842c00001081010000003840000000021000000003842c000000210100000018420000000610b00000204400000000a10c00000018404000000a1010000001842c000000a10000000104430000000a10100000008400000000610100000018408000000610b00000048410000001210b00000038430000000a108
  | 7, 3, 9 => 0x48410000081220000000304400000000a10400000048400000001210c0000030440000000021000000004840000000c01010000003842c000000a10000002018800000000610200000008430000000a10000000008404000001210400000028400000010810800000048400000000e10c00000018420000001210b0000201880000454802000000000842c000000a10000000028408000000e100000000284040041504200
  | 7, 3, 10 => 0x38404001044020000000038400000010810b00000048404000001210000000008400000000210000000008430000000e10b0000002842c000010c1020000001842c000000e1000000000842c000000e10800000048404000000210c00000038420000000e10800000008410004508120000000018430000000e10000000038410000000610b00000008400000000210800000048404000000e1020000002842000000c1100
  | 7, 3, 11 => 0x4840400000021000000a038800000000e10800000018408004250820000002018800000001210c0000003842c003548020000000424400000000610000000414400000000e10c00000018404000000e10200000038420000280e20000000038410000001210c00000404400000000210100000038400000000210b000c9320800000000a10c000000184300000012100000060488000000002104000000084200000002108
  | 7, 3, 12 => 0x4840400000021040000000841000000121000000003842c000000210b0010942080000001081080000003842c000010110000000008420000000610000000414400000000210800000048408000000210c0000010440000000c910000000018404000000a10c0000001842c000001210000000028404000000210100000410404000010d10000000048430000000610200000008408000001210c000000084300000006104
  | 7, 3, 13 => 0x40040000000c51000000001840000000121040000000842000000c91000000003840000000021020000000842c000001210200000048400000000610900000008408000010d10000000008400000001210000000008404000000a1010000020440000000061000000000840000028122000000003841000001091000000002842c000001210400000048408000000210b00000018430000000e10b00000018408000000a104
  | 7, 3, 14 => 0x18408000000e10b00000008400003544020000000048408000180a20000000028410000001210c00000008420000000e10100000414400000000e1000000004842000000411000000004842c000000e10000000028430000000e10200000008404000000a10100000008404000000210400000048430000000210200000038400000001210b00041100800000000610800000018400000000210000000008408000000a100
  | 7, 3, 15 => 0x842000000061080000003840400000121040000003842c000000210c0000003840800000061000009540080000000121040000002840800000c910000000324400000000210c00000028400000001210800000018420000000610000000008404000000e10b00000104430000000a10800000008404000000e10800114204800000000210b0000000842c000000e10b000002144000000002101000000384080000002108
  | 7, 4, 0 => 0x38408000000210b00000028404000000e10400000028420004250820000000048400000181220000000038420000000610100000414400000000a10b0000003840000000121000000010440000001081080000002842c000080a2000000004842c000000a10200000420420000010810b00000008408000000e1080000004842c0000006104000000184300000100108000000184100000006102000060488000000100108
  | 7, 4, 1 => 0x8400000000a10b000d5400800000000210000000410400000000a10c00000214400000001210000000008430000000210400000038404000000a1080000a048800000000610100000038424000000210200000038410000381220000000028408000000e10000000038410000000610b000c1300800000000a108000000084000000002101000d5210800000000210800000038404000010010800000038404000000e100
  | 7, 4, 2 => 0x1840800000c91000000000842c000000610100000028400000000e10b00000018420000001210100000018420000000610800000018410004350c20000000028408000000a10400000028408000000610000000048430000001210000002028800000001210c00000008400000000a10b00000028400000001210b00000314400000001210000000028400000000610b00000048400000000610000000038404000000210c
  | 7, 4, 3 => 0x2840000414022000000041440000000121000000001842c000180a20000000414400000000610400006038800000001210100000038430000001210400000018410000000e101000000484000000002101
  | 8, 0, 0 => 0x32040000000c11000000040440000000021000000040040000000c41000000042440000000c81000000021040000000801000000010040000001001000000004840000000021000000010440000001081000000020440000000c41000000043040000001051000000042440000000021000000004840000000061000000002840000000c110000000104400000000e100000000484000000006100000004044000000006100
  | 8, 0, 1 => 0x3840000000061000000031440000000c410000000424400000000210000000100400000008410000000100400000004110000000314400000000610000000414400000000210000000028400000008110000000304400000000610000000038400000001210000000414400000008410000000028400000010110000000210400000004010000000434400000000a10000000414400000010910000000008400000000a100
  | 8, 0, 2 => 0x420400000008110000000038400000000210000000324400000010c1000000004840000000c510000000008400000010c1000000004840000000c01000000020040000001081000000020440000001081000000001840000001051000000032440000000c510000000028400000000a10000000300400000010410000000214400000000e100000002144000000104100000003244000000085100000003204000000100100
  | 8, 0, 3 => 0x430400000008410000000100400000000e10000000304400000001210000000310400000010910000000414400000000210000000200400000000a1000000010440000000c110000000420400000000610000000204400000010d1000000030440000000c410000000038400000001210000000200400000010110000000300400000010410000000214400000010d100000000384000000080100000004344000000101100
  | 8, 0, 4 => 0x28400000000e10000000104400000004110000000018400000000610000000018400000001210000000410400000000e10000000320400000001210000000324400000010010000000404400000000a10000000310400000010910000000434400000004110000000210400000004010000000008400000010010000000018400000010c1000000004840000000c810000000414400000000210000000400400000000a100
  | 8, 0, 5 => 0x1840000000801000000031440000001081000000020440000001041000000021440000000c01000000003840000000c81000000030040000000c910000000314400000000a10000000410400000008510000000324400000000e10000000210400000004010000000300400000010510000000028400000000210000000320400000000a100000003044000000100100000003144000000006100000003104000000109100
  | 8, 0, 6 => 0xc010000000038400000001210000000008400000010d1000000043040000000c910000000048400000010110000000434400000010410000000214400000000e100000002004000000002100000004304000000108100000000484000000081100
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 13 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_x5_1 roots_x5_1 8 s ws hint
  | 1 => checkCutEntry dom_x2_0 roots_x2_0 7 s ws hint
  | 2 => checkCutEntry dom_x4_0 roots_x4_0 7 s ws hint
  | 3 => checkCutEntry dom_x4_1_x5_1 roots_x4_1_x5_1 5 s ws hint
  | 4 => checkCutEntry dom_x3_0 roots_x3_0 7 s ws hint
  | 5 => checkCutEntry dom_x0_0_x4_1 roots_x0_0_x4_1 5 s ws hint
  | 6 => checkCutEntry dom_x4_1 roots_x4_1 6 s ws hint
  | 7 => checkCutEntry dom_x1_1_x3_0_x4_0 roots_x1_1_x3_0_x4_0 4 s ws hint
  | 8 => checkCutEntry dom_x1_0 roots_x1_0 7 s ws hint
  | 9 => checkCutEntry dom_x1_0_x5_1 roots_x1_0_x5_1 6 s ws hint
  | 10 => checkCutEntry dom_x0_0_x5_1 roots_x0_0_x5_1 5 s ws hint
  | 11 => checkCutEntry dom_x1_1 roots_x1_1 7 s ws hint
  | 12 => checkCutEntry dom_x3_1 roots_x3_1 7 s ws hint
  | 13 => checkCutEntry dom_x0_0_x4_1_x5_1 roots_x0_0_x4_1_x5_1 4 s ws hint
  | 14 => checkCutEntry dom_x0_0 roots_x0_0 6 s ws hint
  | 15 => checkCutEntry dom_x1_1_x4_0 roots_x1_1_x4_0 5 s ws hint
  | 16 => checkCutEntry dom_x1_1_x3_1 roots_x1_1_x3_1 5 s ws hint
  | 17 => checkCutEntry dom_x1_1_x3_0_x5_0 roots_x1_1_x3_0_x5_0 4 s ws hint
  | 18 => checkCutEntry dom_x1_1_x3_0 roots_x1_1_x3_0 5 s ws hint
  | 19 => checkCutEntry dom_x3_0_x5_0 roots_x3_0_x5_0 5 s ws hint
  | 20 => checkCutEntry dom_x5_0 roots_x5_0 6 s ws hint
  | 21 => checkCutEntry dom_x2_0_x4_0 roots_x2_0_x4_0 5 s ws hint
  | 22 => checkCutEntry dom_x2_0_x4_0_x5_1 roots_x2_0_x4_0_x5_1 4 s ws hint
  | 23 => checkCutEntry dom_x3_0_x4_0 roots_x3_0_x4_0 5 s ws hint
  | 24 => checkCutEntry dom_x1_0_x5_0 roots_x1_0_x5_0 5 s ws hint
  | 25 => checkCutEntry dom_x3_0_x4_0_x5_1 roots_x3_0_x4_0_x5_1 4 s ws hint
  | 26 => checkCutEntry dom_x1_0_x3_1_x5_0 roots_x1_0_x3_1_x5_0 4 s ws hint
  | 27 => checkCutEntry dom_x1_0_x3_1 roots_x1_0_x3_1 5 s ws hint
  | 28 => checkCutEntry dom_x2_0_x5_1 roots_x2_0_x5_1 5 s ws hint
  | 29 => checkCutEntry dom_x4_0_x5_1 roots_x4_0_x5_1 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_63 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_1_x3_0_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_1_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_1_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_1_x3_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_1_x3_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x4_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_0_x4_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x3_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_0_x5_1 _ hc
  · contradiction
def p0Subs : List Nat := [8, 1, 11, 2, 4, 12, 0, 14, 5, 6, 21, 20, 9, 15, 27, 10, 18, 23, 19, 3, 7, 13, 16, 22, 26, 17, 24, 25, 28, 29]
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
private theorem z6_192 : ∀ i, 192 ≤ i → i < 209 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 17 192 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 209 → Z 6 i = true := (range_split (range_split z6_0 z6_64) (range_split z6_128 z6_192))
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
private theorem z7_768 : ∀ i, 768 ≤ i → i < 810 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 42 768 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 810 → Z 7 i = true := (range_split (range_split (range_split z7_0 (range_split z7_64 z7_128)) (range_split z7_192 (range_split z7_256 z7_320))) (range_split (range_split z7_384 (range_split z7_448 z7_512)) (range_split (range_split z7_576 z7_640) (range_split z7_704 z7_768))))
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
private theorem z8_320 : ∀ i, 320 ≤ i → i < 384 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 320 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_384 : ∀ i, 384 ≤ i → i < 388 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 4 384 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 388 → Z 8 i = true := (range_split (range_split z8_0 (range_split z8_64 z8_128)) (range_split (range_split z8_192 z8_256) (range_split z8_320 z8_384)))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 37 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 37 0 = true)
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

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 14]⟩], 16⟩
theorem wit_mono : PEqualNP.MetaComplexity.Monotone2 wit := by simp [wit, PEqualNP.MetaComplexity.Monotone2]
theorem wit_size : wit.size ≤ 11 := by decide
theorem wit_eval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = ((fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4209680544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0))) x := by decide +kernel
theorem hT6 : ∀ r : Fin 64, goal_all.testBit r.val = ((fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4209680544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0))) (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4209680544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) t → 11 ≤ t :=
  lower_to_circuit6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4209680544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) goal_all 11 hT6 (by unfold IsConst; decide) low_63

end PEqualNP.Outside.L_meta_40409_aux

theorem PEqualNP.Outside.L_meta_40409 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4209680544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809448 * 2 ^ 32 + 4209680544) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s hs
  have hlb : 11 ≤ s := PEqualNP.Outside.L_meta_40409_aux.lower s hs
  exact ⟨PEqualNP.Outside.L_meta_40409_aux.wit, PEqualNP.Outside.L_meta_40409_aux.wit_mono, le_trans PEqualNP.Outside.L_meta_40409_aux.wit_size hlb, PEqualNP.Outside.L_meta_40409_aux.wit_eval⟩
