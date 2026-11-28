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

namespace PEqualNP.Outside.L_meta_40343_aux

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
  forceN ((((w &&& 4294967295) ^^^ seed) * 2654435761) &&& 4294967295) fun a =>
  forceN (((a ^^^ (a >>> 16)) + ((((w >>> 32) &&& 4294967295) ^^^ (seed + 1)) * 2246822519)) &&& 4294967295) fun x =>
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
def goal_all : Nat := 0xfeeaeee0eeeae8e0
def dom_63 : Nat := 0xffffffffffffffff
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]
def dom_x1_0_x3_1 : Nat := 0x3300330033003300
def roots_x1_0_x3_1 : List Nat := [0x2200220022002200, 0x3000300030003000, 0x3300000033000000, 0x3300330000000000]
def dom_x1_0 : Nat := 0x3333333333333333
def roots_x1_0 : List Nat := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]
def dom_x1_0_x5_1 : Nat := 0x3333333300000000
def roots_x1_0_x5_1 : List Nat := [0x2222222200000000, 0x3030303000000000, 0x3300330000000000, 0x3333000000000000]
def dom_x0_0_x4_1_x5_1 : Nat := 0x5555000000000000
def roots_x0_0_x4_1_x5_1 : List Nat := [0x4444000000000000, 0x5050000000000000, 0x5500000000000000]
def dom_x0_0_x4_1 : Nat := 0x5555000055550000
def roots_x0_0_x4_1 : List Nat := [0x4444000044440000, 0x5050000050500000, 0x5500000055000000, 0x5555000000000000]
def dom_x1_1_x2_0_x5_0 : Nat := 0xc0c0c0c
def roots_x1_1_x2_0_x5_0 : List Nat := [0x8080808, 0xc000c00, 0xc0c0000]
def dom_x1_1_x2_0 : Nat := 0xc0c0c0c0c0c0c0c
def roots_x1_1_x2_0 : List Nat := [0x808080808080808, 0xc000c000c000c00, 0xc0c00000c0c0000, 0xc0c0c0c00000000]
def dom_x2_0_x3_1_x4_0 : Nat := 0xf0000000f00
def roots_x2_0_x3_1_x4_0 : List Nat := [0xa0000000a00, 0xc0000000c00, 0xf0000000000]
def dom_x2_0_x3_1 : Nat := 0xf000f000f000f00
def roots_x2_0_x3_1 : List Nat := [0xa000a000a000a00, 0xc000c000c000c00, 0xf0000000f000000, 0xf000f0000000000]
def dom_x2_0_x4_0 : Nat := 0xf0f00000f0f
def roots_x2_0_x4_0 : List Nat := [0xa0a00000a0a, 0xc0c00000c0c, 0xf0000000f00, 0xf0f00000000]
def dom_x2_0_x5_0 : Nat := 0xf0f0f0f
def roots_x2_0_x5_0 : List Nat := [0xa0a0a0a, 0xc0c0c0c, 0xf000f00, 0xf0f0000]
def dom_x2_0 : Nat := 0xf0f0f0f0f0f0f0f
def roots_x2_0 : List Nat := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]
def dom_x4_1_x5_1 : Nat := 0xffff000000000000
def roots_x4_1_x5_1 : List Nat := [0xaaaa000000000000, 0xcccc000000000000, 0xf0f0000000000000, 0xff00000000000000]
def dom_x0_0_x3_1 : Nat := 0x5500550055005500
def roots_x0_0_x3_1 : List Nat := [0x4400440044004400, 0x5000500050005000, 0x5500000055000000, 0x5500550000000000]
def dom_x2_0_x3_1_x5_0 : Nat := 0xf000f00
def roots_x2_0_x3_1_x5_0 : List Nat := [0xa000a00, 0xc000c00, 0xf000000]
def dom_x3_1_x4_0_x5_0 : Nat := 0xff00
def roots_x3_1_x4_0_x5_0 : List Nat := [0xaa00, 0xcc00, 0xf000]
def dom_x3_1_x4_0 : Nat := 0xff000000ff00
def roots_x3_1_x4_0 : List Nat := [0xaa000000aa00, 0xcc000000cc00, 0xf0000000f000, 0xff0000000000]
def dom_x3_1_x5_0 : Nat := 0xff00ff00
def roots_x3_1_x5_0 : List Nat := [0xaa00aa00, 0xcc00cc00, 0xf000f000, 0xff000000]
def dom_x3_1 : Nat := 0xff00ff00ff00ff00
def roots_x3_1 : List Nat := [0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000]
def dom_x0_0_x5_1 : Nat := 0x5555555500000000
def roots_x0_0_x5_1 : List Nat := [0x4444444400000000, 0x5050505000000000, 0x5500550000000000, 0x5555000000000000]
def dom_x0_0 : Nat := 0x5555555555555555
def roots_x0_0 : List Nat := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]
def dom_x5_1 : Nat := 0xffffffff00000000
def roots_x5_1 : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]
def dom_x1_1_x5_0 : Nat := 0xcccccccc
def roots_x1_1_x5_0 : List Nat := [0x88888888, 0xc0c0c0c0, 0xcc00cc00, 0xcccc0000]
def dom_x4_0_x5_0 : Nat := 0xffff
def roots_x4_0_x5_0 : List Nat := [0xaaaa, 0xcccc, 0xf0f0, 0xff00]
def dom_x5_0 : Nat := 0xffffffff
def roots_x5_0 : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]
def dom_x4_0 : Nat := 0xffff0000ffff
def roots_x4_0 : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]
def dom_x1_1 : Nat := 0xcccccccccccccccc
def roots_x1_1 : List Nat := [0x8888888888888888, 0xc0c0c0c0c0c0c0c0, 0xcc00cc00cc00cc00, 0xcccc0000cccc0000, 0xcccccccc00000000]
def dom_x4_1 : Nat := 0xffff0000ffff0000
def roots_x4_1 : List Nat := [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000]

namespace S_x1_0_x3_1
def pairsG : List (Nat × Nat) := [(9, 13), (9, 25), (9, 41), (12, 13), (24, 25), (28, 29), (28, 60), (40, 41), (44, 45), (44, 60), (56, 57), (56, 60)]
def r1sG : List Nat := [9, 9, 9, 12, 24, 28, 28, 40, 44, 44, 56, 56]
def r2sG : List Nat := [13, 25, 41, 13, 25, 29, 60, 41, 45, 60, 57, 60]
def mpG : Nat := 0xfff
def pool6G : List Nat := [30825722423577, 30825923746061, 48417640025385, 48418109790477]
def xsM : List Nat := roots_x1_0_x3_1.map (· &&& dom_x1_0_x3_1)
def goalM : Nat := goal_all &&& dom_x1_0_x3_1
def NN : Nat → Nat
  | 4 => 5
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x897c9ebd40b0c94c391caec018eb3e570e64878d
  | 5, 0, 0 => 0x391caec0
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x330033000000330000003300030003000300030011001100110011003300330000000000330000003300000030003000300030002200220022002200
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x646468c4688468544474
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x1_0_x3_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x1_0_x3_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x1_0_x3_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x1_0_x3_1 goalM u ys) : RunD dom_x1_0_x3_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x1_0_x3_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x1_0_x3_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 3 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_x1_0_x3_1 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x1_0_x3_1 roots_x1_0_x3_1 goal_all 6 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x1_0_x3_1 goal_all := by
    have h0 : isConstB dom_x1_0_x3_1 goal_all = false := by decide +kernel
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
end S_x1_0_x3_1
theorem low_x1_0_x3_1 : Lower dom_x1_0_x3_1 roots_x1_0_x3_1 goal_all 6 := S_x1_0_x3_1.noCircuit

theorem low_x1_0 : Lower dom_x1_0 roots_x1_0 goal_all 7 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x3300330033003300, 33, 41)] (by decide +kernel) (by decide +kernel) low_x1_0_x3_1

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
  | 4, 0, 0 => 0xcba65d238e1981d253d9707a4a55c3be49ebd58e
  | 5, 0, 0 => 0xcba65d23
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x3333000000000033003300000000030303030000000011111111000000003333000000000000330033000000000030303030000000002222222200000000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x6884646468c468544474
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
  | 3, 0, 0 => 0x8c12a2c1
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
    [(0x5555000000000000, 28, 60)] (by decide +kernel) (by decide +kernel) low_x0_0_x4_1_x5_1

namespace S_x1_1_x2_0_x5_0
def pairsG : List (Nat × Nat) := [(3, 11), (3, 19), (10, 11), (10, 26), (18, 19), (18, 26)]
def r1sG : List Nat := [3, 3, 10, 10, 18, 18]
def r2sG : List Nat := [11, 19, 11, 26, 19, 26]
def mpG : Nat := 0x3f
def pool6G : List Nat := [11008304878347]
def xsM : List Nat := roots_x1_1_x2_0_x5_0.map (· &&& dom_x1_1_x2_0_x5_0)
def goalM : Nat := goal_all &&& dom_x1_1_x2_0_x5_0
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xe4fedbad
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xc0c0000000000000c000c000000000008080808
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x1_1_x2_0_x5_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x1_1_x2_0_x5_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x1_1_x2_0_x5_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x1_1_x2_0_x5_0 goalM u ys) : RunD dom_x1_1_x2_0_x5_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x1_1_x2_0_x5_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x1_1_x2_0_x5_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x1_1_x2_0_x5_0 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x1_1_x2_0_x5_0 roots_x1_1_x2_0_x5_0 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x1_1_x2_0_x5_0 goal_all := by
    have h0 : isConstB dom_x1_1_x2_0_x5_0 goal_all = false := by decide +kernel
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
end S_x1_1_x2_0_x5_0
theorem low_x1_1_x2_0_x5_0 : Lower dom_x1_1_x2_0_x5_0 roots_x1_1_x2_0_x5_0 goal_all 4 := S_x1_1_x2_0_x5_0.noCircuit

theorem low_x1_1_x2_0 : Lower dom_x1_1_x2_0 roots_x1_1_x2_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c0c0c00000000, 10, 42)] (by decide +kernel) (by decide +kernel) low_x1_1_x2_0_x5_0

namespace S_x2_0_x3_1_x4_0
def pairsG : List (Nat × Nat) := [(9, 11), (9, 41), (10, 11), (10, 42), (40, 41), (40, 42)]
def r1sG : List Nat := [9, 9, 10, 10, 40, 40]
def r2sG : List Nat := [11, 41, 11, 42, 41, 42]
def mpG : Nat := 0x3f
def pool6G : List Nat := [11034444835083]
def xsM : List Nat := roots_x2_0_x3_1_x4_0.map (· &&& dom_x2_0_x3_1_x4_0)
def goalM : Nat := goal_all &&& dom_x2_0_x3_1_x4_0
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xc4a41110
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xf000000000000000c0000000c0000000a0000000a00
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x2_0_x3_1_x4_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x2_0_x3_1_x4_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x2_0_x3_1_x4_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x2_0_x3_1_x4_0 goalM u ys) : RunD dom_x2_0_x3_1_x4_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x2_0_x3_1_x4_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x2_0_x3_1_x4_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x2_0_x3_1_x4_0 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x2_0_x3_1_x4_0 roots_x2_0_x3_1_x4_0 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x2_0_x3_1_x4_0 goal_all := by
    have h0 : isConstB dom_x2_0_x3_1_x4_0 goal_all = false := by decide +kernel
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
end S_x2_0_x3_1_x4_0
theorem low_x2_0_x3_1_x4_0 : Lower dom_x2_0_x3_1_x4_0 roots_x2_0_x3_1_x4_0 goal_all 4 := S_x2_0_x3_1_x4_0.noCircuit

theorem low_x2_0_x3_1 : Lower dom_x2_0_x3_1 roots_x2_0_x3_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0000000f000000, 9, 25)] (by decide +kernel) (by decide +kernel) low_x2_0_x3_1_x4_0

theorem low_x2_0_x4_0 : Lower dom_x2_0_x4_0 roots_x2_0_x4_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0000000f00, 3, 11)] (by decide +kernel) (by decide +kernel) low_x2_0_x3_1_x4_0

theorem low_x2_0_x5_0 : Lower dom_x2_0_x5_0 roots_x2_0_x5_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c0c0c, 9, 11)] (by decide +kernel) (by decide +kernel) low_x1_1_x2_0_x5_0

namespace S_x2_0
def pairsG : List (Nat × Nat) := [(1, 17), (3, 11), (3, 19), (9, 11), (9, 25), (9, 41), (10, 11), (10, 26), (10, 42), (16, 17), (18, 19), (18, 26), (24, 25), (24, 26), (33, 41), (33, 49), (34, 42), (35, 43), (35, 51), (40, 41), (40, 42), (48, 49), (50, 51), (50, 58), (56, 57), (56, 58)]
def r1sG : List Nat := [1, 3, 3, 9, 9, 9, 10, 10, 10, 16, 18, 18, 24, 24, 33, 33, 34, 35, 35, 40, 40, 48, 50, 50, 56, 56]
def r2sG : List Nat := [17, 11, 19, 11, 25, 41, 11, 26, 42, 17, 19, 26, 25, 26, 41, 49, 42, 43, 51, 41, 42, 49, 51, 58, 57, 58]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [38526697214219, 11034713270539, 61723815579945, 61615752940314, 55014405573393]
def xsM : List Nat := roots_x2_0.map (· &&& dom_x2_0)
def goalM : Nat := goal_all &&& dom_x2_0
def NN : Nat → Nat
  | 5 => 1
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x441a1221
  | 6, 0, 0 => 0x1bba847f
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xa0a0a0a0a0a0a0a0f0f0f0f000000000f0f00000f0f00000f000f000f000f000c0c0c0c0c0c0c0c0505050505050505
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
  | 0 => 0x6c03f0000000003ffc0000000000003e03e0000000000031831f80000000000c70dc60000000003f93fc0
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x16ed67f0000000003ffc1200000000003e4be9500000000039b79fa0000000002d72dce0000000002912980
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
  | 0 => checkCutEntry dom_x1_1_x2_0 roots_x1_1_x2_0 5 s ws hint
  | 1 => checkCutEntry dom_x2_0_x3_1 roots_x2_0_x3_1 5 s ws hint
  | 2 => checkCutEntry dom_x2_0_x4_0 roots_x2_0_x4_0 5 s ws hint
  | 3 => checkCutEntry dom_x2_0_x5_0 roots_x2_0_x5_0 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x2_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_1_x2_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x5_0 _ hc
  · contradiction
def p0Subs : List Nat := [1, 0, 2, 3]
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

theorem low_x4_1_x5_1 : Lower dom_x4_1_x5_1 roots_x4_1_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa000000000000, 48, 49)] (by decide +kernel) (by decide +kernel) low_x0_0_x4_1_x5_1

namespace S_x0_0_x3_1
def pairsG : List (Nat × Nat) := [(10, 14), (10, 26), (10, 42), (12, 14), (24, 26), (28, 30), (28, 60), (40, 42), (44, 46), (44, 60), (56, 58), (56, 60)]
def r1sG : List Nat := [10, 10, 10, 12, 24, 28, 28, 40, 44, 44, 56, 56]
def r2sG : List Nat := [14, 26, 42, 14, 26, 30, 60, 42, 46, 60, 58, 60]
def mpG : Nat := 0xfff
def pool6G : List Nat := [30830017391130, 30830218713614, 48421934992938, 48422404758030]
def xsM : List Nat := roots_x0_0_x3_1.map (· &&& dom_x0_0_x3_1)
def goalM : Nat := goal_all &&& dom_x0_0_x3_1
def NN : Nat → Nat
  | 4 => 5
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xbc9d16ba9240dc5685a876ed6b1c84cc64286d6f
  | 5, 0, 0 => 0x6b1c84cc
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x550055000000550000005500050005000500050011001100110011005500550000000000550000005500000050005000500050004400440044004400
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x447468c4685468846464
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x0_0_x3_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x0_0_x3_1 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x0_0_x3_1 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x0_0_x3_1 goalM u ys) : RunD dom_x0_0_x3_1 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x0_0_x3_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x0_0_x3_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 3 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_x0_0_x3_1 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x0_0_x3_1 roots_x0_0_x3_1 goal_all 6 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x0_0_x3_1 goal_all := by
    have h0 : isConstB dom_x0_0_x3_1 goal_all = false := by decide +kernel
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
end S_x0_0_x3_1
theorem low_x0_0_x3_1 : Lower dom_x0_0_x3_1 roots_x0_0_x3_1 goal_all 6 := S_x0_0_x3_1.noCircuit

namespace S_x2_0_x3_1_x5_0
def pairsG : List (Nat × Nat) := [(9, 11), (9, 25), (10, 11), (10, 26), (24, 25), (24, 26)]
def r1sG : List Nat := [9, 9, 10, 10, 24, 24]
def r2sG : List Nat := [11, 25, 11, 26, 25, 26]
def mpG : Nat := 0x3f
def pool6G : List Nat := [11034175346955]
def xsM : List Nat := roots_x2_0_x3_1_x5_0.map (· &&& dom_x2_0_x3_1_x5_0)
def goalM : Nat := goal_all &&& dom_x2_0_x3_1_x5_0
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x62a6bbc9
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xf000000000000000c000c00000000000a000a00
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x2_0_x3_1_x5_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x2_0_x3_1_x5_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x2_0_x3_1_x5_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x2_0_x3_1_x5_0 goalM u ys) : RunD dom_x2_0_x3_1_x5_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x2_0_x3_1_x5_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x2_0_x3_1_x5_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x2_0_x3_1_x5_0 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x2_0_x3_1_x5_0 roots_x2_0_x3_1_x5_0 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x2_0_x3_1_x5_0 goal_all := by
    have h0 : isConstB dom_x2_0_x3_1_x5_0 goal_all = false := by decide +kernel
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
end S_x2_0_x3_1_x5_0
theorem low_x2_0_x3_1_x5_0 : Lower dom_x2_0_x3_1_x5_0 roots_x2_0_x3_1_x5_0 goal_all 4 := S_x2_0_x3_1_x5_0.noCircuit

namespace S_x3_1_x4_0_x5_0
def pairsG : List (Nat × Nat) := [(9, 11), (9, 13), (10, 11), (10, 14), (12, 13), (12, 14)]
def r1sG : List Nat := [9, 9, 10, 10, 12, 12]
def r2sG : List Nat := [11, 13, 11, 14, 13, 14]
def mpG : Nat := 0x3f
def pool6G : List Nat := [11033973230859]
def xsM : List Nat := roots_x3_1_x4_0_x5_0.map (· &&& dom_x3_1_x4_0_x5_0)
def goalM : Nat := goal_all &&& dom_x3_1_x4_0_x5_0
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x5b72f794
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xf000000000000000cc00000000000000aa00
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
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x3_1_x4_0_x5_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · contradiction
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x3_1_x4_0_x5_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq] at h; simp only [Bool.and_eq_true] at h; exact checkCutByIdx_sound h.2
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x3_1_x4_0_x5_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x3_1_x4_0_x5_0 goalM u ys) : RunD dom_x3_1_x4_0_x5_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x3_1_x4_0_x5_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
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
def RootG (s : Nat) : Bool := scr dom_x3_1_x4_0_x5_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_x3_1_x4_0_x5_0 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x3_1_x4_0_x5_0 roots_x3_1_x4_0_x5_0 goal_all 4 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x3_1_x4_0_x5_0 goal_all := by
    have h0 : isConstB dom_x3_1_x4_0_x5_0 goal_all = false := by decide +kernel
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
end S_x3_1_x4_0_x5_0
theorem low_x3_1_x4_0_x5_0 : Lower dom_x3_1_x4_0_x5_0 roots_x3_1_x4_0_x5_0 goal_all 4 := S_x3_1_x4_0_x5_0.noCircuit

theorem low_x3_1_x4_0 : Lower dom_x3_1_x4_0 roots_x3_1_x4_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0000000f000, 9, 13)] (by decide +kernel) (by decide +kernel) low_x2_0_x3_1_x4_0

theorem low_x3_1_x5_0 : Lower dom_x3_1_x5_0 roots_x3_1_x5_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf000f000, 9, 13)] (by decide +kernel) (by decide +kernel) low_x2_0_x3_1_x5_0

namespace S_x3_1
def pairsG : List (Nat × Nat) := [(9, 11), (9, 13), (9, 25), (9, 41), (10, 11), (10, 14), (10, 26), (10, 42), (12, 13), (12, 14), (24, 25), (24, 26), (28, 29), (28, 30), (28, 60), (40, 41), (40, 42), (44, 45), (44, 46), (44, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [9, 9, 9, 9, 10, 10, 10, 10, 12, 12, 24, 24, 28, 28, 28, 40, 40, 44, 44, 44, 56, 56, 56]
def r2sG : List Nat := [11, 13, 25, 41, 11, 14, 26, 42, 13, 14, 25, 26, 29, 30, 60, 41, 42, 45, 46, 60, 57, 58, 60]
def mpG : Nat := 0x7fffff
def pool6G : List Nat := [48421614979882, 48418109790477, 30830017383962, 11034241666315, 61611779558697, 30825149762329, 48498924394812, 48422404758030, 30829427886874, 61616074526250, 30825148975885, 30825722416409, 61761782353212, 61693063925052, 11034712217867, 48498940185404, 48498923342652, 48417640025385, 30825923746061, 30830218713614, 48421934992938, 48498941233980, 48498924391228, 61693078932284, 61693062089532]
def xsM : List Nat := roots_x3_1.map (· &&& dom_x3_1)
def goalM : Nat := goal_all &&& dom_x3_1
def NN : Nat → Nat
  | 5 => 40
  | 6 => 120
  | 7 => 22
  | 8 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xfec168fefb4fccc8f27c9fe4eef1b8d4eebcc94be9f365d0dcc415b5dc9a8ac1d838ea04cccada97bff27aa7af70160fa10fbddb9eb7eb899c88f0a996566a7592884ff890030e278972aa3d82b89fce7e578d767742f73371a1d30f715496f66753f6456107b97c5784461b5426d26b538ce0964bacfc9243bd306c30a068152a090c7222777f9b16beee6a15201da30727790005506d790138b6380050a15e
  | 6, 0, 0 => 0x9116889b8fe0c0518d8b5bbc8d324910801110277d45041b7c3e102b7a0b6c09783c43ea7809b66c73bb0ae1711a12986ae743fd6acf63a4698907716780d3a363d05ac05e5440805d9d8c255d5c69915c49f1bb5a066d5957e6ed87565b2ef354888f5854539fcf535bc8e0510bacc34fb8e97b4d07ea374a5006344483efa541ab39f63a1dd2cf38707ed8382adbde34f22da43261b11b3255b0e2301d321e2ff0be2a2cb293d42c02d2de2b0afbef2a01f36425d5ddca25c8d8f12187323f1f1bac811e4962331c946fa41c3322b41c12acf31a2c290f12328203113c17070cd0a56f085295c80727ea35064bdcc705db1d7c021fc72d016c66dd0127f03e
  | 6, 0, 1 => 0xfaa18417f8824743f67c2c9df652d88cf3da6444f2501703f211c1caee8244eded57cc3fec3967a6e84f7652e6ab4101e4406d67dde9597cdb52448cda6c33d1d6eb6d7ad5f3968bd5b14a21cbbf066bcb829462caf7f6bbca701c8cc9a1b5a2c993fdbac7bf3f3cc7b107d6c71bbd50c66d1a11c37093b1bd1b1c9fb9d20578b8cca3f9b8bf8da2b7500f09b6b61d34b3e608ccb2b4ffc9b07d3a5fb076d499aa1ac629a964cba4a95406f0a8fcf3cfa6e66d0aa6847f87a56b47f1a409289fa21f4f9ba1cd3598a13c0eba9c83ded69c4e6c4b943978759327009f9251db66
  | 7, 0, 0 => 0xf9d04ef9e7a12da1e5a7e6abe3528216c3eb1704c2f34015b41b66daaa1ac6299fb4a95381c9f93867033d615e19bc225c13032157e6ed873a0793c131196ae62cb293d41f68dbfc19b23d5e0e93ca530c7d438e0c1b560b
  | 8, 0, 0 => 0x19b23d5e
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xee00ee00ee00ee00ff00ff00ff000000ff00000000000000ff00ff00f000f000f000f00000000000ff00f000ff00f000f0000000f0000000cc00cc00cc00cc0000000000ff00ff00f000f000f000f0000000ff000000ff00ff00ff0000000000ff000000ff000000550055005500550033003300330033000f000f000f000f00
  | 1 => 0xfe00fe00fe00fe001100110011001100ff00ff00ff00f000ff00cc00cc00cc00ff00aa00aa00aa00fc00fc00cc00cc00fa00fa00aa00aa00fc00cc00fc00cc00fa00aa00fa00aa00aa00aa00aa00aa00ff00ff00cc00cc00ff00ff00aa00aa00ff00cc00ff00cc00ff00aa00ff00aa00fc00fc00fc00fc00fa00fa00fa00fa00
  | 2 => 0x33003300ff00ff00ff00cc000000330000003300ff00ff00fc00fc00ff00fc00ff00fc0003000300030003000000000055005500ff00ff00ff00aa000000550000005500ff00ff00fa00fa00ff00fa00ff00fa000500050005000500ff00ff00ee00ee00ff00ee00ff00ee00
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x7540c62166004289581574448621667550c62166004297216501550318f50041820455004298216500420200551035c63c861036063d6600458100557444c621663032cf21661036463c86003182047500320200757440d12166003581007500c0d9216500c0cb20251036863d6600c0cb581500e6c6216500c0da216538d18f216600e706216500620214750040d140f500658114750044d218f510a24f2166
  | 5, 0, 1 => 0xe3462025008580147511b0c63c8600e34658150040c204057440d0216611c0c63d660042892025
  | 6, 0, 0 => 0xc10340859801120c6581600e113188598011b0c621661031893c859c000428921650048c318859801120c8580600c5031885980003188587500e103188098e10340621671033463c859c01063c858560040c6216b58054418858560140c62161d8011c0c621660044c318f59803840c65816004283408598010318859e600e1032160180103189202600a0c62161d801130c6202600c543188598010334620260040df188598000418808550040c625605801101885856
  | 6, 0, 1 => 0x480318859801031880856015103188098010368621660040c658115801034063c86004a431885980384486216600444621615801033c8580601510321601804c318858760001885851d40a840c6216600e54318859809040c621663044c318859c00040c6081500c106216158010340658160040d140859801120c63c860001062161540113486216600038d18859400040c808050040d02160180b040c621663840c63c859c00d1188587601410621615800040d60405
  | 6, 0, 2 => 0x26103188598428318f216701d1031885980003196047501410318f219510a0c621670000c85801d403040c658160040c62021d803040d121660040d9188598010318b20260040c62169d804831885876021103188598010a4c6216600010321601401031885a560003032c8594010319604760040c62d605805040c6581630448318859c010a0c620263840d118859c05440c63d660040c6216a1805040c858060044c6216158010a0c6581600428344859803940c62166
  | 6, 0, 3 => 0x318f2161d801034463d660040cd196058054318858760155031885980004196045500429218859801130c858063040c63c859d410a0c6216700010858015401031885a260040d1188098011218858560040c620201840c62cf21670000c62021d400d018858760040d718859801031885ab60040c6581018010360621660040d121601803040c62026
  | 7, 0, 0 => 0x10a0c6216610318f216610318858565440c621660040c6202510340621660040c658150040c858051120c621663840c6216610318921661130c62166103346216600418858551034462166103188580600318858753040c621660040c62165103188587610318b21665040c62166
  | 8, 0, 0 => 0x40c62165
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 40
  | 6 => 46
  | 7 => 40
  | 8 => 34
  | _ => 0
def stateM : Nat → Nat
  | 5 => 0xffffffffff
  | 6 => 0x3fffffffffff
  | 7 => 0xffffffffff
  | 8 => 0x3ffffffff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0xff00000000007ffc00000000000070000000000000007ff30000000000000e000000000000007e7f00000000000000700000000000000000f00000000000007fff00000000000e730000000000000f83ff00000000007f80000000000000707c0000000000007ffff000000000007fff0f0000000000718cff
  | 1 => 0xe73ff00000000007fff0000000000007fff0000000000007000f0000000000070000f00000000000e00f000000000000e000f00000000000070f0000000000000700f000000000000000f00000000007f80f000000000007f800f0000000000707cf00000000000707c0f00000000000e73f000000000000e730f
  | 2 => 0x7f0f00000000007ffcf000000000000f830f00000000007ff3f000000000007e7ff00000000000718c0f0000000000007ff000000000007ffc0f00000000000f83f000000000007ff30f00000000007e7f0f0000000000718cf000000000007f80ff0000000000707cff
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x37bfff00000000007ffccc000000000078400000000000007ff3aa00000000004e400000000000007e7f6600000000004870000000000000252af10000000000003f7700000000004e732200000000000783bb00000000007fc0880000000000787c4400000000006d6ae000000000005ad50e0000000000318cdd
  | 1 => 0x7fffff000000000048400000000000007fffee00000000007d6af100000000007ad51f00000000006f6af100000000005ed51f00000000006d7af100000000005af51f000000000012951f00000000007feaf900000000007fd59f00000000007d7ef500000000007afd5f00000000006f7bf300000000005ef73f
  | 2 => 0x150600000000007ffefd000000000002810a00000000007ffbfb00000000007f7ff7000000000010840c0000000000002a6000000000007ffddf00000000000502a000000000007ff7bf00000000007eff7f00000000002108c000000000007fffff00000000007fffff
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 46 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 46 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 46 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 46 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 46 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0x3f) :: stateWiresD n (ids >>> 6)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0x3f) :: stateWiresS n (ids >>> 6)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 8 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 5 => 39
  | 6 => 42
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xf2501703e70a0886e6f59eeee319fb19e265a37bd6eb6d7acf1ae000ce3a7005cc8d5949c71bbd50c2485055bdf5d41ebbd5aed3b847afa4b46a1f2ab41b66daaa1ac6299ed96e4b92c17a6b799e26ab6677ed3a623646885fcdd5d057e6ed8754539fcf4ca595a94483efa5433e81d940fbe0ee3d0a974e3adf7d4f38b0e298318f492a2cb293d42b4f595329f9fd9b21713bf6214eb8a2021fc72d
  | 6, 0, 0 => 0xf5ef9e8df3fbe706f2b53e3aea8899b7dda409c1dc1f4db2d864d6c9d68ffa11d3a36910d26bddccd2302a0fb89b8cf1ad307d16ad0137ffa6fbd05ca4ecb7b8a1c80e64a01788b69d50e41889eb7510864737db816f906e7693b4b17634a85b71f16cbd7094780f6dc87d4167f0cc0c6667b44f5eb71b5d563b36bb53f82c663b335a9c3499501c34135f39325719632e64a3622a98af6b246402b115bcf36a08df058601c453c4
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x8400000000610100000038400000000210100000028400000000e10100000018404000000610000000008404000000610100000018404000000e10000000008400000000e10000000028400000000610000000028404000000610100000028404000000610000000008404000000210100000028400000000e10100000038404000000a10100000038404000000210100000008400000000e10100000018404000000a101
  | 5, 0, 1 => 0xa10000000028404000000610000000324414000000e10000000038404000000a101
  | 6, 0, 0 => 0x28404000000610000000038404000000210100000038404000000610100000028404000000210000000038400000000a10000000018400000000a10100000038404000000610000000008404000000a10000000008400000000610100000028400000000e10000000038404000000610000000038400000000210100000028400000000a10100000008404000000610100000018404000000a10100000038400000000a100
  | 6, 0, 1 => 0x8400000000610100000038404000000e10100000008404000000610000000028404000000e100000000184040000002100
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 7 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_x1_0_x3_1 roots_x1_0_x3_1 6 s ws hint
  | 1 => checkCutEntry dom_x0_0_x3_1 roots_x0_0_x3_1 6 s ws hint
  | 2 => checkCutEntry dom_x2_0_x3_1_x4_0 roots_x2_0_x3_1_x4_0 4 s ws hint
  | 3 => checkCutEntry dom_x2_0_x3_1_x5_0 roots_x2_0_x3_1_x5_0 4 s ws hint
  | 4 => checkCutEntry dom_x3_1_x4_0_x5_0 roots_x3_1_x4_0_x5_0 4 s ws hint
  | 5 => checkCutEntry dom_x2_0_x3_1 roots_x2_0_x3_1 5 s ws hint
  | 6 => checkCutEntry dom_x3_1_x4_0 roots_x3_1_x4_0 5 s ws hint
  | 7 => checkCutEntry dom_x3_1_x5_0 roots_x3_1_x5_0 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x3_1 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x3_1_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x3_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_1_x4_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_1_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_1_x5_0 _ hc
  · contradiction
def p0Subs : List Nat := [1, 0, 5, 6, 7, 2, 3, 4]
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
private theorem z5 : ∀ i, 0 ≤ i → i < 40 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 40 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 64 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 64 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6_64 : ∀ i, 64 ≤ i → i < 120 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 56 64 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 120 → Z 6 i = true := (range_split z6_0 z6_64)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7 : ∀ i, 0 ≤ i → i < 22 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 22 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8 : ∀ i, 0 ≤ i → i < 1 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 1 0 = true)
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
def RootG (s : Nat) : Bool := scr dom_x3_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 8) (h : RunD dom_x3_1 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x3_1 roots_x3_1 goal_all 9 := by
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
theorem low_x3_1 : Lower dom_x3_1 roots_x3_1 goal_all 9 := S_x3_1.noCircuit

theorem low_x0_0_x5_1 : Lower dom_x0_0_x5_1 roots_x0_0_x5_1 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0x5555000000000000, 44, 60)] (by decide +kernel) (by decide +kernel) low_x0_0_x4_1_x5_1

namespace S_x0_0
def pairsG : List (Nat × Nat) := [(2, 6), (4, 6), (10, 14), (10, 26), (10, 42), (12, 14), (18, 22), (18, 26), (20, 22), (24, 26), (28, 30), (28, 60), (34, 38), (34, 42), (36, 38), (40, 42), (44, 46), (44, 60), (50, 54), (50, 58), (52, 54), (52, 60), (56, 58), (56, 60)]
def r1sG : List Nat := [2, 4, 10, 10, 10, 12, 18, 18, 20, 24, 28, 28, 34, 34, 36, 40, 44, 44, 50, 50, 52, 52, 56, 56]
def r2sG : List Nat := [6, 6, 14, 26, 42, 14, 22, 26, 22, 26, 30, 60, 38, 42, 38, 42, 46, 60, 54, 58, 54, 60, 58, 60]
def mpG : Nat := 0xffffff
def pool6G : List Nat := [30830017391130, 55096716822042, 30830218717702, 61761799194172, 48421934996010, 55165436298794]
def xsM : List Nat := roots_x0_0.map (· &&& dom_x0_0)
def goalM : Nat := goal_all &&& dom_x0_0
def NN : Nat → Nat
  | 4 => 1
  | 5 => 9
  | 6 => 12
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x4561e2b9
  | 5, 0, 0 => 0xed64ba7fe9b24219d13cff91d0a381b5b5e22c2597330fd08188e31e38cce0b010891f1f
  | 6, 0, 0 => 0xdde73355b49e5fb1860d7fa98109688b7f81043572c1235352750242391009652d01d1ec2a506aae1757a53a069d373b
  | 7, 0, 0 => 0x73b5f571
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0x4444444400000000444400004444000054545454000000005454000054540000444444444444444454545454545454540000000055555555505050505050505000005555000055555500550055005500111111111111111105050505050505055555555500000000555500005555000054005400540054004040404040404040
  | 1 => 0x50505050000000005050000050500000
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x188204
  | 5, 0, 0 => 0x33310b5199053a88cd42d4465912a3119405188c52288c82a5466590ea31050b5
  | 6, 0, 0 => 0xc464154623220b6188c85918623290b600cc859d4623216e6188c85bd8623222b600c46591462321606008c85a5462321656
  | 7, 0, 0 => 0x31190b5
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 24
  | 5 => 29
  | 6 => 34
  | 7 => 29
  | _ => 0
def stateM : Nat → Nat
  | 4 => 0xffffff
  | 5 => 0x1fffffff
  | 6 => 0x3ffffffff
  | 7 => 0x1fffffff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0xc300000000000000c00c000000000003f700000000000003c0dc000000000000c30dd00000000003f7dff0000000000000fff0000000000334d22000000000003f03f0000000000c38e3c0000000000f3cf220000000000ccb2dd0000000000fff0000000000000fc0fc00000000000030c3c0000000000000000
  | 1 => 0x3340000000000000300d00
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x5df01000000000005c07c80000000000fff8100000000000fe0fc800000000005df7ff0000000000ffffff00000000000007ef0000000000b75d67000000000001f0370000000000ebaebc0000000000a20800000000000048a2980000000000fff8100000000000fe0fc80000000000ebaebc0000000000155567
  | 1 => 0xb758000000000000b60d40
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 18 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 18 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 18 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 18 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 18 then wireAt i else 0
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 5 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 5 => 12
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xe08254e2d1eeb1cecad82830c58fd1b3922ea5a69167b64b7c8478f473109f6a4314070f3301872b23f600d30b4554dd
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x18400000000a10000000038400000000a10000000018400000000210000000038400000000610000000008400000000a10000000008400000000e100
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 5 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_x0_0_x3_1 roots_x0_0_x3_1 6 s ws hint
  | 1 => checkCutEntry dom_x0_0_x4_1 roots_x0_0_x4_1 5 s ws hint
  | 2 => checkCutEntry dom_x0_0_x5_1 roots_x0_0_x5_1 5 s ws hint
  | 3 => checkCutEntry dom_x0_0_x4_1_x5_1 roots_x0_0_x4_1_x5_1 4 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x0_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_1_x5_1 _ hc
  · contradiction
def p0Subs : List Nat := [0, 1, 2, 3]
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  (forceN (cidxH s h) fun i => decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws ((CV s (i / 512) (i / 32 % 16) >>> (42 * (i % 32))) &&& 0x3ffffffffff)) ||
  p0Subs.any (fun k => checkCutByIdx s ws k)
theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_x0_0 goalM u ys := by
  unfold cutHitH at h; rw [forceN_eq, Bool.or_eq_true] at h; rcases h with h1 | h0
  · simp only [Bool.and_eq_true] at h1; exact checkCutByIdx_sound h1.2
  · obtain ⟨k, _, hk⟩ := List.any_eq_true.1 h0; exact checkCutByIdx_sound hk
def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_x0_0 goalM u ys := cutHitH_sound h
def ori (zs : List Nat) : List Nat := zs
theorem ori_ok {u ys} (h : RunD dom_x0_0 goalM u ys) : RunD dom_x0_0 goalM u (ori ys) := h
def Z (s : Nat) := bar dom_x0_0 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 9 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 9 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 12 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 0 = true)
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
def RootG (s : Nat) : Bool := scr dom_x0_0 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_x0_0 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr; rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower dom_x0_0 roots_x0_0 goal_all 8 := by
  intro p bank hr ha; by_contra! hsmall
  have hnc : ¬ IsConst dom_x0_0 goal_all := by
    have h0 : isConstB dom_x0_0 goal_all = false := by decide +kernel
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
end S_x0_0
theorem low_x0_0 : Lower dom_x0_0 roots_x0_0 goal_all 8 := S_x0_0.noCircuit

theorem low_x5_1 : Lower dom_x5_1 roots_x5_1 goal_all 7 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccccccc00000000, 36, 38)] (by decide +kernel) (by decide +kernel) low_x1_0_x5_1

theorem low_x1_1_x5_0 : Lower dom_x1_1_x5_0 roots_x1_1_x5_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c0c0c0, 2, 6)] (by decide +kernel) (by decide +kernel) low_x1_1_x2_0_x5_0

theorem low_x4_0_x5_0 : Lower dom_x4_0_x5_0 roots_x4_0_x5_0 goal_all 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xff00, 3, 11)] (by decide +kernel) (by decide +kernel) low_x3_1_x4_0_x5_0

namespace S_x5_0
def pairsG : List (Nat × Nat) := [(1, 5), (1, 17), (2, 6), (3, 7), (3, 11), (3, 19), (4, 5), (4, 6), (9, 11), (9, 13), (9, 25), (10, 11), (10, 14), (10, 26), (12, 13), (12, 14), (16, 17), (18, 19), (18, 22), (18, 26), (20, 21), (20, 22), (24, 25), (24, 26), (28, 29), (28, 30)]
def r1sG : List Nat := [1, 1, 2, 3, 3, 3, 4, 4, 9, 9, 9, 10, 10, 10, 12, 12, 16, 18, 18, 18, 20, 20, 24, 24, 28, 28]
def r2sG : List Nat := [5, 17, 6, 7, 11, 19, 5, 6, 11, 13, 25, 11, 14, 26, 13, 14, 17, 19, 22, 26, 21, 22, 25, 26, 29, 30]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [30799378974213, 11008304877835, 30799513585157, 30799362196742, 30825148777989]
def xsM : List Nat := roots_x5_0.map (· &&& dom_x5_0)
def goalM : Nat := goal_all &&& dom_x5_0
def NN : Nat → Nat
  | 5 => 1
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x3d440825
  | 6, 0, 0 => 0xeba6a037
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xaaaaaaaa00000000ffff000000000000ff00ff0000000000f0f0f0f000000000cccccccc0000000055555555
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
  | 0 => 0x73b0000000003ff00000000000003c0ff00000000000330c0c000000000000e383c0000000003fff8c4
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x1534f7b0000000003ff24220000000003c8ff10000000000334d2cd0000000002aeb9bc0000000002acb084
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
  | 0 => checkCutEntry dom_x1_1_x5_0 roots_x1_1_x5_0 5 s ws hint
  | 1 => checkCutEntry dom_x2_0_x5_0 roots_x2_0_x5_0 5 s ws hint
  | 2 => checkCutEntry dom_x3_1_x5_0 roots_x3_1_x5_0 5 s ws hint
  | 3 => checkCutEntry dom_x4_0_x5_0 roots_x4_0_x5_0 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_x5_0 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_0_x5_0 _ hc
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

theorem low_x4_0 : Lower dom_x4_0 roots_x4_0 goal_all 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xf0f00000f0f0, 1, 5)] (by decide +kernel) (by decide +kernel) low_x2_0_x4_0

theorem low_x1_1 : Lower dom_x1_1 roots_x1_1 goal_all 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c0c0c0c0c0c0c0, 2, 6)] (by decide +kernel) (by decide +kernel) low_x1_1_x2_0

theorem low_x4_1 : Lower dom_x4_1 roots_x4_1 goal_all 6 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xaaaa0000aaaa0000, 16, 17)] (by decide +kernel) (by decide +kernel) low_x0_0_x4_1

namespace S_63
def pairsG : List (Nat × Nat) := [(1, 5), (1, 17), (2, 6), (3, 7), (3, 11), (3, 19), (4, 5), (4, 6), (9, 11), (9, 13), (9, 25), (9, 41), (10, 11), (10, 14), (10, 26), (10, 42), (12, 13), (12, 14), (16, 17), (18, 19), (18, 22), (18, 26), (20, 21), (20, 22), (24, 25), (24, 26), (28, 29), (28, 30), (28, 60), (33, 37), (33, 41), (33, 49), (34, 38), (34, 42), (35, 39), (35, 43), (35, 51), (36, 37), (36, 38), (40, 41), (40, 42), (44, 45), (44, 46), (44, 60), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (52, 60), (56, 57), (56, 58), (56, 60)]
def r1sG : List Nat := [1, 1, 2, 3, 3, 3, 4, 4, 9, 9, 9, 9, 10, 10, 10, 10, 12, 12, 16, 18, 18, 18, 20, 20, 24, 24, 28, 28, 28, 33, 33, 33, 34, 34, 35, 35, 35, 36, 36, 40, 40, 44, 44, 44, 48, 50, 50, 50, 52, 52, 52, 56, 56, 56]
def r2sG : List Nat := [5, 17, 6, 7, 11, 19, 5, 6, 11, 13, 25, 41, 11, 14, 26, 42, 13, 14, 17, 19, 22, 26, 21, 22, 25, 26, 29, 30, 60, 37, 41, 49, 38, 42, 39, 43, 51, 37, 38, 41, 42, 45, 46, 60, 49, 51, 54, 58, 53, 54, 60, 57, 58, 60]
def mpG : Nat := 0x3fffffffffffff
def pool6G : List Nat := [55096716822042, 38526697214219, 48421614979882, 48417640023337, 61761781826876, 30830218717702, 55019119381274, 38604006032901, 61796830021180, 38603908187409, 30825148777989, 55096783936006, 48421934990890, 61693063923004, 11034241139979, 55014405573393, 38526698262795, 61796577379644, 61611779556649, 57214001480977, 57214099326469, 55018683172102]
def xsM : List Nat := roots_63.map (· &&& dom_63)
def goalM : Nat := goal_all &&& dom_63
def NN : Nat → Nat
  | 5 => 3
  | 6 => 42
  | 7 => 260
  | 8 => 194
  | 9 => 25
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x85020c742cd226390d373141
  | 6, 0, 0 => 0xf996b1a4f81cd27cefc5d0f2e7ad99bddc2d6e24d070b976cf9b7c3bc6d1583fb337f5deb333ba91b2126421b0008743addbe416a17034afa0acf2db9480177f901291ec8e40ef1e89ffa51f71c796166ae706016312355962e79fe95c3e269b57a33a8f55254641452560404413f2664357648a3b2c665439afdadd3724f1e532fd6c982f95ac532f4cd5152f24641d2a7c48821a14e5e51931a69c0ff9a3c50f896f250e45865c
  | 7, 0, 0 => 0x48e20fe3489da6fe460fba1b45a94192456818c442938fae416ff7343f13b75e3e65d4ab3c8249c83bfcbf53396d428b38dc31f638b7f353365df42435e9d286354b2ed734fab66d34e168ad339b6de1335a55be31ebb49331b11237313c88582c7578892b34637e2a4fd3262a48301e2830a93726bc8e5f2621c4c4238082da22d91c03229cc4da200b758d1fe7aa6f1f77aed01e8de2b11dc391671cc62f361c9454711991eef716cb1ea816b23578168167a415d84d99154673b513d02b00137f022a11fdbf3c0f6f534d0e821ebc0a64e1b90a52d2db076e6ac505df2e75049ecc13047395a20301cfe2028052cc023aafeb012cad0b0119597b0021d7e4
  | 7, 0, 1 => 0x7e7f11787e53ca6f7c1510b67bf9cb407b9792677af94a5e793744fd78f62cda78a6640976e9018375e6de73758bbf567584a59a74f1a12574e65d91749160a27265aaf4725db59871ff901071834b80710bb69670c572a76edeb4586c85336f6c1c94436a9866b66a5b0bf0691bdb3f690ea92868a58ae16721459a665b236e663e751665aaaf1363a3badb62929e14628567a3610e58cd610aec2c5f4644f85e90647f5d152c8b5c5ed6485b3ec2c5599c50055933582b58d5ad6d574e0c8b568d8744564be97b545c29f852c2c0a0527a9afc524d2e2151d3a487512a7daf509d90eb4fd92ea54e2fbf2a4dd3eb7b4d7f10a44b95249a4b21d40f4a201ead
  | 7, 0, 2 => 0xbf7e924ebedd1ea2bed404b1be86e2f4bd35e142bc9ed8cfbc5ad31bbb21b576ba69463fb96ba581b8c78acab7470254b66a2cacb4c5a9cdb3367456b1ac661fb1658437b0945291afafd4d5ae95ef88ae5635d0ad809560ab52976aab3182cea7d633f7a7100fb7a6aa2fe9a4e17db2a39dc7a8a177a9eb9f019ed99e1a06709e028a559cbfde239ac7ad14997db02a985e97bc97ac0d5c94c637029481528992cb4ffc925e59e491a2af88915c8ed690a6ab8e8ebb40d88da868fb8c2028678b438d778a6bcc348a335bae89fdcdad870f3af185d96a0e85802ef484e6e27583eae0e083afd251821087ae810f2d9380e3a7d37f9dc7f17f4b1a627ecc938c
  | 7, 0, 3 => 0xfe99c0fdfe58cd7ffd80606ffd51801efb19c03ef6b6b9a6f5a6fe98f3910cd3f35d0fd4f1d8d8c1f1bf6a05f09756b2ef7d9b99edd59e1fed349631ebab792feab7dde3e9d3d0f4e96e7129e75f1e46e641f93fe5adc7b3e591f1ade3a0da2be191b813e122979adf59f7ecdf198746de72b37eddb68b26dd47e478dd42b95adc39cdc7dc12b551db7ecb46db25fa7ad9069a79d7423459d6c80451d69534b5d6706e01d1eae36ad1b4db32d1475b17d13fdd85d0cdef19d03c767dd018f33dcb7de521cacc77c6cabb024cc9cbe633c9b3fa78c720e726c6ed1e9fc6ab04afc612d2bbc5f6fcb5c3bc0e61c191f704c17693fbc13a5e9ac134a243c1129ee3
  | 7, 0, 4 => 0xffcccbc1ff43dbfdff077c9dfef4ece4
  | 8, 0, 0 => 0x5a0ae59e57b0e66f558dc52654e623cf52119ab95208c53c4df9e3134c0054d3485a3d0145ed68064567dd91451032fa42d860c94169bf9e3ead9e393dee1f1e3c3b8b8b3afd60273ab26e893a13af9c39bed33d393b39313585e373337aa73c32a7cf853098ad6d2e60ed462cbd80802c443a412a85c0a02a00362b27f900ef264929b325ff72af259c2a0f2577635b22fd0d35225215781f436bd71b3d035d1924335718da718b18baefd2187a7d1a1663beb0161b97911519c81514fdf20f13cffff70e8587a80e17cc080ddeb3e00cfe6b7a0cfa623d0c634b1b0ba5ce290b00d3fd0a97cb490a8e8a9e088d6a6008729adb0156e3cc00b35b79003e590a
  | 8, 0, 1 => 0xa3631f52a2621fdea1c9b5faa0da99e1a03173099cebbd729bcc1aa59a11c9cc99e4c213968d45fc958b46a5957361ca9516af759429b7b29423a0089368ebeb907a592f9076ec8e8f879c588f44884c8eb2455a889f588d887437e587bee8ad859a3bc08564e97e8502b0a58464689c8452243183c82a5a82a2633b8274e04182614b1881e69b5e81dbc0a3817d9b1b80437db27e5cbf637e4f26f97d9bbf8c7d1d106e7a8dd4717a76d4d47722f8037719515175f051ad75d92e797528ba1e7456cb0e7445e99a721c2af07210a91f708c63d870229cb06fa9935468b1633665ee3ccc65c9f486644d690f63076e4362f517fd6240cbab60a888ba5a65cb09
  | 8, 0, 2 => 0xfcf7b91ffa387828f7d62721f6dd2951f6170511f33eef32f18f68c8f0a0a2a5f07e9f45ebc6d37deb06ecc3eafcd651ea8db5d8e884a584e6b302b6e2a274b8e132e63de00052f3de77c545ddc23632dbd5ffcbda4a82d1da390d57d616304bd48a317dd01622edd003ae56ce520fbcce04edffcdd388e6cd8606d2ca9fc081ca003fb8c9bceffdc8e9b08cc5c5f159c3ed52ebc367c876c32100e9c1ca8ac0c10eafeac012abf0bfdd512fbd1acaecbd14695dbc542854bb8c28c9bad0a275baaf8dd9b99f5c10b6283af4b5456a70b31bd2b3b0b45387b07b2df5b0154e27ab65cba2aa45b81fa8a3455fa7dca2c7a65501e5a62afc61a552ded5a3ff5d94
  | 8, 0, 3 => 0xff9b47ebfd53a92a
  | 9, 0, 0 => 0xff82234ffa0bc0e3f531f1bbe5943b56df814e89d36b5df6d2cf1fb4c97dca2ec4f74707bf935932beb088aeb4d0e9e0b20e639db147c105afaf7e14a494ba809ff8643a981d639891df562357650151556b73113a03cbab2f07484d17f0a5e609b68333
  | 10, 0, 0 => 0xeeff5994
  | _, _, _ => 0
def dictB : Nat → Nat
  | 0 => 0xc0c0c0c0c0c0c0c00303030303030303f0f0f0f0f0f0f0f0fffff0f0fffff0f0f0f00000f0f0000000000000ffffffff0f0f0f0f0f0f0f0f0000ffff0000fffff0f00f0ff0f00f0faaaaaaaaaaaaaaaa3333333333333333ffffffff00000000ffff0000ffff0000ff00ff00ff00ff00c3c3c3c3c3c3c3c35555555555555555
  | 1 => 0xfafafafafafafafaeeeeeeeeeeeeeeeef0f0ffff00000000ffffffffffff0000ffff000000000000ffffffff0f0f000000ff00ff33ff33ffff00ff00cc00cc00ffffffffcccccccccccccccc00000000ffffffffcccc0000ffffccccffffcccccccc0000cccc0000ccccccccccccccccc0c0ffffc0c0fffffcfcfcfcfcfcfcfc
  | 2 => 0x505555505055555ffaa0000eeaa00001111111155555555cccc3333cccc33331515151515151515f0f0fffff0f0ffff0000f0f00000f0f000000f0f00000f0ffafaaaaafafaaaaaeeeeeeeeaaaaaaaac8c8c8c8c8c8c8c8fafa0000fafa000000ff11ff00ff11fffe00fe00fe00fe0001ff01ff01ff01ffffffffffc8c8c8c8
  | 3 => 0x505050505050505ccccffffccccfffffcfcfcfcccccccccfcfcccccfcfcccccfffffffff0f0f0f00f0f0f0f000000000f0f00000f0f00000c0c0c0c0c0c0c0cfcfcfcfcf0f0f0f0fcfcf0f0fcfcf0f0ffffffffc0c0c0c0ffffc0c0ffffc0c0fcfc0000fcfc0000f0f0f0f00000000033330000333300003030303030303030
  | 4 => 0x555500005555ffffaaaaffffaaaafffffffffafafafafafafafa00000000fefefefefafafafafafafafac8c8c8c8fefefafafefefafaeeeeaaaaeeeeaaaafafac8c8fafac8c8fefefefe00000000fffffafafffffafaff00ee00ff00ee00fefefefefefefefefefe0000fefe00001111111111111111eeee0000eeee0000
  | 5 => 0xababababababababffffaaaaaaaaaaaa0000ffff00000000aaaaffffaaaaffff0000333300003333fffff0f0ffff0000fafafafaaaaaaaaabbbbaaaabbbbaaaaffff3030ffff3030babababababababa0f0f0f0f0a0a0a0affffffffaaaaaaaaf0f0f5f5f0f0f5f50f0f0a0a0f0f0a0aeaeaeaeaeaeaeaeafcfca8a8fcfca8a8
  | 6 => 0xccccfcfcccccfcfcf0f0fcfcf0f0fcfc05050505555555550f0f0f0f0f0f00000000cccc0000ccccffff0f0fffff0000afafafafaaaaaaaaafafaaaaafafaaaaffffccccffff0000ff000000cc000000fff0fff0fcf0fcf0ffaaffaaeeaaeeaa111155551111555500003f3f00003f3fffffeaeaffffeaeafefeaaaafefeaaaa
  | 7 => 0xfffff0f0f0f0f0f0ffffccccccccccccffff0000f0f00000ffff0000cccc0000fffffcfcfffffcfcffff0000aaaa0000f0f0a0a0f0f0a0a0cccc8888cccc8888ffffeeeeffffeeeef0f0fffff0f0f0f0ccccffffccccccccffffffff0000ffffffffffff0000f0f0
  | _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x101070c1542020218428406080805
  | 6, 0, 0 => 0x340c11200258182001448a62e08b06122182031a483236080869256218004041c9065044800910298b83045800960434005102982031a48321608b8c0d241982034435286608301270c158004060808650808005122182032418499608886920c218b8304983096080869222018202203c008608087861c218b83043432d62e0c11f1a99820c0490305608501130025820d2418c886400c11f1a798203043c00e608609061221811d1a182886080c6920065820254182a96
  | 6, 0, 1 => 0x80cc120025820c044832f608085860aa182031a783196083010b0015811d1a480086041828910298e1b04480096001010d58194a8304480096
  | 7, 0, 0 => 0x80c1120c267b8008606920c21824e060880f0ce1016e1a4830870008e8d2418435408089061221c00404a890652c101821a182cf709381120c244383047c9061229c20304a86860ae541823e349067093810d0c144380386c1120c25820304349001ce1018225a430970608f8d0c145384049c6920c21c203049890612e101101a783087080890612235b8404483097421c20305286920ce1010d7c48008708301822419fb84060a4120c25c004066069200c101821a4832d7005418224184b0428089061221c01a060890612c101821a483557
  | 7, 0, 1 => 0x80c112d0184b80080cc120c258203043400512e10182a034906708086be0c1443840436e060a21c203043400560e0020c04909066093810d2419cb849c0c1060a25c20c9c0890612e101822400488708086860a214b80085010d26018202203490010e1064e04343057080c10d7c4803849c0890612e5c2021a4830e10e1010d24580087080c10d00144384060938d0c15c203c8606920ce1010d64480087080b98d24184380083010b0c158e1b047c6920ce0c10d2419f8a7080cc0d2418cb80085010d801982021a4800910e1270304368927
  | 7, 0, 2 => 0x381018224004b8404343051221c00c042c90614c1228304343057080c1120c27638008086800a2182021a182b010e1011e24184887001018d2418cb040660f8d2419c203044090012e101821a480397080c1122c004b840434f060a21c20c060890012e101827a349007080c10d241b1b84060880d0015c2021a4878010e106030434005708086920d0443840608692d019c203044800972e101821ac8005708086860a22db84066330d2419c2023e34f1210e1350304483097005c1821a983304060a58d2419c202863490610e106023e909067
  | 7, 0, 3 => 0x6086920024538008501130c2582030448309a4e101102418488708089061222eb84066c1120025c202245830910e101820c144887080c1531a48338404f46920c21c202203430510e10182c034906708086860a22ebce06089061229c20336086800ae002034434906600106024e48330418086860a21c2030436e060ae101826c7c9067080c1120024538404359060a21e703043430514eec20304480097080c11f1a792b80080c1101e0181824e3490614e00203043c30e6080c1431a9433848a0c1120c25c004044800910c101821a182a87
  | 7, 0, 4 => 0x80c10db0182b97080c1120025c203043430572e0010d240040a608301820c144b802e0c10d2c01825706086860ae10d821a182887085011f1a4c338008086922219810d3c4830814e101820c144b9708089061220538304406920029c004043689210cec20224184887080868b240043840608692be19c004044078610c12f0304483097001018200144b1c08089061221c2030434906a4e101821a7893f709781821a182b8405646920c21e68305306920ce1010d2400288708301823e7893840688f8d2419c20304cc69200e701821ac89007
  | 7, 0, 5 => 0xc112002453048a0920d2419c20304cc6860ae101821b003057080c1471a4833802a0c10d24018b84044830910e1011f1a182887093812a1a48338006086800a2982021bbc90610e00b821a58308600101421a483304060a48d2419c2021b4490610e01a830434900606089061220538404349130021c0710434906bac101821b58305704406920c2053840608692b019c1821a1828814e101821a2c0057080950d2400438406089000a25c004041828910c002021a483626080c1591a182b84060890012e1c21404a86920ce086920c2440a7
  | 7, 0, 6 => 0x5410d241843040794c0d2419c21406086800ae002033034f06600086860a205304060950d2401c2030434906dae10182244c0097080c1361a48038404349067e21c25a06086860ae01a821a483086380c1591a48338c06089061229c01c360869200c00203043492b608086f22418438404345860a21c603043430514e0c1120c25c8a70011a021a48030406086920cbdd003047c6920ce101120c14488700ec182644803040609e0d2401c203043689256e038021a483086080a11f1a483384c20c10da249c2023e4830910e101120c25c087
  | 7, 0, 7 => 0x80c1241a182b840608f8d4c49c20c06085860ae1010d0c158887085010d0c14438406089061355c203043490656e08f8d241840a7080c11f1b20938406086860afdcb83047c6960cf5018224184ba7060a31f1a483384180c11f0c15c203043490062e0020c042c9006080c1120025d384ce0c1120c25c2021a9890610e1012a1a182887001010d7c1b5b0076099120c218202783490610e0c10d164800a7085018224004b840608f860a25c20304dc69200e001120c2440a608086c82418438406086800ac5c0170608b0612c002021a4c35b6
  | 7, 0, 8 => 0x101c41a48330008085920ca18003041828914c101371a483087
  | 8, 0, 0 => 0x101825434906700127021a4830870010182244c309700101826c349067000c11f1a4830a79a101823e3490680000e1b04349066093818220349068080c11f4834906800101821a98906700002340434906609381821a48b068080c11f9834906809381821ac890680001d8304c89066001018278349067001010d241846b70000182241848a600101824834906700101821b2090670010603042c9067a8101821a483098080c11f1a4833f80000a830434906609381821a4830980010a021a483087080c11f1a483058080c11f1a49286800001821a1828a600101821a4833f70001a83043490662e101823e349068
  | 8, 0, 1 => 0x10a0304349867080c1101a48308800101821a480097001010d7c483087001010d25703087000020330349066015020304483097001270304483097001010d24184297001270304343057001064e0434906708501823e34906800101821a48008700101824e34906701c42021a48308700101822034f06700101821a483317080c10d3c483088000020c042c9066080c11f1a489868001018224184ba709381821a4878680013c030434906709381821a4ba868000c10d164830a70010a030448309700101826e34906700101821a182b1700101821a4834f70010a030434305700106140434906701502021a483087
  | 8, 0, 2 => 0x101821a18288700101821a48341700106021a48308700101821a4ae067001010d6448308701381821a4830a7005c2030434f06700101823e34f12709141823e34906800101828634906700101821a4800a7080c10d3d00906808301822034906800ec2030434900700101821a483287001010d2418488708301821a48b06838101821a483098a8101821a2c906800122830434906700002021a48008609381821a2c9068007020304349007001010d3c48308709381821a48305800101822034900700101821a4830e700101821a48b00700501821a4830a700106030434900700101821ac8900708301821a789068
  | 8, 0, 3 => 0x1010d243c3087080c10d24182888001060304343057001018224184b9700101821ac83057080c11f1a4830880013a0304349067001010d241840a70013d830434906700002030448009600ec2021a48308709381821a48986800101821a18289709381821bd89068080c110663490680012f030434906700002030434005600101821a182b0700101821a4835b700702021a48308700101823c48309700101821a783057001018224184887000021404349866080c1433e34906800101101a483087001010d241845d7001019b0434900700101821af8906700101821a487807001010d245830870013e0304349067
  | 8, 0, 4 => 0x1019b0448309738101823e34906800001821a4800a6005c2021a483087001019b04343057001061b043490670010a030434f06708301821a483058000c10d3c4830a70010182241848a7080c1103e349068080c11f1a48b06800002030436892608301823e34906800ec20304483097000c10d241840a700101821a2c90070000203044078660000202241848860070203044830970010182b234906700101fa0434906700101821a48005700002021a18288600101822048309700101821a48339700101822458309700106030448309700101827a349067005c203043490070010182203430570010d821a483087
  | 8, 0, 5 => 0x101f90434906700101821a2c305700ec19b04349067001012a1a483087001018224182897001338304349067007019b0434906700101823e483097001018224184b87005c203044830970011a03043490670010a030434900700101823e343057000010d241840a60000b830434b06600101821b4490670012d030434906700101821a489807080cd823e349068000c1101a4830a700101f704349067001010d1648308700301821a4830a7000020304182896080c11f1a4830a8001010d2418288776101823e34906800101826634906700101821b00906700701821ac89067000c10d241848a7001011f1a483087
  | 8, 0, 6 => 0x1010d244c30870010603047c9067
  | 9, 0, 0 => 0x101821a483057080c11f1a483397080c10d2419c004060890612c0020304343056080cd821a48338406086921e19c203043490614eec20304349067001010d2418431c080c10d2419c20304406920ce101821a48b06708301821a48338406086b22419c203043490612e0020304349006080c10d3c48338406086920c21ea0406086920ce127030434906708501821a48338406086922619c003043490614c101821a2c9067
  | 10, 0, 0 => 0x20304349066
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 39
  | 6 => 46
  | 7 => 53
  | 8 => 60
  | 9 => 53
  | 10 => 46
  | _ => 0
def stateM : Nat → Nat
  | 5 => 0x7fffffffff
  | 6 => 0x3fffffffffff
  | 7 => 0x1fffffffffffff
  | 8 => 0xfffffffffffffff
  | 9 => 0x1fffffffffffff
  | 10 => 0x3fffffffffff
  | _ => 0
def wireAt (i : Nat) : Nat := (dictB (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def dictP1B : Nat → Nat
  | 0 => 0x381180e3040f0300070e601cc300c0003ffe601fff00c0000700001cc00000000000001fffffff0038f19fe33cff3f00000fffe003ffff0007019ffcc0ff3f0000001ce0000f3b003f1fe0ffc70fc3003fffffe0000000003ff0001ffc000000380f801f03ff0000381180e3040f03003fffe31ffff0c4
  | 1 => 0x70e7cfcc30ffb0000e01fe038ff3f00070fffe0000000003ffffffffc0000003ff00000000000003fffffe33c00000007f07fffff0fff00380f800000f000003fffffe038f03c0000e01f00000000003fffffe0380000003ff01f1ffcf03c0000e000003800000000e01f0038f03c00000fffe003ffff0007ee7f1cfbf0fc
  | 2 => 0x38ffe3033ff0c40038000000000000003f1fe01ffff0c40000efe0e03b0fc3003fffe31ffff0c400070ffffcc3ffff00000e60000300c00000019fe000ff3f0007001cfcc00f3b0000e01fe0000f3b0000001c00000038000700001cc000000007ffffe0ff00ff00000e001c03ff00003ff1ffe3fc00ff003fffffe0000038
  | 3 => 0x38f183033cf0040000efffe03bffff0007ee7f0038f03c0007e01f1cf8f03c003ffffffcc300c00038f19fe00000000038f000033c00000000e01f0038f03c0007ee7f1cc300c00007ee601cfb00c0003fffffe0000000003ff0001ffc00000007e0001cf8000000070e6000000000003f10001fc4000000070e601cc300c0
  | 4 => 0xfe30003f0c4003ff01cfffc0f3b003ffffffcc30ffb00070e7ce00000000007ee7ffcc30ffb00070e7ce00000380007ee7cfcfb0ffb0000e01ce0380f3b0007001c1cc000380007ee7fe0000000003ffe7cffff0ffb003800001f00ff000007ee7ffcfbffff0007e0001cf80000003f1fe01fc700c00000e00000380000
  | 5 => 0x38119ce3040f3b003ff01ce0000f3b00000fffe000000000000fffe003ffff00000fe0e0030fc3003ffe601ffc000000070e7ce0000f3b003f101cffc40f3b003ffe601fff00c000070e7cfcc30ffb0038f19fe0000f3b003fffffe0000f3b00070fe31cc3f0c40038f01ce33c0f3b0000001ce0000f3b0007e01c1cf80038
  | 6 => 0xee7f003bf0fc00070e7f1cc3f0fc0038f1831ffff0c40038f19fe33c00000000001f0000f03c003ff19ffffc00000038f19fe0000f3b0038f01ce33c0f3b003ff01f1ffc00000038000000000000003f0fe01cc3f0c000380f9ce000ff3b003f1fe31fc7f0c400000fffe003ffff003ff01cfffc0f3b0007e01cfcf80f3b
  | 7 => 0x3ffe601cc300c0003ff01f0038f03c003ff0001cc00000003ff00000380000003ffe7f1ffff0fc003ff00000000000000700001cc000000000e01c00380038003ff01ffffcff3f00070ffffcc300c00000efffe038f03c003fffffe003ffff003fffffe00300c0
  | _ => 0
def dictP2B : Nat → Nat
  | 0 => 0x244450892208c00081080c1040c0200274e653cd322cd003ffe75bfff66ef002748001cd00000000000000fff77ff0018b19ac32cdd32000007ef6003bbdd0027498a5cd09910000932bce54d1f7b002d1aa0f5450e43003ffffff0008800003ff8109ffc4422003c8f8a5f23ff10000a54c5c9962c8e0036cd431ab2e084
  | 1 => 0x2f7efdfddf3fff001bf7ffefffffff00274fef70008800003ffffffffccc22003ff81090000000003ffffff32ccc2200037075a5dd06ef003c8f8a5a22f910003ffffffabaf9bc0012e55f00008000003ffffffab8c820003ffd5f9ffef5be0012e0100ab840200012e55f0abaf1bc000247ef6893bbdd0037ef7f3efbf3fd
  | 2 => 0x1085430222e084003db8109f6c4422002408001ab260840012e2b06ab94a61003489021220c00000274fef7cd3bbdd00000665200322cd0000018a40009910002f7abcfddd1f7b001bf7ffe54d9f7b0002645d089a31bc002f78109ddc042200037075a0dc00ef003c8f8a5f23ff1000037075a0dc00ef003ffffff89ab9bc
  | 3 => 0x1081020220c0000012e7ff6abbfbfd0037ef7f3abaf1bc0037ed5f1efaf1bc003ffffffcd3aacd0018b19ac00088000018b010832c44220010a11a0228d1300037ef7f3cd3a2cd0037ee753efb62ed003ffffff892a88c003ffc559ffe64ae0037e8101ef8402000274e6530000000002d18009544040200250a2034410241
  | 4 => 0x5430002a084003ffabcfffd5f7b003ffffffddfbfff002f7efdf0000800003ffffffddfbfff002f7efdf89a39bc003ffefdffff7fff001bf2bceffd5f7b002f7c5d9dde35be003ffffff0008800003ffefdffff7fff003c8f8a5f23ff10003fffffffffffff003ff8109ffc44220024080010000000001bf0108ffc4422
  | 5 => 0x932bce54d1f7b003ffabcf54d1f7b000007ef60008800000937ffe54fbfff000002a060010a41003ffe75bffc4422002f7efdf54d1f7b002d3abcf54d1f7b003ffa30bffd4663002d3abcf54d1f7b0018b19ac10c9d32003ffffff54d9f7b00274f673cd3a2cd0018b098c32c5d32000b76fdeddf3fff0037ea3c3ef95379
  | 6 => 0x12e77f2abbf3fd00274f6f3cd3b3dd001081020ab2e0840018b19ac32ccc220000054f0002b19c003ff99adffccc220019b3bee54d9f7b0019b2bce76d5f7b003ffd5f9ffcc422003c88001a204000003fcfef7ef3fbdd003dbfbeff6fff7b00240d431002a084000003aa60019b51003ffefdffff7fff003ffabcfffd5f7b
  | 7 => 0x3ffe75bcd322cd003ffd5f9abaf1bc003ff8109cd00000003ff8109ab84020003fff7fbffff7ff003ff810954c042200274a243cd102490012e01c0ab85138003fffffffffffff00274fef7cd3aacd0012e7ff6abaf9bc003ffffff003bbdd003ffffff003aacd
  | _ => 0
def p1At (i : Nat) : Nat := (dictP1B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def p2At (i : Nat) : Nat := (dictP2B (i / 16) >>> (64 * (i % 16))) &&& 0xffffffffffffffff
def wireDAt (i : Nat) : Nat × Nat × Nat := if i < 125 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool := (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
theorem wireD_ok_all : ∀ i, 0 ≤ i → i < 125 → wireDOK i = true := span_ok (by decide +kernel : span wireDOK 125 0 = true)
theorem wireDAt_eq (i : Nat) : wireDAt i = (let w := if i < 125 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt; split
  · next hi => have h := wireD_ok_all i (Nat.zero_le i) hi; simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h; simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 125 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => [] | n + 1, ids => wireDAt (ids &&& 0x7f) :: stateWiresD n (ids >>> 7)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => [] | n + 1, ids => wireSAt (ids &&& 0x7f) :: stateWiresS n (ids >>> 7)
def SD (s j : Nat) : List (Nat × Nat × Nat) := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat := let packed := (stateB s (j / 512) (j / 32 % 16) >>> (stateW s * (j % 32))) &&& stateM s; stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) : stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with | zero => rfl | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) : SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := stateWiresD_eq _ _
def htAt (s i : Nat) : Nat := (HT s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def idxH (s h : Nat) : Nat := bsr (htAt s) h 10 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 5 => 6
  | 6 => 344
  | 7 => 1787
  | 8 => 521
  | _ => 0
def CH : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0xe38c0815dc294230c278d6478c9238d2852f72ed1972a58a
  | 6, 0, 0 => 0x2c4d82672bf31c342a7f87ff276c990d273f7a3d25b941fa258a6b4825525106248b8add235eb59a22d9887b2125dab4210d717520e112351fc22f391fa6552d1f77aed01f436bd71d81b2001ca4dc581bff8b661a93503f1a506dfc1993e41f196a98f81901d3c918baefd217e715cb16960b7615ea84811568e7f41519c81514b92f601483b5a313f386d5139e13b8135968a4131eb9cf1305f67711dcb9d01096048b0f3345910e8587a80d96cb910d6112240d467bd70cf309aa0ce4df950bb749890bb6ff020ba5ce290b7a0cb10b1c2d5e0a8477b908729adb065a428e063405ac041b80ce041746cc017ff6500119597b00ec586900b35b79006d0574
  | 6, 0, 1 => 0x5cf59dae5bbb2d5a5b8875b55b8587ee5b6fc5625a382f915a1f8cbf59da8e1058486b775710a096555e67e854e4c26e54e418085419179c52fce94052f0d7115208c53c51e628db518b86fb4f3b7e804f1259744ee3af324e7868144e17a39e4c7ca8eb4c3ad5604be8775f4b8e112c4b53332a49c815a3475f4bae47078e05455436f243829424437d690642c682d042747d7341b4b8004108e09f40a8666d40515020400decbb3f65a4273f5eeb863f414a253ab26e89391f9bf3389cc8c137820ac3377cc46f3730eb08367726293653a2e9364d97753549cd7635492310341eaa9b337924813355e2193338f6da31dc878731a42c922feeaa242f97ee34
  | 6, 0, 2 => 0x9389b30892d7717d920d279191fe7def916f132a91626b0491176c51907a592f8ee476b68da868fb8cf73e0b8c1f05208ba0e1ad8937811389076c5488f33ba687bee8ad8781b0d1866a38fe854c032884fac2a2843d4abd83fe411383d53fe482fb2daa82e04ed98276561f7e2a5df07e06d7367d1bd0f67cb46f517c97f9977c4c689b7c12fd457acfdd24797837fc78f1b93577d88f1e75e9aec375dcc7ad75d305db7265aaf4718ef35071267bf3708c63d870124a406fe8078f6f839a9b6f67c9956f5390286e135d0c699c8c1b690c058a68755f976763375266cf440666c1b1d0667ce951657e8ba965422c4964e47d6d61a93fa55ef9e07e5cfe5c60
  | 6, 0, 3 => 0xbe733d0cbe32d514bdfc7b32bdbb5a85bd14695dbc032673bbe9b7b7bbe0b750bb7d825fbb4fa636bb2df6b5ba876de5ba35ef6db9a7e94bb99f5c10b826d8c6b7676172b7634d28b699b54db694c7b0b66a2cacb6283af4b50533e8b3e0cc85b3b9c050b35c1024b324a800b213ebf9b0c5d667b0887c4cb0154e27af62fb40af386337af37411eaf27801baea7dca6ae66cea4ad20cdc4a9c40857a9b61836a84147e1a81c77bea74516c1a54e670aa2b9bd2ba22e5b14a10b9c7ea031c9ca9ef2a2ff9e546ba79d947ed49d2e78f39c15311c9be75d939b765f749b4417a99afa3f049aec78ed996fed76977557d1968d45fc95a236e2956372a79453fcf4
  | 6, 0, 4 => 0xf2bca4e0f2a546caf19b4e70f0fdf766f06e0b5af00cc204ed9d3194ed49ea9de9933066e884a584e6be3ee3e6b302b6e5da0f16e48e7a1be471344ae35d11bce123f52ee0dc832adfc72249de9ccdc6de3999fbde020c15dda94fdcdc5d5e17dbc86b69dba80337daea1147d9e1aea9d975484fd8a05aa0d7b59905d702566ad6fe4220d62fbca8d616304bd5358fe9d3cec1dcd3b36f06d16defffd0d31662cf568aebce023c9ccdd2ca04cd5bf546ccbbc2bccc8a5d3ecc432444c9de6a87c8e9b08cc7dc3cd9c77c1db7c7490879c6add4ffc56bd83cc4ded543c2b26c1bc1c9500cc1890036c140e382c0be6b72c09ae832c048dc3ac00c74bfbf8c5b38
  | 6, 0, 5 => 0xffdcb9d8ffb85fd6ff90c3a5ff762a73fe781b4afde6bd08fd03388efb066caefaf85b47fab57904fa080caff9e92deff97ca3a1f97bcfd0f94a054cf90a3f8ff8990990f774f70ef47a20d8f4727dd0f3e318a7f383c4d7f369b6d4f33fe497
  | 7, 0, 0 => 0xa7d15dd0a3a0d4009eade4f09e33ae009d62c9209c68f8a09b6833309aab2f0099dcefe0988b3e10984a56c0934680908f19f4508930434083d26bf08344ae408102014080465a607e4ce4507c7a31e07c54ddf07a58cff07a2cd180783f7450774f847073fc36a0715498d067c0c5b066e56cc066c22b5066a42820642ce0505e991b905c2b37a0578a07d0508e7ca04afa52d0456044b0451f4ec043dfd4e041cb05b03fad7f6038502980367149d030aa55f02f807ca02e7c1df02917d280206ca5101fec3c701f41ef501ec392301e8a27c014e30ba011d6dc000f72f1500d9f06100c19d7300b994f0006a3524004c7978004157d0001f71bf0019b8c6
  | 7, 0, 1 => 0x143c0d0f142db03814281eeb13cffff713bdf119138cc5f61330fd7012f686ef12bca7f612b8e9bc12b5664212a4430011f38f3b11a07b4e1186f8741143415d1139848a10eb0ca710d68feb108067cb1054652a1045a0e010319ca8102d7a0f102cb7d21027983a0ff627ad0fe17bff0f97b7810f686dc40f61488e0f3a80ac0ef0b7720eddf50b0ebd8d6a0e8a642f0e17cc080e1752730ddeb3e00dda8feb0dd83aac0dc548f10da59a5d0da542800da3dff10d7f1b960d79d9290d77f8140d32c3940ce459350c8fb1910c65ac0d0c4e5f240c3d2c8d0c342bf10c2a12020c011c820ba6a5e00ba5ce290b8d8e810b5757610aeba37c0aba4c6d0a9e9508
  | 7, 0, 2 => 0x1f42fa661f12a9411f0851631e3f932a1e3b52531e00b8781dfbc0ce1df9c4691db5c7de1d8beab91d8428691d06cf9b1cf843df1cc486e21c93a5081c62eaa01c41bc801c1ae5b41c1928291c0fc7181be52b2a1ba8047d1b801a1c1b5afefa1b50e8881b1a0aea1aea5eef1ae1c80f1ad080241ad066b31ac4c55a1a47855b19aa6ddc199bfe51196feb971956825f192439d718ea819418baefd218b78a3f18b72fcd187af5e4180ab88d1808ead417f0a5e617b8277b1798c2df1778fdec1745ae291730672f170efe2f16ef033316b5dda1168afa601686c783164ffdd3161e1f0415c726f3157fe1d11517cf4514fdf20f14b81fcf146c2e60145087b6
  | 7, 0, 3 => 0x288fdb3d288c943d28736fa128478b4b282f2c93281c5a6927f5011927ccd79227ab150c2794d84c2786f5df27495f9627313b8826e0e8d5269e5e7d268d093a26724f63266b17482667fbbc264d5b9c264af0f7264929b3264239f425ecb53025c3e2462577635b248e04d6244e3f2023e8cd4d23d1667b23b2424023a54ab82393016923891cfe236342d823619af9235c143d234f190923317b5a2309b3c522db09d522d5b73622a43a05228f58152222b3e5221d02bd220bcbbd21f9f50f21f55e4921e2144c21c6d875215c89d7213c2611210b6317210b522120f4b4dc20ea3d8520dac52720d2b17c20792b7d20549af6204966a31ff2d60f1fda0bbc
  | 7, 0, 4 => 0x337ffdba3333a5b832e0981432dfa60432d0d1a432c778e432917f31327a00333276a5c131aaf603314e2aac30da702d30cf69a7305858cb303aef642fef5a222fc771ae2fad58322f57d36e2f55ca092f48319f2f32ac792f2f932e2f2460382f092b4e2f07484d2efc3d862eb7a8982e8bac6a2e6269bb2e2baaa82dbd9e352da7bb612da66f232d9337d72d4bcb562cd24e8c2cbd80802c8735d62c581c0f2c00a1052be9541c2b86df172b3412562abf42042a8c8a5f2a5541652a4104882a2802972a180ad529fbba1a29d1891029a27822299e0a8b2998e5e02971218a295bb095293cb1472923a8d928f8e9ee28e8a40328cf5d0128bf480928b6f452
  | 7, 0, 5 => 0x3e32c6173dd6474b3dbb4e813d96b5c63d6029903d5dec943d527db13d3afab93d2d59613d26dfb13d1efc8a3d0a83a13cce35373cc14c493c820d253c50dff73c469f8f3c3b8b8b3c071d803bc809173b2c329f3aeca3da3aebdd803a57bf6c3a3cef333a03cbab39d0e21b39bf504639bed33d3998633338bf2ecf385294e03845fc4938447118383b36073822516937a3dfcc378f7ea93713f2e436ebeecb36bb486a3677c0e43674c99e3650d299364de9bc35d88b5c35b51c4a3585e3733527aa6e349ec51a3498b9d5348cbf683447de1e343f9dab341901f5340e389233e9fbbb33db294933d719ea33c313e333c0b67e33b3de4c33abe670339a3b98
  | 7, 0, 6 => 0x490f020948dd246448ae4aba485a3d0147f18e7a47d7c521476d95e94760553447475e204721ead7471b5dfb470d89b446571df2463e8005463b029f461d0bc14613374e45e9308645c8e5324595c52745736df5455204464510997344fb624244ca310c4461f6914424122e44130e1a43fce5de43f56eff43e93418433c00594329f17b432411f64307b1bf42d860c94252923d42429ea4422a4d0d421a0a4d4210af7741bcd38a41a8e6a141a654454169bf9e415a9292412e27994122ba3f40ef18be4085327d4073bd03400204ed3fab50003f98b8343f7813d53f3a50ce3eef1ec33eeb63b83ead9e393e86703c3e7bd8083e6ca6e33e6bde3f3e60a773
  | 7, 0, 7 => 0x51419c6f513785fd5132c30b50f578d050ee023f50ea4d4150ddfc5f50c8658450ac32a4505623894ff34dc34fe855494fe12bdb4fc489724f9eecaf4f842a294f7e558c4f7203ae4f248afd4f20a1d04ed455d94ed03f254ebf55304ead78f44ea461854e9b175b4e8d76614e79a1c14e5d34534e505f124e4f9ac64e1a14854dabf7304d27355a4d1149304d0aebe04cedb2624cd6a0334cc5254b4c72cffd4c6a0abf4c6848c84c63ca1a4c620f5f4c4f72774bd749734badbce24b1404df4b139a5d4ad562814a5a36fc4a58dad34a26ab4a4a06002c49ff50a149dbf98049d9330449d5ca7749c6ea2f498bffe2493931a44933dad8492e83c24920cbe2
  | 7, 0, 8 => 0x5c5824aa5c51b4bd5c4f96145c1e1ec75be653d35bbfe3525b155d0b5ad9d2d75a54486259f2b46459840b3759799ede58fe5e6758d1b3c858b8c81958ad2426584d1326583b5d635824cb315823f8cb5802866957ed89d857ca187457650151573d6a7c572a73a156f4e56256db525156d49f9d56b94ef156aeea8756aaa9b0569d3bea5692d977565384e655f03c4655e8deb455cb759255cae882558dc526556b731155338e9d54e623cf54907169548c8e8e54634bdf53ca8d5d53b3f6ed5389633853563928533494dc531c369552d7ee7c52b535335299fdbb526d9a5752626ddc5214f52b52119ab95201832951f8cbd351ea3640518dc5f4518b2c61
  | 7, 0, 9 => 0x65d5f79765bab452659010486583ba7e6567bbad6552782e6541a5e964fe300964e1132b64ae805d642e1f796414dd5964059ff763d7296f63d3a282639797ea638e58d6638aaafd636de205636ac6bb635eceb863519efa63398a67633268cb632e3b85631867646312074d62b01f8f628b8ef7627f654662250a8b6218426461a4319a617d01fd613cf91d6110af9660ecbfa4607327d4602b88496002d9b35ece265e5eb4ff7d5e9b93905e57bee95e45feae5e26ca935e2165345e10d6cd5da4c1f05d84ab1d5d7af3195d4be1eb5d4a14835d481a365d3eb22d5d34488c5d277d895d1b4eb85d17d8fd5d14d5085d1192b75d0b44be5cd1a90b5c984c78
  | 7, 0, 10 => 0x6f39e1a76f2fcc576f2a9fc76f01b0706eb456616ead4a876e7f23a66e7c85646e46f12e6e4231556e2bfd176e2473a76e199e9b6e0b865c6ddf3ab76db5097d6db1a7736d5105186d22ccfb6d1aad046d0f27876c9db3576c8f9dc26c5800166c3a35996c2d4cab6c224c846c1dede56c033dc06bee0d876bcd41946b96a74b6b184a996b0680c06af8c9c96a482c536a12e57469a01f2c6998a8f26970bf6f6961df276926f4da6924f41a68d45be968d4269c68ce16f36848325867cc4dea679eea8b67919378678c837267239c6367160b2466ee0b2566e89ded66a87eac667246a26663a4d166450eaa663a15a6662748cc66028f3465d9f5aa65d974fd
  | 7, 0, 11 => 0x786e7c7b78635000784f9aff7815d74f780bc8f677db7f2f77c63d63779ff703778f7713774a58f576eb2f6576d85f74768deb3976892af076459ea876417a3d762e200476261010760532dd75d6d40b75bbefc87528ba1e74cbb07774c037547497834b747c99587473fbda74527bb4744a1f4f7442d8ba741a0b8f7419638c7405513173b882b473a1ec4473726f357365b971733b925573391b267334830e7330cfda732c730073245830731f1b4c726890537264ac3e725b8fae72502a2b7210a91f7207ba907202ea8271e07dd571bdd1d571964d6f7193c0cb71782f1b715a035970de390770d27af57088f737706ff8f57017b43d6ff61c576f834a41
  | 7, 0, 12 => 0x82b9f4a58274e041826ea14c8265acf082614b18825cd773821de44181fb573f81c99ac581969e81817d9b1b8143ad5c8039a60c801675d58000a0997ff396887fc67d417f1a2a947f1521377efdf8a57ef59f7e7ec6754f7eb7710b7eb1e7da7e9278507e7303227e4df54a7e25ad557e0f5a8b7dee6bfc7dc1bf8b7d99aff67d68e8707d5834587d3809da7d2b55c57cf4d2817ce6d6e37ce30f2e7cd4a9257ccf3d847c9e74ce7c54670a7c24d5ec7c0af7747be9c0d87ba2da817b98cb277b8148cb7b5477c17b38a1bb7b3824cc7aaa70187a8dd4717a76d4d47a5d0c1c7a31903a7a0aafa379c7315379b4d911797f979a7952e83378f583f878ae4f38
  | 7, 0, 13 => 0x8caf50f58ca960d08c9d2b3f8c83d95f8c3a225b8c260f548bf8ba958bda57218bd6d9bb8bb213078a993b7c8a93bec18a81b0a88a5ef7d58a2f019d8a079ee18a06821b89f5f58889e5f2198999d50c898e35fb8979ea32896ba8df894fd47e8937bce189339dea891cb00588c457d788c25140887437e588690beb885015c788036e8c87b20036877a78c9875b27b18745189e873c904e870bce5086bfb66f869c6428867e76068670e4cc86396688860d3b9a85e1d75d857e1b838541295f853a3606851351e58502b0a584cf088284621ee784522431841c14d083f3954e837bd53d8358bc12834af6a783324f9182f9c3b082e3c47c82d47f5f82c92169
  | 7, 0, 14 => 0x95842c65957c2c3f956bdaed9516af7594d9f12f94ca0e3394bab74494a17b46949b9cf29488a0359466a56f9430ce119425b0dd93e73daf93e5144793b5eba193ab439c939b7f5e9368ebeb935b807a931ec53192f8302c92d6874d92d55f5692c36a6a92a5e56092a472e69294dde2927ee9ed9247e2969210b3f592041fe491f684a691f2907191df562391bf6345918c63c0918c5a799173c5b6911c7b8390fc9af190c0704c9076ec8e9073f5f5905dee4c903ae5d79026721190012c808fdf91ec8f879c588f71a1938f713f988f62c14b8f3188038f27d6fe8ed53e0d8ed508c08e74549d8e33b09b8dc6f20f8d8249758d70d7768cebfa108ccf0a71
  | 7, 0, 15 => 0x9cf7feb19cd2fed29cbd32db9ca7e2709ca201249c7331cb9c4680cc9c13ec2f9bc0931f9bbfcae49b90cfd89b86c07e9b80928f9b5c14ea9a98656f9a9859c99a9218b99a8799c19a43bade9a2dfc089a11c9cc99f8011499e4c213998006f3997351599966c74d99669b959962264b994267be9936b9749931b1fe99253a549905756d98e3794f98e27f3198c478a698bfdbbe989adfa69871e53598510c4f981d6398980971739800305f9794a2ef974afbfe973d7dbb973aebfb97384e4c96f52b4496ef31db96d35d1996c654cb96acf15696a547bf9670db19963faf75963393ff961e06bd961a6f3396147f0e95f4027a95cbcdc295bb394895ae098a
  | 7, 1, 0 => 0xa428cecaa410e776a3c2a1afa3aed91ca38e8a46a2e7b907a2e5eb9fa2e3f152a2dac139a2d1b9d3a2cd4489a2cc83aea2b9f024a2b783b0a29f56f2a2763b37a264bb56a237e894a20635c1a1e79df4a1b43f61a1a3bca5a199ad4ba1964c37a191278ca1822aefa10c22a1a0ed1e35a0e42f7da0e0760fa0da99e1a0b789b5a0927c55a08c56eba06176dba04512f1a03ba547a020378aa00b5fff9ffda58b9ff982e99ff8643a9ff4f7999fee95f09fb9948f9fb16acd9f4b173e9f03921c9f0199059ef6661c9ef59fdc9ee19dff9eb47f2f9eb46aa69e96a0299e60f8799e549f359e40bca09e2aebef9df311db9dafb4e29da28d5d9d9059379d4b3b19
  | 7, 1, 1 => 0xad3b5923ad2dbfedad18982fad0bcc6ead06daa8ad0464fbacd2dda9acce2efbacb976acac9d464cac87d158ac40a987ac2817b2ac27da11ac0e1dbeabc1044caba28d3dab93af8dab76f7d6ab5b97e0ab0392c9aafe6657aaf16d61aae2c829aae1e6a8aacae70baaabf859aa45b81faa343074a9d21a08a9a17713a98b55c8a9689b7ca934ca04a9131075a8e4d034a8e4a6a0a8a212f7a862c48ea8500690a7bb9b61a7a46f4aa7448f80a740734ba6fb7775a6d1b8b7a6acde02a67be8f6a64463e4a6421094a62d40b0a60182bda5d45b80a5c75f65a5af02d8a57ccc55a4f0a5fca4e84de5a4c75773a4ae46dda494ba80a473e546a46b1b87a433c8ba
  | 7, 1, 2 => 0xb4835f10b47a4ed1b474e627b46eb107b43492bfb41c3c91b40ba394b3c7d433b3848b72b3832b99b2f67572b2ecdc34b2c8f278b2b55d4fb2a67dc3b25e5f62b2500118b24fee72b24a8eb9b23b047fb23aad95b22fd2dab21d840eb20e639db1fc71dfb1db9bf1b1d1ad52b1ae1d88b18d94c5b189e4a3b15a583db158780cb147c105b1446f9bb12758b8b0d3ebbeb0b45387b0978fe9b09629b1b094a0e5b08da57cb08217e5b07b2df5b053476eafaf7e14af87c055af6c33b0af34800eaefcbf9daee02b81aea33930ae94ecadae792b02ae69ee0fae4cb3d0adf47384adf3fcf7adefd1c3add14485adcba09aad83c098ad703eccad55b4eead4bd754
  | 7, 1, 3 => 0xbbc874d2bbc8136fbb9731b2bb536b52bb2bc4d0bb20d37bbad0a275ba678793ba5ea660ba58198eb9ffbf23b9f0b52ab9c5022cb9bf5ab4b9a4cadcb964f444b9501ba2b9305d15b8f36ac4b8c8a55db8c84a1cb8b5cb1db8a6c784b86e02edb84c4a65b835d49eb824c4bdb812fae4b7f766cab7ee25b6b7e190bfb7ce9b54b7c99c1bb7ace222b7a27ad6b7842f4bb75f91c2b74c752eb735d60cb734c20cb72b7312b728e152b6e24499b6a12c76b68a26d3b67eb1e8b647e64eb608648ab5d83fcdb5b8fbb5b5b522d9b5a76137b598f159b5853ba2b556c2dcb5562e40b5238438b5172137b4e21eb8b4d0e9e0b4b87ad3b4b8038ab4a63668b4a55639
  | 7, 1, 4 => 0xc4b774dcc4b5d2b9c49c3c34c49af72bc4686aa8c44f0733c3de321ec3bcfe22c3b27a64c3a36f81c2d3e0f6c2bb39e0c28d123bc26778a6c1f42b18c1bf2bdbc1af4796c16ea0a3c1528514c13eb19dc131a89dc0ed8bf9c0ce6b66c0cafec5c0c0db0ec07a4c42c04dba9dc045954ac012abf0c00e2ce1bffc6bd3bfe9d026bfdbae8fbf9f6024bf989a83bf935932bf898ae8bf605e05bf4349e2bf10d6aebf0bbb85bf065791bee60c36bed7be86bec55acabeb088aebe9d8865be7c92f7be753832be5d4f2abe445b27be011283bdf3a368bdcb3d81bd803234bd3e5fdfbd3a18b7bd32f271bd14695dbcb41943bc840d96bc62ecabbc1b5157bbf85d37
  | 7, 1, 5 => 0xcd71a101cd669592cd3c884dcd0e8dbfccf0a9e6ccd29adbcc88a61ecc6923f3cc546ba4cc266771cc202cdccc04a432cbfd2d53cbd53da4cbc30625cbaef9a3cb8e1c8ecb81317ecb66d75dcb296f2ecaac01c0ca95c58cca948c7aca8818bbca7dbd21ca68a6bcca65dc03ca38d44ac9d37c31c9c56731c9981195c98f6c6ac98cc83bc97dca2ec9794b1fc9421defc92fc7a9c922bf5bc8cd45a9c87b7b57c87367adc83c6390c82ae006c82971d5c80717e5c7fdb986c7972e5bc773c809c76c30c1c76571e1c7079967c6e38824c6e33866c6e15833c68d390fc673906cc5df58dcc5b24cf1c59c77b5c56ac1acc549f7d0c535909dc4f74707c4c895a0
  | 7, 1, 6 => 0xd67f0e98d5e44300d5b5f79fd5a6f10cd5442397d542562fd533bed0d52c8a38d4eadf53d4b8d850d4a1efa9d4536fcbd4190236d4002735d3f617dbd3b73189d370b361d36b5df6d33ce8ecd312ba80d307bcccd2cf1fb4d2b7b812d255423cd24c54b9d21dc831d215dcb3d2003cd0d1fcebc3d1e583b1d1e26ebbd1cc9685d1c1e670d19491b1d1484d94d12eac18d1154e0fd104d318d0f43e54d0eaf067d0df6493d0b1959ad0b109c5d0858540d08247e8d028034dd01622edcfea3e97cfdf8375cfa7a5a9cf8c37eccf5a9d44cf1c48b3ceec12e2ce520fbcce2b6ec8ce1af5a2ce1502afce141fface04edffcdfc440ecd8f687ccd8606d2cd84e435
  | 7, 1, 7 => 0xddf2b66edd663279dd3d44e7dd3d24f6dcc41091dcc1369edc812ba1dc77ccd0dc48c872dc2b0159dc13de25dbfde1a3dbede8d5dbeb56ffdbd5ffcbdbb9ddd9db852709db71cc45db6369cadb571064db569198db2d04aedb2839b2db1ae12edab8c3dadaad8f87da99ca56da75c84bda460ee5da2c3ed5d9f9a6dad9f7682dd9f4b273d99bfd39d96c7a47d959200cd93008b9d9169c22d8f75796d8f20b95d8d1265dd87756e5d85ded4dd855128ad84b58cbd8465bc2d840e3bad830b4fed808f7e5d7fd5403d7a300b0d78613e0d77224a2d75b3a61d747d71ad73a717ad7283adcd6fa86bad6f87d55d6d04fd6d6c71384d6a9141cd6a466f5d68d98cd
  | 7, 1, 8 => 0xe7d75888e7c466cde7b84ac7e7a4b839e71c1557e6f2317fe6f02fade68e1704e67e2d5ee67c4d2be5fd4df7e5df9629e5cb67a2e5a5c3bce5997ca7e5943b56e58c788ee58a6d0ce50c9da9e4e6ee5ae4c1afd6e4976f0fe489d6a5e4832199e48252d5e47d751be45fe2fee4552f85e43a8f21e3e9fc2be3e64f33e3d66f38e3c5a0fbe3a9d0cce36fe4eae35d12d2e34e8109e34ccce7e27b0792e25929fde22ce42ae1eb50d1e1ddbc77e1be25e6e19813d6e18278c8e15892a1e12ca6f4e10865bee100943ae0e0ce7ae0cf402ce0c8841de0b18480e0a662d8e08e0c62e07b2a37e069605edfe8af95dfc1d156df814e89def9b0dcdeb97c26de36b6c2
  | 7, 1, 9 => 0xefd833eeef98f3b9ef7a786def794545ef452d54ef4205d3ef1083d3eee729c4eeda0839eeb73dabeeaee791ee77bbe7edf99859edb5ea9aed8be3d2ed7d5dd3ed7a456ded710c24ed687b94ed548ae9ed49643ded33deb5ed275ae7ecde9f3decd035e6eccfc2fdec7c632aec5914c8ec14f493ebe03b00eba0de16eb9f992aeb98224beb4ad9f4eb3d6051eb03a010eafc90c9ea9f1848ea9bd94fea8cd3ddea681c52ea5693f8ea34e2a8ea30ba84ea2b9a92ea053820ea02da06e9f36e47e9ed1452e9bcbd99e9b35c88e98606ece9145362e8dd12e7e8af8fede89bfac4e88df45fe8685acae84a9507e8214b0ae816704fe7ebaedde7e9232de7d9adc7
  | 7, 1, 10 => 0xf7f8e245f7f6ed3cf7ee52dbf7ebc58ef7e665d5f78b0895f742441bf7325e1bf72108d8f6e87c11f6e672acf6dd2951f6b508dbf6b19c3af660e837f61a0390f6170511f6164d06f5ffda11f5eb20bbf5ca81d8f5c24c04f57f37f8f55a7045f531f1bbf5304b86f4ecf506f49c29b2f4416522f4350afff42c9798f422fc21f415e4d3f415021ef3ed48f2f3c6c34ff3c4153cf3bbdaadf3b20571f39b1c2df3967e69f3751320f2f18c0af2db1cc7f2d7724bf2b64da9f26a0617f262ca44f2554dc8f20e15f9f1bf72fff19fb472f197e0bbf10f3cd9f10d2b1bf0cd59eaf0a8ec02f091c2daf085e55ff07e9f45f066be27f05d4fbdf03a0d1bf01d3ce0
  | 7, 1, 11 => 0xffee6a96ffdce536ffd6a4ecffafc6adffad28e7ff82234fff34a3adff1f0a48fef2edb9fea621f3fe590036fe519dd3fe4d5cfcfe09da09fd810311fd6bdaa3fd5b3219fd5427d0fd48b93efd438e20fcf95f79fcf7b91ffcd839dffcd295f4fcc7f5a8fca6c788fc8ab5f2fc4bfa3efc21d1c1fc1c2099fc0d0f85fbebd6fafbd94c56fbc5f651fbad4796fb515f21fb4486effb433853faf3d2b8faadec30fa9c2651fa638275fa5451effa53b8d2fa502ef3fa48847ffa19e45afa0bc0e3f9e9bd83f9a39b97f9921879f959117cf91fc747f9076f3ff8e9a39ff87d843ef8637ed4f825528df80eb781
  | 8, 0, 0 => 0x26c8448826c17c5625de5cbc25ce08de2597cdcb258603f224eb385a24368a0d23071c8f2280846c223cfbcd2103e11d1fa04f471f1c08551e267e0b1d53af701be5022a1bc4f8f81b0b998c192abff41928bdfb18ddfae01885506618491349178270b115fa176615ea2dc015e84d8d15cc23b914ccf9dc131f4f8c1315d12e11d44dce10e87ecc108ae1ac1076a8040fe72a990fd560c00f54aff70ef660100e7d19c40da8ed200ce278c60cd232db0b69e2050acf6a2c0a9899f8097ffda408cf1df806ffe09b06d554670666871c0663a259064812d4063313e6058e5e4e0522378c04ae569104a62e7c03d13a0603bf702d0334fbc4032331eb00486864
  | 8, 0, 1 => 0x4b12b9ab4af0fcd64ade3d7049ce19fe499655e64978086c48e4af30485681f648503368478990d04691fdef4639537545f14ddf45bbfe3545af2d6b451a42544422b1fc431db41f42a4748a4291e304422923bc40982e5a3fcf5cc13f08ba293e7b850e3d880f153d7077383d4b05d83c5059973bcf8e9d3ad68a4b3a1dbef63a1c5f433a0a956a39a60da2394637d0390d085a3909cf60384665c2374ca99036ae22d13366d8583316a5f43255b3a43253c24131601f57309620c52fe7ff5f2fd635862fb879da2f4b1d992db95d5e2da043882d7d07ca2d2eb55a2b97cb312b935f3d2b8dd2232b31f6b32a5fd31a28c67460282125ee2764e2a726f708f7
  | 8, 0, 2 => 0x6c9959c36c92e0136b200a506b022d8e6a69a7bb6a5967b86a57dde269c0e37869ad2dc16916efa46910ef7f69089f4e68c124c768666c2466d93e12667ff346660c53db65ed79a065bcd2fb64eeec5464dfafd26389c217632f1445629bcaf2627b77fa612c571a60c73bd4609018d86081e9ba6046708f6000993c5fbf99f95f6d245d5f5b5a845eb0dedf5e9f6fd55e68564b5dd4ff705dce6a1d5da661335b6ca1675b55547e5b3916d25a6a02b359cdc471590a0aed57c86c81573ec3525717156e5707833656618b4755d528fd54f25879534d92b752b8402b512f0a4b507c6eeb4da0f7e84d5452564c8de4c04c7181d24bf5ebc44bceeb024b85288b
  | 8, 0, 3 => 0x8b73c1868b57ffe18af983f689797c2b895eb4c688fff5b68895799e87ced70687ccba0787b913888790cb938680c80c8675f0ff8636941585bf85488558924284db144384158e568332bdd282f2eadf828f70e18224362d81d99ab981a2729c8187f7eb810a65a0805efbc27edfec597e9d06ce7e6b4a6f7e2b55927e1949c17e08edba7c8106d07c3096787bd60b217b1bd08179fe9a1779531f0478a4ffe57836a2657806243d77c22f61774a58f5769098c175c9f62975c31e547501c5897431b33873c08ca273b01f3e7355347a716d59a77166433c708ebaa170276af56ff132df6e4c31696de290936d984e506d6960e56d4247ad6cc9ecf66cbcbd38
  | 8, 0, 4 => 0xa4c0fd24a494ba80a40383ada3eac9f2a34cc39aa333da41a328ba33a2d1b9d3a27a8444a18e9a8ba1748fb1a15392e4a091bf2da03e7b57a03ce6b2a004e02f9ff852fe9fa0a8709eef4aa39ecc14489ea5e2099e0571b09cf5cccc9c6d2ebf9b7e5d089b171ca199ca934498dcbfd19892f53c98405c4b980df69f97ed931a97777c57975154d896b2205f964f52ea961a6f3395c9e79995c3f31a9541f7f995379eaf944d138d93ef9a1c9371a0599328f78491df562391c8cfc39190b4939165d2a091526b2b90b527f09037996c8e8cb7168e3a26c08dffff528d8d65968d431c738cb614e58c7d04a98c64e1ee8be0c6678b969fb78b89027f8b82116a
  | 8, 0, 5 => 0xc233685ac2037a77c182a05ec1628508c1027068c0bbfdc6c0290ea1bfe76089bf8cd05fbf23bad5bed23673be5f5723bd9fb0fdbd24da46bcf7064dbcee49d7bcc84171bc5e37aebc1b5157bbfbe808bba622bdbaf502e1bac5f4bdb9b426dfb89f9e4cb893ca02b8708326b86f5b6ab831e6bdb819de68b63b7ad9b608648ab605ed0ab54c9475b4b05633b408f741b31d6796b30c9551b277763eb265c412b229c4cdb1b4f7b2afab3129af6ca0fbaefb9166ae43986eae3afb86ae3275b1ac52d745ac5109ddabba8fd5ab6e3959ab5f00adab0edae3aa16707aa9f273f7a95f898ca95635b5a84a25ffa791a059a6d87d86a5b19f0aa5879fbca57c8260
  | 8, 0, 6 => 0xddc02084dd1af66bdc72db0adc6a17cedbecf762db6ddf06d90d7775d8f206efd8947344d8293d25d713283ad6880befd6093950d5264043d4fa9690d4e8ccb7d49440d7d46b83c8d330856fd2fa8aa8d251ec01d24db4ebd1024c99d04c7671d0459b76d00dbdb0cf8c37eccf1d6b2fcf0795f3ce38b857ce24c56fcc53ac0bcc3eff34cbb907bccbb1e63dcb2bcb46caade5a5caa9cfdbca883bb0c9c6ff57c9c5ed55c97dca2ec87175cfc86e161dc7c4c4cfc77571d5c6f26785c6e49a15c6dd499fc6a97e1dc6485bd3c5ab8fdac5866f95c573d8c8c5491818c4e4ed42c44526a1c4045873c34caa51c2d28e99c2c829e6c28a9299c2453233c24287af
  | 8, 0, 7 => 0xf9e3a63ef9d1dc65f9316793f88bc9acf81a05cff67433def55d2317f54b593ef5087817f4b5f832f3897d71f327dbd7f31e7ac6f315725ef2fb5f6ef2450b53f1d37908f16a559cf0aab1ffeff93542efe76b69ef1664beef049ae5eef58b4aee77bbe7ed84fd02ec3fd3faeb97b9b2eb09b191ea97c532e8bca3e2e8ab2ddae8656c85e818ef00e7088a33e6c9718ee66c4bf1e5a2e642e536c5f0e525fa75e524fc17e4dc43aae4c22ea2e412eb26e3e0e689e34400b9e32c6c35e2df9ab7e2743fade26275d4e2435c75e1efa266e1ca5fc4e1ad9d15e19bd33ce1687241e16359cee107afe6e03d9934e0155a24e003904bde81d49fde63a60edde5965d
  | 8, 0, 8 => 0xff82234ffe8600cffe581344fd80205cfd2fbf52fd124cd3fcfb68defc786195fbd8d109
  | _, _, _ => 0
def CV : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x28404000000e10200000018404000000610100000018408000000a101
  | 6, 0, 0 => 0x84140042002200000d4104828000000a10c00006048828000000e1020000001842800314c420a0000e048828000000e1020000a048824c4058c530900000008430000081220a00000008428060280e309000c5310828002510120a001153108240041441209068d5210c25193500a30900006048824000000610200000038408000000e10a00000104430000000210500000434414000080e209001152108241a05484309
  | 6, 0, 1 => 0x42508008c24000000210c00000038428000000210c00094404828020281230900094104828000001210d0004110082800314c420a00915310c24000000210c00000008430000000210000000038414020181230900000048434004350c20941504038c24d825441309324c8008c24852100e30900000048430000000e1000180a048c240000002100000d5210824024548430915055038c25144540e309000000384300042508209
  | 6, 0, 2 => 0x280e048c25054100a30931016314c24004548520903915310c24000180e20900000018414000001210c0000002843000000061000000001843400000021000180e048c2400324c820900000018408000000e10003915210c24000000610c000000184010d4300230906815210c24000001210c00000008414000000210c00108038800000000e10500105008824001044020a0000e008828000000e100008d5210c24c8058c9309
  | 6, 0, 3 => 0xc13008280000002105324c8018c25050550430900000008434d80588430900108018800000010d10500000038400c53504130900000008400000000e10500000048430002510120a00000028430004140e20900000414424c93200230900915210c24000000610500000028409182540e30900000008414942540e30915055038c24004150420a42508038c24000001210c00000028434002504120a00101400828000001210c
  | 6, 0, 4 => 0x84010d4300a30900000018400000001210500105028824000180e20a00000008414004050020a00000414424c9054c8309000000284300e4548430900002038824000590820031416310c24000000210c324d4204c24000000e10500000038414000000210c314c4008c240a454c4309000d4104828000000210500000028430000000610032016324c24060281230906514210c24000000210200000038400000000e100
  | 6, 0, 5 => 0x8408000000610000000018408002510120a324c8018c24020180e309001151008280000806209000164148240e05484309314d4104c24002510120a000d4104828000001210c000c5310828000000e105000c5310824000000e10c00000038414000080e20a00000018400000000e10525095038c24000004110c00000038430000000e10000000008400000000e100324c8048c240e0548430900000038430000001210d
  | 6, 0, 6 => 0x28430000000e10500000028430c53100a30900000028434000000210003855200c24000590820000000008414002510120a00000018408c93508130932415320c24000000210000000028434000000e102314c4008c24000000e10500000414424000010810000006038828000000e10000000038414000000610500000018400852100230921016214c24020280e309000020288241935084309000000384000000002100
  | 6, 0, 7 => 0x41100828004050020a03815210c24000381220a00015210824000080620a00101400829191508130900000008430000000e10200002038828852100e30900000008400004504120a00085210824000000e10500915310c24020180a30900000038408000000210236095104c24000280e20900000048434020381230941415410c24004050020a00000038408000000e10200094304828000004110c00006038824942540e309
  | 6, 0, 8 => 0x180a038c24000000e102000060288241a3548430900806048c24000001210500002038828852100230921016214c24000000210c00000038408020280e30900000038400000000e105264d4100c24c93201230900002048824000000e10500000420400020180e30900000008414000000e10000000008428000000a101000000384000000002100000060388280000002102000000084000000002105000000184001a05484309
  | 6, 0, 9 => 0x18400000000210200000018409192500e30921484038c2400314c420a00000048430020180a30900000048434000381220936095104c240041504209028d5200c24c53100a30946095104c2406254c03090000003840000454c020a018d5200c24000010d10500006038828000000e105000020488280000105109000c5310828000000610a00002018828020281230900000048430c9054c8309000c13008280e454c4309
  | 6, 0, 10 => 0x8434020381230900000104430000000a10c00101400829054100230902915310c24000000610c21484008c24000000210c008d5210c24000000e1000280e048c24840588530900000104430000000210200000028404000001210d0010d430828000181220a03815210c2400000021020180e048c24000000e100
  | 7, 0, 0 => 0x85028824000000a10c000d5210824000000e10500000018414000000210a0000003840000000c010a00000430428003140e20900015018824000281220900000038428000000e1090000e0488240000012100000d510482400028122090010c038824000000a10d00000048428000000e10a00000038414000000210500000008428002510120a00000304428000180e2090000e048824000000e100000554308240025504209
  | 7, 0, 1 => 0x8430004300e20900000028430000000210a00000008400000001210d00000320424000180a20900084038824000000210d00000048424000000210c0000000840800425082090009440482400001051090010d008824003240620900109420824000000610c00000018434000000e10a000d520482400324c820900114214824000010910d000d4028824000080620a00115310824004200620900006028824000000e100
  | 7, 0, 2 => 0x8430004100a209000c531082400000c410a000d4204824003240a20900015310824000000a10c00000028434000000610000000018428000000e10a00000018414000000e10a00000008428000550c20900000038428003200e20900055420824004140220900002048824000004110c000d521082400351012090010d430824000000610a00115310824002140620900114204824000004110c00000008400003200e209
  | 7, 0, 3 => 0x38428000540a20900084008824001500e20900000048434000000610a0001541082400054842090010d43082400000c410d00000048428000000610900000310428002140a209000d54208240035504209000c5310828000000e10a00000018400003500a209000c4008824000000210a0000002843000255002090000003841400454842090000001842800000121050000000843400000061050000000841400000c110a
  | 7, 0, 4 => 0x38428000281220900000018408000550820900000008414000381220a000d5210824004150420900000028424000000e10200000430428000000210000000048424002550c2090010402882400008062090011520482400058c420900000018414003510920900002018824002510120a00000028430000180e20900000018400000000e10a000c5310824000010810000055320824000000a10c000d54108240045484209
  | 7, 0, 5 => 0x115310824000000210c0000001840800000061050000201882400304c020a000000084240002812209000c9008824000080a20900109420824000000e10000000048400000001210a000c9320824000280e20900000038400004140a2090000e048824000181220900015310824000000e1000010d0288240035484209000c500882400454c4209000000484240020406209000c93208240042508209000060488240041504209
  | 7, 0, 6 => 0xd5410824000000210c000c9314824000000210a0000001842800054842090000004843000000c510a0000004840000018122090000004841400000021050000a048824000000a10c00115300828001040620900000048428004300620900109028824003250c2090000000842800000061050000e048824002040a209000c8008824000000210a000540288240035002209000000184000000006102000950388240021484209
  | 7, 0, 7 => 0x94404828000000e10200006048824000001210a000d521082400000061050010c028824000000210a0010d038824004310920900000008400001041220900095038824000550420900000008424003540a20900000048400000180a20900000008428000281220900000038414002540e2090000001840000028122090000004841400254c420900109420824000080a209000c50188240035484209000004004280035109209
  | 7, 0, 8 => 0xc9204824000000610a000000084280035105209000c801882400350062090000031043400354842090010503882400038122090000010442800454c02090000000841400320062090000003840000000021000010c018824000001210c000c50288240025006209000c9430824000080e20900000008414000000e100000c5104824000001210500000048434000000a1090000a048824000001210c000000084140042508209
  | 7, 0, 9 => 0x18428000000610a0010d430824000000210a00000038428000000210c00000310428000000210d00000038428000588120900016324824002040e2090000001842800000021090010c028824003100e20900000028434001510d2090000a048824000001210a00000404428000001210d0000003840800008122090011503882400000c410900000038414004350c20900000048430000080e209000c932082400250c1209
  | 7, 0, 10 => 0x85048824000000e10a000d4028824000548420900000038400000000210000006038824000000610a0000603882400304c020a00000310434000180e20900000008424000010810000000008428003548520900000404428004050020a0000003842400350852090011521082400350412090000000843000435082090000041442400000c010a00000038400002100e2090000a048824000001210500000018434000000e109
  | 7, 0, 11 => 0x15310824000180e20900000100428000000e10900081048824000080e209000c9320824000000e1000000e048828000280e20900000048414000010d1050000a038824000000e10200002038824000180a20900000410428003500620900006048824000000610a00105410828000010c10a000c503882400008062090000001842800000c51090000001840000314c420900114028824000000210a00000038414000000210c
  | 7, 0, 12 => 0x114028824000001210c00000018400000080e209000000484280000006100000000384140002812209000d4404824004144120900000018400003500a20900015320824000000e10a000d4018824000080e20900000038414003200e209000c9048824000001210a0000001842800251052090000002843000454c420900000038414000181220a00115038824000080a209000000184080000012105000d4204824004500e209
  | 7, 0, 13 => 0xd5210824000548420900109420824002500e209000000084240000012105000d5420824002148420900000314428000000e10000000414424000000210000002038828000001210a000c4008824000001210c00000048414000001210a000c9320824003040e2090000003842800154c820900000314428000000610c00000038400000010c10a0005403882400054842090008504882400000121000000a038824001500e209
  | 7, 0, 14 => 0x10d028824002500e20900000414428003201220900105410824000000e10a000003044280015109209000060388280000002100000000484300000006100000d521082400018122090011531082400150c920900000048424000548420900000038414000000e105000c9320824000000610c00085210824000000e100000c9104824000080620900000008424000080620900000008434000000e10500015410824003544020a
  | 7, 0, 15 => 0xd5210824003140220900000038424000000e10a00000008414000001210c000153208240020406209000d4018824000000610000000038424000081220900041100828000004110a00002028824004350c20900000048414000000610000000028434000000610d00000008428000000a10c0000e048824000010d10500000048414000010910d00000018408000000610c000950088240000806209000c93208240000002100
  | 7, 1, 0 => 0x95038824000004010a000c1038824003100a2090000003842400254c420900109430824000080a20900000304424000000a10d0005503882400314c420900000028430000080a20900000038428000001210c00000008400000004010a00095310824000000610a0010d4308240000002109000d4104824000080e20900000048430000001210d00015038824004140a209000000084240002812209000000284240035485209
  | 7, 1, 1 => 0xc5048824000180a209000d402882400255042090000000840000454c4209000d52108240031406209000c9314824000180e209001153208240035504209000d5210824000000610a00000008400000000610500101038824000010510900041038824000001210d00000048430000001210c0010d430824000010110900000008414000000e10000055400824002040a20900105410828001500a209000000484140000812209
  | 7, 1, 2 => 0x10d4308240000105109000000484340000806209000c5028824003200620900000008408000001210a0000203882800255042090000001843000254c4209000c1300828000000210d0000a038824004250c20900000018400000000610900000038428000080620900002038824000000210d000c9018824000000210900000404428000081220a00095038824000180a209000d4018824004350c20a0000004843000058c1209
  | 7, 1, 3 => 0xc4038824003500a20900000048428003040620900000008434000010410a000c804882400324c120900006038828000000a10c00000038428000010410a00002038824000180a20900115210824000000a109000c9204824000010810000085210824000000e10a00002028824003240a20900000008430003510520900006048828000001210c00000018430000000a10d000004204000015508209000003004280000006105
  | 7, 1, 4 => 0xc531082800324c82090000000840800000061050011402882400314c420900105008824000180e20900000038424000180e20900000028430002040e20900000048434000000210c00000018414000080e20a00000048430000588120900000038424000080a20900000038428004548420900000038428000000e10000000008408003544120900000018428004350820900000018424000001210a000d5214824000001210c
  | 7, 1, 5 => 0xa038824000001210a0000e048824004540e20900000038414000181220900000104428000001210c000c9320824002144120900000008430000001210a00115038824000000e10900006038828000000e10000105410824000000210900000018400000010d10500081104824000000a10d000d4018824000080620a00000028424000001210000000048428000000a10c00000038400000080e20900000100428003040a209
  | 7, 1, 6 => 0x48400000000210a00000018430000000e10a000020388280021002209000c9320824000001210000000038428000080e20900000038400000001210c00000008428000000a10c00002018824000000e109000d5204824000001210a0000001843400454c420900015320824001540a20900000038424000000e100000161048240000002100000c5038824000000e10500000038424000010910d000004304280003812209
  | 7, 1, 7 => 0x2028824000000a10c00015038824000000a10d00114028824000000610c00094038824000000210d00000038400000500e20900000028430000000e105000d501882400058852090000e0488240030406209000000384000005484209001151008280000006109000c9304824000280e2090000000842400028122090000203882800314c420900105410824003508120900000008400000001210d0000030442800054c4209
  | 7, 1, 8 => 0x8428003141220900002018824000000610000101400828000180e20900000048434002540e20900000038424000001210c000c1028824002100220900006038824000000a10900002038824000000e10a0000003840000425082090005532082400314c4209000060388280025441209000020488240000002105000d5100828001500e20900000008414000000a10c000d440482400314c420900000048430002500e209
  | 7, 1, 9 => 0xd5210824002550c20900094404828000540e2090000603882400001051090000a038824000081220900000008434000004010a00015038824000000e10a00000048434003240220900002038824000180a20900000038408000001210d0001541082400000c010a000d5210824000381220a0000040042800058c120900000300428000000e10a00101028824001040a20900006028824000001210500000048434000000a10d
  | 7, 1, 10 => 0xc9320824004548420900000018424004310d2090000040042800250062090000001841400008122090000203882800000c510a00085210824000000210d00000038408000080a2090010d43082400000c010900055038824000000210500114038824000080620a00000038414001540e20900000008428000080620900000018428000000210a0000202882400000021050000a038824000000e10a00000048430000000e10a
  | 7, 1, 11 => 0x6038828000000610000015420824002540e209000c1038824000000210d00000008434000000a10c000c402882400254c420900000008400000000e1020000001842800314c420900000018428000004110a00002028824004310d20900015210824000000210d00000400428003504120900000018428000000610900081048824004140e2090000001840000314c420a00081018824000280e20900000048430000000210a
  | 7, 1, 12 => 0x6038824000000610000000038424000000210c00000008424000000e1090000031442800000121050010800882400314062090009401882400350852090000001842400324c52090004110082800000121000000001842800058c520900006028824000181220900000028424001540e20900006028824002040a20900000028434004548420900101038824000001210c00041038824000000210500000038424000010c10a
  | 7, 1, 13 => 0xa048824000000210000101400828000180a20900002048824000000e10a00000300428000588520900095410824000548420900000038424000000610d00000048434000010d10a00000038400000000610000000424434000004010a0001543082400410022090000000842800350062090008403882400314c420900108008824000001210d00115310824003240220900016304824003504120a000004204000000006100
  | 7, 1, 14 => 0x41038824000000610c000c8048824000000e109000c1048824000000210c00085104824000000a10900000104424000280e20900000048434000000a109000d4404824000381220a00000048434000000210a001151008280000002109000c502882400000061050000000840800000c510a0000002842400314c4209000060488240021402209000020388240025406209000000484240021484209000020488240032412209
  | 7, 1, 15 => 0x38428000180e209000000184240035508209000d5420824000004110c0000a048824000000a10c000d5214824002100e20900002018824000000210a0008521082400314c420900002018828001044020a00101400828000001210500000028434000010510a0000e048824000000e1050005543082400008122090000001842800454c420900002018828000000e10500000038428000010d10a000000184280000006100
  | 7, 2, 0 => 0x115210824000000e10a0000000842400154c82090000e048828000180e20a000000184240043402209001140288240000002109000940188240000806209000d5210824003240e2090000000843400000c010a00000104428000000a10c00015210824000000210c00000048428000081220a00000048424000000210a00000018400000010c10a00000038428003041220900000018434000000e10000000018400000000610a
  | 7, 2, 1 => 0x85104824000000e1050000002843400450c120900006038824000180a2090000a038824000000a10d001094208240005006209000000384140000806209000001044300000012105000000284300035006209000d520482400000c410a0000003842800454c020a00000018428000080a2090000001842800038122090000004841400000061000001631482400324c820900015210824000080e209000d40288240000012105
  | 7, 2, 2 => 0x18428000001210d00002038824000000610a00000018428000010c10a00000008424000000610a0001503882400054c820900000018428000004110c00054404824000000e10a00000404428003548420900109008824004350c20900016324824000080a20900000048434000000610200109008824000280e20900000018434004540e20900006048828000000e10500000028424000000610a00000424434000000e100
  | 7, 2, 3 => 0x2842400450c920900085210824000000e1050000e048828004350c20900000300428000000210c00000008408000080620a00015210824002540e209000c1018824000001210a00000018408000001210d000c9304824000001210d00006038824004150420a0000002843400054c8209000c9038824000000210000095104824000081220900000008414003500a2090000003840000054842090000a038824000000e10a
  | 7, 2, 4 => 0x324424000000210500000038424000000e10a000d4424824004200e20900085210824000000610200015210824001041220900002018824004150420900000420424000001210000115100828004140a209000d5100828000010110a00105104824002500e209000c4008824000000a10c00000314428000080a20900000048434002044120900000038428000000210500000008400001040620900000008434000004110a
  | 7, 2, 5 => 0x41042800038122090000e048824004500e20900101028824002100220900105410824000000a10c00105410824001040a20900104038824000000a10900095430824000180e20900000028430004200e20900006048824000000610a00000008424003040a20900016104824003240e2090000031042800001041090010103882400254c020900015038824001500a20900000314428000280e20900000048430001044020a
  | 7, 2, 6 => 0x38424000000210000094404828000000e10500002028824000000e10a00000310428003550020a00002048828000000610d00000400428000000210a00000038424000281220900000038408000080620900000048428002140e2090005530082400008122090010d430824004350c20a00114038824000381220900000314428000000e1000000004843400000851090010c008824000000210a00055038824000004110c
  | 7, 2, 7 => 0x2028824000001210a0000004843400314c420900006038824001540e2090000e048824000000a10900115300828000000e10a00006048824000000e10a00115210824000000e10a00000104428000000610d00000018414000000210a0004101882400324812090000a03882400324c820900000028434000000210d00015038824000001210c000c130082800314c420900006028824000000610d00000048434000010010a
  | 7, 2, 8 => 0x1631482400324062090010d038824000000e10900006038824000000610a0000001842800000c410a0000e048828001040a2090000004843400000c010a00000028424000010d10900055038824000001210c00000018414000000e10900000038414000000a10d00000410428000081220900000018400000181220a0010140082800454c420900015210824000000610a000c51048240000812209000020288240005881209
  | 7, 2, 9 => 0x115310824002148420900000018414000000e10000000434414000000210c0010d430828000550c20900006038824000000610000006028824000000610500000038424000180e2090000000842800000121090000001842400000c510a00000018434000280e20900081048824003510120a00002018824002500620900000434428000000210a0008500882400314c42090000a048824000080620a000000384240000012109
  | 7, 2, 10 => 0xd42048240000012109000000084280041002209000c5048824000000610d000000484240032402209000c9320824000000210d00015210824000000210000000018428000000e1090000a048824003544020a00114104824000000a10d00000414428000000610500108008824000080a20900000018428000548420900109038824003240a2090000a038824000180a20900109038824004544020a00000424424000000a109
  | 7, 2, 11 => 0x38400000000e1050008521082400150c120900000048434000000610a00015210824000001210c0000003840800314c4209000d5104824002140220900000008400000000a10d00002048828000000610d00000048428000000610a00000310428000010910d00000038428000000210c00000310428000588520900000038400000010110a0000e048824001550c20900000400428000280e20900000038428000180a209
  | 7, 2, 12 => 0x28434000000a10d00000018430003500a20900000018424000001210d000c5310828000000210c0000003841400054842090000004840000420062090000000840000454c020a00006038824000000e10a00000008414000001210a00014028824000000210a00000008430001040e209000d4214824004250820900000008414000000e100000c403882400350412090010d430828000280e2090000a0488240045484209
  | 7, 2, 13 => 0x10500882400434022090005530082400214062090000604882400038122090000e048824000001210900095100824000000210a00115310824004300e20900000038400000081220900000048428002100e20900105410824000010c10900000404428000000e10500006048828000008410900000100428000000e10000108018824003240620900015210824004350c20900104008824000000e109000003004280035484209
  | 7, 2, 14 => 0x85210824004150420a0000000840800000c510a0005520082400304c020a00104028824000000e10a0000003841400454c420900002048824004350c209000d5204824000000e10000054038824003240a20900000048434004040a20900000100428000000210500000018414000000a10c00000038400004544020a00000028424000280e20900000038428000001210a00002038824001550820900000038428000000610a
  | 7, 2, 15 => 0xc1300828000381220900000038428003544020a0000003841400454c020900000008430002510d20900000018408004240220900016324824000381220900055008824000001210d000d4404824002140a2090000001843400104122090000a03882400028122090000003841400450c520900095104824000000e105000000084000000002102000d402882400028122090000000842800415042090009403882400058c9209
  | 7, 3, 0 => 0x10d430828000180e209000154208240000002109000003104280000812209000000184240043002209001153008280042508209000d5008824002540e20900000028434000000210500000104430000180a209000d4424824000000610000000310428000080620900095104824000081220900000008400000010410a00002038828000180e20900085038824000001210c00000018424000081220a00000314428000000a10c
  | 7, 3, 1 => 0x48434000000e10000015038824000000e10a00105410824000010d10500094104824000180e20a00108038824000280e20900000028424001041220900000304424000000e10a0010d028824000000a109000d5210824000180a20900006048828000000a10d00000038414003041220900105104824004548420900015310824000000a10c000c5008824000000210a00000038428000001210c0000e0488240020441209
  | 7, 3, 2 => 0x38400004240a20900114038824003200220900000048430004300220900000018400001540e20900000018428000000610c00000018414000001210c00000008434001044020a00084008824002148420900109420824000280e20900006028824000000210a00000018400004100e20900095430824000180e20900000028424000180a209000944048280005841209000c903882400000061090000a048824000001210c
  | 7, 3, 3 => 0x8428000000610a000000384140005841209000d5200824003544020a00000048428000004110a00041018824000001210c0000a0388240000812209000c5310824000000e10500000038428000180a209000001004280045484209000152108240000006105000c8008824002148420900000048428000000610d00115210824003510520900000414428000010910d0010d430824004240a20900105410828002140e209
  | 7, 3, 4 => 0x18400003100a2090000003842400000c110a000c9320824003250c2090000030442800038122090005543082400314412090000002843400254c020900000018430000000e1090000002843000000c410a00000048414000000e10000000048414000001210a00104038824000000610a00000038428000000610500015210824000000210500000048430001500a2090000a048824000010d10500000038428000000e100
  | 7, 3, 5 => 0xe048824000000610d000c9320824000000610a00000028424000080e20900000404428000080e20900000038414000180a20900000008428002540e20900002018824002500620900000314428004140e2090000602882400000c010a00000048400000000610a0010d43082800058c52090010d038824000001210c0000041442400018122090004102882400324122090010c018824000000210000115210824000000210d
  | 7, 3, 6 => 0x314428000381220900000048430000000210000006048824000000610d00109038824000004110c0000602882400000061050000a048824002040e20900000304428003548420900000048428004300a20900000038400004150420900000038408000000610000000204424001500a2090001543082400314c420a00000104428000000610500000038408000001210a0000604882800454c4209000850488240032412209
  | 7, 3, 7 => 0x435082090000003840000214062090000001843000350812090000001842400314c420a00115310824000000610a000d4214824003504120900000038414000080e20900000028434001508120900000008400000000e10a00006048824000000610000000038400000000610a000d4414824000000e10a00094314824000080a209000000084000035484209
  | 8, 0, 0 => 0x1842400000c410900000304428000010110900000008428000000610900000214424000000610900000304424000008110900000048424000001210900000048424000000a10900000018424000008110900000414424000010c10900000314424000000a1090000021042400000c11090000000842400000c010a00000204424000001210900000414424000010c10a00000430424000004010a000002104240000105109
  | 8, 0, 1 => 0x43442400000c510900000104424000000e1090000040442800001051090000043442400001011090000004842400000c41090000030442400001041090000003842400000411090000004842800000c81090000031442400000c41090000021442400000c810900000028424000000e10900000038424000010410900000324424000000610a00000420424000000a1090000043042400000c8109000000184240000006109
  | 8, 0, 2 => 0x31042800000c81090000043042400001011090000041042400000841090000032442400000c11090000042042400000c510900000018424000000a10900000048424000010c10900000404424000000210a0000001842400000121090000032442400000021090000020442400000c51090000020442400000c510900000028424000001210900000424424000008110900000414424000000e10a000000484240000002109
  | 8, 0, 3 => 0x104428000000e1090000040442400001011090000003842800000c510900000304424000001210a0000040042800000c510a00000038424000000e1090000041042800000061090000043442400000c510900000404424000010110a00000310424000008510900000304424000000e10a0000041042400000c91090000031042400000c41090000042042400000c81090000032042400000851090000001842800000c4109
  | 8, 0, 4 => 0x30042800000c410900000038424000008510900000410428000000e10900000008424000000a10900000414424000001210900000414428000010c1090000021042400000021090000031042800000121090000043442400000c810900000038428000000e10a00000434428000000610a0000042442400000411090000004842400000c510900000038424000000a109000004344240000109109000000284240000012109
  | 8, 0, 5 => 0x48428000000a1090000041042400001011090000030442800000c910900000314424000010c10900000430428000000610a0000010042800000c110900000420424000000e10a00000404424000000610900000104424000010010a00000018424000004110900000304424000004110a0000021042400000c410900000404424000010c10900000400428000008410900000304424000008110900000314428000001210a
  | 8, 0, 6 => 0x424424000010810900000414424000000610a00000018428000004110900000104428000000e10900000048428000010c10a00000434424000000e10a0000040042800000c510a0000000842800000c110900000410428000000e10900000414428000000a10900000434424000000a1090000000842400000c510a00000320424000000e10a0000021442400000c51090000043442800000061090000000842400000c9109
  | 8, 0, 7 => 0x404428000004110a00000404424000010510a0000001842400000c11090000040042800000c510a00000204424000010110900000104424000000610900000028424000010410a00000304424000000e10900000104424000000e10a00000434428000010510900000048424000010c10a0000000842400000851090000010042800000811090000030042800001041090000003842400000c51090000004842400000c9109
  | 8, 0, 8 => 0x320424000004010a00000214424000001210900000038428000004110a0000000842800000c410900000434428000000610a00000410424000000210900000324424000000e10900000424424000010810900000324424000000a1090000032042400000c110a00000018428000000210a00000048428000000a10900000018424000000210900000430424000000e10900000210424000004110900000038424000010d109
  | 8, 0, 9 => 0x324424000000a10900000008428000010110a00000204424000004110900000420424000000210a00000420424000008510900000038424000000e1090000043442400000c510900000430424000001210a0000031042800000841090000004842400001041090000002842400000c910900000038424000010810900000414428000004110900000424424000000610900000018424000008110900000028424000010c10a
  | 8, 0, 10 => 0x310424000010c10900000210424000000a10900000204424000000e10900000410424000000a10900000434424000010910900000028424000000210900000210424000010510900000008428000001210a00000018424000000e10900000104424000010d10900000048424000000210900000018428000010c10a00000018424000004010a00000214424000004110900000424424000001210900000410424000000e109
  | 8, 0, 11 => 0x3842400001051090000041042400000061090000031442400000c91090000043042400000851090000021042400001081090000041442400000121090000040442400001041090000004842400000411090000031042400000c910900000018428000000a10900000304424000000e10900000420424000010110a0000041442400000061090000042442400000c410a00000028424000010810900000048424000000210a
  | 8, 0, 12 => 0x18424000010110a00000104424000008410900000424424000000e10900000100428000010d10900000210424000001210900000104424000008510900000314424000000a10900000320424000010c10900000204424000001210a00000210424000010410900000008424000000e1090000030042800000c910900000214424000000210a00000420424000000210a000003204240000105109000000384280000084109
  | 8, 0, 13 => 0x30042800000121090000004842800000c11090000020442400000c110900000028424000001210900000424424000000a1090000041442400000c810900000008428000008510900000018428000000a10900000048424000010910900000038424000000610900000028424000010d1090000004842400000021090000030442800001091090000001842800000c91090000003842400000c410a000004344240000006109
  | 8, 0, 14 => 0x21442400000c41090000043042400000811090000021042400001041090000010442800001011090000021442400000c910900000048424000010410900000048424000010810900000304424000010c1090000040042800001041090000021042400001051090000042042400000c510a0000032442400001011090000001842400000c410900000310428000010410a00000420424000010c109000004044240000084109
  | 8, 0, 15 => 0x4842800000121090000002842400001091090000003842400000c810900000414428000010910900000028424000010910900000300428000000e1090000001842400000c510900000018424000010d10900000018424000010410a00000028424000000e10a00000038424000010d10a0000043442400000061090000004842800000811090000001842400000c8109000004144280000006109000003044280000105109
  | 8, 1, 0 => 0x61090000030442800000411090000031042400000c810900000048424000000a1090000043442800000c4109
  | _, _, _ => 0
def chAt (s i : Nat) : Nat := (CH s (i / 1024) (i / 64 % 16) >>> (32 * (i % 64))) &&& 0xffffffff
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 12 0 (CN s)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_x1_0 roots_x1_0 7 s ws hint
  | 1 => checkCutEntry dom_x1_0_x3_1 roots_x1_0_x3_1 6 s ws hint
  | 2 => checkCutEntry dom_x1_0_x5_1 roots_x1_0_x5_1 6 s ws hint
  | 3 => checkCutEntry dom_x0_0_x4_1 roots_x0_0_x4_1 5 s ws hint
  | 4 => checkCutEntry dom_x1_1_x2_0 roots_x1_1_x2_0 5 s ws hint
  | 5 => checkCutEntry dom_x2_0 roots_x2_0 7 s ws hint
  | 6 => checkCutEntry dom_x2_0_x4_0 roots_x2_0_x4_0 5 s ws hint
  | 7 => checkCutEntry dom_x2_0_x3_1_x4_0 roots_x2_0_x3_1_x4_0 4 s ws hint
  | 8 => checkCutEntry dom_x4_1_x5_1 roots_x4_1_x5_1 5 s ws hint
  | 9 => checkCutEntry dom_x3_1 roots_x3_1 9 s ws hint
  | 10 => checkCutEntry dom_x0_0 roots_x0_0 8 s ws hint
  | 11 => checkCutEntry dom_x0_0_x4_1_x5_1 roots_x0_0_x4_1_x5_1 4 s ws hint
  | 12 => checkCutEntry dom_x5_1 roots_x5_1 7 s ws hint
  | 13 => checkCutEntry dom_x5_0 roots_x5_0 7 s ws hint
  | 14 => checkCutEntry dom_x4_0 roots_x4_0 6 s ws hint
  | 15 => checkCutEntry dom_x1_1 roots_x1_1 6 s ws hint
  | 16 => checkCutEntry dom_x1_1_x5_0 roots_x1_1_x5_0 5 s ws hint
  | 17 => checkCutEntry dom_x4_1 roots_x4_1 6 s ws hint
  | 18 => checkCutEntry dom_x4_0_x5_0 roots_x4_0_x5_0 5 s ws hint
  | 19 => checkCutEntry dom_x1_1_x2_0_x5_0 roots_x1_1_x2_0_x5_0 4 s ws hint
  | 20 => checkCutEntry dom_x3_1_x4_0 roots_x3_1_x4_0 5 s ws hint
  | 21 => checkCutEntry dom_x2_0_x5_0 roots_x2_0_x5_0 5 s ws hint
  | _ => false
theorem checkCutByIdx_sound {u ys hint} (hc : checkCutByIdx u ys hint = true) : ¬ RunD dom_63 goalM u ys := by
  unfold checkCutByIdx at hc; split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_0_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_1_x2_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x3_1_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x0_0_x4_1_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x5_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_1_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x4_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x1_1_x2_0_x5_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x3_1_x4_0 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) low_x2_0_x5_0 _ hc
  · contradiction
def p0Subs : List Nat := [0, 5, 12, 10, 13, 2, 15, 17, 4, 14, 9, 6, 3, 8, 11, 16, 18, 19, 21, 7, 20]
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
private theorem z5 : ∀ i, 0 ≤ i → i < 3 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 3 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 42 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 42 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_0 : ∀ i, 0 ≤ i → i < 64 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_64 : ∀ i, 64 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 64 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_128 : ∀ i, 128 ≤ i → i < 192 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_192 : ∀ i, 192 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 64 192 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z7_256 : ∀ i, 256 ≤ i → i < 260 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 4 256 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 260 → Z 7 i = true := (range_split (range_split z7_0 z7_64) (range_split z7_128 (range_split z7_192 z7_256)))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_0 : ∀ i, 0 ≤ i → i < 64 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 0 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_64 : ∀ i, 64 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 64 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_128 : ∀ i, 128 ≤ i → i < 192 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 64 128 = true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z8_192 : ∀ i, 192 ≤ i → i < 194 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 2 192 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 194 → Z 8 i = true := (range_split (range_split z8_0 z8_64) (range_split z8_128 z8_192))
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 25 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 25 0 = true)
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

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 13]⟩], 16⟩
theorem wit_mono : PEqualNP.MetaComplexity.Monotone2 wit := by simp [wit, PEqualNP.MetaComplexity.Monotone2]
theorem wit_size : wit.size ≤ 11 := by decide
theorem wit_eval : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = ((fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4008372448) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0))) x := by decide +kernel
theorem hT6 : ∀ r : Fin 64, goal_all.testBit r.val = ((fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4008372448) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0))) (pt6 r.val) := by decide +kernel
theorem lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4008372448) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) t → 11 ≤ t :=
  lower_to_circuit6 (fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4008372448) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) goal_all 11 hT6 (by unfold IsConst; decide) low_63

end PEqualNP.Outside.L_meta_40343_aux

theorem PEqualNP.Outside.L_meta_40343 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4008372448) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809440 * 2 ^ 32 + 4008372448) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s hs
  have hlb : 11 ≤ s := PEqualNP.Outside.L_meta_40343_aux.lower s hs
  exact ⟨PEqualNP.Outside.L_meta_40343_aux.wit, PEqualNP.Outside.L_meta_40343_aux.wit_mono, le_trans PEqualNP.Outside.L_meta_40343_aux.wit_size hlb, PEqualNP.Outside.L_meta_40343_aux.wit_eval⟩
