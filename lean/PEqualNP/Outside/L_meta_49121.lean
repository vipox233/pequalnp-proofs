import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_49121

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def fullMask : Nat := 0xffffffffffffffff

abbrev Masked (mask w : Nat) : Prop := w &&& mask = w

def bsel {α : Type} (c : Bool) (t f : α) : α := Bool.rec f t c

theorem bsel_true {α : Type} (t f : α) : bsel true t f = t := rfl
theorem bsel_false {α : Type} (t f : α) : bsel false t f = f := rfl

theorem beq_false_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem ne_of_beq_false {a b : Nat} (h : Nat.beq a b = false) : a ≠ b := by
  intro e; subst e; rw [Nat.beq_refl] at h; exact Bool.noConfusion h

theorem masked_zero (mask : Nat) : Masked mask 0 := by
  unfold Masked; simp

theorem masked_self (mask : Nat) : Masked mask mask := by
  unfold Masked; simp

theorem masked_land_right (mask w : Nat) : Masked mask (w &&& mask) := by
  unfold Masked; apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and]

theorem masked_xor {mask a b : Nat} (ha : Masked mask a) (hb : Masked mask b) :
    Masked mask (a ^^^ b) := by
  unfold Masked at ha hb ⊢
  apply Nat.eq_of_testBit_eq; intro i
  have ea := congrArg (fun x => x.testBit i) ha
  have eb := congrArg (fun x => x.testBit i) hb
  simp only [Nat.testBit_and, Nat.testBit_xor] at ea eb ⊢
  cases hm : mask.testBit i <;> simp_all

theorem xor_cancel_left (mask v : Nat) : mask ^^^ (mask ^^^ v) = v := by
  apply Nat.eq_of_testBit_eq; intro i; simp

theorem masked_sub_and {mask cut w : Nat} (sub : mask &&& cut = cut) :
    (w &&& mask) &&& cut = w &&& cut := by
  apply Nat.eq_of_testBit_eq; intro i
  have es := congrArg (fun x => x.testBit i) sub
  simp only [Nat.testBit_and] at es ⊢
  cases hc : cut.testBit i <;> simp_all

theorem masked_sub_xor {mask cut w : Nat} (sub : mask &&& cut = cut) :
    (mask ^^^ w) &&& cut = cut ^^^ (w &&& cut) := by
  apply Nat.eq_of_testBit_eq; intro i
  have es := congrArg (fun x => x.testBit i) sub
  simp only [Nat.testBit_and, Nat.testBit_xor] at es ⊢
  cases hc : cut.testBit i <;> simp_all

def canon (mask w : Nat) : Nat :=
  let v := w &&& mask
  bsel (Nat.beq v 0 || Nat.beq v mask) 0
    (let iv := mask ^^^ v; bsel (Nat.blt v iv) v iv)

theorem canon_zero (mask : Nat) : canon mask 0 = 0 := by
  unfold canon; simp [bsel]

theorem canon_self (mask : Nat) : canon mask mask = 0 := by
  unfold canon; simp [bsel]

theorem canon_land (mask w : Nat) : canon mask (w &&& mask) = canon mask w := by
  unfold canon; dsimp only; rw [masked_land_right mask w]

theorem canon_cases (mask w : Nat) :
    (canon mask w = 0 ∧ (w &&& mask = 0 ∨ w &&& mask = mask)) ∨
    (canon mask w ≠ 0 ∧ (canon mask w = w &&& mask ∨ canon mask w = mask ^^^ (w &&& mask))) := by
  unfold canon; dsimp only
  set v := w &&& mask
  by_cases hv0 : v = 0
  · left; rw [hv0]; simp [bsel]
  · by_cases hvm : v = mask
    · left; rw [hvm]; simp [bsel]
    · right
      rw [beq_false_ne hv0, beq_false_ne hvm]
      simp only [Bool.or_false, bsel_false]
      cases hlt : Nat.blt v (mask ^^^ v)
      · rw [bsel_false]
        refine ⟨?_, Or.inr rfl⟩
        intro hz
        have e := congrArg (fun x => mask ^^^ x) hz
        rw [xor_cancel_left] at e
        exact hvm (by simpa using e)
      · rw [bsel_true]; exact ⟨hv0, Or.inl rfl⟩

theorem canon_masked (mask w : Nat) : Masked mask (canon mask w) := by
  rcases canon_cases mask w with ⟨h0, _⟩ | ⟨_, h1 | h2⟩
  · rw [h0]; exact masked_zero mask
  · rw [h1]; exact masked_land_right mask w
  · rw [h2]; exact masked_xor (masked_self mask) (masked_land_right mask w)

theorem canon_xor_mask (mask w : Nat) : canon mask (mask ^^^ w) = canon mask w := by
  have hsub : (mask ^^^ w) &&& mask = mask ^^^ (w &&& mask) := masked_sub_xor (masked_self mask)
  unfold canon; dsimp only
  rw [hsub]
  generalize hv : w &&& mask = v
  set iv := mask ^^^ v
  have hiv : mask ^^^ iv = v := xor_cancel_left mask v
  rw [hiv]
  by_cases hv0 : v = 0
  · have hivm : iv = mask := by simp [iv, hv0]
    rw [hv0, hivm]; simp [bsel]
  · by_cases hvm : v = mask
    · have hiv0 : iv = 0 := by simp [iv, hvm]
      rw [hvm, hiv0]; simp [bsel]
    · have hiv0 : iv ≠ 0 := by
        intro h; apply hvm
        have e := congrArg (fun x => mask ^^^ x) h
        rw [hiv] at e; simpa using e
      have hivm : iv ≠ mask := by
        intro h; apply hv0
        have e := congrArg (fun x => mask ^^^ x) h
        rw [hiv] at e; simpa using e
      rw [beq_false_ne hv0, beq_false_ne hvm, beq_false_ne hiv0, beq_false_ne hivm]
      simp only [Bool.or_false, bsel_false]
      have hne : v ≠ iv := by
        intro h
        have hm0 : mask = 0 := by
          apply Nat.eq_of_testBit_eq; intro i
          have ei := congrArg (fun x => x.testBit i) h
          simp only [iv, Nat.testBit_xor] at ei
          cases hv' : v.testBit i <;> cases hm' : mask.testBit i <;> simp_all
        have : v = 0 := by rw [← hv, hm0]; simp
        exact hv0 this
      by_cases hlt : v < iv
      · have h1 : Nat.blt v iv = true := Nat.blt_eq.mpr hlt
        have h2 : Nat.blt iv v = false := by cases h : Nat.blt iv v; rfl; have := Nat.blt_eq.mp h; omega
        rw [h1, h2, bsel_true, bsel_false]
      · have hgt : iv < v := by omega
        have h1 : Nat.blt v iv = false := by cases h : Nat.blt v iv; rfl; have := Nat.blt_eq.mp h; omega
        have h2 : Nat.blt iv v = true := Nat.blt_eq.mpr hgt
        rw [h1, h2, bsel_false, bsel_true]

theorem canon_idem (mask w : Nat) : canon mask (canon mask w) = canon mask w := by
  rcases canon_cases mask w with ⟨h0, _⟩ | ⟨_, h1 | h2⟩
  · rw [h0, canon_zero]
  · calc canon mask (canon mask w) = canon mask (w &&& mask) := by rw [h1]
      _ = canon mask w := canon_land mask w
  · calc canon mask (canon mask w) = canon mask (mask ^^^ (w &&& mask)) := by rw [h2]
      _ = canon mask (w &&& mask) := canon_xor_mask mask (w &&& mask)
      _ = canon mask w := canon_land mask w

theorem canon_submask {mask cut w : Nat} (sub : mask &&& cut = cut) (hc : canon mask w ≠ 0) :
    canon cut (canon mask w) = canon cut w := by
  rcases canon_cases mask w with ⟨h0, _⟩ | ⟨_, h1 | h2⟩
  · exact absurd h0 hc
  · rw [h1, ← canon_land cut (w &&& mask), masked_sub_and sub, canon_land]
  · rw [h2, ← canon_land cut (mask ^^^ (w &&& mask)), masked_sub_xor sub, masked_sub_and sub]
    rw [← masked_sub_xor (masked_self cut), canon_land, canon_xor_mask]

theorem canon_submask_zero {mask cut w : Nat} (sub : mask &&& cut = cut) (hc : canon mask w = 0) :
    canon cut w = 0 := by
  rcases canon_cases mask w with ⟨_, h0 | hm⟩ | ⟨hne, _⟩
  · rw [← canon_land cut w, ← masked_sub_and sub, h0]; simp [canon_zero]
  · rw [← canon_land cut w, ← masked_sub_and sub, hm, sub, canon_self]
  · exact absurd hc hne

theorem canon_testBit_eq {mask w p n : Nat} (hp : mask.testBit p = true) (hn : mask.testBit n = true) :
    ((canon mask w).testBit p = (canon mask w).testBit n) ↔ (w.testBit p = w.testBit n) := by
  rcases canon_cases mask w with ⟨h0, h1 | h2⟩ | ⟨_, h1 | h2⟩
  · rw [h0]
    have e1 := congrArg (fun x => x.testBit p) h1
    have e2 := congrArg (fun x => x.testBit n) h1
    simp [Nat.testBit_and, hp, hn] at e1 e2 ⊢; simp [e1, e2]
  · rw [h0]
    have e1 := congrArg (fun x => x.testBit p) h2
    have e2 := congrArg (fun x => x.testBit n) h2
    simp [Nat.testBit_and, hp, hn] at e1 e2 ⊢; simp [e1, e2]
  · rw [h1]; simp [Nat.testBit_and, hp, hn]
  · rw [h2]; simp [Nat.testBit_xor, Nat.testBit_and, hp, hn]

def binOp (mask op a b : Nat) : Nat :=
  bsel (Nat.beq op 0) (canon mask (a &&& b))
    (bsel (Nat.beq op 1) (canon mask (a ||| b))
      (bsel (Nat.beq op 2) (canon mask (a &&& (mask ^^^ b)))
        (canon mask ((mask ^^^ a) &&& b))))

theorem binOp_canon (mask op a b : Nat) : canon mask (binOp mask op a b) = binOp mask op a b := by
  unfold binOp
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false] <;> exact canon_idem mask _

theorem binOp_comm (mask op a b : Nat) (hop : op < 4) :
    ∃ op' < 4, binOp mask op a b = binOp mask op' b a := by
  have hland : a &&& b = b &&& a := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  have hlor : a ||| b = b ||| a := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_or, Bool.or_comm]
  have h23 : a &&& (mask ^^^ b) = (mask ^^^ b) &&& a := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  have h32 : (mask ^^^ a) &&& b = b &&& (mask ^^^ a) := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  rcases (show op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 by omega) with rfl | rfl | rfl | rfl
  · exact ⟨0, by omega, by change canon mask (a &&& b) = canon mask (b &&& a); rw [hland]⟩
  · exact ⟨1, by omega, by change canon mask (a ||| b) = canon mask (b ||| a); rw [hlor]⟩
  · exact ⟨3, by omega, by change canon mask (a &&& (mask ^^^ b)) = canon mask ((mask ^^^ b) &&& a); rw [h23]⟩
  · exact ⟨2, by omega, by change canon mask ((mask ^^^ a) &&& b) = canon mask (b &&& (mask ^^^ a)); rw [h32]⟩

theorem binOp_zero_left (mask op b : Nat) : binOp mask op 0 b = 0 ∨ binOp mask op 0 b = canon mask b := by
  unfold binOp
  have hmb : (mask ^^^ 0) &&& b = b &&& mask := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
  · right; rw [hmb, canon_land]
  · left; simp [canon_zero]
  · right; simp
  · right; simp
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]

theorem binOp_zero_right (mask op a : Nat) : binOp mask op a 0 = 0 ∨ binOp mask op a 0 = canon mask a := by
  unfold binOp
  have hma : a &&& (mask ^^^ 0) = a &&& mask := by simp
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
  · left; simp [canon_zero]
  · right; rw [hma, canon_land]
  · right; simp
  · right; simp
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]

theorem binOp_self (mask op a : Nat) : binOp mask op a a = 0 ∨ binOp mask op a a = canon mask a := by
  have h2 : canon mask (a &&& (mask ^^^ a)) = 0 := by
    rw [← canon_land]
    have : (a &&& (mask ^^^ a)) &&& mask = 0 := by
      apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
      cases a.testBit i <;> cases mask.testBit i <;> rfl
    rw [this, canon_zero]
  have h3 : canon mask ((mask ^^^ a) &&& a) = 0 := by
    rw [← canon_land]
    have : ((mask ^^^ a) &&& a) &&& mask = 0 := by
      apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
      cases a.testBit i <;> cases mask.testBit i <;> rfl
    rw [this, canon_zero]
  unfold binOp
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
  · left; exact h3
  · left; exact h2
  · right; simp
  · right; simp
  · right; simp
  · right; simp
  · right; simp
  · right; simp

theorem deMorgan_or_mask {mask a b : Nat} (ha : Masked mask a) (hb : Masked mask b) :
    mask ^^^ (a &&& b) = (mask ^^^ a) ||| (mask ^^^ b) := by
  unfold Masked at ha hb
  apply Nat.eq_of_testBit_eq; intro i
  have ea := congrArg (fun x => x.testBit i) ha
  have eb := congrArg (fun x => x.testBit i) hb
  simp only [Nat.testBit_and] at ea eb
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor]
  cases hm : mask.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all

theorem canon_and_in_binOp (mask x y : Nat) :
    canon mask (x &&& y) = 0 ∨
    canon mask (x &&& y) = canon mask x ∨
    canon mask (x &&& y) = canon mask y ∨
    ∃ op < 4, canon mask (x &&& y) = binOp mask op (canon mask x) (canon mask y) := by
  have hxy : canon mask (x &&& y) = canon mask ((x &&& mask) &&& (y &&& mask)) := by
    rw [← canon_land mask (x &&& y), ← canon_land mask ((x &&& mask) &&& (y &&& mask))]
    congr 1; apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_and]
    cases x.testBit i <;> cases y.testBit i <;> cases mask.testBit i <;> rfl
  rw [hxy]
  have hvxm : Masked mask (x &&& mask) := masked_land_right mask x
  have hvym : Masked mask (y &&& mask) := masked_land_right mask y
  rcases canon_cases mask x with ⟨hx0, hx1 | hx2⟩ | ⟨_, hx1 | hx2⟩
  · left; rw [hx1]; simp [canon_zero]
  · right; right; left; rw [hx2]
    have : mask &&& (y &&& mask) = y &&& mask := by
      apply Nat.eq_of_testBit_eq; intro i
      have e := congrArg (fun t => t.testBit i) hvym
      simp only [Nat.testBit_and] at e ⊢; rw [Bool.and_comm]; exact e
    rw [this, canon_land]
  · rcases canon_cases mask y with ⟨hy0, hy1 | hy2⟩ | ⟨_, hy1 | hy2⟩
    · left; rw [hy1]; simp [canon_zero]
    · right; left; rw [hy2, hvxm, canon_land]
    · right; right; right; refine ⟨0, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask (canon mask x &&& canon mask y)
      rw [hx1, hy1]
    · right; right; right; refine ⟨2, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask (canon mask x &&& (mask ^^^ canon mask y))
      rw [hx1, hy2, xor_cancel_left]
  · rcases canon_cases mask y with ⟨hy0, hy1 | hy2⟩ | ⟨_, hy1 | hy2⟩
    · left; rw [hy1]; simp [canon_zero]
    · right; left; rw [hy2, hvxm, canon_land]
    · right; right; right; refine ⟨3, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask ((mask ^^^ canon mask x) &&& canon mask y)
      rw [hx2, hy1, xor_cancel_left]
    · right; right; right; refine ⟨1, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask (canon mask x ||| canon mask y)
      rw [hx2, hy2, ← deMorgan_or_mask hvxm hvym, canon_xor_mask]

theorem canon_or_in_binOp (mask x y : Nat) :
    canon mask (x ||| y) = 0 ∨
    canon mask (x ||| y) = canon mask x ∨
    canon mask (x ||| y) = canon mask y ∨
    ∃ op < 4, canon mask (x ||| y) = binOp mask op (canon mask x) (canon mask y) := by
  have hxy : canon mask (x ||| y) = canon mask ((mask ^^^ x) &&& (mask ^^^ y)) := by
    rw [← canon_xor_mask mask (x ||| y), ← canon_land mask (mask ^^^ (x ||| y))]
    rw [← canon_land mask ((mask ^^^ x) &&& (mask ^^^ y))]
    congr 1; apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor]
    cases mask.testBit i <;> cases x.testBit i <;> cases y.testBit i <;> rfl
  rw [hxy]
  have h := canon_and_in_binOp mask (mask ^^^ x) (mask ^^^ y)
  rwa [canon_xor_mask, canon_xor_mask] at h

theorem canon_sub_binOp {mask cut op a b : Nat} (sub : mask &&& cut = cut) :
    canon cut (binOp mask op a b) = 0 ∨
    canon cut (binOp mask op a b) = canon cut a ∨
    canon cut (binOp mask op a b) = canon cut b ∨
    ∃ op' < 4, canon cut (binOp mask op a b) = binOp cut op' (canon cut a) (canon cut b) := by
  have go (u : Nat) : canon cut (canon mask u) = canon cut u := by
    by_cases h : canon mask u = 0
    · rw [h, canon_zero, (canon_submask_zero sub h).symm]
    · exact canon_submask sub h
  have hmx1 : canon cut ((mask ^^^ a) &&& b) = canon cut ((cut ^^^ a) &&& b) := by
    rw [← canon_land cut ((mask ^^^ a) &&& b), ← canon_land cut ((cut ^^^ a) &&& b)]
    congr 1; apply Nat.eq_of_testBit_eq; intro i
    have es := congrArg (fun t => t.testBit i) sub
    simp only [Nat.testBit_and] at es
    simp only [Nat.testBit_and, Nat.testBit_xor]
    cases hc : cut.testBit i
    · simp
    · simp only [hc, Bool.and_true] at es ⊢; rw [es]
  have hmx2 : canon cut (a &&& (mask ^^^ b)) = canon cut (a &&& (cut ^^^ b)) := by
    rw [← canon_land cut (a &&& (mask ^^^ b)), ← canon_land cut (a &&& (cut ^^^ b))]
    congr 1; apply Nat.eq_of_testBit_eq; intro i
    have es := congrArg (fun t => t.testBit i) sub
    simp only [Nat.testBit_and] at es
    simp only [Nat.testBit_and, Nat.testBit_xor]
    cases hc : cut.testBit i
    · simp
    · simp only [hc, Bool.and_true] at es ⊢; rw [es]
  have hsub_case1 : canon cut ((cut ^^^ a) &&& b) = 0 ∨ canon cut ((cut ^^^ a) &&& b) = canon cut a ∨
      canon cut ((cut ^^^ a) &&& b) = canon cut b ∨
      ∃ op' < 4, canon cut ((cut ^^^ a) &&& b) = binOp cut op' (canon cut a) (canon cut b) := by
    have h := canon_and_in_binOp cut (cut ^^^ a) b
    rwa [canon_xor_mask] at h
  have hsub_case2 : canon cut (a &&& (cut ^^^ b)) = 0 ∨ canon cut (a &&& (cut ^^^ b)) = canon cut a ∨
      canon cut (a &&& (cut ^^^ b)) = canon cut b ∨
      ∃ op' < 4, canon cut (a &&& (cut ^^^ b)) = binOp cut op' (canon cut a) (canon cut b) := by
    have h := canon_and_in_binOp cut a (cut ^^^ b)
    rwa [canon_xor_mask] at h
  have hbin_eq : binOp mask op a b = canon mask (a &&& b) ∨ binOp mask op a b = canon mask (a ||| b) ∨
      binOp mask op a b = canon mask (a &&& (mask ^^^ b)) ∨ binOp mask op a b = canon mask ((mask ^^^ a) &&& b) := by
    unfold binOp
    cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp [bsel]
  rcases hbin_eq with h | h | h | h <;> rw [h, go]
  · exact canon_and_in_binOp cut a b
  · exact canon_or_in_binOp cut a b
  · rw [hmx2]; exact hsub_case2
  · rw [hmx1]; exact hsub_case1

def Avail (bank : List Nat) (w : Nat) : Prop := w = 0 ∨ w ∈ bank

def GateBin (mask : Nat) (bank : List Nat) (v : Nat) : Prop :=
  ∃ a b op, op < 4 ∧ Avail bank a ∧ Avail bank b ∧ v = binOp mask op a b

def BuildsBin (mask : Nat) (bank : List Nat) : List Nat → Prop
  | [] => True
  | v :: vs => GateBin mask bank v ∧ BuildsBin mask (v :: bank) vs

def LowerBin (mask : Nat) (stock : List Nat) (goal m : Nat) : Prop :=
  ∀ vs, BuildsBin mask stock vs → Avail (vs ++ stock) goal → m ≤ vs.length

theorem avail_weaken {b1 b2 : List Nat} (sub : ∀ w ∈ b1, w ∈ b2) {w : Nat} (h : Avail b1 w) :
    Avail b2 w := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (sub w h)

theorem gate_weaken {mask : Nat} {b1 b2 : List Nat} (sub : ∀ w ∈ b1, w ∈ b2) {v : Nat}
    (h : GateBin mask b1 v) : GateBin mask b2 v := by
  obtain ⟨a, b, op, hop, ha, hb, hv⟩ := h
  exact ⟨a, b, op, hop, avail_weaken sub ha, avail_weaken sub hb, hv⟩

theorem builds_weaken {mask : Nat} {b1 b2 vs : List Nat} (sub : ∀ w ∈ b1, w ∈ b2)
    (h : BuildsBin mask b1 vs) : BuildsBin mask b2 vs := by
  induction vs generalizing b1 b2 with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨gate_weaken sub h.1, ih ?_ h.2⟩
    intro w hw; rcases List.mem_cons.mp hw with rfl | hw
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (sub w hw)

theorem builds_append {mask : Nat} {roots first second : List Nat}
    (h1 : BuildsBin mask roots first) (h2 : BuildsBin mask (first ++ roots) second) :
    BuildsBin mask roots (first ++ second) := by
  induction first generalizing roots with
  | nil => exact h2
  | cons v vs ih =>
    refine ⟨h1.1, ih h1.2 ?_⟩
    exact builds_weaken (fun w hw => by simp only [List.mem_append, List.mem_cons] at hw ⊢; tauto) h2

def dropIf (drop : Bool) (x : Nat) (S : Finset Nat) : Finset Nat :=
  if drop then S.erase x else S

theorem dropIf_subset (drop : Bool) (x : Nat) (S : Finset Nat) : dropIf drop x S ⊆ S := by
  unfold dropIf; split; exact Finset.erase_subset _ _; exact Finset.Subset.refl _

theorem dropIf_card_le (drop : Bool) (x : Nat) (S : Finset Nat) :
    S.card ≤ (dropIf drop x S).card + 1 := by
  unfold dropIf; split
  · by_cases hx : x ∈ S
    · have := Finset.card_erase_add_one hx; omega
    · rw [Finset.erase_eq_of_notMem hx]; omega
  · omega

inductive LiveBin (mask goal : Nat) : Nat → Finset Nat → Prop
  | done : LiveBin mask goal 0 {goal}
  | step {k : Nat} {S : Finset Nat} {a b op : Nat}
      (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hop : op < 4)
      (hz : binOp mask op a b ≠ 0) (hf : binOp mask op a b ∉ S)
      (keepA keepB : Bool) :
      LiveBin mask goal k (insert (binOp mask op a b) (dropIf (!keepA) a (dropIf (!keepB) b S))) →
      LiveBin mask goal (k + 1) S

theorem liveBin_zero_not_mem {mask goal k : Nat} {S : Finset Nat} (hg : goal ≠ 0)
    (h : LiveBin mask goal k S) : 0 ∉ S := by
  induction h with
  | done => simp [hg.symm]
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB _ ih =>
    intro h0; apply ih
    apply Finset.mem_insert_of_mem
    unfold dropIf
    split
    · apply Finset.mem_erase.mpr; refine ⟨ha0.symm, ?_⟩
      split
      · exact Finset.mem_erase.mpr ⟨hb0.symm, h0⟩
      · exact h0
    · split
      · exact Finset.mem_erase.mpr ⟨hb0.symm, h0⟩
      · exact h0

theorem liveBin_card_le {mask goal k : Nat} {S : Finset Nat} (h : LiveBin mask goal k S) :
    S.card ≤ k + 1 := by
  induction h with
  | done => simp
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB _ ih =>
    set z := binOp mask op a b
    have h1 := dropIf_card_le (!keepB) b S
    have h2 := dropIf_card_le (!keepA) a (dropIf (!keepB) b S)
    have hz' : z ∉ dropIf (!keepA) a (dropIf (!keepB) b S) := fun hm =>
      hf (dropIf_subset _ _ _ (dropIf_subset _ _ _ hm))
    have h3 : (insert z (dropIf (!keepA) a (dropIf (!keepB) b S))).card =
        (dropIf (!keepA) a (dropIf (!keepB) b S)).card + 1 := Finset.card_insert_of_notMem hz'
    omega

theorem extractLiveBin_aux {mask goal : Nat} (hg : goal ≠ 0) :
    ∀ (vs bank : List Nat) (k : Nat) (L : Finset Nat),
      BuildsBin mask bank vs → (∀ w ∈ bank, canon mask w = w) →
      L ⊆ (vs ++ bank).toFinset → LiveBin mask goal k L →
      ∃ k' S, k' ≤ k + vs.length ∧ S ⊆ bank.toFinset ∧ LiveBin mask goal k' S
  | [], bank, k, L, _, _, hsub, hlive => ⟨k, L, by simp, hsub, hlive⟩
  | v :: vs, bank, k, L, hbuild, hcb, hsub, hlive => by
    have hcv : canon mask v = v := by
      obtain ⟨a, b, op, _, _, _, rfl⟩ := hbuild.1; exact binOp_canon mask op a b
    have hcb' : ∀ w ∈ v :: bank, canon mask w = w := by
      intro w hw; rcases List.mem_cons.mp hw with rfl | hw; exact hcv; exact hcb w hw
    have hsub' : L ⊆ (vs ++ (v :: bank)).toFinset := by
      intro w hw
      have := hsub hw
      simp only [List.toFinset_append, List.toFinset_cons, Finset.mem_union, Finset.mem_insert] at this ⊢
      tauto
    obtain ⟨k1, L1, hk1, hL1sub, hlive1⟩ := extractLiveBin_aux hg vs (v :: bank) k L hbuild.2 hcb' hsub' hlive
    by_cases hv : v ∈ L1 ∧ v ∉ bank
    · obtain ⟨hvL, hvb⟩ := hv
      have hv0 : v ≠ 0 := fun h0 => liveBin_zero_not_mem hg hlive1 (h0 ▸ hvL)
      obtain ⟨a, b, op, hop, haA, hbA, hvEq⟩ := hbuild.1
      have ha0 : a ≠ 0 := by
        intro h0; subst h0
        rcases binOp_zero_left mask op b with h | h
        · exact hv0 (hvEq.trans h)
        · rcases hbA with rfl | hbM
          · rw [canon_zero] at h; exact hv0 (hvEq.trans h)
          · rw [hcb b hbM] at h; exact hvb ((hvEq.trans h) ▸ hbM)
      have hb0 : b ≠ 0 := by
        intro h0; subst h0
        rcases binOp_zero_right mask op a with h | h
        · exact hv0 (hvEq.trans h)
        · rcases haA with rfl | haM
          · rw [canon_zero] at h; exact hv0 (hvEq.trans h)
          · rw [hcb a haM] at h; exact hvb ((hvEq.trans h) ▸ haM)
      have haM : a ∈ bank := haA.resolve_left ha0
      have hbM : b ∈ bank := hbA.resolve_left hb0
      have hab : a ≠ b := by
        intro h; subst h
        rcases binOp_self mask op a with h0 | ha'
        · exact hv0 (hvEq.trans h0)
        · rw [hcb a haM] at ha'; exact hvb ((hvEq.trans ha') ▸ haM)
      set R := L1.erase v
      set S := insert a (insert b R)
      have hSsub : S ⊆ bank.toFinset := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact List.mem_toFinset.mpr haM
        · rcases Finset.mem_insert.mp hw with rfl | hw
          · exact List.mem_toFinset.mpr hbM
          · have h1 := hL1sub (Finset.mem_of_mem_erase hw)
            simp only [List.toFinset_cons, Finset.mem_insert] at h1
            exact h1.resolve_left (Finset.ne_of_mem_erase hw)
      have hvNotS : v ∉ S := by
        intro hm
        rcases Finset.mem_insert.mp hm with rfl | hm
        · exact hvb haM
        · rcases Finset.mem_insert.mp hm with rfl | hm
          · exact hvb hbM
          · exact (Finset.notMem_erase v L1) hm
      have hL1eq : insert v (dropIf (!(decide (a ∈ R))) a (dropIf (!(decide (b ∈ R))) b S)) = L1 := by
        ext w
        by_cases haR : a ∈ R <;> by_cases hbR : b ∈ R
        · simp only [haR, hbR, decide_true, Bool.not_true, Bool.false_eq_true, dropIf, ite_false, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | rfl | rfl | ⟨_, hw⟩); exact hvL; exact (Finset.mem_erase.mp haR).2; exact (Finset.mem_erase.mp hbR).2; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h; exact Or.inr (Or.inr (Or.inr ⟨h, hw⟩))
        · simp only [haR, hbR, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, dropIf, ite_true, ite_false, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨hwb, rfl | rfl | ⟨_, hw⟩⟩); exact hvL; exact (Finset.mem_erase.mp haR).2; exact absurd rfl hwb; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h
            refine Or.inr ⟨?_, Or.inr (Or.inr ⟨h, hw⟩)⟩
            intro hwb; subst hwb; exact hbR (Finset.mem_erase.mpr ⟨h, hw⟩)
        · simp only [haR, hbR, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, dropIf, ite_true, ite_false, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨hwa, rfl | rfl | ⟨_, hw⟩⟩); exact hvL; exact absurd rfl hwa; exact (Finset.mem_erase.mp hbR).2; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h
            refine Or.inr ⟨?_, Or.inr (Or.inr ⟨h, hw⟩)⟩
            intro hwa; subst hwa; exact haR (Finset.mem_erase.mpr ⟨h, hw⟩)
        · simp only [haR, hbR, decide_false, Bool.not_false, dropIf, ite_true, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨hwa, hwb, rfl | rfl | ⟨_, hw⟩⟩); exact hvL; exact absurd rfl hwa; exact absurd rfl hwb; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h
            refine Or.inr ⟨?_, ?_, Or.inr (Or.inr ⟨h, hw⟩)⟩
            · intro hwa; subst hwa; exact haR (Finset.mem_erase.mpr ⟨h, hw⟩)
            · intro hwb; subst hwb; exact hbR (Finset.mem_erase.mpr ⟨h, hw⟩)
      refine ⟨k1 + 1, S, by simp only [List.length_cons]; omega, hSsub, ?_⟩
      apply LiveBin.step (a := a) (b := b) (op := op)
        (Finset.mem_insert_self a _) (Finset.mem_insert_of_mem (Finset.mem_insert_self b _))
        hab ha0 hb0 hop (hvEq ▸ hv0) (hvEq ▸ hvNotS) (decide (a ∈ R)) (decide (b ∈ R))
      rw [← hvEq, hL1eq]; exact hlive1
    · refine ⟨k1, L1, by simp only [List.length_cons]; omega, ?_, hlive1⟩
      intro w hw
      have h1 := hL1sub hw
      simp only [List.toFinset_cons, Finset.mem_insert] at h1
      rcases h1 with rfl | h1
      · have hvb : w ∈ bank := by by_contra hnb; exact hv ⟨hw, hnb⟩
        exact List.mem_toFinset.mpr hvb
      · exact h1

theorem extractLiveBin {mask goal : Nat} {stock vs : List Nat}
    (hg : goal ≠ 0) (hcs : ∀ w ∈ stock, canon mask w = w)
    (hbuild : BuildsBin mask stock vs) (hhit : Avail (vs ++ stock) goal) :
    ∃ k S, k ≤ vs.length ∧ S ⊆ stock.toFinset ∧ LiveBin mask goal k S := by
  have hmem : goal ∈ vs ++ stock := hhit.resolve_left hg
  have hsub : ({goal} : Finset Nat) ⊆ (vs ++ stock).toFinset := by
    intro w hw; rw [Finset.mem_singleton.mp hw]; exact List.mem_toFinset.mpr hmem
  obtain ⟨k, S, hk, hS, hL⟩ := extractLiveBin_aux hg vs stock 0 {goal} hbuild hcs hsub LiveBin.done
  exact ⟨k, S, by omega, hS, hL⟩

theorem liveBin_agrees {mask goal k p n : Nat} {S : Finset Nat}
    (hp : mask.testBit p = true) (hn : mask.testBit n = true)
    (h : LiveBin mask goal k S) (hag : ∀ w ∈ S, w.testBit p = w.testBit n) :
    goal.testBit p = goal.testBit n := by
  induction h with
  | done => exact hag goal (Finset.mem_singleton_self goal)
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB _ ih =>
    apply ih; intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · have ea := hag a ha
      have eb := hag b hb
      unfold binOp
      cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
      all_goals rw [canon_testBit_eq hp hn]
      all_goals simp [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, hp, hn, ea, eb]
    · exact hag w (dropIf_subset _ _ _ (dropIf_subset _ _ _ hw))

def forceW {α : Type} (w : Nat) (k : Nat → α) : α :=
  Nat.rec (k 0) (fun m _ => k (m + 1)) w

theorem forceW_eq {α : Type} (w : Nat) (k : Nat → α) : forceW w k = k w := by
  cases w <;> rfl

def forceWs (ws : List Nat) (k : List Nat → Bool) : Bool :=
  (List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k [])
    (fun w _ next k => forceW w (fun v => next (fun rest => k (v :: rest)))) ws) k

theorem forceWs_eq (ws : List Nat) (k : List Nat → Bool) : forceWs ws k = k ws := by
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih =>
    change forceW w (fun v => forceWs ws (fun rest => k (v :: rest))) = _
    rw [forceW_eq, ih]

def dagPart (ws : List Nat) : Nat → Nat → Bool :=
  List.rec
    (fun p n => Nat.beq p 0 || Nat.beq n 0)
    (fun w _ rest p n =>
      (Nat.beq p 0 || Nat.beq n 0) ||
        forceW (p &&& w) (fun up =>
          forceW (n &&& w) (fun down =>
            rest up down &&
              forceW (p ^^^ up) (fun offP =>
                forceW (n ^^^ down) (rest offP))))) ws

theorem offBits {v w i : Nat} (h : (v ^^^ (v &&& w)).testBit i = true) :
    v.testBit i = true ∧ w.testBit i = false := by
  rw [Nat.testBit_xor, Nat.testBit_and] at h
  cases hv : v.testBit i <;> cases hw : w.testBit i <;> simp [hv, hw] at h ⊢

theorem dagPart_sound {ws : List Nat} {pos neg : Nat} (fail : dagPart ws pos neg = false) :
    ∃ p n, pos.testBit p = true ∧ neg.testBit n = true ∧ ∀ w ∈ ws, w.testBit p = w.testBit n := by
  have nonempty {w : Nat} (hn : w ≠ 0) : ∃ j, w.testBit j = true := by
    by_contra! all; apply hn; apply Nat.eq_of_testBit_eq; intro i; simp [all i]
  induction ws generalizing pos neg with
  | nil =>
    change (Nat.beq pos 0 || Nat.beq neg 0) = false at fail
    simp only [Bool.or_eq_false_iff] at fail
    obtain ⟨p, hp⟩ := nonempty (ne_of_beq_false fail.1)
    obtain ⟨n, hn⟩ := nonempty (ne_of_beq_false fail.2)
    exact ⟨p, n, hp, hn, by simp⟩
  | cons w ws ih =>
    change ((Nat.beq pos 0 || Nat.beq neg 0) ||
      forceW (pos &&& w) (fun up =>
        forceW (neg &&& w) (fun down =>
          dagPart ws up down &&
            forceW (pos ^^^ up) (fun offP =>
              forceW (neg ^^^ down) (dagPart ws offP))))) = false at fail
    simp only [forceW_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at fail
    rcases fail.2 with on | off
    · obtain ⟨p, n, hp, hn, ag⟩ := ih on
      rw [Nat.testBit_and, Bool.and_eq_true] at hp hn
      refine ⟨p, n, hp.1, hn.1, fun a ha => ?_⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · rw [hp.2, hn.2]
      · exact ag a ha
    · obtain ⟨p, n, hp, hn, ag⟩ := ih off
      have hp' := offBits hp
      have hn' := offBits hn
      refine ⟨p, n, hp'.1, hn'.1, fun a ha => ?_⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · rw [hp'.2, hn'.2]
      · exact ag a ha

theorem dagPart_live {mask goal k : Nat} {ws : List Nat}
    (hgm : Masked mask goal) (hlive : LiveBin mask goal k ws.toFinset) :
    dagPart ws goal (mask ^^^ goal) = true := by
  by_contra hf
  have hfalse : dagPart ws goal (mask ^^^ goal) = false := by
    cases h : dagPart ws goal (mask ^^^ goal) <;> simp_all
  obtain ⟨p, n, hp, hn, ag⟩ := dagPart_sound hfalse
  have hpm : mask.testBit p = true := by
    have e := congrArg (fun x => x.testBit p) hgm
    simp only [Nat.testBit_and, hp, Bool.true_and] at e; exact e
  have hnm : mask.testBit n = true ∧ goal.testBit n = false := by
    rw [Nat.testBit_xor] at hn
    have imp : goal.testBit n = true → mask.testBit n = true := by
      intro hg
      have e := congrArg (fun x => x.testBit n) hgm
      simp only [Nat.testBit_and, hg, Bool.true_and] at e; exact e
    cases hm : mask.testBit n <;> cases hg : goal.testBit n <;> simp_all
  have eq := liveBin_agrees hpm hnm.1 hlive (fun w hw => ag w (List.mem_toFinset.mp hw))
  rw [hp, hnm.2] at eq; exact Bool.noConfusion eq

def flatSet (cut : Nat) (S : Finset Nat) : Finset Nat :=
  S.filter (fun w => Nat.beq (canon cut w) 0)

theorem flatSet_insert_notMem {cut w : Nat} {S : Finset Nat} (hw : w ∉ S) :
    (flatSet cut (insert w S)).card =
      if canon cut w = 0 then (flatSet cut S).card + 1 else (flatSet cut S).card := by
  unfold flatSet
  rw [Finset.filter_insert]
  by_cases hc : canon cut w = 0
  · simp only [hc, Nat.beq_refl, ite_true]
    exact Finset.card_insert_of_notMem (fun h => hw (Finset.mem_filter.mp h).1)
  · simp only [beq_false_ne hc, Bool.false_eq_true, ite_false, hc]

theorem flatSet_erase {cut w : Nat} {S : Finset Nat} :
    (flatSet cut S).card ≤ (flatSet cut (S.erase w)).card + (if canon cut w = 0 then 1 else 0) := by
  unfold flatSet
  rw [Finset.filter_erase]
  by_cases hm : w ∈ S.filter (fun x => Nat.beq (canon cut x) 0)
  · have hcw : canon cut w = 0 := Nat.eq_of_beq_eq_true (Finset.mem_filter.mp hm).2
    have hcard := Finset.card_erase_add_one hm
    simp only [hcw, ite_true]; omega
  · rw [Finset.erase_eq_of_notMem hm]; omega

theorem maskedBuildBin {mask cut goal k : Nat} {S : Finset Nat}
    (sub : mask &&& cut = cut) (hgnf : canon cut goal ≠ 0)
    (h : LiveBin mask goal k S) :
    ∀ (bank : List Nat), (∀ w ∈ S, Avail bank (canon cut w)) →
      ∃ vs, vs.length + (flatSet cut S).card ≤ k ∧ BuildsBin cut bank vs ∧
        Avail (vs ++ bank) (canon cut goal) := by
  induction h with
  | done =>
    intro bank hsup
    have hfl : (flatSet cut {goal}).card = 0 := by
      unfold flatSet
      simp [hgnf]
    exact ⟨[], by simp [hfl], trivial, hsup goal (Finset.mem_singleton_self goal)⟩
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB tail ih =>
    intro bank hsup
    set z := binOp mask op a b
    set S1 := dropIf (!keepB) b S
    set S2 := dropIf (!keepA) a S1
    set S' := insert z S2
    have hS2sub : S2 ⊆ S := Finset.Subset.trans (dropIf_subset _ _ _) (dropIf_subset _ _ _)
    have hzNotS2 : z ∉ S2 := fun hm => hf (hS2sub hm)
    have hfl1 : (flatSet cut S).card ≤ (flatSet cut S1).card + (if canon cut b = 0 then 1 else 0) := by
      unfold S1 dropIf; split; exact flatSet_erase; omega
    have hfl2 : (flatSet cut S1).card ≤ (flatSet cut S2).card + (if canon cut a = 0 then 1 else 0) := by
      unfold S2 dropIf; split; exact flatSet_erase; omega
    have hfl3 : (flatSet cut S').card =
        if canon cut z = 0 then (flatSet cut S2).card + 1 else (flatSet cut S2).card :=
      flatSet_insert_notMem hzNotS2
    have hcz : canon cut z = 0 ∨ canon cut z = canon cut a ∨ canon cut z = canon cut b ∨
        ∃ op' < 4, canon cut z = binOp cut op' (canon cut a) (canon cut b) :=
      canon_sub_binOp sub
    by_cases hfa : canon cut a = 0
    · by_cases hfb : canon cut b = 0
      · have hfz : canon cut z = 0 := by
          rcases hcz with h | h | h | ⟨op', _, h⟩
          · exact h
          · exact h.trans hfa
          · exact h.trans hfb
          · rw [hfa, hfb] at h
            rcases binOp_zero_left cut op' 0 with h0 | h0
            · exact h.trans h0
            · exact h.trans (h0.trans (canon_zero cut))
        have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact Or.inl hfz
          · exact hsup w (hS2sub hw)
        obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
        simp only [hfa, hfb, hfz, ite_true] at hfl1 hfl2 hfl3
        exact ⟨vs, by omega, hbd, hhit⟩
      · have hfz : canon cut z = 0 ∨ canon cut z = canon cut b := by
          rcases hcz with h | h | h | ⟨op', _, h⟩
          · exact Or.inl h
          · exact Or.inl (h.trans hfa)
          · exact Or.inr h
          · rw [hfa] at h
            rcases binOp_zero_left cut op' (canon cut b) with h0 | h0
            · exact Or.inl (h.trans h0)
            · exact Or.inr (h.trans (h0.trans (canon_idem cut b)))
        have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · rcases hfz with h0 | hb'
            · exact Or.inl h0
            · rw [hb']; exact hsup b hb
          · exact hsup w (hS2sub hw)
        obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
        simp only [hfa, hfb, ite_true, ite_false] at hfl1 hfl2
        have : (flatSet cut S2).card ≤ (flatSet cut S').card := by split at hfl3 <;> omega
        exact ⟨vs, by omega, hbd, hhit⟩
    · by_cases hfb : canon cut b = 0
      · have hfz : canon cut z = 0 ∨ canon cut z = canon cut a := by
          rcases hcz with h | h | h | ⟨op', _, h⟩
          · exact Or.inl h
          · exact Or.inr h
          · exact Or.inl (h.trans hfb)
          · rw [hfb] at h
            rcases binOp_zero_right cut op' (canon cut a) with h0 | h0
            · exact Or.inl (h.trans h0)
            · exact Or.inr (h.trans (h0.trans (canon_idem cut a)))
        have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · rcases hfz with h0 | ha'
            · exact Or.inl h0
            · rw [ha']; exact hsup a ha
          · exact hsup w (hS2sub hw)
        obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
        simp only [hfa, hfb, ite_true, ite_false] at hfl1 hfl2
        have : (flatSet cut S2).card ≤ (flatSet cut S').card := by split at hfl3 <;> omega
        exact ⟨vs, by omega, hbd, hhit⟩
      · simp only [hfa, hfb, ite_false] at hfl1 hfl2
        have hfl_le : (flatSet cut S).card ≤ (flatSet cut S').card := by split at hfl3 <;> omega
        rcases hcz with h0 | ha' | hb' | ⟨op', hop', hbin⟩
        · have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · exact Or.inl h0
            · exact hsup w (hS2sub hw)
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
          exact ⟨vs, by omega, hbd, hhit⟩
        · have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · rw [ha']; exact hsup a ha
            · exact hsup w (hS2sub hw)
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
          exact ⟨vs, by omega, hbd, hhit⟩
        · have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · rw [hb']; exact hsup b hb
            · exact hsup w (hS2sub hw)
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
          exact ⟨vs, by omega, hbd, hhit⟩
        · set cz := canon cut z
          have hgate : GateBin cut bank cz := ⟨canon cut a, canon cut b, op', hop', hsup a ha, hsup b hb, hbin⟩
          have hsup' : ∀ w ∈ S', Avail (cz :: bank) (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · exact Or.inr List.mem_cons_self
            · exact avail_weaken (fun u hu => List.mem_cons_of_mem _ hu) (hsup w (hS2sub hw))
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih (cz :: bank) hsup'
          refine ⟨cz :: vs, by simp only [List.length_cons]; omega, ⟨hgate, hbd⟩, ?_⟩
          exact avail_weaken (fun u hu => by simp only [List.mem_append, List.mem_cons] at hu ⊢; tauto) hhit

def flatCount (cut : Nat) (ws : List Nat) : Nat :=
  List.rec 0 (fun w _ cnt => bsel (Nat.beq (canon cut w) 0) (cnt + 1) cnt) ws

theorem flatCount_card (cut : Nat) {ws : List Nat} (nd : ws.Nodup) :
    flatCount cut ws = (flatSet cut ws.toFinset).card := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have hnd := List.nodup_cons.mp nd
    have fresh : w ∉ ws.toFinset := by simpa using hnd.1
    change bsel (Nat.beq (canon cut w) 0) (flatCount cut ws + 1) (flatCount cut ws) = _
    rw [List.toFinset_cons, flatSet_insert_notMem fresh, ih hnd.2]
    by_cases hc : canon cut w = 0
    · simp [hc, bsel]
    · rw [beq_false_ne hc, bsel_false]; simp [hc]

def availB (bank : List Nat) (w : Nat) : Bool :=
  Nat.beq w 0 || bank.contains w

theorem availB_spec {bank : List Nat} {w : Nat} : availB bank w = true ↔ Avail bank w := by
  unfold availB Avail; simp [Nat.beq_eq]

def recipeGateBin (cut : Nat) (bank : List Nat) (vc ac bc : Nat) : Bool :=
  availB bank ac && availB bank bc &&
    (Nat.beq vc (binOp cut 0 ac bc) || Nat.beq vc (binOp cut 1 ac bc) ||
     Nat.beq vc (binOp cut 2 ac bc) || Nat.beq vc (binOp cut 3 ac bc))

theorem recipeGateBin_spec {cut : Nat} {bank : List Nat} {vc ac bc : Nat}
    (h : recipeGateBin cut bank vc ac bc = true) : GateBin cut bank vc := by
  unfold recipeGateBin at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq, availB_spec] at h
  obtain ⟨⟨ha, hb⟩, ((h0 | h1) | h2) | h3⟩ := h
  · exact ⟨ac, bc, 0, by omega, ha, hb, h0⟩
  · exact ⟨ac, bc, 1, by omega, ha, hb, h1⟩
  · exact ⟨ac, bc, 2, by omega, ha, hb, h2⟩
  · exact ⟨ac, bc, 3, by omega, ha, hb, h3⟩

def addUniq (w : Nat) (l : List Nat) : List Nat :=
  if l.contains w then l else w :: l

def recipeStart (cut : Nat) (stock ws : List Nat) : List Nat :=
  List.rec [] (fun w _ acc =>
    let v := canon cut w
    if availB stock v then acc else addUniq v acc) ws

def recipeClose (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun (w, a, b) _ next acc =>
      let v := canon cut w
      if acc.contains v then
        let va := canon cut a
        let vb := canon cut b
        let acc1 := if availB stock va then acc else addUniq va acc
        let acc2 := if availB stock vb then acc1 else addUniq vb acc1
        next acc2
      else next acc) hist needed

def replayRec (cut : Nat) (needed : List Nat) (hist : List (Nat × Nat × Nat)) (bank : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun _ => [])
    (fun (w, a, b) _ next bank =>
      let v := canon cut w
      if needed.contains v && !(availB bank v) && recipeGateBin cut bank v (canon cut a) (canon cut b) then
        v :: next (v :: bank)
      else next bank) hist bank

theorem replayRec_builds (cut : Nat) (needed : List Nat) (hist : List (Nat × Nat × Nat)) (bank : List Nat) :
    BuildsBin cut bank (replayRec cut needed hist bank) := by
  induction hist generalizing bank with
  | nil => trivial
  | cons rec hist ih =>
    obtain ⟨w, a, b⟩ := rec
    change BuildsBin cut bank
      (if needed.contains (canon cut w) && !(availB bank (canon cut w)) &&
          recipeGateBin cut bank (canon cut w) (canon cut a) (canon cut b) then
        canon cut w :: replayRec cut needed hist (canon cut w :: bank)
      else replayRec cut needed hist bank)
    split
    · rename_i hyes
      exact ⟨recipeGateBin_spec (Bool.and_eq_true_iff.mp hyes).2, ih _⟩
    · exact ih _

def boundCloses (target : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat))
    (bound : Nat × List Nat × Nat × Nat) : Bool :=
  let (cut, stock, lower, goal) := bound
  let (fuel, ws, hist) := state
  Nat.beq (canon cut target) goal && !(Nat.beq goal 0) &&
    forceW (fuel - flatCount cut ws) (fun rem =>
      if Nat.blt rem lower then
        forceWs (recipeStart cut stock ws) (fun start =>
          if Nat.blt (start.length + rem) lower then
            forceWs (recipeClose cut stock hist start) (fun needed =>
              if Nat.blt (needed.length + rem) lower then
                forceWs (replayRec cut needed hist.reverse stock) (fun replay =>
                  Nat.blt (replay.length + rem) lower &&
                    ws.all (fun w => availB (replay ++ stock) (canon cut w)))
              else false)
          else false)
      else false)

def knownCloses (target : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  List.rec false (fun b _ rest => boundCloses target state b || rest) bounds

def KnownBin (bounds : List (Nat × List Nat × Nat × Nat)) : Prop :=
  ∀ b ∈ bounds, LowerBin b.1 b.2.1 b.2.2.2 b.2.2.1

theorem boundCloses_sound {mask goal : Nat} {state : Nat × List Nat × List (Nat × Nat × Nat)}
    {bound : Nat × List Nat × Nat × Nat}
    (hlow : LowerBin bound.1 bound.2.1 bound.2.2.2 bound.2.2.1)
    (sub : mask &&& bound.1 = bound.1)
    (nd : state.2.1.Nodup) {k : Nat} (hk : k ≤ state.1)
    (hlive : LiveBin mask goal k state.2.1.toFinset) :
    boundCloses goal state bound = false := by
  obtain ⟨fuel, ws, hist⟩ := state
  obtain ⟨cut, stock, lower, bgoal⟩ := bound
  dsimp only at hlow sub nd hk hlive
  apply Bool.eq_false_iff.mpr
  intro hc
  unfold boundCloses at hc
  simp only [forceW_eq, forceWs_eq, Bool.and_eq_true, Nat.beq_eq, Bool.not_eq_true'] at hc
  obtain ⟨⟨hgeq, hgnz⟩, scan⟩ := hc
  have hgnz' : bgoal ≠ 0 := ne_of_beq_false hgnz
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  simp only [Bool.and_eq_true, Nat.blt_eq] at scan
  obtain ⟨hlen, hsrc⟩ := scan
  set replay := replayRec cut (recipeClose cut stock hist (recipeStart cut stock ws)) hist.reverse stock
  have hgnf : canon cut goal ≠ 0 := hgeq.symm ▸ hgnz'
  have hsup : ∀ w ∈ ws.toFinset, Avail (replay ++ stock) (canon cut w) := by
    intro w hw
    exact availB_spec.mp (List.all_eq_true.mp hsrc w (List.mem_toFinset.mp hw))
  obtain ⟨ys, hylen, hybd, hyhit⟩ := maskedBuildBin sub hgnf hlive (replay ++ stock) hsup
  rw [← flatCount_card cut nd] at hylen
  have hboth := builds_append (replayRec_builds cut _ hist.reverse stock) hybd
  have hfinal : Avail ((replay ++ ys) ++ stock) bgoal := by
    rw [← hgeq]
    exact avail_weaken (fun u hu => by simp only [List.mem_append] at hu ⊢; tauto) hyhit
  have heno := hlow (replay ++ ys) hboth hfinal
  simp only [List.length_append] at heno
  omega

theorem knownCloses_sound {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    {state : Nat × List Nat × List (Nat × Nat × Nat)}
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (nd : state.2.1.Nodup) {k : Nat} (hk : k ≤ state.1)
    (hlive : LiveBin mask goal k state.2.1.toFinset) :
    knownCloses goal bounds state = false := by
  induction bounds with
  | nil => rfl
  | cons b bs ih =>
    change (boundCloses goal state b || knownCloses goal bs state) = false
    rw [boundCloses_sound (hknown b List.mem_cons_self) (hsub b List.mem_cons_self) nd hk hlive]
    exact ih (fun x hx => hknown x (List.mem_cons_of_mem _ hx)) (fun x hx => hsub x (List.mem_cons_of_mem _ hx))

def insertSorted (x : Nat) (l : List Nat) : List Nat :=
  List.rec [x] (fun y ys ih => bsel (Nat.ble x y) (x :: y :: ys) (y :: ih)) l

theorem insertSorted_mem {x w : Nat} {l : List Nat} :
    w ∈ insertSorted x l ↔ w = x ∨ w ∈ l := by
  induction l with
  | nil => simp [insertSorted]
  | cons y ys ih =>
    change w ∈ bsel (Nat.ble x y) (x :: y :: ys) (y :: insertSorted x ys) ↔ _
    cases Nat.ble x y
    · rw [bsel_false]; simp only [List.mem_cons, ih]; tauto
    · rw [bsel_true]; simp only [List.mem_cons]

theorem insertSorted_nodup {x : Nat} {l : List Nat} (hx : x ∉ l) (nd : l.Nodup) :
    (insertSorted x l).Nodup := by
  induction l with
  | nil => simp [insertSorted]
  | cons y ys ih =>
    have hnd := List.nodup_cons.mp nd
    have hxy : x ≠ y := fun h => hx (h ▸ List.mem_cons_self)
    have hxs : x ∉ ys := fun h => hx (List.mem_cons_of_mem _ h)
    change (bsel (Nat.ble x y) (x :: y :: ys) (y :: insertSorted x ys)).Nodup
    cases Nat.ble x y
    · rw [bsel_false]
      apply List.nodup_cons.mpr
      refine ⟨fun hm => ?_, ih hxs hnd.2⟩
      rcases insertSorted_mem.mp hm with h | h
      · exact hxy h.symm
      · exact hnd.1 h
    · rw [bsel_true]; exact List.nodup_cons.mpr ⟨hx, nd⟩

def dropVal (drop : Bool) (x : Nat) (l : List Nat) : List Nat :=
  bsel drop (List.rec [] (fun y _ ih => bsel (Nat.beq y x) ih (y :: ih)) l) l

theorem dropVal_mem {drop : Bool} {x w : Nat} {l : List Nat} :
    w ∈ dropVal drop x l ↔ w ∈ l ∧ (drop = true → w ≠ x) := by
  cases drop
  · simp [dropVal, bsel]
  · induction l with
    | nil => simp [dropVal, bsel]
    | cons y ys ih =>
      change w ∈ bsel (Nat.beq y x) (dropVal true x ys) (y :: dropVal true x ys) ↔ _
      cases hb : Nat.beq y x
      · rw [bsel_false]
        have hne : y ≠ x := ne_of_beq_false hb
        simp only [List.mem_cons, ih, true_implies]
        constructor
        · rintro (rfl | ⟨hw, hwx⟩); exact ⟨Or.inl rfl, hne⟩; exact ⟨Or.inr hw, hwx⟩
        · rintro ⟨rfl | hw, hwx⟩; exact Or.inl rfl; exact Or.inr ⟨hw, hwx⟩
      · rw [bsel_true]
        have heq : y = x := Nat.eq_of_beq_eq_true hb
        subst heq
        simp only [List.mem_cons, ih, true_implies]
        constructor
        · rintro ⟨hw, hwx⟩; exact ⟨Or.inr hw, hwx⟩
        · rintro ⟨rfl | hw, hwx⟩; exact absurd rfl hwx; exact ⟨hw, hwx⟩

theorem dropVal_nodup {drop : Bool} {x : Nat} {l : List Nat} (nd : l.Nodup) :
    (dropVal drop x l).Nodup := by
  cases drop
  · exact nd
  · induction l with
    | nil => simp [dropVal, bsel]
    | cons y ys ih =>
      have hnd := List.nodup_cons.mp nd
      change (bsel (Nat.beq y x) (dropVal true x ys) (y :: dropVal true x ys)).Nodup
      cases Nat.beq y x
      · rw [bsel_false]
        exact List.nodup_cons.mpr ⟨fun hm => hnd.1 (dropVal_mem.mp hm).1, ih hnd.2⟩
      · rw [bsel_true]; exact ih hnd.2

theorem dropVal_toFinset (drop : Bool) (x : Nat) (l : List Nat) :
    (dropVal drop x l).toFinset = dropIf drop x l.toFinset := by
  ext w; simp only [List.mem_toFinset, dropVal_mem, dropIf]
  cases drop <;> simp [Finset.mem_erase, and_comm]

def subsetWords (stock : List Nat) (bits : Nat) : List Nat :=
  (List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun w _ ih b =>
      let rest := ih (b >>> 1)
      bsel (Nat.beq (b &&& 1) 1) (insertSorted w rest) rest) stock) bits

theorem subsetWords_subset (stock : List Nat) (bits : Nat) :
    ∀ w ∈ subsetWords stock bits, w ∈ stock := by
  induction stock generalizing bits with
  | nil => intro w hw; simp [subsetWords] at hw
  | cons x xs ih =>
    intro w hw
    change w ∈ bsel (Nat.beq (bits &&& 1) 1)
      (insertSorted x (subsetWords xs (bits >>> 1))) (subsetWords xs (bits >>> 1)) at hw
    cases hb : Nat.beq (bits &&& 1) 1
    · rw [hb, bsel_false] at hw; exact List.mem_cons_of_mem _ (ih _ w hw)
    · rw [hb, bsel_true] at hw
      rcases insertSorted_mem.mp hw with rfl | hm
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih _ w hm)

theorem subsetWords_nodup {stock : List Nat} (nd : stock.Nodup) (bits : Nat) :
    (subsetWords stock bits).Nodup := by
  induction stock generalizing bits with
  | nil => simp [subsetWords]
  | cons x xs ih =>
    have hnd := List.nodup_cons.mp nd
    change (bsel (Nat.beq (bits &&& 1) 1)
      (insertSorted x (subsetWords xs (bits >>> 1))) (subsetWords xs (bits >>> 1))).Nodup
    cases Nat.beq (bits &&& 1) 1
    · rw [bsel_false]; exact ih hnd.2 _
    · rw [bsel_true]; exact insertSorted_nodup (fun hm => hnd.1 (subsetWords_subset xs _ x hm)) (ih hnd.2 _)

theorem exists_subsetToken (stock : List Nat) (S : Finset Nat) :
    ∃ bits < 2 ^ stock.length, (subsetWords stock bits).toFinset = S ∩ stock.toFinset := by
  induction stock with
  | nil => exact ⟨0, by simp, by simp [subsetWords]⟩
  | cons x xs ih =>
    obtain ⟨b, hb, heq⟩ := ih
    by_cases hx : x ∈ S
    · refine ⟨2 * b + 1, by simp only [List.length_cons, Nat.pow_succ]; omega, ?_⟩
      have hdiv : (2 * b + 1) >>> 1 = b := by change (2 * b + 1) / 2 = b; omega
      have hmod : ((2 * b + 1) &&& 1) = 1 := by rw [Nat.and_one_is_mod]; omega
      change (bsel (Nat.beq ((2 * b + 1) &&& 1) 1)
        (insertSorted x (subsetWords xs ((2 * b + 1) >>> 1)))
        (subsetWords xs ((2 * b + 1) >>> 1))).toFinset = _
      rw [hdiv, hmod, Nat.beq_refl, bsel_true]
      ext w; simp only [List.mem_toFinset, insertSorted_mem, Finset.mem_inter, List.toFinset_cons, Finset.mem_insert]
      have hw : w ∈ subsetWords xs b ↔ w ∈ S ∧ w ∈ xs := by
        have e := congrArg (fun t => w ∈ t) heq; simpa [List.mem_toFinset] using e
      rw [hw]; constructor
      · rintro (rfl | ⟨hs, hxs⟩); exact ⟨hx, Or.inl rfl⟩; exact ⟨hs, Or.inr hxs⟩
      · rintro ⟨hs, rfl | hxs⟩; exact Or.inl rfl; exact Or.inr ⟨hs, hxs⟩
    · refine ⟨2 * b, by simp only [List.length_cons, Nat.pow_succ]; omega, ?_⟩
      have hdiv : (2 * b) >>> 1 = b := by change (2 * b) / 2 = b; omega
      have hmod : ((2 * b) &&& 1) = 0 := by rw [Nat.and_one_is_mod]; omega
      change (bsel (Nat.beq ((2 * b) &&& 1) 1)
        (insertSorted x (subsetWords xs ((2 * b) >>> 1)))
        (subsetWords xs ((2 * b) >>> 1))).toFinset = _
      rw [hdiv, hmod]
      change (subsetWords xs b).toFinset = _
      ext w; simp only [List.mem_toFinset, Finset.mem_inter, List.toFinset_cons, Finset.mem_insert]
      have hw : w ∈ subsetWords xs b ↔ w ∈ S ∧ w ∈ xs := by
        have e := congrArg (fun t => w ∈ t) heq; simpa [List.mem_toFinset] using e
      rw [hw]; constructor
      · rintro ⟨hs, hxs⟩; exact ⟨hs, Or.inr hxs⟩
      · rintro ⟨hs, rfl | hxs⟩; exact absurd hs hx; exact ⟨hs, hxs⟩

def rootState (stock : List Nat) (fuel token : Nat) : Nat × List Nat × List (Nat × Nat × Nat) :=
  (fuel, subsetWords stock token, [])

def makeToken (a b op keep : Nat) : Nat := ((a * 16 + b) * 4 + op) * 4 + keep

def childState (mask token : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  let (fuel, ws, hist) := state
  let keep := token &&& 3
  let op := (token >>> 2) &&& 3
  let b := (token >>> 4) &&& 15
  let a := token >>> 8
  if Nat.beq fuel 0 || !(Nat.blt a b) || !(Nat.blt b ws.length) then none
  else
    let x := ws.getD a 0
    let y := ws.getD b 0
    let z := binOp mask op x y
    if Nat.beq z 0 || ws.contains z then none
    else
      let keepA := Nat.beq (keep &&& 1) 1
      let keepB := Nat.beq ((keep >>> 1) &&& 1) 1
      let rest := dropVal (!keepA) x (dropVal (!keepB) y ws)
      some (fuel - 1, insertSorted z rest, (z, x, y) :: hist)

theorem childState_wf {mask token : Nat} {st ch : Nat × List Nat × List (Nat × Nat × Nat)}
    (nd : st.2.1.Nodup) (h : childState mask token st = some ch) :
    ch.1 < st.1 ∧ ch.2.1.Nodup := by
  obtain ⟨fuel, ws, hist⟩ := st
  dsimp only at nd
  unfold childState at h; dsimp only at h
  split at h
  · contradiction
  · rename_i hok
    split at h
    · contradiction
    · rename_i hfresh
      have heq := Option.some.inj h
      subst ch
      simp only [Bool.or_eq_true, Nat.beq_eq, Bool.not_eq_true'] at hok hfresh
      have hfpos : fuel ≠ 0 := fun hf => hok (Or.inl (Or.inl hf))
      have hznot : ¬(ws.contains (binOp mask ((token >>> 2) &&& 3) (ws.getD (token >>> 8) 0)
          (ws.getD ((token >>> 4) &&& 15) 0)) = true) := fun hm => hfresh (Or.inr hm)
      refine ⟨by dsimp; omega, ?_⟩
      apply insertSorted_nodup
      · intro hm
        have hmem := (dropVal_mem.mp (dropVal_mem.mp hm).1).1
        exact hznot (List.contains_iff_mem.mpr hmem)
      · exact dropVal_nodup (dropVal_nodup nd)

def dagTrace (mask : Nat) (stock : List Nat) (fuel : Nat) (forest : Nat → Nat × Nat) (i : Nat) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
    (fun _ prev j =>
      let (parent, token) := forest j
      if Nat.beq parent 0 then
        if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
      else (prev (parent - 1)).bind (childState mask token)) (fuel + 1)) i

theorem dagTrace_nodup {mask fuel : Nat} {stock : List Nat} {forest : Nat → Nat × Nat}
    (nd : stock.Nodup) {i : Nat} {st : Nat × List Nat × List (Nat × Nat × Nat)}
    (h : dagTrace mask stock fuel forest i = some st) : st.2.1.Nodup := by
  unfold dagTrace at h
  suffices ∀ steps j s,
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) steps) j = some s → s.2.1.Nodup from
    this (fuel + 1) i st h
  intro steps
  induction steps with
  | zero => intro j s h; contradiction
  | succ n ih =>
    intro j s h; dsimp only at h
    split at h
    · split at h
      · have e := Option.some.inj h; subst s; exact subsetWords_nodup nd _
      · contradiction
    · cases hp : (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) n) ((forest j).1 - 1) with
      | none => rw [hp] at h; contradiction
      | some p => rw [hp] at h; exact (childState_wf (ih _ _ hp) h).2

def dagLocal (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  let (fuel, ws, _) := state
  Nat.blt (fuel + 1) ws.length ||
    !(dagPart ws goal (mask ^^^ goal)) ||
    knownCloses goal bounds state

theorem dagLocal_open {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    {state : Nat × List Nat × List (Nat × Nat × Nat)}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (nd : state.2.1.Nodup) {k : Nat} (hk : k ≤ state.1)
    (hlive : LiveBin mask goal k state.2.1.toFinset) :
    dagLocal mask goal bounds state = false := by
  obtain ⟨fuel, ws, hist⟩ := state
  dsimp only at nd hk hlive
  unfold dagLocal
  have hcard : ws.length ≤ fuel + 1 := by
    have := liveBin_card_le hlive
    rw [List.toFinset_card_of_nodup nd] at this; omega
  have h1 : Nat.blt (fuel + 1) ws.length = false := by
    cases h : Nat.blt (fuel + 1) ws.length; rfl; have := Nat.blt_eq.mp h; omega
  have h2 : dagPart ws goal (mask ^^^ goal) = true := dagPart_live hgm hlive
  have h3 : knownCloses goal bounds (fuel, ws, hist) = false :=
    knownCloses_sound hknown hsub nd hk hlive
  simp [h1, h2, h3]

def treeBlock (lo hi : Nat) (f : Nat → Bool) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ next a b =>
      if Nat.blt a b then
        let m := (a + b) / 2
        if Nat.beq a m then f a else next a m && next m b
      else true) (hi - lo + 1)) lo hi

theorem treeBlock_at {lo hi : Nat} {f : Nat → Bool} (h : treeBlock lo hi f = true) :
    ∀ {i : Nat}, lo ≤ i → i < hi → f i = true := by
  unfold treeBlock at h
  suffices ∀ steps a b, b - a ≤ steps →
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          if Nat.blt x y then
            let m := (x + y) / 2
            if Nat.beq x m then f x else next x m && next m y
          else true) steps) a b = true →
      ∀ i, a ≤ i → i < b → f i = true by
    intro i h1 h2; exact this (hi - lo + 1) lo hi (by omega) h i h1 h2
  intro steps
  induction steps with
  | zero => intro a b hba _ i h1 h2; omega
  | succ s ih =>
    intro a b hba h i h1 h2
    dsimp only at h
    have hab : Nat.blt a b = true := Nat.blt_eq.mpr (by omega)
    simp only [hab, ite_true] at h
    set m := (a + b) / 2
    by_cases ham : a = m
    · have hbm : Nat.beq a m = true := Nat.beq_eq.mpr ham
      simp only [hbm, ite_true] at h
      have hia : i = a := by omega
      subst hia; exact h
    · have hbm : Nat.beq a m = false := beq_false_ne ham
      simp only [hbm, Bool.false_eq_true, ite_false] at h
      rcases Bool.and_eq_true_iff.mp h with ⟨hl, hr⟩
      by_cases him : i < m
      · exact ih a m (by omega) hl i h1 him
      · exact ih m b (by omega) hr i (by omega) h2

theorem block_join {a m b : Nat} {f : Nat → Bool}
    (h1 : ∀ i, a ≤ i → i < m → f i = true)
    (h2 : ∀ i, m ≤ i → i < b → f i = true) :
    ∀ i, a ≤ i → i < b → f i = true := by
  intro i hi1 hi2
  by_cases h : i < m
  · exact h1 i hi1 h
  · exact h2 i (by omega) hi2

def dagRef (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (parent token : Nat)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  match links parent token with
  | none => false
  | some dest =>
    Nat.blt dest count &&
      match states dest with
      | none => false
      | some saved => Nat.beq saved.1 state.1 && (saved.2.1 == state.2.1)

def dagCheckChildren (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  let (fuel, ws, hist) := state
  let n := ws.length
  !(ws.contains goal) &&
    (Nat.beq fuel 0 ||
      (Nat.blt n 17 &&
        treeBlock 0 n (fun a =>
          let x := ws.getD a 0
          treeBlock (a + 1) n (fun b =>
            let y := ws.getD b 0
            treeBlock 0 4 (fun op =>
              forceW (binOp mask op x y) (fun z =>
                Nat.beq z 0 || ws.contains z ||
                  treeBlock 0 4 (fun keep =>
                    let keepA := Nat.beq (keep &&& 1) 1
                    let keepB := Nat.beq ((keep >>> 1) &&& 1) 1
                    let newLen := n - 1 + (if keepA then 1 else 0) + (if keepB then 1 else 0)
                    Nat.blt fuel newLen ||
                      forceWs (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))) (fun ws' =>
                        let ch := (fuel - 1, ws', (z, x, y) :: hist)
                        dagLocal mask goal bounds ch || ref (makeToken a b op keep) ch))))))))

def dagCheckNode (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some st => dagCheckChildren mask goal bounds (dagRef count states links (i + 1)) st

def dagCheckRoots (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (stock : List Nat) (fuel : Nat) : Bool :=
  treeBlock 0 (2 ^ stock.length) (fun token =>
    forceWs (subsetWords stock token) (fun ws =>
      let st := (fuel, ws, [])
      dagLocal mask goal bounds st || ref token st))

theorem getElem_index_lt {l : List Nat} {x : Nat} (hx : x ∈ l) :
    ∃ i < l.length, l.getD i 0 = x := by
  obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hx
  refine ⟨i, hi, ?_⟩
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, heq]

theorem list_len_child {x y z : Nat} {ws : List Nat} {keepA keepB : Bool}
    (nd : ws.Nodup) (hx : x ∈ ws) (hy : y ∈ ws) (hxy : x ≠ y) (hz : z ∉ ws) :
    (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))).length =
      ws.length - 1 + (if keepA then 1 else 0) + (if keepB then 1 else 0) := by
  have nd' : (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))).Nodup :=
    insertSorted_nodup (fun hm => hz (dropVal_mem.mp (dropVal_mem.mp hm).1).1) (dropVal_nodup (dropVal_nodup nd))
  have h1 := List.toFinset_card_of_nodup nd'
  have h2 := List.toFinset_card_of_nodup nd
  have hset : (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))).toFinset =
      insert z (dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset)) := by
    ext w
    simp only [List.mem_toFinset, insertSorted_mem, Finset.mem_insert, ← dropVal_toFinset]
  rw [hset] at h1
  have hz' : z ∉ dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset) :=
    fun hm => hz (List.mem_toFinset.mp (dropIf_subset _ _ _ (dropIf_subset _ _ _ hm)))
  rw [Finset.card_insert_of_notMem hz'] at h1
  set T := dropIf (!keepB) y ws.toFinset
  have hxb : x ∈ T := by
    unfold T dropIf; split
    · exact Finset.mem_erase.mpr ⟨hxy, List.mem_toFinset.mpr hx⟩
    · exact List.mem_toFinset.mpr hx
  have hcb : T.card = ws.toFinset.card - (if keepB then 0 else 1) := by
    unfold T dropIf; cases keepB
    · have := Finset.card_erase_add_one (List.mem_toFinset.mpr hy); simp; omega
    · simp
  have hca : (dropIf (!keepA) x T).card = T.card - (if keepA then 0 else 1) := by
    unfold dropIf; cases keepA
    · have := Finset.card_erase_add_one hxb; simp only [Bool.not_false, Bool.false_eq_true, ite_true, ite_false]; omega
    · simp
  have hlen2 : 2 ≤ ws.toFinset.card := by
    have hsub : ({x, y} : Finset Nat) ⊆ ws.toFinset := by
      intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
      · exact List.mem_toFinset.mpr hx
      · rw [Finset.mem_singleton.mp hw]; exact List.mem_toFinset.mpr hy
    have hpair : ({x, y} : Finset Nat).card = 2 := Finset.card_pair hxy
    have := Finset.card_le_card hsub; omega
  rw [← h1, hca, hcb, h2]
  cases keepA <;> cases keepB <;> simp <;> omega

theorem dagAllNodes {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {links : Nat → Nat → Option Nat}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1) (snd : stock.Nodup)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNode mask goal bounds count
      (dagTrace mask stock fuel forest) links i = true) :
    ∀ cap i st, i < count → dagTrace mask stock fuel forest i = some st →
      st.1 = cap → ∀ k, k ≤ cap → ¬LiveBin mask goal k st.2.1.toFinset := by
  intro cap
  induction cap using Nat.strong_induction_on with
  | ind cap ih =>
    intro i st hi htr hcap k hk hlive
    obtain ⟨rem, ws, hist⟩ := st
    dsimp only at hcap hlive
    have nd : ws.Nodup := dagTrace_nodup snd htr
    have hchk := hnodes i (Nat.zero_le i) hi
    unfold dagCheckNode at hchk
    rw [htr] at hchk
    unfold dagCheckChildren at hchk
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, Nat.beq_eq, Nat.blt_eq] at hchk
    obtain ⟨hnohit, hstep⟩ := hchk
    generalize hS : ws.toFinset = S at hlive
    cases hlive with
    | done =>
      have hgm' : goal ∈ ws := List.mem_toFinset.mp (hS.symm ▸ Finset.mem_singleton_self goal)
      have hc : ws.contains goal = true := List.contains_iff_mem.mpr hgm'
      rw [hc] at hnohit; exact Bool.noConfusion hnohit
    | @step k' _ a0 b0 op0 ha0 hb0 hab0 _ _ hop0 hz0 hf0 keepA0 keepB0 tail0 =>
      rw [← hS] at ha0 hb0 hf0 tail0
      have hrem_pos : rem ≠ 0 := by omega
      rcases hstep with hrem0 | ⟨hn17, hblock⟩
      · exact hrem_pos hrem0
      · have haM : a0 ∈ ws := List.mem_toFinset.mp ha0
        have hbM : b0 ∈ ws := List.mem_toFinset.mp hb0
        obtain ⟨ia0, hia0, hea0⟩ := getElem_index_lt haM
        obtain ⟨ib0, hib0, heb0⟩ := getElem_index_lt hbM
        have hiab_ne : ia0 ≠ ib0 := fun heq => hab0 (hea0.symm.trans (heq ▸ heb0))
        have ⟨a, b, op, keepA, keepB, ha_lt, hab_lt, hb_lt, hop_lt, hax, hby, hzeq, htail⟩ :
            ∃ a b op keepA keepB, a < ws.length ∧ a < b ∧ b < ws.length ∧ op < 4 ∧
              ws.getD a 0 = (if ia0 < ib0 then a0 else b0) ∧
              ws.getD b 0 = (if ia0 < ib0 then b0 else a0) ∧
              binOp mask op (ws.getD a 0) (ws.getD b 0) = binOp mask op0 a0 b0 ∧
              LiveBin mask goal k' (insert (binOp mask op (ws.getD a 0) (ws.getD b 0))
                (dropIf (!keepA) (ws.getD a 0) (dropIf (!keepB) (ws.getD b 0) ws.toFinset))) := by
          by_cases hlt : ia0 < ib0
          · exact ⟨ia0, ib0, op0, keepA0, keepB0, hia0, hlt, hib0, hop0,
              by simp only [hlt, ite_true]; exact hea0,
              by simp only [hlt, ite_true]; exact heb0,
              by rw [hea0, heb0], by rw [hea0, heb0]; exact tail0⟩
          · obtain ⟨op1, hop1, hopEq⟩ := binOp_comm mask op0 a0 b0 hop0
            have hswap : dropIf (!keepB0) b0 (dropIf (!keepA0) a0 ws.toFinset) =
                dropIf (!keepA0) a0 (dropIf (!keepB0) b0 ws.toFinset) := by
              ext w; simp only [dropIf]; cases keepA0 <;> cases keepB0 <;> simp [Finset.mem_erase, and_left_comm]
            exact ⟨ib0, ia0, op1, keepB0, keepA0, hib0, by omega, hia0, hop1,
              by simp only [hlt, ite_false]; exact heb0,
              by simp only [hlt, ite_false]; exact hea0,
              by rw [hea0, heb0, hopEq],
              by rw [hea0, heb0, ← hopEq, hswap]; exact tail0⟩
        set x := ws.getD a 0
        set y := ws.getD b 0
        set z := binOp mask op x y
        set keep := (if keepA then 1 else 0) + (if keepB then 2 else 0)
        have hkeep_lt : keep < 4 := by cases keepA <;> cases keepB <;> simp [keep]
        have hkA : Nat.beq (keep &&& 1) 1 = keepA := by cases keepA <;> cases keepB <;> decide
        have hkB : Nat.beq ((keep >>> 1) &&& 1) 1 = keepB := by cases keepA <;> cases keepB <;> decide
        have hkA' : (keep &&& 1 = 1) ↔ keepA = true := by cases keepA <;> cases keepB <;> decide
        have hkB' : ((keep >>> 1) &&& 1 = 1) ↔ keepB = true := by cases keepA <;> cases keepB <;> decide
        have hA := treeBlock_at hblock (Nat.zero_le a) ha_lt
        have hB := treeBlock_at hA (by omega : a + 1 ≤ b) hb_lt
        have hO := treeBlock_at hB (Nat.zero_le op) hop_lt
        simp only [forceW_eq, Bool.or_eq_true, Nat.beq_eq] at hO
        have hznz : z ≠ 0 := hzeq.symm ▸ hz0
        have hznm : ws.contains z = false := by
          cases h : ws.contains z
          · rfl
          · exact absurd (List.mem_toFinset.mpr (List.contains_iff_mem.mp h)) (hzeq.symm ▸ hf0)
        rcases hO with (hz' | hcm) | hK
        · exact hznz hz'
        · rw [hznm] at hcm; exact Bool.noConfusion hcm
        · have hKe := treeBlock_at hK (Nat.zero_le keep) hkeep_lt
          simp only [hkA, hkB, hkA', hkB', forceWs_eq, Bool.or_eq_true, Nat.blt_eq] at hKe
          set ws' := insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))
          have hxM : x ∈ ws := by simp only [x, hax]; split; exact haM; exact hbM
          have hyM : y ∈ ws := by simp only [y, hby]; split; exact hbM; exact haM
          have hxy : x ≠ y := by simp only [x, y, hax, hby]; split; exact hab0; exact hab0.symm
          have hzNotW : z ∉ ws := fun hm => by
            have := List.contains_iff_mem.mpr hm; rw [hznm] at this; exact Bool.noConfusion this
          have hnd' : ws'.Nodup :=
            insertSorted_nodup (fun hm => hzNotW (dropVal_mem.mp (dropVal_mem.mp hm).1).1) (dropVal_nodup (dropVal_nodup nd))
          have hset' : ws'.toFinset = insert z (dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset)) := by
            ext w; simp only [ws', List.mem_toFinset, insertSorted_mem, Finset.mem_insert, ← dropVal_toFinset]
          have hlive' : LiveBin mask goal k' ws'.toFinset := by rwa [hset']
          have hlen' := list_len_child (z := z) (keepA := keepA) (keepB := keepB) nd hxM hyM hxy hzNotW
          have hcard' : ws'.length ≤ rem := by
            have := liveBin_card_le hlive'
            rw [List.toFinset_card_of_nodup hnd'] at this; omega
          rcases hKe with hwide | hloc | href
          · change ws'.length = _ at hlen'; rw [← hlen'] at hwide; omega
          · have hopen := dagLocal_open (state := (rem - 1, ws', (z, x, y) :: hist)) hgm hknown hsub hnd' (k := k') (by omega) hlive'
            rw [hopen] at hloc; exact Bool.noConfusion hloc
          · unfold dagRef at href
            split at href
            · contradiction
            · rename_i dest _
              simp only [Bool.and_eq_true, Nat.blt_eq] at href
              obtain ⟨hdest, hst⟩ := href
              cases htr2 : dagTrace mask stock fuel forest dest with
              | none => rw [htr2] at hst; contradiction
              | some saved =>
                rw [htr2] at hst
                simp only [Bool.and_eq_true, Nat.beq_eq, beq_iff_eq] at hst
                obtain ⟨hfEq, hwEq⟩ := hst
                have hbelow : rem - 1 < cap := by omega
                exact ih (rem - 1) hbelow dest saved hdest htr2 hfEq k' (by omega) (hwEq ▸ hlive')

theorem lowerDag {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {links : Nat → Nat → Option Nat}
    (hgm : Masked mask goal) (hgnz : goal ≠ 0)
    (hcs : stock.all (fun w => Nat.beq (canon mask w) w) = true)
    (snd : stock.Nodup)
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hroots : dagCheckRoots mask goal bounds
      (dagRef count (dagTrace mask stock fuel forest) links 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNode mask goal bounds count
      (dagTrace mask stock fuel forest) links i = true) :
    LowerBin mask stock goal (fuel + 1) := by
  intro vs hbuild hhit
  by_contra! hlt
  have hcs' : ∀ w ∈ stock, canon mask w = w := fun w hw =>
    Nat.beq_eq.mp (List.all_eq_true.mp hcs w hw)
  obtain ⟨k, S, hk, hSsub, hlive⟩ := extractLiveBin hgnz hcs' hbuild hhit
  obtain ⟨tok, htok, hteq⟩ := exists_subsetToken stock S
  rw [Finset.inter_eq_left.mpr hSsub] at hteq
  have hchk := treeBlock_at hroots (Nat.zero_le tok) htok
  simp only [forceWs_eq, Bool.or_eq_true] at hchk
  have hnd : (subsetWords stock tok).Nodup := subsetWords_nodup snd tok
  have hlive' : LiveBin mask goal k (subsetWords stock tok).toFinset := by rwa [hteq]
  rcases hchk with hloc | href
  · have hopen := dagLocal_open (state := (fuel, subsetWords stock tok, [])) hgm hknown hsub hnd (k := k) (by omega) hlive'
    rw [hopen] at hloc; exact Bool.noConfusion hloc
  · unfold dagRef at href
    split at href
    · contradiction
    · rename_i dest _
      simp only [Bool.and_eq_true, Nat.blt_eq] at href
      obtain ⟨hdest, hst⟩ := href
      cases htr : dagTrace mask stock fuel forest dest with
      | none => rw [htr] at hst; contradiction
      | some saved =>
        rw [htr] at hst
        simp only [Bool.and_eq_true, Nat.beq_eq, beq_iff_eq] at hst
        obtain ⟨hfEq, hwEq⟩ := hst
        exact dagAllNodes hgm hknown hsub snd hnodes fuel dest saved hdest htr hfEq k (by omega) (hwEq ▸ hlive')

def unpack (data width idx : Nat) : Nat :=
  (data >>> (idx * width)) &&& ((1 <<< width) - 1)

def unpackForest (data pBits tBits : Nat) : Nat → Nat × Nat := fun i =>
  let w := pBits + tBits
  let code := unpack data w i
  (code >>> tBits, code &&& ((1 <<< tBits) - 1))

def unpackLinks (index data idxW sizeBits tokBits destBits steps : Nat) : Nat → Nat → Option Nat :=
  fun parent tok =>
    let entry := unpack index idxW parent
    let sz := entry &&& ((1 <<< sizeBits) - 1)
    let off := entry >>> sizeBits
    let w := tokBits + destBits
    (Nat.rec (motive := fun _ => Nat → Nat → Option Nat) (fun _ _ => none)
      (fun _ next lo hi =>
        if Nat.blt lo hi then
          let mid := (lo + hi) / 2
          let code := unpack data w mid
          let key := code &&& ((1 <<< tokBits) - 1)
          if Nat.beq tok key then some (code >>> tokBits)
          else if Nat.blt tok key then next lo mid else next (mid + 1) hi
        else none) steps) off (off + sz)

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true

def binaryCost (gs : List Gate) : Nat := (gs.filter isBinary).length

def legal (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def evalBit (k : Nat) (w : Nat) : Bool := w.testBit k

def stepBool (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def actionWord (w : List Nat) (g : Gate) : Nat := match g.op with
  | .not => fullMask ^^^ ((g.inputs.head?.map (fun i => w.getD i 0)).getD 0)
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) fullMask
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

theorem fullMask_eq : fullMask = 2 ^ 64 - 1 := by decide

theorem fullMask_bit {k : Nat} (hk : k < 64) : fullMask.testBit k = true := by
  rw [fullMask_eq, Nat.testBit_two_pow_sub_one]; simp [hk]

theorem readBit (w : List Nat) (i k : Nat) :
    (w.map (evalBit k)).getD i false = evalBit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), evalBit]

theorem actionWord_spec (w : List Nat) (g : Gate) (hg : legal g) {k : Nat} (hk : k < 64) :
    stepBool (w.map (evalBit k)) g = (w ++ [actionWord w g]).map (evalBit k) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hcap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hcap
  have hfm := fullMask_bit hk
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at hcap
  all_goals rcases hop with rfl | rfl | rfl <;>
    simp only [stepBool, List.map_cons, List.map_nil, readBit, List.map_append, actionWord,
      GateOp.eval, List.foldr_cons, List.foldr_nil, List.head?_cons, List.head?_nil,
      List.headD_cons, List.headD_nil, Option.map_some, Option.map_none, Option.getD_some,
      Option.getD_none, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq,
      Bool.and_true, Bool.or_false, evalBit, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor,
      Nat.zero_testBit, hfm, Bool.true_xor]

def rawVars : List Nat :=
  [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

def rootStock : List Nat :=
  [0x5555555555555555, 0x3333333333333333, 0x0f0f0f0f0f0f0f0f,
   0x00ff00ff00ff00ff, 0x0000ffff0000ffff, 0x00000000ffffffff]

theorem rawVars_avail : ∀ u ∈ rawVars, Avail rootStock (canon fullMask u) := by
  intro u hu
  simp only [rawVars, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Or.inr (by decide)

theorem compileBin_aux (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (w bank : List Nat)
    (hw : ∀ u ∈ w, Avail bank (canon fullMask u)) :
    ∃ vs, vs.length ≤ binaryCost gs ∧ BuildsBin fullMask bank vs ∧
      ∀ u ∈ gs.foldl (fun acc g => acc ++ [actionWord acc g]) w, Avail (vs ++ bank) (canon fullMask u) := by
  induction gs generalizing w bank with
  | nil => exact ⟨[], Nat.le_refl _, trivial, by simpa using hw⟩
  | cons g gs ih =>
    have hg0 := hg g List.mem_cons_self
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    set z := actionWord w g
    have hread (i : Nat) : Avail bank (canon fullMask (w.getD i 0)) := by
      by_cases hi : i < w.length
      · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi])
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi), canon_zero]; exact Or.inl rfl
    have hstep : Avail bank (canon fullMask z) ∨ (isBinary g = true ∧ GateBin fullMask bank (canon fullMask z)) := by
      obtain ⟨op, args⟩ := g
      obtain ⟨hop, hcap⟩ := hg0
      change op = .and ∨ op = .or ∨ op = .not at hop
      change args.length ≤ 2 at hcap
      rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at hcap
      · rcases hop with rfl | rfl | rfl
        · left; simp [z, actionWord, canon_self]; exact Or.inl rfl
        · left; simp [z, actionWord, canon_zero]; exact Or.inl rfl
        · left; simp [z, actionWord, canon_self]; exact Or.inl rfl
      · rcases hop with rfl | rfl | rfl
        · left; simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
          rw [canon_land]; exact hread i
        · left; simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.or_zero]
          exact hread i
        · left; simp only [z, actionWord, List.head?_cons, Option.map_some, Option.getD_some]
          rw [canon_xor_mask]; exact hread i
      · rcases hop with rfl | rfl | rfl
        · simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
          have h1 : canon fullMask (w.getD i 0 &&& (w.getD j 0 &&& fullMask)) =
              canon fullMask (w.getD i 0 &&& w.getD j 0) := by
            rw [← canon_land fullMask (w.getD i 0 &&& (w.getD j 0 &&& fullMask))]
            rw [← canon_land fullMask (w.getD i 0 &&& w.getD j 0)]
            congr 1; apply Nat.eq_of_testBit_eq; intro k; simp only [Nat.testBit_and]
            cases (w.getD i 0).testBit k <;> cases (w.getD j 0).testBit k <;> cases fullMask.testBit k <;> rfl
          rw [h1]
          rcases canon_and_in_binOp fullMask (w.getD i 0) (w.getD j 0) with h0 | hi' | hj' | ⟨op', hop', hbin⟩
          · left; exact Or.inl h0
          · left; rw [hi']; exact hread i
          · left; rw [hj']; exact hread j
          · right; exact ⟨rfl, canon fullMask (w.getD i 0), canon fullMask (w.getD j 0), op', hop', hread i, hread j, hbin⟩
        · simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.or_zero]
          rcases canon_or_in_binOp fullMask (w.getD i 0) (w.getD j 0) with h0 | hi' | hj' | ⟨op', hop', hbin⟩
          · left; exact Or.inl h0
          · left; rw [hi']; exact hread i
          · left; rw [hj']; exact hread j
          · right; exact ⟨rfl, canon fullMask (w.getD i 0), canon fullMask (w.getD j 0), op', hop', hread i, hread j, hbin⟩
        · left; simp only [z, actionWord, List.head?_cons, Option.map_some, Option.getD_some]
          rw [canon_xor_mask]; exact hread i
    rcases hstep with hav | ⟨hbin, hgate⟩
    · have hw' : ∀ u ∈ w ++ [z], Avail bank (canon fullMask u) := by
        intro u hu; rcases List.mem_append.mp hu with hu | hu
        · exact hw u hu
        · rw [List.mem_singleton.mp hu]; exact hav
      obtain ⟨vs, hlen, hbd, hall⟩ := ih hgs (w ++ [z]) bank hw'
      have hbc : binaryCost gs ≤ binaryCost (g :: gs) := by
        unfold binaryCost; simp only [List.filter]; cases isBinary g <;> simp
      exact ⟨vs, Nat.le_trans hlen hbc, hbd, hall⟩
    · set cz := canon fullMask z
      have hw' : ∀ u ∈ w ++ [z], Avail (cz :: bank) (canon fullMask u) := by
        intro u hu; rcases List.mem_append.mp hu with hu | hu
        · exact avail_weaken (fun a ha => List.mem_cons_of_mem _ ha) (hw u hu)
        · rw [List.mem_singleton.mp hu]; exact Or.inr List.mem_cons_self
      obtain ⟨vs, hlen, hbd, hall⟩ := ih hgs (w ++ [z]) (cz :: bank) hw'
      have hbc : binaryCost (g :: gs) = binaryCost gs + 1 := by
        unfold binaryCost; simp [hbin]
      refine ⟨cz :: vs, by simp only [List.length_cons, hbc]; omega, ⟨hgate, hbd⟩, ?_⟩
      intro u hu
      exact avail_weaken (fun a ha => by simp only [List.mem_append, List.mem_cons] at ha ⊢; tauto) (hall u hu)

theorem foldl_evalBit (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (w : List Nat) {k : Nat} (hk : k < 64) :
    gs.foldl stepBool (w.map (evalBit k)) =
      (gs.foldl (fun acc g => acc ++ [actionWord acc g]) w).map (evalBit k) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [actionWord_spec w g (hg g List.mem_cons_self) hk]
    exact ih (fun x hx => hg x (List.mem_cons_of_mem _ hx)) (w ++ [actionWord w g])

theorem rawVars_ofFn (x : Fin 6 → Bool) :
    List.ofFn x = rawVars.map (evalBit (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0)) := by
  have hx : ∀ (b0 b1 b2 b3 b4 b5 : Bool),
      [b0, b1, b2, b3, b4, b5] =
      rawVars.map (evalBit ((if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) +
        (if b3 then 8 else 0) + (if b4 then 16 else 0) + (if b5 then 32 else 0))) := by
    decide +kernel
  have hsum : (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0) =
      (if x 0 then 1 else 0) + (if x 1 then 2 else 0) + (if x 2 then 4 else 0) +
      (if x 3 then 8 else 0) + (if x 4 then 16 else 0) + (if x 5 then 32 else 0) := by
    simp [Fin.sum_univ_six]
  rw [hsum, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  exact hx (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

theorem sum_bits_6 (n : Nat) (hn : n < 64) :
    (∑ i : Fin 6, if n.testBit i.val then 2 ^ (i : Nat) else 0) = n := by
  simp only [Fin.sum_univ_six, Fin.val_zero, Fin.val_one, Fin.val_two]
  change (if n.testBit 0 then 1 else 0) + (if n.testBit 1 then 2 else 0) +
    (if n.testBit 2 then 4 else 0) + (if n.testBit 3 then 8 else 0) +
    (if n.testBit 4 then 16 else 0) + (if n.testBit 5 then 32 else 0) = n
  revert n; decide +kernel

theorem table2_from_lowerBin (target m : Nat)
    (hlow : LowerBin fullMask rootStock (canon fullMask target) (m - 1))
    (wg : List Gate) (wout : Nat) (hsz : wg.length = m)
    (hmono : Monotone2 ⟨wg, wout⟩)
    (heval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, wout⟩ (List.ofFn x) =
      Nat.testBit target (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0)) :
    ∀ s : Nat, HasCircuitSize 6 (fun x : Fin 6 → Bool =>
      Nat.testBit target (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0)) s →
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool,
      C.eval (List.ofFn x) = Nat.testBit target (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0) := by
  intro s ⟨C, hfan, hsize, hC⟩
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, hgm, hgop⟩ := hasNot
    have hshort : binaryCost C.gates < C.gates.length :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr ⟨g, hgm, by simp [isBinary, hgop]⟩
    have hleg : ∀ g ∈ C.gates, legal g := by
      intro g hg
      obtain ⟨hop, hlen⟩ := hfan g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      exact ⟨hop, hlen⟩
    obtain ⟨vs, hvlen, hvbd, hvhit⟩ := compileBin_aux C.gates hleg rawVars rootStock rawVars_avail
    set finalW := C.gates.foldl (fun acc g => acc ++ [actionWord acc g]) rawVars
    have hout_eq : finalW.getD C.output 0 &&& fullMask = target &&& fullMask := by
      apply Nat.eq_of_testBit_eq; intro k
      by_cases hk : k < 64
      · have hfm := fullMask_bit hk
        simp only [Nat.testBit_and, hfm, Bool.and_true]
        let x : Fin 6 → Bool := fun i => k.testBit i.val
        have hxidx : (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0) = k := sum_bits_6 k hk
        have h1 := hC x
        dsimp only at h1
        rw [hxidx, rawVars_ofFn x, hxidx] at h1
        change (C.gates.foldl stepBool (rawVars.map (evalBit k))).getD C.output false = target.testBit k at h1
        rw [foldl_evalBit C.gates hleg rawVars hk, readBit] at h1
        exact h1
      · have hfm0 : fullMask.testBit k = false := by
          rw [fullMask_eq, Nat.testBit_two_pow_sub_one]; simp [hk]
        simp [Nat.testBit_and, hfm0]
    have hout_avail : Avail (vs ++ rootStock) (canon fullMask target) := by
      rw [← canon_land fullMask target, ← hout_eq, canon_land]
      by_cases hi : C.output < finalW.length
      · exact hvhit _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi])
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi), canon_zero]; exact Or.inl rfl
    have hge := hlow vs hvbd hout_avail
    have hcsz : C.size = C.gates.length := rfl
    have hwsz : (⟨wg, wout⟩ : Circuit).size = m := hsz
    exact ⟨⟨wg, wout⟩, hmono, by omega, heval⟩
  · refine ⟨C, ?_, hsize, hC⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    refine ⟨?_, hlen⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g, hg, h⟩).elim

def memN (z : Nat) (l : List Nat) : Bool :=
  List.rec false (fun w _ ih => Bool.rec ih true (Nat.beq z w)) l

theorem memN_eq (z : Nat) (l : List Nat) : memN z l = l.contains z := by
  apply Bool.eq_iff_iff.mpr
  rw [List.contains_iff_mem]
  induction l with
  | nil => simp [memN]
  | cons w ws ih =>
    change Bool.rec (memN z ws) true (Nat.beq z w) = true ↔ z ∈ w :: ws
    cases h : Nat.beq z w
    · have hne : z ≠ w := ne_of_beq_false h
      simp [ih, hne]
    · have heq : z = w := Nat.eq_of_beq_eq_true h
      simp [heq]

def allN (p : Nat → Bool) (l : List Nat) : Bool :=
  List.rec true (fun w _ ih => Bool.rec false ih (p w)) l

theorem allN_eq (p : Nat → Bool) (l : List Nat) : allN p l = l.all p := by
  induction l with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec false (allN p ws) (p w) = (p w && ws.all p)
    rw [ih]; cases p w <;> rfl

def lenN (l : List Nat) : Nat :=
  List.rec 0 (fun _ _ ih => Nat.add ih 1) l

theorem lenN_eq (l : List Nat) : lenN l = l.length := by
  induction l with
  | nil => rfl
  | cons _ ws ih => change Nat.add (lenN ws) 1 = ws.length + 1; rw [ih]

def appN (l r : List Nat) : List Nat :=
  List.rec r (fun w _ ih => w :: ih) l

theorem appN_eq (l r : List Nat) : appN l r = l ++ r := by
  induction l with
  | nil => rfl
  | cons w ws ih => change w :: appN ws r = w :: (ws ++ r); rw [ih]

def revAccN {α : Type} (l acc : List α) : List α :=
  (List.rec (motive := fun _ => List α → List α) (fun a => a) (fun w _ ih a => ih (w :: a)) l) acc

theorem revAccN_eq {α : Type} (l acc : List α) : revAccN l acc = l.reverse ++ acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons w ws ih =>
    change revAccN ws (w :: acc) = (w :: ws).reverse ++ acc
    rw [ih, List.reverse_cons, List.append_assoc]; rfl

def getDN (l : List Nat) (i : Nat) : Nat :=
  (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun w _ ih k => Nat.rec w (fun m _ => ih m) k) l) i

theorem getDN_eq (l : List Nat) (i : Nat) : getDN l i = l.getD i 0 := by
  induction l generalizing i with
  | nil => rfl
  | cons w ws ih =>
    cases i with
    | zero => rfl
    | succ m => change getDN ws m = (w :: ws).getD (m + 1) 0; rw [ih]; rfl

def eqListN (l1 : List Nat) : List Nat → Bool :=
  List.rec
    (fun l2 => List.rec true (fun _ _ _ => false) l2)
    (fun x _ ih l2 => List.rec false (fun y ys _ => Bool.rec false (ih ys) (Nat.beq x y)) l2) l1

theorem eqListN_eq (l1 l2 : List Nat) : eqListN l1 l2 = (l1 == l2) := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> rfl
  | cons x xs ih =>
    cases l2 with
    | nil => rfl
    | cons y ys =>
      change Bool.rec false (eqListN xs ys) (Nat.beq x y) = ((x :: xs) == (y :: ys))
      rw [ih]
      by_cases h : x = y
      · subst h; simp [Nat.beq_refl]
      · have h1 : Nat.beq x y = false := beq_false_ne h
        have h2 : (x == y) = false := beq_false_of_ne h
        simp [h1, h2]

def canonF (mask w : Nat) : Nat :=
  let v := Nat.land w mask
  Bool.rec
    (Bool.rec
      (let iv := Nat.xor mask v
       Bool.rec iv v (Nat.blt v iv))
      0 (Nat.beq v mask))
    0 (Nat.beq v 0)

theorem canonF_eq (mask w : Nat) : canonF mask w = canon mask w := by
  unfold canonF canon bsel; dsimp only
  change (Bool.rec (Bool.rec (Bool.rec (mask ^^^ (w &&& mask)) (w &&& mask) ((w &&& mask).blt (mask ^^^ (w &&& mask)))) 0 ((w &&& mask).beq mask)) 0 ((w &&& mask).beq 0) : Nat) = _
  cases Nat.beq (w &&& mask) 0 <;> cases Nat.beq (w &&& mask) mask <;> rfl

def binOpF (mask op a b : Nat) : Nat :=
  Bool.rec
    (Bool.rec
      (Bool.rec (canonF mask (Nat.land (Nat.xor mask a) b))
        (canonF mask (Nat.land a (Nat.xor mask b))) (Nat.beq op 2))
      (canonF mask (Nat.lor a b)) (Nat.beq op 1))
    (canonF mask (Nat.land a b)) (Nat.beq op 0)

theorem binOpF_eq (mask op a b : Nat) : binOpF mask op a b = binOp mask op a b := by
  unfold binOpF binOp bsel
  simp only [canonF_eq]
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> rfl

def dagPartF (ws : List Nat) : Nat → Nat → Bool :=
  List.rec
    (fun p n => Bool.rec (Nat.beq n 0) true (Nat.beq p 0))
    (fun w _ rest p n =>
      Bool.rec
        (Bool.rec
          (forceW (Nat.land p w) (fun up =>
            forceW (Nat.land n w) (fun down =>
              Bool.rec false
                (forceW (Nat.xor p up) (fun offP =>
                  forceW (Nat.xor n down) (rest offP)))
                (rest up down))))
          true (Nat.beq n 0))
        true (Nat.beq p 0)) ws

theorem dagPartF_eq (ws : List Nat) (p n : Nat) : dagPartF ws p n = dagPart ws p n := by
  induction ws generalizing p n with
  | nil =>
    change Bool.rec (Nat.beq n 0) true (Nat.beq p 0) = (Nat.beq p 0 || Nat.beq n 0)
    cases Nat.beq p 0 <;> rfl
  | cons w ws ih =>
    change Bool.rec (Bool.rec (forceW (Nat.land p w) (fun up =>
      forceW (Nat.land n w) (fun down =>
        Bool.rec false (forceW (Nat.xor p up) (fun offP => forceW (Nat.xor n down) (dagPartF ws offP)))
          (dagPartF ws up down)))) true (Nat.beq n 0)) true (Nat.beq p 0) =
      ((Nat.beq p 0 || Nat.beq n 0) || forceW (p &&& w) (fun up =>
        forceW (n &&& w) (fun down => dagPart ws up down &&
          forceW (p ^^^ up) (fun offP => forceW (n ^^^ down) (dagPart ws offP)))))
    simp only [forceW_eq]
    cases Nat.beq p 0
    · cases Nat.beq n 0
      · change Bool.rec false (dagPartF ws _ _) (dagPartF ws _ _) = (dagPart ws _ _ && dagPart ws _ _)
        rw [ih, ih]; cases dagPart ws (p &&& w) (n &&& w) <;> rfl
      · rfl
    · rfl

def flatCountF (cut : Nat) (ws : List Nat) : Nat :=
  List.rec 0 (fun w _ cnt =>
    let v := Nat.land w cut
    Bool.rec (Bool.rec cnt (Nat.add cnt 1) (Nat.beq v cut)) (Nat.add cnt 1) (Nat.beq v 0)) ws

theorem flatCountF_eq (cut : Nat) (ws : List Nat) : flatCountF cut ws = flatCount cut ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec (Bool.rec (flatCountF cut ws) (Nat.add (flatCountF cut ws) 1) (Nat.beq (Nat.land w cut) cut))
      (Nat.add (flatCountF cut ws) 1) (Nat.beq (Nat.land w cut) 0) =
      bsel (Nat.beq (canon cut w) 0) (flatCount cut ws + 1) (flatCount cut ws)
    rw [ih]
    rcases canon_cases cut w with ⟨h0, h1 | h2⟩ | ⟨hne, _⟩
    · have hb : Nat.beq (Nat.land w cut) 0 = true := Nat.beq_eq.mpr h1
      rw [h0, hb, Nat.beq_refl]; rfl
    · have hb : Nat.beq (Nat.land w cut) cut = true := Nat.beq_eq.mpr h2
      rw [h0, hb, Nat.beq_refl]; cases Nat.beq (Nat.land w cut) 0 <;> rfl
    · have h1 : Nat.beq (Nat.land w cut) 0 = false := beq_false_ne (fun e => by
        change w &&& cut = 0 at e; exact hne (by unfold canon; dsimp only; rw [e]; simp [bsel]))
      have h2 : Nat.beq (Nat.land w cut) cut = false := beq_false_ne (fun e => by
        change w &&& cut = cut at e; exact hne (by unfold canon; dsimp only; rw [e]; simp [bsel]))
      rw [h1, h2, beq_false_ne hne]; rfl

def availBF (bank : List Nat) (w : Nat) : Bool :=
  Bool.rec (memN w bank) true (Nat.beq w 0)

theorem availBF_eq (bank : List Nat) (w : Nat) : availBF bank w = availB bank w := by
  unfold availBF availB; rw [memN_eq]; cases Nat.beq w 0 <;> rfl

def recipeGateBinF (cut : Nat) (bank : List Nat) (vc ac bc : Nat) : Bool :=
  Bool.rec false
    (Bool.rec false
      (Bool.rec
        (Bool.rec
          (Bool.rec (Nat.beq vc (binOpF cut 3 ac bc)) true (Nat.beq vc (binOpF cut 2 ac bc)))
          true (Nat.beq vc (binOpF cut 1 ac bc)))
        true (Nat.beq vc (binOpF cut 0 ac bc)))
      (availBF bank bc))
    (availBF bank ac)

theorem recipeGateBinF_eq (cut : Nat) (bank : List Nat) (vc ac bc : Nat) :
    recipeGateBinF cut bank vc ac bc = recipeGateBin cut bank vc ac bc := by
  unfold recipeGateBinF recipeGateBin
  simp only [availBF_eq, binOpF_eq]
  cases availB bank ac <;> cases availB bank bc <;>
    cases Nat.beq vc (binOp cut 0 ac bc) <;> cases Nat.beq vc (binOp cut 1 ac bc) <;>
    cases Nat.beq vc (binOp cut 2 ac bc) <;> cases Nat.beq vc (binOp cut 3 ac bc) <;> rfl

def addUniqF (w : Nat) (l : List Nat) : List Nat :=
  Bool.rec (w :: l) l (memN w l)

theorem addUniqF_eq (w : Nat) (l : List Nat) : addUniqF w l = addUniq w l := by
  unfold addUniqF addUniq; rw [memN_eq]; cases l.contains w <;> rfl

def recipeStartF (cut : Nat) (stock ws : List Nat) : List Nat :=
  List.rec [] (fun w _ acc =>
    let v := canonF cut w
    Bool.rec (addUniqF v acc) acc (availBF stock v)) ws

theorem recipeStartF_eq (cut : Nat) (stock ws : List Nat) : recipeStartF cut stock ws = recipeStart cut stock ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec (addUniqF (canonF cut w) (recipeStartF cut stock ws)) (recipeStartF cut stock ws) (availBF stock (canonF cut w)) =
      (if availB stock (canon cut w) then recipeStart cut stock ws else addUniq (canon cut w) (recipeStart cut stock ws))
    rw [ih, canonF_eq, availBF_eq, addUniqF_eq]; cases availB stock (canon cut w) <;> rfl

def recipeCloseF (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun (w, a, b) _ next acc =>
      let v := canonF cut w
      Bool.rec (next acc)
        (let va := canonF cut a
         let vb := canonF cut b
         let acc1 := Bool.rec (addUniqF va acc) acc (availBF stock va)
         let acc2 := Bool.rec (addUniqF vb acc1) acc1 (availBF stock vb)
         next acc2)
        (memN v acc)) hist needed

theorem recipeCloseF_eq (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) :
    recipeCloseF cut stock hist needed = recipeClose cut stock hist needed := by
  induction hist generalizing needed with
  | nil => rfl
  | cons rec hist ih =>
    obtain ⟨w, a, b⟩ := rec
    have hL : recipeCloseF cut stock ((w, a, b) :: hist) needed =
        Bool.rec (recipeCloseF cut stock hist needed)
          (let va := canonF cut a; let vb := canonF cut b
           let acc1 := Bool.rec (addUniqF va needed) needed (availBF stock va)
           let acc2 := Bool.rec (addUniqF vb acc1) acc1 (availBF stock vb)
           recipeCloseF cut stock hist acc2)
          (memN (canonF cut w) needed) := rfl
    have hR : recipeClose cut stock ((w, a, b) :: hist) needed =
        (if needed.contains (canon cut w) then
          let va := canon cut a; let vb := canon cut b
          let acc1 := if availB stock va then needed else addUniq va needed
          let acc2 := if availB stock vb then acc1 else addUniq vb acc1
          recipeClose cut stock hist acc2
        else recipeClose cut stock hist needed) := rfl
    rw [hL, hR]; dsimp only
    simp only [canonF_eq, memN_eq, availBF_eq, addUniqF_eq]
    cases needed.contains (canon cut w)
    · exact ih needed
    · dsimp only; rw [ih]
      cases availB stock (canon cut a) <;> cases availB stock (canon cut b) <;> rfl

def replayRecF (cut : Nat) (needed : List Nat) (hist : List (Nat × Nat × Nat)) (bank : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun _ => [])
    (fun (w, a, b) _ next bank =>
      let v := canonF cut w
      Bool.rec (next bank)
        (Bool.rec
          (Bool.rec (next bank) (v :: next (v :: bank))
            (recipeGateBinF cut bank v (canonF cut a) (canonF cut b)))
          (next bank) (availBF bank v))
        (memN v needed)) hist bank

theorem replayRecF_eq (cut : Nat) (needed : List Nat) (hist : List (Nat × Nat × Nat)) (bank : List Nat) :
    replayRecF cut needed hist bank = replayRec cut needed hist bank := by
  induction hist generalizing bank with
  | nil => rfl
  | cons rec hist ih =>
    obtain ⟨w, a, b⟩ := rec
    have hL : replayRecF cut needed ((w, a, b) :: hist) bank =
        let v := canonF cut w
        Bool.rec (replayRecF cut needed hist bank)
          (Bool.rec
            (Bool.rec (replayRecF cut needed hist bank) (v :: replayRecF cut needed hist (v :: bank))
              (recipeGateBinF cut bank v (canonF cut a) (canonF cut b)))
            (replayRecF cut needed hist bank) (availBF bank v))
          (memN v needed) := rfl
    have hR : replayRec cut needed ((w, a, b) :: hist) bank =
        (let v := canon cut w
         if needed.contains v && !(availB bank v) && recipeGateBin cut bank v (canon cut a) (canon cut b) then
           v :: replayRec cut needed hist (v :: bank)
         else replayRec cut needed hist bank) := rfl
    rw [hL, hR]; dsimp only
    simp only [canonF_eq, memN_eq, availBF_eq, recipeGateBinF_eq]
    rw [ih bank, ih (canon cut w :: bank)]
    cases needed.contains (canon cut w) <;> cases availB bank (canon cut w) <;>
      cases recipeGateBin cut bank (canon cut w) (canon cut a) (canon cut b) <;> rfl

def boundClosesF (state : Nat × List Nat × List (Nat × Nat × Nat))
    (bound : Nat × List Nat × Nat × Nat) : Bool :=
  let (cut, stock, lower, _) := bound
  let (fuel, ws, hist) := state
  forceW (Nat.sub fuel (flatCountF cut ws)) (fun rem =>
    Bool.rec false
      (forceWs (recipeStartF cut stock ws) (fun start =>
        Bool.rec false
          (forceWs (recipeCloseF cut stock hist start) (fun needed =>
            Bool.rec false
              (forceWs (replayRecF cut needed (revAccN hist []) stock) (fun replay =>
                Bool.rec false
                  (allN (fun w => availBF (appN replay stock) (canonF cut w)) ws)
                  (Nat.blt (Nat.add (lenN replay) rem) lower)))
              (Nat.blt (Nat.add (lenN needed) rem) lower)))
          (Nat.blt (Nat.add (lenN start) rem) lower)))
      (Nat.blt rem lower))

theorem boundClosesF_eq {target : Nat} {state : Nat × List Nat × List (Nat × Nat × Nat)}
    {bound : Nat × List Nat × Nat × Nat}
    (hg : canon bound.1 target = bound.2.2.2) (hnz : bound.2.2.2 ≠ 0) :
    boundClosesF state bound = boundCloses target state bound := by
  obtain ⟨fuel, ws, hist⟩ := state
  obtain ⟨cut, stock, lower, bgoal⟩ := bound
  dsimp only at hg hnz
  unfold boundClosesF boundCloses
  simp only [forceW_eq, forceWs_eq, flatCountF_eq, recipeStartF_eq, recipeCloseF_eq,
    replayRecF_eq, revAccN_eq, List.append_nil, lenN_eq, allN_eq, appN_eq, availBF_eq, canonF_eq,
    hg, Nat.beq_refl, beq_false_ne hnz, Bool.not_false, Bool.and_true, Bool.true_and]
  cases Nat.blt (fuel - flatCount cut ws) lower
  · rfl
  · cases Nat.blt ((recipeStart cut stock ws).length + (fuel - flatCount cut ws)) lower
    · rfl
    · cases Nat.blt ((recipeClose cut stock hist (recipeStart cut stock ws)).length + (fuel - flatCount cut ws)) lower
      · rfl
      · cases Nat.blt ((replayRec cut (recipeClose cut stock hist (recipeStart cut stock ws)) hist.reverse stock).length + (fuel - flatCount cut ws)) lower <;> rfl

def knownClosesF (bounds : List (Nat × List Nat × Nat × Nat))
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  List.rec false (fun b _ rest => Bool.rec rest true (boundClosesF state b)) bounds

theorem knownClosesF_eq {target : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 target = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    knownClosesF bounds state = knownCloses target bounds state := by
  induction bounds with
  | nil => rfl
  | cons b bs ih =>
    change Bool.rec (knownClosesF bs state) true (boundClosesF state b) =
      (boundCloses target state b || knownCloses target bs state)
    have h0 := hgoals b List.mem_cons_self
    rw [boundClosesF_eq h0.1 h0.2, ih (fun x hx => hgoals x (List.mem_cons_of_mem _ hx))]
    cases boundCloses target state b <;> rfl

def insertSortedF (x : Nat) (l : List Nat) : List Nat :=
  List.rec [x] (fun y ys ih => Bool.rec (y :: ih) (x :: y :: ys) (Nat.ble x y)) l

theorem insertSortedF_eq (x : Nat) (l : List Nat) : insertSortedF x l = insertSorted x l := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    change Bool.rec (y :: insertSortedF x ys) (x :: y :: ys) (Nat.ble x y) =
      bsel (Nat.ble x y) (x :: y :: ys) (y :: insertSorted x ys)
    rw [ih]; cases Nat.ble x y <;> rfl

def dropValF (drop : Bool) (x : Nat) (l : List Nat) : List Nat :=
  Bool.rec l (List.rec [] (fun y _ ih => Bool.rec (y :: ih) ih (Nat.beq y x)) l) drop

theorem dropValF_eq (drop : Bool) (x : Nat) (l : List Nat) : dropValF drop x l = dropVal drop x l := by
  cases drop
  · rfl
  · induction l with
    | nil => rfl
    | cons y ys ih =>
      change Bool.rec (y :: dropValF true x ys) (dropValF true x ys) (Nat.beq y x) =
        bsel (Nat.beq y x) (dropVal true x ys) (y :: dropVal true x ys)
      rw [ih]; cases Nat.beq y x <;> rfl

def subsetWordsF (stock : List Nat) (bits : Nat) : List Nat :=
  (List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun w _ ih b =>
      let rest := ih (Nat.shiftRight b 1)
      Bool.rec rest (insertSortedF w rest) (Nat.beq (Nat.land b 1) 1)) stock) bits

theorem subsetWordsF_eq (stock : List Nat) (bits : Nat) : subsetWordsF stock bits = subsetWords stock bits := by
  induction stock generalizing bits with
  | nil => rfl
  | cons x xs ih =>
    change Bool.rec (subsetWordsF xs (Nat.shiftRight bits 1))
      (insertSortedF x (subsetWordsF xs (Nat.shiftRight bits 1))) (Nat.beq (Nat.land bits 1) 1) =
      bsel (Nat.beq (bits &&& 1) 1) (insertSorted x (subsetWords xs (bits >>> 1))) (subsetWords xs (bits >>> 1))
    rw [ih, insertSortedF_eq]; cases Nat.beq (bits &&& 1) 1 <;> rfl

def childStateF (mask token : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  let (fuel, ws, hist) := state
  let keep := Nat.land token 3
  let op := Nat.land (Nat.shiftRight token 2) 3
  let b := Nat.land (Nat.shiftRight token 4) 15
  let a := Nat.shiftRight token 8
  Bool.rec
    (Bool.rec none
      (Bool.rec none
        (let x := getDN ws a
         let y := getDN ws b
         let z := binOpF mask op x y
         Bool.rec
           (Bool.rec
             (let keepA := Nat.beq (Nat.land keep 1) 1
              let keepB := Nat.beq (Nat.land (Nat.shiftRight keep 1) 1) 1
              let rest := dropValF (Bool.rec true false keepA) x (dropValF (Bool.rec true false keepB) y ws)
              some (Nat.sub fuel 1, insertSortedF z rest, (z, x, y) :: hist))
             none (memN z ws))
           none (Nat.beq z 0))
        (Nat.blt b (lenN ws)))
      (Nat.blt a b))
    none (Nat.beq fuel 0)

theorem childStateF_eq (mask token : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    childStateF mask token state = childState mask token state := by
  obtain ⟨fuel, ws, hist⟩ := state
  unfold childStateF childState
  simp only [lenN_eq, getDN_eq, binOpF_eq, memN_eq, dropValF_eq, insertSortedF_eq]
  cases Nat.beq fuel 0
  · cases Nat.blt (token >>> 8) ((token >>> 4) &&& 15)
    · rfl
    · cases Nat.blt ((token >>> 4) &&& 15) ws.length
      · rfl
      · cases Nat.beq (binOp mask ((token >>> 2) &&& 3) (ws.getD (token >>> 8) 0) (ws.getD ((token >>> 4) &&& 15) 0)) 0
        · cases ws.contains (binOp mask ((token >>> 2) &&& 3) (ws.getD (token >>> 8) 0) (ws.getD ((token >>> 4) &&& 15) 0))
          · cases Nat.beq ((token &&& 3) &&& 1) 1 <;> cases Nat.beq (((token &&& 3) >>> 1) &&& 1) 1 <;> rfl
          · rfl
        · rfl
  · rfl

def dagTraceF (mask : Nat) (stock : List Nat) (fuel : Nat) (forest : Nat → Nat × Nat) (i : Nat) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
    (fun _ prev j =>
      let (parent, token) := forest j
      Bool.rec
        (match prev (Nat.sub parent 1) with
         | none => none
         | some st => childStateF mask token st)
        (Bool.rec none (some (fuel, subsetWordsF stock token, []))
          (Nat.blt token (Nat.shiftLeft 1 (lenN stock))))
        (Nat.beq parent 0)) (Nat.add fuel 1)) i

theorem dagTraceF_eq (mask : Nat) (stock : List Nat) (fuel : Nat) (forest : Nat → Nat × Nat) (i : Nat) :
    dagTraceF mask stock fuel forest i = dagTrace mask stock fuel forest i := by
  unfold dagTraceF dagTrace
  suffices ∀ steps j,
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          Bool.rec
            (match prev (Nat.sub parent 1) with
             | none => none
             | some st => childStateF mask token st)
            (Bool.rec none (some (fuel, subsetWordsF stock token, []))
              (Nat.blt token (Nat.shiftLeft 1 (lenN stock))))
            (Nat.beq parent 0)) steps) j =
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) steps) j from
    this (fuel + 1) i
  intro steps
  induction steps with
  | zero => intro j; rfl
  | succ n ih =>
    intro j
    dsimp only
    have hpow : Nat.shiftLeft 1 (lenN stock) = 2 ^ stock.length := by
      rw [lenN_eq]; change 1 <<< stock.length = _; rw [Nat.shiftLeft_eq, Nat.one_mul]
    cases Nat.beq (forest j).1 0
    · dsimp only
      rw [ih]
      cases (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          if Nat.beq (forest k).1 0 then
            if Nat.blt (forest k).2 (2 ^ stock.length) then some (rootState stock fuel (forest k).2) else none
          else (prev ((forest k).1 - 1)).bind (childState mask (forest k).2)) n) ((forest j).1 - 1)
      · rfl
      · exact childStateF_eq mask (forest j).2 _
    · dsimp only
      rw [hpow, subsetWordsF_eq]
      cases Nat.blt (forest j).2 (2 ^ stock.length) <;> rfl

theorem knownCloses_of_mem {target : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    {state : Nat × List Nat × List (Nat × Nat × Nat)} {b : Nat × List Nat × Nat × Nat}
    (hmem : b ∈ bounds) (hb : boundCloses target state b = true) :
    knownCloses target bounds state = true := by
  induction bounds with
  | nil => cases hmem
  | cons x xs ih =>
    change (boundCloses target state x || knownCloses target xs state) = true
    rcases List.mem_cons.mp hmem with rfl | htl
    · rw [hb]; rfl
    · rw [ih htl]; cases boundCloses target state x <;> rfl

theorem treeBlock_mono {lo hi : Nat} {f g : Nat → Bool}
    (hf : treeBlock lo hi f = true)
    (himp : ∀ i, lo ≤ i → i < hi → f i = true → g i = true) :
    treeBlock lo hi g = true := by
  unfold treeBlock at hf ⊢
  suffices ∀ steps a b,
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          if Nat.blt x y then
            let m := (x + y) / 2
            if Nat.beq x m then f x else next x m && next m y
          else true) steps) a b = true →
      (∀ i, a ≤ i → i < b → f i = true → g i = true) →
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          if Nat.blt x y then
            let m := (x + y) / 2
            if Nat.beq x m then g x else next x m && next m y
          else true) steps) a b = true from
    this (hi - lo + 1) lo hi hf himp
  intro steps
  induction steps with
  | zero => intro a b _ _; rfl
  | succ s ih =>
    intro a b h hfg
    dsimp only at h ⊢
    cases hlt : Nat.blt a b
    · rfl
    · simp only [hlt, ite_true] at h ⊢
      have hab : a < b := Nat.blt_eq.mp hlt
      cases heq : Nat.beq a ((a + b) / 2)
      · simp only [heq, Bool.false_eq_true, ite_false, Bool.and_eq_true] at h ⊢
        exact ⟨ih a ((a + b) / 2) h.1 (fun i h1 h2 => hfg i h1 (by omega)),
               ih ((a + b) / 2) b h.2 (fun i h1 h2 => hfg i (by omega) h2)⟩
      · simp only [heq, ite_true] at h ⊢
        exact hfg a (Nat.le_refl a) hab h

def nthBound (bounds : List (Nat × List Nat × Nat × Nat)) (i : Nat) :
    Option (Nat × List Nat × Nat × Nat) :=
  (List.rec (motive := fun _ => Nat → Option (Nat × List Nat × Nat × Nat))
    (fun _ => none)
    (fun b _ ih k => Nat.rec (some b) (fun m _ => ih m) k) bounds) i

theorem nthBound_mem {bounds : List (Nat × List Nat × Nat × Nat)} {i : Nat} {b : Nat × List Nat × Nat × Nat}
    (h : nthBound bounds i = some b) : b ∈ bounds := by
  induction bounds generalizing i with
  | nil => simp [nthBound] at h
  | cons x xs ih =>
    cases i with
    | zero => cases h; exact List.mem_cons_self
    | succ m => exact List.mem_cons_of_mem _ (ih h)

def knownClosesTopF (bounds : List (Nat × List Nat × Nat × Nat))
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  match bounds with
  | [] => false
  | b0 :: rest =>
    Bool.rec
      (match rest with
       | [] => false
       | b1 :: rest1 =>
         Bool.rec
           (match rest1 with
            | [] => false
            | b2 :: _ => boundClosesF state b2)
           true (boundClosesF state b1))
      true (boundClosesF state b0)

theorem knownClosesTopF_imp {target : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 target = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    {state : Nat × List Nat × List (Nat × Nat × Nat)}
    (h : knownClosesTopF bounds state = true) :
    knownCloses target bounds state = true := by
  cases bounds with
  | nil => exact Bool.noConfusion h
  | cons b0 rest =>
    unfold knownClosesTopF at h; dsimp only at h
    have h0 := hgoals b0 List.mem_cons_self
    cases hb0 : boundClosesF state b0
    · rw [hb0] at h; dsimp only at h
      cases rest with
      | nil => exact Bool.noConfusion h
      | cons b1 rest1 =>
        dsimp only at h
        have h1 := hgoals b1 (List.mem_cons_of_mem _ List.mem_cons_self)
        cases hb1 : boundClosesF state b1
        · rw [hb1] at h; dsimp only at h
          cases rest1 with
          | nil => exact Bool.noConfusion h
          | cons b2 rest2 =>
            dsimp only at h
            have h2 := hgoals b2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
            rw [boundClosesF_eq h2.1 h2.2] at h
            exact knownCloses_of_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) h
        · rw [boundClosesF_eq h1.1 h1.2] at hb1
          exact knownCloses_of_mem (List.mem_cons_of_mem _ List.mem_cons_self) hb1
    · rw [boundClosesF_eq h0.1 h0.2] at hb0
      exact knownCloses_of_mem List.mem_cons_self hb0

def edgeAxis (mask goal stride lm : Nat) : Nat :=
  let neg := Nat.xor mask goal
  Nat.land (Nat.lor (Nat.land (Nat.shiftRight goal stride) neg)
    (Nat.land goal (Nat.shiftRight neg stride))) lm

def edgePack (mask goal : Nat) : Nat :=
  Nat.lor (edgeAxis mask goal 1 0x5555555555555555)
    (Nat.lor (Nat.shiftLeft (edgeAxis mask goal 2 0x3333333333333333) 64)
      (Nat.lor (Nat.shiftLeft (edgeAxis mask goal 4 0x0f0f0f0f0f0f0f0f) 128)
        (Nat.lor (Nat.shiftLeft (edgeAxis mask goal 8 0x00ff00ff00ff00ff) 192)
          (Nat.lor (Nat.shiftLeft (edgeAxis mask goal 16 0x0000ffff0000ffff) 256)
            (Nat.shiftLeft (edgeAxis mask goal 32 0x00000000ffffffff) 320)))))

def sepAxis (stride lm w : Nat) : Nat :=
  Nat.land (Nat.xor (Nat.shiftRight w stride) w) lm

def sepPack (w : Nat) : Nat :=
  Nat.lor (sepAxis 1 0x5555555555555555 w)
    (Nat.lor (Nat.shiftLeft (sepAxis 2 0x3333333333333333 w) 64)
      (Nat.lor (Nat.shiftLeft (sepAxis 4 0x0f0f0f0f0f0f0f0f w) 128)
        (Nat.lor (Nat.shiftLeft (sepAxis 8 0x00ff00ff00ff00ff w) 192)
          (Nat.lor (Nat.shiftLeft (sepAxis 16 0x0000ffff0000ffff w) 256)
            (Nat.shiftLeft (sepAxis 32 0x00000000ffffffff w) 320)))))

def orSep (ws : List Nat) : Nat :=
  List.rec 0 (fun w _ ih => Nat.lor (sepPack w) ih) ws

theorem edgeAxis_live {mask goal stride lm k : Nat} {ws : List Nat}
    (hgm : Masked mask goal) (hlive : LiveBin mask goal k ws.toFinset)
    {n : Nat} (he : (edgeAxis mask goal stride lm).testBit n = true) :
    ∃ w ∈ ws, (sepAxis stride lm w).testBit n = true := by
  unfold edgeAxis at he
  change (((goal >>> stride &&& (mask ^^^ goal)) ||| (goal &&& ((mask ^^^ goal) >>> stride))) &&& lm).testBit n = true at he
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftRight, Bool.and_eq_true, Bool.or_eq_true] at he
  obtain ⟨hcases, hlm⟩ := he
  have hpm : ∀ j, goal.testBit j = true → mask.testBit j = true := fun j hg => by
    have e := congrArg (fun x => x.testBit j) hgm
    simp only [Nat.testBit_and, hg, Bool.true_and] at e; exact e
  have hnm : ∀ j, (mask ^^^ goal).testBit j = true → mask.testBit j = true ∧ goal.testBit j = false := fun j hn => by
    rw [Nat.testBit_xor] at hn
    cases hm : mask.testBit j <;> cases hg : goal.testBit j <;> simp_all
  have hsep : ∃ w ∈ ws, w.testBit (stride + n) ≠ w.testBit n := by
    by_contra! hall
    rcases hcases with ⟨hg1, hn0⟩ | ⟨hg0, hn1⟩
    · have h1 := hpm (stride + n) hg1
      have h0 := hnm n hn0
      have eq := liveBin_agrees h1 h0.1 hlive (fun w hw => hall w (List.mem_toFinset.mp hw))
      rw [hg1, h0.2] at eq; exact Bool.noConfusion eq
    · have h0 := hpm n hg0
      have h1 := hnm (stride + n) hn1
      have eq := liveBin_agrees h0 h1.1 hlive (fun w hw => (hall w (List.mem_toFinset.mp hw)).symm)
      rw [hg0, h1.2] at eq; exact Bool.noConfusion eq
  obtain ⟨w, hw, hne⟩ := hsep
  refine ⟨w, hw, ?_⟩
  unfold sepAxis
  change (((w >>> stride) ^^^ w) &&& lm).testBit n = true
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight, hlm, Bool.and_true]
  cases hb1 : w.testBit (stride + n) <;> cases hb2 : w.testBit n <;> simp_all

theorem orSep_testBit {ws : List Nat} {w j : Nat}
    (hw : w ∈ ws) (hb : (sepPack w).testBit j = true) : (orSep ws).testBit j = true := by
  induction ws with
  | nil => cases hw
  | cons x xs ih =>
    change (sepPack x ||| orSep xs).testBit j = true
    rw [Nat.testBit_or, Bool.or_eq_true]
    rcases List.mem_cons.mp hw with rfl | htl
    · exact Or.inl hb
    · exact Or.inr (ih htl)

theorem sepPack_live {mask goal k : Nat} {ws : List Nat}
    (hgm : Masked mask goal) (hlive : LiveBin mask goal k ws.toFinset) :
    Nat.beq (Nat.land (edgePack mask goal) (orSep ws)) (edgePack mask goal) = true := by
  apply Nat.beq_eq.mpr
  apply Nat.eq_of_testBit_eq; intro j
  change ((edgePack mask goal) &&& (orSep ws)).testBit j = (edgePack mask goal).testBit j
  rw [Nat.testBit_and]
  cases he : (edgePack mask goal).testBit j
  · rfl
  · simp only [Bool.true_and]
    have hlane (stride lm shift : Nat)
        (hl : (edgeAxis mask goal stride lm <<< shift).testBit j = true)
        (hs : ∀ w, (sepAxis stride lm w <<< shift).testBit j = true → (sepPack w).testBit j = true) :
        (orSep ws).testBit j = true := by
      rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at hl
      obtain ⟨w, hw, hsw⟩ := edgeAxis_live hgm hlive hl.2
      apply orSep_testBit hw
      apply hs w
      rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hl.1, hsw⟩
    unfold edgePack at he
    change (edgeAxis mask goal 1 0x5555555555555555 |||
      ((edgeAxis mask goal 2 0x3333333333333333 <<< 64) |||
        ((edgeAxis mask goal 4 0x0f0f0f0f0f0f0f0f <<< 128) |||
          ((edgeAxis mask goal 8 0x00ff00ff00ff00ff <<< 192) |||
            ((edgeAxis mask goal 16 0x0000ffff0000ffff <<< 256) |||
              (edgeAxis mask goal 32 0x00000000ffffffff <<< 320)))))).testBit j = true at he
    simp only [Nat.testBit_or, Bool.or_eq_true] at he
    rcases he with h0 | h1 | h2 | h3 | h4 | h5
    · obtain ⟨w, hw, hsw⟩ := edgeAxis_live hgm hlive h0
      exact orSep_testBit hw (by
        unfold sepPack
        change (sepAxis 1 0x5555555555555555 w ||| _).testBit j = true
        simp [Nat.testBit_or, hsw])
    · exact hlane 2 0x3333333333333333 64 h1 (fun w hw => by
        unfold sepPack
        change (_ ||| ((sepAxis 2 0x3333333333333333 w <<< 64) ||| _)).testBit j = true
        simp [Nat.testBit_or, hw])
    · exact hlane 4 0x0f0f0f0f0f0f0f0f 128 h2 (fun w hw => by
        unfold sepPack
        change (_ ||| (_ ||| ((sepAxis 4 0x0f0f0f0f0f0f0f0f w <<< 128) ||| _))).testBit j = true
        simp [Nat.testBit_or, hw])
    · exact hlane 8 0x00ff00ff00ff00ff 192 h3 (fun w hw => by
        unfold sepPack
        change (_ ||| (_ ||| (_ ||| ((sepAxis 8 0x00ff00ff00ff00ff w <<< 192) ||| _)))).testBit j = true
        simp [Nat.testBit_or, hw])
    · exact hlane 16 0x0000ffff0000ffff 256 h4 (fun w hw => by
        unfold sepPack
        change (_ ||| (_ ||| (_ ||| (_ ||| ((sepAxis 16 0x0000ffff0000ffff w <<< 256) ||| _))))).testBit j = true
        simp [Nat.testBit_or, hw])
    · exact hlane 32 0x00000000ffffffff 320 h5 (fun w hw => by
        unfold sepPack
        change (_ ||| (_ ||| (_ ||| (_ ||| (_ ||| (sepAxis 32 0x00000000ffffffff w <<< 320)))))).testBit j = true
        simp [Nat.testBit_or, hw])

def mapSep (ws : List Nat) : List (Nat × Nat) :=
  List.rec [] (fun w _ ih => (w, sepPack w) :: ih) ws

def forceSepPairs : List Nat → (List (Nat × Nat) → Bool) → Bool
  | [], k => k []
  | w :: ws, k => forceW (sepPack w) (fun sp => forceSepPairs ws (fun rest => k ((w, sp) :: rest)))

theorem forceSepPairs_eq (ws : List Nat) (k : List (Nat × Nat) → Bool) :
    forceSepPairs ws k = k (mapSep ws) := by
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih =>
    change forceW (sepPack w) (fun sp => forceSepPairs ws (fun rest => k ((w, sp) :: rest))) = _
    rw [forceW_eq, ih]; rfl

def orSepAll (ps : List (Nat × Nat)) : Nat :=
  List.rec 0 (fun p _ ih => Nat.lor p.2 ih) ps

def orSepSkip (x : Nat) (ps : List (Nat × Nat)) : Nat :=
  List.rec 0 (fun p _ ih => Bool.rec (Nat.lor p.2 ih) ih (Nat.beq p.1 x)) ps

def orSepSkip2 (x y : Nat) (ps : List (Nat × Nat)) : Nat :=
  List.rec 0 (fun p _ ih => Bool.rec (Bool.rec (Nat.lor p.2 ih) ih (Nat.beq p.1 y)) ih (Nat.beq p.1 x)) ps

theorem orSepAll_mapSep (ws : List Nat) : orSepAll (mapSep ws) = orSep ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih => change Nat.lor (sepPack w) (orSepAll (mapSep ws)) = Nat.lor (sepPack w) (orSep ws); rw [ih]

theorem orSepSkip_mapSep (x : Nat) (ws : List Nat) :
    orSepSkip x (mapSep ws) = orSep (dropVal true x ws) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec (Nat.lor (sepPack w) (orSepSkip x (mapSep ws))) (orSepSkip x (mapSep ws)) (Nat.beq w x) =
      orSep (bsel (Nat.beq w x) (dropVal true x ws) (w :: dropVal true x ws))
    rw [ih]
    cases Nat.beq w x <;> rfl

theorem dropVal_comm (x y : Nat) (l : List Nat) :
    dropVal true y (dropVal true x l) = dropVal true x (dropVal true y l) := by
  induction l with
  | nil => rfl
  | cons u us ih =>
    change dropVal true y (bsel (Nat.beq u x) (dropVal true x us) (u :: dropVal true x us)) =
      dropVal true x (bsel (Nat.beq u y) (dropVal true y us) (u :: dropVal true y us))
    cases hux : Nat.beq u x <;> cases huy : Nat.beq u y
    · simp only [bsel_false]
      change bsel (Nat.beq u y) (dropVal true y (dropVal true x us)) (u :: dropVal true y (dropVal true x us)) =
        bsel (Nat.beq u x) (dropVal true x (dropVal true y us)) (u :: dropVal true x (dropVal true y us))
      rw [huy, hux, bsel_false, bsel_false, ih]
    · simp only [bsel_false, bsel_true]
      change bsel (Nat.beq u y) (dropVal true y (dropVal true x us)) (u :: dropVal true y (dropVal true x us)) = _
      rw [huy, bsel_true, ih]
    · simp only [bsel_true, bsel_false]
      change _ = bsel (Nat.beq u x) (dropVal true x (dropVal true y us)) (u :: dropVal true x (dropVal true y us))
      rw [hux, bsel_true, ih]
    · simp only [bsel_true]; exact ih

theorem orSepSkip2_mapSep (x y : Nat) (ws : List Nat) :
    orSepSkip2 x y (mapSep ws) = orSep (dropVal true y (dropVal true x ws)) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec (Bool.rec (Nat.lor (sepPack w) (orSepSkip2 x y (mapSep ws))) (orSepSkip2 x y (mapSep ws)) (Nat.beq w y))
      (orSepSkip2 x y (mapSep ws)) (Nat.beq w x) =
      orSep (dropVal true y (bsel (Nat.beq w x) (dropVal true x ws) (w :: dropVal true x ws)))
    rw [ih]
    cases hx : Nat.beq w x
    · rw [bsel_false]
      change Bool.rec (Nat.lor (sepPack w) (orSep (dropVal true y (dropVal true x ws))))
        (orSep (dropVal true y (dropVal true x ws))) (Nat.beq w y) =
        orSep (bsel (Nat.beq w y) (dropVal true y (dropVal true x ws)) (w :: dropVal true y (dropVal true x ws)))
      cases Nat.beq w y <;> rfl
    · rw [bsel_true]

def treeBlockF (lo hi : Nat) (f : Nat → Bool) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ next a b =>
      Bool.rec true
        (let m := Nat.shiftRight (Nat.add a b) 1
         Bool.rec (Bool.rec false (next m b) (next a m)) (f a) (Nat.beq a m))
        (Nat.blt a b)) (Nat.add (Nat.sub hi lo) 1)) lo hi

theorem treeBlockF_eq (lo hi : Nat) (f : Nat → Bool) : treeBlockF lo hi f = treeBlock lo hi f := by
  unfold treeBlockF treeBlock
  suffices ∀ steps a b,
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          Bool.rec true
            (let m := Nat.shiftRight (Nat.add x y) 1
             Bool.rec (Bool.rec false (next m y) (next x m)) (f x) (Nat.beq x m))
            (Nat.blt x y)) steps) a b =
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          if Nat.blt x y then
            let m := (x + y) / 2
            if Nat.beq x m then f x else next x m && next m y
          else true) steps) a b from
    this (hi - lo + 1) lo hi
  intro steps
  induction steps with
  | zero => intro a b; rfl
  | succ s ih =>
    intro a b
    dsimp only
    have hdiv : Nat.shiftRight (Nat.add a b) 1 = (a + b) / 2 := by
      change (a + b) >>> 1 = (a + b) / 2; rw [Nat.shiftRight_eq_div_pow]
    rw [hdiv]
    cases Nat.blt a b
    · rfl
    · cases Nat.beq a ((a + b) / 2)
      · rw [ih, ih]
        change Bool.rec false _ _ = (_ && _)
        cases (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true) _ s) a ((a + b) / 2) <;> rfl
      · rfl

theorem treeBlockF_at {lo hi : Nat} {f : Nat → Bool} (h : treeBlockF lo hi f = true) :
    ∀ {i : Nat}, lo ≤ i → i < hi → f i = true := by
  rw [treeBlockF_eq] at h; exact treeBlock_at h

def forceWC (w : Nat) (k : Nat → Bool × List (Nat × Nat)) : Bool × List (Nat × Nat) :=
  match w with
  | 0 => k 0
  | m + 1 => k (m + 1)

theorem forceWC_eq (w : Nat) (k : Nat → Bool × List (Nat × Nat)) : forceWC w k = k w := by
  cases w <;> rfl

def closeFallbackV4 (mask goal ep : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (st : Nat × List Nat × List (Nat × Nat × Nat)) (sp : Nat) : Bool :=
  Bool.rec true
    (Bool.rec
      (Bool.rec true false (dagPartF st.2.1 goal (Nat.xor mask goal)))
      true (knownClosesTopF bounds st))
    (Nat.beq (Nat.land ep sp) ep)

theorem closeFallbackV4_open {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    {st : Nat × List Nat × List (Nat × Nat × Nat)}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (nd : st.2.1.Nodup) {k : Nat} (hk : k ≤ st.1)
    (hlive : LiveBin mask goal k st.2.1.toFinset) :
    closeFallbackV4 mask goal (edgePack mask goal) bounds st (orSep st.2.1) = false := by
  unfold closeFallbackV4
  have hsp : Nat.beq (Nat.land (edgePack mask goal) (orSep st.2.1)) (edgePack mask goal) = true :=
    sepPack_live hgm hlive
  have hkt : knownClosesTopF bounds st = false := by
    cases h : knownClosesTopF bounds st
    · rfl
    · have hk1 := knownClosesTopF_imp hgoals h
      have hk0 := knownCloses_sound hknown hsub nd hk hlive
      rw [hk0] at hk1; exact Bool.noConfusion hk1
  have hdp : dagPartF st.2.1 goal (Nat.xor mask goal) = true := by
    have heq : dagPartF st.2.1 goal (Nat.xor mask goal) = dagPart st.2.1 goal (mask ^^^ goal) :=
      dagPartF_eq st.2.1 goal (mask ^^^ goal)
    rw [heq]; exact dagPart_live hgm hlive
  rw [hsp, hkt, hdp]

def stepLeafV4 (mask goal ep count : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel1 z spZ baseSp : Nat) (rest : List Nat) (hist1 : List (Nat × Nat × Nat))
    (tok : Nat) (cur : List (Nat × Nat)) : Bool × List (Nat × Nat) :=
  match cur with
  | (t, code) :: tl =>
    Bool.rec
      (closeFallbackV4 mask goal ep bounds (fuel1, z :: rest, hist1) (Nat.lor spZ baseSp), cur)
      (Bool.rec
        (match nthBound bounds (Nat.shiftRight code 1) with
         | none => (false, tl)
         | some b => (boundClosesF (fuel1, z :: rest, hist1) b, tl))
        (let dest := Nat.shiftRight code 1
         let ok := Bool.rec false
           (match states dest with
            | none => false
            | some saved => Bool.rec false (eqListN saved.2.1 (insertSortedF z rest)) (Nat.beq saved.1 fuel1))
           (Nat.blt dest count)
         (ok, tl))
        (Nat.beq (Nat.land code 1) 0))
      (Nat.beq tok t)
  | [] =>
    (closeFallbackV4 mask goal ep bounds (fuel1, z :: rest, hist1) (Nat.lor spZ baseSp), [])

theorem stepLeafV4_ref {mask goal count fuel1 z tok : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {rest : List Nat} {hist1 : List (Nat × Nat × Nat)} {cur : List (Nat × Nat)}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (nd : (z :: rest).Nodup) {k : Nat} (hk : k ≤ fuel1)
    (hlive : LiveBin mask goal k (z :: rest).toFinset)
    (h : (stepLeafV4 mask goal (edgePack mask goal) count bounds states fuel1 z (sepPack z) (orSep rest) rest hist1 tok cur).1 = true) :
    ∃ dest < count, ∃ saved, states dest = some saved ∧ saved.1 = fuel1 ∧ saved.2.1 = insertSorted z rest := by
  have hfb : closeFallbackV4 mask goal (edgePack mask goal) bounds (fuel1, z :: rest, hist1) (Nat.lor (sepPack z) (orSep rest)) = false :=
    closeFallbackV4_open (st := (fuel1, z :: rest, hist1)) hgm hknown hsub hgoals nd hk hlive
  unfold stepLeafV4 at h
  cases cur with
  | nil => dsimp only at h; rw [hfb] at h; exact Bool.noConfusion h
  | cons hd tl =>
    obtain ⟨t, code⟩ := hd
    dsimp only at h
    cases ht : Nat.beq tok t
    · rw [ht] at h; dsimp only at h; rw [hfb] at h; exact Bool.noConfusion h
    · rw [ht] at h; dsimp only at h
      cases hev : Nat.beq (Nat.land code 1) 0
      · rw [hev] at h; dsimp only at h
        cases hb : nthBound bounds (Nat.shiftRight code 1) with
        | none => rw [hb] at h; exact Bool.noConfusion h
        | some b =>
          rw [hb] at h; dsimp only at h
          have hmem := nthBound_mem hb
          have hg := hgoals b hmem
          rw [boundClosesF_eq hg.1 hg.2] at h
          have h0 := boundCloses_sound (state := (fuel1, z :: rest, hist1)) (hknown b hmem) (hsub b hmem) nd hk hlive
          rw [h0] at h; exact Bool.noConfusion h
      · rw [hev] at h; dsimp only at h
        cases hlt : Nat.blt (Nat.shiftRight code 1) count
        · rw [hlt] at h; exact Bool.noConfusion h
        · rw [hlt] at h; dsimp only at h
          cases hst : states (Nat.shiftRight code 1) with
          | none => rw [hst] at h; exact Bool.noConfusion h
          | some saved =>
            rw [hst] at h; dsimp only at h
            cases hf : Nat.beq saved.1 fuel1
            · rw [hf] at h; exact Bool.noConfusion h
            · rw [hf] at h; dsimp only at h
              rw [eqListN_eq, insertSortedF_eq, beq_iff_eq] at h
              exact ⟨Nat.shiftRight code 1, Nat.blt_eq.mp hlt, saved, hst, Nat.beq_eq.mp hf, h⟩

def checkKeepsV4 (mask goal ep count : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n z spZ spAll spNoA spNoB spNoAB : Nat)
    (ws0 wsNoA wsNoB wsNoAB : List Nat) (hist1 : List (Nat × Nat × Nat))
    (tokBase : Nat) (cur : List (Nat × Nat)) : Bool × List (Nat × Nat) :=
  let (ok0, c1) : Bool × List (Nat × Nat) := Bool.rec
    (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spNoAB wsNoAB hist1 tokBase cur)
    (true, cur) (Nat.blt fuel (Nat.sub n 1))
  Bool.rec (false, c1)
    (let (ok1, c2) : Bool × List (Nat × Nat) := Bool.rec
       (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spNoB wsNoB hist1 (Nat.add tokBase 1) c1)
       (true, c1) (Nat.blt fuel n)
     Bool.rec (false, c2)
       (let (ok2, c3) : Bool × List (Nat × Nat) := Bool.rec
          (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spNoA wsNoA hist1 (Nat.add tokBase 2) c2)
          (true, c2) (Nat.blt fuel n)
        Bool.rec (false, c3)
          (Bool.rec
            (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spAll ws0 hist1 (Nat.add tokBase 3) c3)
            (true, c3) (Nat.blt fuel (Nat.add n 1)))
          ok2)
       ok1)
    ok0

theorem checkKeepsV4_at {mask goal ep count fuel fuel1 n z spZ spAll spNoA spNoB spNoAB tokBase : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 wsNoA wsNoB wsNoAB : List Nat} {hist1 : List (Nat × Nat × Nat)} {cur : List (Nat × Nat)}
    (h : (checkKeepsV4 mask goal ep count bounds states fuel fuel1 n z spZ spAll spNoA spNoB spNoAB
      ws0 wsNoA wsNoB wsNoAB hist1 tokBase cur).1 = true)
    (keepA keepB : Bool) :
    match keepA, keepB with
    | false, false => Nat.blt fuel (n - 1) = true ∨ ∃ c, (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spNoAB wsNoAB hist1 tokBase c).1 = true
    | true, false => Nat.blt fuel n = true ∨ ∃ c, (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spNoB wsNoB hist1 (tokBase + 1) c).1 = true
    | false, true => Nat.blt fuel n = true ∨ ∃ c, (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spNoA wsNoA hist1 (tokBase + 2) c).1 = true
    | true, true => Nat.blt fuel (n + 1) = true ∨ ∃ c, (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spAll ws0 hist1 (tokBase + 3) c).1 = true := by
  unfold checkKeepsV4 at h
  generalize hp0 : (Bool.rec (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spNoAB wsNoAB hist1 tokBase cur)
    (true, cur) (Nat.blt fuel (Nat.sub n 1)) : Bool × List (Nat × Nat)) = p0 at h
  obtain ⟨ok0, c1⟩ := p0
  dsimp only at h
  cases ok0
  · exact Bool.noConfusion h
  · dsimp only at h
    generalize hp1 : (Bool.rec (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spNoB wsNoB hist1 (Nat.add tokBase 1) c1)
      (true, c1) (Nat.blt fuel n) : Bool × List (Nat × Nat)) = p1 at h
    obtain ⟨ok1, c2⟩ := p1
    dsimp only at h
    cases ok1
    · exact Bool.noConfusion h
    · dsimp only at h
      generalize hp2 : (Bool.rec (stepLeafV4 mask goal ep count bounds states fuel1 z spZ spNoA wsNoA hist1 (Nat.add tokBase 2) c2)
        (true, c2) (Nat.blt fuel n) : Bool × List (Nat × Nat)) = p2 at h
      obtain ⟨ok2, c3⟩ := p2
      dsimp only at h
      cases ok2
      · exact Bool.noConfusion h
      · dsimp only at h
        cases keepA <;> cases keepB
        · cases hw : Nat.blt fuel (n - 1)
          · have hw' : Nat.blt fuel (Nat.sub n 1) = false := hw
            rw [hw'] at hp0; exact Or.inr ⟨cur, congrArg Prod.fst hp0⟩
          · exact Or.inl rfl
        · cases hw : Nat.blt fuel n
          · rw [hw] at hp2; exact Or.inr ⟨c2, congrArg Prod.fst hp2⟩
          · exact Or.inl rfl
        · cases hw : Nat.blt fuel n
          · rw [hw] at hp1; exact Or.inr ⟨c1, congrArg Prod.fst hp1⟩
          · exact Or.inl rfl
        · cases hw : Nat.blt fuel (n + 1)
          · have hw' : Nat.blt fuel (Nat.add n 1) = false := hw
            rw [hw'] at h; exact Or.inr ⟨c3, h⟩
          · exact Or.inl rfl

def checkOpV4 (mask goal ep count : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n x y rawZ op : Nat) (spAll spNoA spNoB spNoAB : Nat)
    (ws0 wsNoA wsNoB wsNoAB : List Nat) (hist : List (Nat × Nat × Nat))
    (tokAB : Nat) (cur : List (Nat × Nat)) : Bool × List (Nat × Nat) :=
  forceWC (canonF mask rawZ) (fun z =>
    Bool.rec
      (Bool.rec
        (forceWC (sepPack z) (fun spZ =>
          checkKeepsV4 mask goal ep count bounds states fuel fuel1 n z spZ spAll spNoA spNoB spNoAB
            ws0 wsNoA wsNoB wsNoAB ((z, x, y) :: hist) (Nat.shiftLeft (Nat.add tokAB op) 2) cur))
        (true, cur) (memN z ws0))
      (true, cur) (Nat.beq z 0))

def check4OpsV4 (mask goal ep count : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n x nx y : Nat) (spAll spNoA spNoB spNoAB : Nat)
    (ws0 wsNoA wsNoB wsNoAB : List Nat) (hist : List (Nat × Nat × Nat))
    (tokAB : Nat) (cur : List (Nat × Nat)) : Bool × List (Nat × Nat) :=
  let (o0, c1) := checkOpV4 mask goal ep count bounds states fuel fuel1 n x y (Nat.land x y) 0 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur
  Bool.rec (false, c1)
    (let (o1, c2) := checkOpV4 mask goal ep count bounds states fuel fuel1 n x y (Nat.lor x y) 1 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c1
     Bool.rec (false, c2)
       (let (o2, c3) := checkOpV4 mask goal ep count bounds states fuel fuel1 n x y (Nat.land x (Nat.xor mask y)) 2 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c2
        Bool.rec (false, c3)
          (checkOpV4 mask goal ep count bounds states fuel fuel1 n x y (Nat.land nx y) 3 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c3) o2) o1) o0

theorem check4OpsV4_at {mask goal ep count fuel fuel1 n x y spAll spNoA spNoB spNoAB tokAB op : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 wsNoA wsNoB wsNoAB : List Nat} {hist : List (Nat × Nat × Nat)} {cur : List (Nat × Nat)}
    (hop : op < 4)
    (h : (check4OpsV4 mask goal ep count bounds states fuel fuel1 n x (Nat.xor mask x) y
      spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur).1 = true) :
    let z := binOp mask op x y
    z = 0 ∨ ws0.contains z = true ∨
      ∃ c, (checkKeepsV4 mask goal ep count bounds states fuel fuel1 n z (sepPack z) spAll spNoA spNoB spNoAB
        ws0 wsNoA wsNoB wsNoAB ((z, x, y) :: hist) (Nat.shiftLeft (Nat.add tokAB op) 2) c).1 = true := by
  unfold check4OpsV4 at h
  generalize hp0 : checkOpV4 mask goal ep count bounds states fuel fuel1 n x y (Nat.land x y) 0 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur = p0 at h
  obtain ⟨o0, c1⟩ := p0; dsimp only at h
  cases o0
  · exact Bool.noConfusion h
  · dsimp only at h
    generalize hp1 : checkOpV4 mask goal ep count bounds states fuel fuel1 n x y (Nat.lor x y) 1 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c1 = p1 at h
    obtain ⟨o1, c2⟩ := p1; dsimp only at h
    cases o1
    · exact Bool.noConfusion h
    · dsimp only at h
      generalize hp2 : checkOpV4 mask goal ep count bounds states fuel fuel1 n x y (Nat.land x (Nat.xor mask y)) 2 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c2 = p2 at h
      obtain ⟨o2, c3⟩ := p2; dsimp only at h
      cases o2
      · exact Bool.noConfusion h
      · dsimp only at h
        have extract (rawZ op' : Nat) (c0 : List (Nat × Nat))
            (hz : canon mask rawZ = binOp mask op' x y)
            (hok : (checkOpV4 mask goal ep count bounds states fuel fuel1 n x y rawZ op' spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c0).1 = true) :
            binOp mask op' x y = 0 ∨ ws0.contains (binOp mask op' x y) = true ∨
              ∃ c, (checkKeepsV4 mask goal ep count bounds states fuel fuel1 n (binOp mask op' x y) (sepPack (binOp mask op' x y))
                spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB ((binOp mask op' x y, x, y) :: hist) (Nat.shiftLeft (Nat.add tokAB op') 2) c).1 = true := by
          unfold checkOpV4 at hok
          rw [forceWC_eq, canonF_eq, hz] at hok
          cases h0 : Nat.beq (binOp mask op' x y) 0
          · rw [h0] at hok; dsimp only at hok
            cases hm : memN (binOp mask op' x y) ws0
            · rw [hm] at hok; dsimp only at hok
              rw [forceWC_eq] at hok
              exact Or.inr (Or.inr ⟨c0, hok⟩)
            · rw [memN_eq] at hm; exact Or.inr (Or.inl hm)
          · exact Or.inl (Nat.beq_eq.mp h0)
        rcases (by omega : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3) with rfl | rfl | rfl | rfl
        · exact extract _ 0 cur rfl (congrArg Prod.fst hp0)
        · exact extract _ 1 c1 rfl (congrArg Prod.fst hp1)
        · exact extract _ 2 c2 rfl (congrArg Prod.fst hp2)
        · exact extract _ 3 c3 rfl h

def loopB_V4 (mask goal ep count : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n a x nx spAll spNoA : Nat) (ws0 wsNoA : List Nat) (ps : List (Nat × Nat)) (hist : List (Nat × Nat × Nat)) :
    Nat → Nat → List (Nat × Nat) → Bool × List (Nat × Nat)
  | 0, _, c => (true, c)
  | rem + 1, b, cur =>
    let y := getDN ws0 b
    let wsNoB := dropValF true y ws0
    let wsNoAB := dropValF true y wsNoA
    forceWC (orSepSkip y ps) (fun spNoB =>
      forceWC (orSepSkip2 x y ps) (fun spNoAB =>
        let tokAB := Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2
        let (ok, cur1) := check4OpsV4 mask goal ep count bounds states fuel fuel1 n x nx y spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur
        Bool.rec (false, cur1) (loopB_V4 mask goal ep count bounds states fuel fuel1 n a x nx spAll spNoA ws0 wsNoA ps hist rem (Nat.add b 1) cur1) ok))

theorem loopB_V4_at {mask goal ep count fuel fuel1 n a x nx spAll spNoA : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 wsNoA : List Nat} {ps : List (Nat × Nat)} {hist : List (Nat × Nat × Nat)}
    {rem b0 b : Nat} {cur : List (Nat × Nat)}
    (hb1 : b0 ≤ b) (hb2 : b < b0 + rem)
    (h : (loopB_V4 mask goal ep count bounds states fuel fuel1 n a x nx spAll spNoA ws0 wsNoA ps hist rem b0 cur).1 = true) :
    let y := getDN ws0 b
    ∃ c, (check4OpsV4 mask goal ep count bounds states fuel fuel1 n x nx y spAll spNoA
      (orSepSkip y ps) (orSepSkip2 x y ps) ws0 wsNoA (dropValF true y ws0) (dropValF true y wsNoA)
      hist (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2) c).1 = true := by
  induction rem generalizing b0 cur with
  | zero => omega
  | succ r ih =>
    unfold loopB_V4 at h; dsimp only at h
    rw [forceWC_eq, forceWC_eq] at h
    cases hp : check4OpsV4 mask goal ep count bounds states fuel fuel1 n x nx (getDN ws0 b0) spAll spNoA
      (orSepSkip (getDN ws0 b0) ps) (orSepSkip2 x (getDN ws0 b0) ps) ws0 wsNoA
      (dropValF true (getDN ws0 b0) ws0) (dropValF true (getDN ws0 b0) wsNoA)
      hist (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b0) 2) cur with
    | mk ok cur1 =>
      rw [hp] at h; dsimp only at h
      cases ok
      · exact Bool.noConfusion h
      · dsimp only at h
        by_cases heq : b = b0
        · subst heq; exact ⟨cur, by rw [hp]⟩
        · exact ih (by change b0 + 1 ≤ b; omega) (by change b < (b0 + 1) + r; omega) h

def loopA_V4 (mask goal ep count : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n spAll : Nat) (ws0 : List Nat) (ps : List (Nat × Nat)) (hist : List (Nat × Nat × Nat)) :
    Nat → Nat → List (Nat × Nat) → Bool × List (Nat × Nat)
  | 0, _, c => (true, c)
  | rem + 1, a, cur =>
    let x := getDN ws0 a
    let wsNoA := dropValF true x ws0
    forceWC (Nat.xor mask x) (fun nx =>
      forceWC (orSepSkip x ps) (fun spNoA =>
        let (ok, cur1) := loopB_V4 mask goal ep count bounds states fuel fuel1 n a x nx spAll spNoA ws0 wsNoA ps hist (Nat.sub n (Nat.add a 1)) (Nat.add a 1) cur
        Bool.rec (false, cur1) (loopA_V4 mask goal ep count bounds states fuel fuel1 n spAll ws0 ps hist rem (Nat.add a 1) cur1) ok))

theorem loopA_V4_at {mask goal ep count fuel fuel1 n spAll : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 : List Nat} {ps : List (Nat × Nat)} {hist : List (Nat × Nat × Nat)}
    {rem a0 a : Nat} {cur : List (Nat × Nat)}
    (ha1 : a0 ≤ a) (ha2 : a < a0 + rem)
    (h : (loopA_V4 mask goal ep count bounds states fuel fuel1 n spAll ws0 ps hist rem a0 cur).1 = true) :
    let x := getDN ws0 a
    ∃ c, (loopB_V4 mask goal ep count bounds states fuel fuel1 n a x (Nat.xor mask x) spAll
      (orSepSkip x ps) ws0 (dropValF true x ws0) ps hist (Nat.sub n (Nat.add a 1)) (Nat.add a 1) c).1 = true := by
  induction rem generalizing a0 cur with
  | zero => omega
  | succ r ih =>
    unfold loopA_V4 at h; dsimp only at h
    rw [forceWC_eq, forceWC_eq] at h
    cases hp : loopB_V4 mask goal ep count bounds states fuel fuel1 n a0 (getDN ws0 a0) (Nat.xor mask (getDN ws0 a0)) spAll
      (orSepSkip (getDN ws0 a0) ps) ws0 (dropValF true (getDN ws0 a0) ws0) ps hist (Nat.sub n (Nat.add a0 1)) (Nat.add a0 1) cur with
    | mk ok cur1 =>
      rw [hp] at h; dsimp only at h
      cases ok
      · exact Bool.noConfusion h
      · dsimp only at h
        by_cases heq : a = a0
        · subst heq; exact ⟨cur, by rw [hp]⟩
        · exact ih (by change a0 + 1 ≤ a; omega) (by change a < (a0 + 1) + r; omega) h

def dagCheckNodeV4 (mask goal ep : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (cursors : Nat → List (Nat × Nat)) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some (fuel, ws, hist) =>
    forceWs ws (fun ws0 =>
      let n := lenN ws0
      Bool.rec
        (Bool.rec
          (Bool.rec false
            (forceSepPairs ws0 (fun ps =>
              forceW (orSepAll ps) (fun spAll =>
                (loopA_V4 mask goal ep count bounds states fuel (Nat.sub fuel 1) n spAll ws0 ps hist n 0 (cursors (Nat.add i 1))).1)))
            (Nat.blt n 17))
          true (Nat.beq fuel 0))
        false (memN goal ws0))

def stepRootV4 (mask goal ep count fuel : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (ws : List Nat) (tok : Nat) (cur : List (Nat × Nat)) : Bool × List (Nat × Nat) :=
  Bool.rec
    (match cur with
     | (t, code) :: tl =>
       Bool.rec
         (closeFallbackV4 mask goal ep bounds (fuel, ws, []) (orSep ws), cur)
         (Bool.rec
           (match nthBound bounds (Nat.shiftRight code 1) with
            | none => (false, tl)
            | some b => (boundClosesF (fuel, ws, []) b, tl))
           (let dest := Nat.shiftRight code 1
            let ok := Bool.rec false
              (match states dest with
               | none => false
               | some saved => Bool.rec false (eqListN saved.2.1 ws) (Nat.beq saved.1 fuel))
              (Nat.blt dest count)
            (ok, tl))
           (Nat.beq (Nat.land code 1) 0))
         (Nat.beq tok t)
     | [] =>
       (closeFallbackV4 mask goal ep bounds (fuel, ws, []) (orSep ws), []))
    (true, cur) (Nat.blt (Nat.add fuel 1) (lenN ws))

def loopRootsV4 (mask goal ep count fuel : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (stock : List Nat) : Nat → Nat → List (Nat × Nat) → Bool × List (Nat × Nat)
  | 0, _, c => (true, c)
  | rem + 1, tok, cur =>
    let ws := subsetWordsF stock tok
    let (ok, cur1) := stepRootV4 mask goal ep count fuel bounds states ws tok cur
    Bool.rec (false, cur1) (loopRootsV4 mask goal ep count fuel bounds states stock rem (Nat.add tok 1) cur1) ok

def dagCheckRootsV4 (mask goal ep count : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (rootCur : List (Nat × Nat)) (stock : List Nat) (fuel : Nat) : Bool :=
  (loopRootsV4 mask goal ep count fuel bounds states stock (Nat.shiftLeft 1 (lenN stock)) 0 rootCur).1

theorem loopRootsV4_at {mask goal ep count fuel : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {stock : List Nat} {rem t0 tok : Nat} {cur : List (Nat × Nat)}
    (ht1 : t0 ≤ tok) (ht2 : tok < t0 + rem)
    (h : (loopRootsV4 mask goal ep count fuel bounds states stock rem t0 cur).1 = true) :
    ∃ c, (stepRootV4 mask goal ep count fuel bounds states (subsetWordsF stock tok) tok c).1 = true := by
  induction rem generalizing t0 cur with
  | zero => omega
  | succ r ih =>
    unfold loopRootsV4 at h; dsimp only at h
    cases hp : stepRootV4 mask goal ep count fuel bounds states (subsetWordsF stock t0) t0 cur with
    | mk ok cur1 =>
      rw [hp] at h; dsimp only at h
      cases ok
      · exact Bool.noConfusion h
      · dsimp only at h
        by_cases heq : tok = t0
        · subst heq; exact ⟨cur, by rw [hp]⟩
        · exact ih (by change t0 + 1 ≤ tok; omega) (by change tok < (t0 + 1) + r; omega) h

theorem dagAllNodesV4 {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {cursors : Nat → List (Nat × Nat)}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (snd : stock.Nodup)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeV4 mask goal (edgePack mask goal) bounds count
      (dagTrace mask stock fuel forest) cursors i = true) :
    ∀ cap i st, i < count → dagTrace mask stock fuel forest i = some st →
      st.1 = cap → ∀ k, k ≤ cap → ¬LiveBin mask goal k st.2.1.toFinset := by
  intro cap
  induction cap using Nat.strong_induction_on with
  | ind cap ih =>
    intro i st hi htr hcap k hk hlive
    obtain ⟨rem, ws, hist⟩ := st
    dsimp only at hcap hlive
    have nd : ws.Nodup := dagTrace_nodup snd htr
    have hchk := hnodes i (Nat.zero_le i) hi
    unfold dagCheckNodeV4 at hchk
    rw [htr] at hchk; dsimp only at hchk
    rw [forceWs_eq, lenN_eq, memN_eq] at hchk
    generalize hS : ws.toFinset = S at hlive
    cases hlive with
    | done =>
      have hgm' : goal ∈ ws := List.mem_toFinset.mp (hS.symm ▸ Finset.mem_singleton_self goal)
      have hc : ws.contains goal = true := List.contains_iff_mem.mpr hgm'
      rw [hc] at hchk; exact Bool.noConfusion hchk
    | @step k' _ a0 b0 op0 ha0 hb0 hab0 _ _ hop0 hz0 hf0 keepA0 keepB0 tail0 =>
      rw [← hS] at ha0 hb0 hf0 tail0
      have hrem_pos : rem ≠ 0 := by omega
      cases hcg : ws.contains goal
      · rw [hcg] at hchk; dsimp only at hchk
        have hrem0 : Nat.beq rem 0 = false := beq_false_ne hrem_pos
        rw [hrem0] at hchk; dsimp only at hchk
        cases h17 : Nat.blt ws.length 17
        · rw [h17] at hchk; exact Bool.noConfusion hchk
        · rw [h17] at hchk; dsimp only at hchk
          rw [forceSepPairs_eq, forceW_eq] at hchk
          have haM : a0 ∈ ws := List.mem_toFinset.mp ha0
          have hbM : b0 ∈ ws := List.mem_toFinset.mp hb0
          obtain ⟨ia0, hia0, hea0⟩ := getElem_index_lt haM
          obtain ⟨ib0, hib0, heb0⟩ := getElem_index_lt hbM
          have hiab_ne : ia0 ≠ ib0 := fun heq => hab0 (hea0.symm.trans (heq ▸ heb0))
          have ⟨a, b, op, keepA, keepB, ha_lt, hab_lt, hb_lt, hop_lt, hax, hby, hzeq, htail⟩ :
              ∃ a b op keepA keepB, a < ws.length ∧ a < b ∧ b < ws.length ∧ op < 4 ∧
                ws.getD a 0 = (if ia0 < ib0 then a0 else b0) ∧
                ws.getD b 0 = (if ia0 < ib0 then b0 else a0) ∧
                binOp mask op (ws.getD a 0) (ws.getD b 0) = binOp mask op0 a0 b0 ∧
                LiveBin mask goal k' (insert (binOp mask op (ws.getD a 0) (ws.getD b 0))
                  (dropIf (!keepA) (ws.getD a 0) (dropIf (!keepB) (ws.getD b 0) ws.toFinset))) := by
            by_cases hlt : ia0 < ib0
            · exact ⟨ia0, ib0, op0, keepA0, keepB0, hia0, hlt, hib0, hop0,
                by simp only [hlt, ite_true]; exact hea0,
                by simp only [hlt, ite_true]; exact heb0,
                by rw [hea0, heb0], by rw [hea0, heb0]; exact tail0⟩
            · obtain ⟨op1, hop1, hopEq⟩ := binOp_comm mask op0 a0 b0 hop0
              have hswap : dropIf (!keepB0) b0 (dropIf (!keepA0) a0 ws.toFinset) =
                  dropIf (!keepA0) a0 (dropIf (!keepB0) b0 ws.toFinset) := by
                ext w; simp only [dropIf]; cases keepA0 <;> cases keepB0 <;> simp [Finset.mem_erase, and_left_comm]
              exact ⟨ib0, ia0, op1, keepB0, keepA0, hib0, by omega, hia0, hop1,
                by simp only [hlt, ite_false]; exact heb0,
                by simp only [hlt, ite_false]; exact hea0,
                by rw [hea0, heb0, hopEq],
                by rw [hea0, heb0, ← hopEq, hswap]; exact tail0⟩
          obtain ⟨cA, hB⟩ := loopA_V4_at (a := a) (Nat.zero_le a) (by omega) hchk
          obtain ⟨cB, hO⟩ := loopB_V4_at (b := b) (by change a + 1 ≤ b; omega) (by change b < (a + 1) + (ws.length - (a + 1)); omega) hB
          simp only [getDN_eq, dropValF_eq, orSepAll_mapSep, orSepSkip_mapSep, orSepSkip2_mapSep] at hO
          set x := ws.getD a 0
          set y := ws.getD b 0
          set z := binOp mask op x y
          have hznz : z ≠ 0 := hzeq.symm ▸ hz0
          have hznm : ws.contains z = false := by
            cases h : ws.contains z
            · rfl
            · exact absurd (List.mem_toFinset.mpr (List.contains_iff_mem.mp h)) (hzeq.symm ▸ hf0)
          rcases check4OpsV4_at hop_lt hO with hz' | hcm | ⟨cK, hK⟩
          · exact hznz hz'
          · rw [hznm] at hcm; exact Bool.noConfusion hcm
          · have hxM : x ∈ ws := by simp only [x, hax]; split; exact haM; exact hbM
            have hyM : y ∈ ws := by simp only [y, hby]; split; exact hbM; exact haM
            have hxy : x ≠ y := by simp only [x, y, hax, hby]; split; exact hab0; exact hab0.symm
            have hzNotW : z ∉ ws := fun hm => by
              have := List.contains_iff_mem.mpr hm; rw [hznm] at this; exact Bool.noConfusion this
            have hdropComm : dropVal true y (dropVal true x ws) = dropVal true x (dropVal true y ws) :=
              dropVal_comm x y ws
            set rest := dropVal (!keepA) x (dropVal (!keepB) y ws)
            have hnd_u : (z :: rest).Nodup :=
              List.nodup_cons.mpr ⟨fun hm => hzNotW (dropVal_mem.mp (dropVal_mem.mp hm).1).1,
                dropVal_nodup (dropVal_nodup nd)⟩
            have hset_u : (z :: rest).toFinset = insert z (dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset)) := by
              ext w; simp only [rest, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, ← dropVal_toFinset]
            have hlive_u : LiveBin mask goal k' (z :: rest).toFinset := by rwa [hset_u]
            have hset_s : (insertSorted z rest).toFinset = (z :: rest).toFinset := by
              ext w; simp only [List.mem_toFinset, insertSorted_mem, List.mem_cons]
            have hlive_s : LiveBin mask goal k' (insertSorted z rest).toFinset := by rwa [hset_s]
            have hlen' : (insertSorted z rest).length =
                ws.length - 1 + (if keepA then 1 else 0) + (if keepB then 1 else 0) :=
              list_len_child (z := z) (keepA := keepA) (keepB := keepB) nd hxM hyM hxy hzNotW
            have hcard' : (insertSorted z rest).length ≤ rem := by
              have hnd_s : (insertSorted z rest).Nodup :=
                insertSorted_nodup (fun hm => hzNotW (dropVal_mem.mp (dropVal_mem.mp hm).1).1) (dropVal_nodup (dropVal_nodup nd))
              have := liveBin_card_le hlive_s
              rw [List.toFinset_card_of_nodup hnd_s] at this; omega
            have h2len : 2 ≤ ws.length := by
              have hsub2 : ({x, y} : Finset Nat) ⊆ ws.toFinset := by
                intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
                · exact List.mem_toFinset.mpr hxM
                · rw [Finset.mem_singleton.mp hw]; exact List.mem_toFinset.mpr hyM
              have hpair : ({x, y} : Finset Nat).card = 2 := Finset.card_pair hxy
              have hc := Finset.card_le_card hsub2
              rw [List.toFinset_card_of_nodup nd] at hc; omega
            have hka := checkKeepsV4_at hK keepA keepB
            have finish {tok' : Nat} {c' : List (Nat × Nat)}
                (hstep : (stepLeafV4 mask goal (edgePack mask goal) count bounds (dagTrace mask stock fuel forest)
                  (Nat.sub rem 1) z (sepPack z) (orSep rest) rest ((z, x, y) :: hist) tok' c').1 = true) : False := by
              obtain ⟨dest, hdest, saved, htr2, hfEq, hwEq⟩ :=
                stepLeafV4_ref hgm hknown hsub hgoals hnd_u (k := k') (by change k' ≤ rem - 1; omega) hlive_u hstep
              exact ih (rem - 1) (by omega) dest saved hdest htr2 hfEq k' (by omega) (hwEq ▸ hlive_s)
            cases keepA <;> cases keepB
            · rcases hka with hwide | ⟨c', hst⟩
              · have := Nat.blt_eq.mp hwide; simp only [Bool.false_eq_true, ite_false] at hlen'; omega
              · rw [hdropComm] at hst
                exact finish hst
            · rcases hka with hwide | ⟨c', hst⟩
              · have := Nat.blt_eq.mp hwide; simp only [Bool.false_eq_true, ite_false, ite_true] at hlen'; omega
              · exact finish hst
            · rcases hka with hwide | ⟨c', hst⟩
              · have := Nat.blt_eq.mp hwide; simp only [Bool.false_eq_true, ite_false, ite_true] at hlen'; omega
              · exact finish hst
            · rcases hka with hwide | ⟨c', hst⟩
              · have := Nat.blt_eq.mp hwide; simp only [ite_true] at hlen'; omega
              · exact finish hst
      · rw [hcg] at hchk; exact Bool.noConfusion hchk

theorem lowerDagV4 {mask goal ep fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {cursors : Nat → List (Nat × Nat)}
    (hgm : Masked mask goal) (hgnz : goal ≠ 0)
    (hcs : stock.all (fun w => Nat.beq (canon mask w) w) = true)
    (snd : stock.Nodup)
    (hep : ep = edgePack mask goal)
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hroots : dagCheckRootsV4 mask goal ep count bounds
      (dagTraceF mask stock fuel forest) (cursors 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeV4 mask goal ep bounds count
      (dagTraceF mask stock fuel forest) cursors i = true) :
    LowerBin mask stock goal (fuel + 1) := by
  subst hep
  have htr : dagTraceF mask stock fuel forest = dagTrace mask stock fuel forest := by
    funext i; exact dagTraceF_eq mask stock fuel forest i
  rw [htr] at hroots hnodes
  intro vs hbuild hhit
  by_contra! hlt
  have hcs' : ∀ w ∈ stock, canon mask w = w := fun w hw =>
    Nat.beq_eq.mp (List.all_eq_true.mp hcs w hw)
  obtain ⟨k, S, hk, hSsub, hlive⟩ := extractLiveBin hgnz hcs' hbuild hhit
  obtain ⟨tok, htok, hteq⟩ := exists_subsetToken stock S
  rw [Finset.inter_eq_left.mpr hSsub] at hteq
  unfold dagCheckRootsV4 at hroots
  have hpow : Nat.shiftLeft 1 (lenN stock) = 2 ^ stock.length := by
    rw [lenN_eq]; change 1 <<< stock.length = _; rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [hpow] at hroots
  obtain ⟨c, hsr⟩ := loopRootsV4_at (tok := tok) (Nat.zero_le tok) (by omega) hroots
  rw [subsetWordsF_eq] at hsr
  have hnd : (subsetWords stock tok).Nodup := subsetWords_nodup snd tok
  have hlive' : LiveBin mask goal k (subsetWords stock tok).toFinset := by rwa [hteq]
  have hcard : (subsetWords stock tok).length ≤ fuel + 1 := by
    have := liveBin_card_le hlive'
    rw [List.toFinset_card_of_nodup hnd] at this; omega
  have hnw : Nat.blt (Nat.add fuel 1) (lenN (subsetWords stock tok)) = false := by
    rw [lenN_eq]
    cases h : Nat.blt (Nat.add fuel 1) (subsetWords stock tok).length
    · rfl
    · have hlt' : fuel + 1 < (subsetWords stock tok).length := Nat.blt_eq.mp h
      omega
  have hfb := closeFallbackV4_open (st := (fuel, subsetWords stock tok, [])) hgm hknown hsub hgoals hnd (k := k) (by omega) hlive'
  unfold stepRootV4 at hsr
  rw [hnw] at hsr; dsimp only at hsr
  cases c with
  | nil => dsimp only at hsr; rw [hfb] at hsr; exact Bool.noConfusion hsr
  | cons hd tl =>
    obtain ⟨t, code⟩ := hd
    dsimp only at hsr
    cases ht : Nat.beq tok t
    · rw [ht] at hsr; dsimp only at hsr; rw [hfb] at hsr; exact Bool.noConfusion hsr
    · rw [ht] at hsr; dsimp only at hsr
      cases hev : Nat.beq (Nat.land code 1) 0
      · rw [hev] at hsr; dsimp only at hsr
        cases hb : nthBound bounds (Nat.shiftRight code 1) with
        | none => rw [hb] at hsr; exact Bool.noConfusion hsr
        | some b =>
          rw [hb] at hsr; dsimp only at hsr
          have hmem := nthBound_mem hb
          have hg := hgoals b hmem
          rw [boundClosesF_eq hg.1 hg.2] at hsr
          have h0 := boundCloses_sound (state := (fuel, subsetWords stock tok, [])) (hknown b hmem) (hsub b hmem) hnd (k := k) (by omega) hlive'
          rw [h0] at hsr; exact Bool.noConfusion hsr
      · rw [hev] at hsr; dsimp only at hsr
        cases hltc : Nat.blt (Nat.shiftRight code 1) count
        · rw [hltc] at hsr; exact Bool.noConfusion hsr
        · rw [hltc] at hsr; dsimp only at hsr
          cases htr2 : dagTrace mask stock fuel forest (Nat.shiftRight code 1) with
          | none => rw [htr2] at hsr; exact Bool.noConfusion hsr
          | some saved =>
            rw [htr2] at hsr; dsimp only at hsr
            cases hf : Nat.beq saved.1 fuel
            · rw [hf] at hsr; exact Bool.noConfusion hsr
            · rw [hf] at hsr; dsimp only at hsr
              rw [eqListN_eq, beq_iff_eq] at hsr
              exact dagAllNodesV4 hgm hknown hsub hgoals snd hnodes fuel (Nat.shiftRight code 1) saved
                (Nat.blt_eq.mp hltc) htr2 (Nat.beq_eq.mp hf) k (by omega) (hsr ▸ hlive')

def unpackF (data width idx : Nat) : Nat :=
  Nat.land (Nat.shiftRight data (Nat.mul idx width)) (Nat.sub (Nat.shiftLeft 1 width) 1)

def unpackForestF (data pBits tBits : Nat) : Nat → Nat × Nat := fun i =>
  let w := Nat.add pBits tBits
  let code := unpackF data w i
  (Nat.shiftRight code tBits, Nat.land code (Nat.sub (Nat.shiftLeft 1 tBits) 1))

def unpackListAux (data off w wMask tokBits tokMask : Nat) : Nat → List (Nat × Nat) → List (Nat × Nat)
  | 0, acc => acc
  | k + 1, acc =>
    let code := Nat.land (Nat.shiftRight data (Nat.mul (Nat.add off k) w)) wMask
    unpackListAux data off w wMask tokBits tokMask k ((Nat.land code tokMask, Nat.shiftRight code tokBits) :: acc)

def unpackCursorV4 (index data idxW idxMask sizeBits sizeMask tokBits tokMask w wMask : Nat) :
    Nat → List (Nat × Nat) :=
  fun parent =>
    let entry := Nat.land (Nat.shiftRight index (Nat.mul parent idxW)) idxMask
    let sz := Nat.land entry sizeMask
    let off := Nat.shiftRight entry sizeBits
    unpackListAux data off w wMask tokBits tokMask sz []

def m_0 : Nat := 0xa000a000a000a00
def s_0 : List Nat := [0x200020002000200, 0xa0000000a00, 0xa000a00]
def g_0 : Nat := 0x20002000a00
def ep_0 : Nat := 0x200080000000200000008000000000000000000000000000000000000000200020000000000000000000000
theorem epk_0 : ep_0 = edgePack m_0 g_0 := by decide +kernel
def bds_0 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_0 : KnownBin bds_0 := by intro b hb; simp [bds_0] at hb
theorem sub_0 : ∀ b ∈ bds_0, m_0 &&& b.1 = b.1 := by intro b hb; simp [bds_0] at hb
theorem gl_0 : ∀ b ∈ bds_0, canon b.1 g_0 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_0] at hb
def cur_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_0 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_0 : dagCheckRootsV4 m_0 g_0 ep_0 1 bds_0 (dagTraceF m_0 s_0 3 f_0) (cur_0 0) s_0 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_0 : treeBlockF 0 1 (dagCheckNodeV4 m_0 g_0 ep_0 bds_0 1 (dagTraceF m_0 s_0 3 f_0) cur_0) = true := by decide +kernel
theorem nc_0 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_0 g_0 ep_0 bds_0 1 (dagTraceF m_0 s_0 3 f_0) cur_0) i = true := fun _ h1 h2 => treeBlockF_at nb_0 h1 h2
theorem lb_0 : LowerBin m_0 s_0 g_0 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_0 kn_0 sub_0 gl_0 rc_0 nc_0

def m_1 : Nat := 0x2200220022002200
def s_1 : List Nat := [0x200020002000200, 0x220000002200, 0x22002200]
def g_1 : Nat := 0x20002002200
def ep_1 : Nat := 0x200200000000200000020000000000000000000000002000200000000000000000000000000000000000000
theorem epk_1 : ep_1 = edgePack m_1 g_1 := by decide +kernel
def bds_1 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_1 : KnownBin bds_1 := by intro b hb; simp [bds_1] at hb
theorem sub_1 : ∀ b ∈ bds_1, m_1 &&& b.1 = b.1 := by intro b hb; simp [bds_1] at hb
theorem gl_1 : ∀ b ∈ bds_1, canon b.1 g_1 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_1] at hb
def cur_1 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_1 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_1 : dagCheckRootsV4 m_1 g_1 ep_1 1 bds_1 (dagTraceF m_1 s_1 3 f_1) (cur_1 0) s_1 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_1 : treeBlockF 0 1 (dagCheckNodeV4 m_1 g_1 ep_1 bds_1 1 (dagTraceF m_1 s_1 3 f_1) cur_1) = true := by decide +kernel
theorem nc_1 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_1 g_1 ep_1 bds_1 1 (dagTraceF m_1 s_1 3 f_1) cur_1) i = true := fun _ h1 h2 => treeBlockF_at nb_1 h1 h2
theorem lb_1 : LowerBin m_1 s_1 g_1 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_1 kn_1 sub_1 gl_1 rc_1 nc_1

def m_2 : Nat := 0xcccc0000
def s_2 : List Nat := [0x44440000, 0xc0c0000, 0xcc0000]
def g_2 : Nat := 0x44c0000
def ep_2 : Nat := 0x480000000000000408000000000000000000000000000004400000
theorem epk_2 : ep_2 = edgePack m_2 g_2 := by decide +kernel
def bds_2 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_2 : KnownBin bds_2 := by intro b hb; simp [bds_2] at hb
theorem sub_2 : ∀ b ∈ bds_2, m_2 &&& b.1 = b.1 := by intro b hb; simp [bds_2] at hb
theorem gl_2 : ∀ b ∈ bds_2, canon b.1 g_2 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_2] at hb
def cur_2 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_2 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_2 : dagCheckRootsV4 m_2 g_2 ep_2 1 bds_2 (dagTraceF m_2 s_2 3 f_2) (cur_2 0) s_2 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_2 : treeBlockF 0 1 (dagCheckNodeV4 m_2 g_2 ep_2 bds_2 1 (dagTraceF m_2 s_2 3 f_2) cur_2) = true := by decide +kernel
theorem nc_2 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_2 g_2 ep_2 bds_2 1 (dagTraceF m_2 s_2 3 f_2) cur_2) i = true := fun _ h1 h2 => treeBlockF_at nb_2 h1 h2
theorem lb_2 : LowerBin m_2 s_2 g_2 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_2 kn_2 sub_2 gl_2 rc_2 nc_2

def m_3 : Nat := 0xf000f000000000
def s_3 : List Nat := [0x50005000000000, 0x30003000000000, 0xf000000000]
def g_3 : Nat := 0x10007000000000
def ep_3 : Nat := 0x60000000000000000000000000000000000000000000100020000000000010004000000000
theorem epk_3 : ep_3 = edgePack m_3 g_3 := by decide +kernel
def bds_3 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_3 : KnownBin bds_3 := by intro b hb; simp [bds_3] at hb
theorem sub_3 : ∀ b ∈ bds_3, m_3 &&& b.1 = b.1 := by intro b hb; simp [bds_3] at hb
theorem gl_3 : ∀ b ∈ bds_3, canon b.1 g_3 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_3] at hb
def cur_3 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_3 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_3 : dagCheckRootsV4 m_3 g_3 ep_3 1 bds_3 (dagTraceF m_3 s_3 3 f_3) (cur_3 0) s_3 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_3 : treeBlockF 0 1 (dagCheckNodeV4 m_3 g_3 ep_3 bds_3 1 (dagTraceF m_3 s_3 3 f_3) cur_3) = true := by decide +kernel
theorem nc_3 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_3 g_3 ep_3 bds_3 1 (dagTraceF m_3 s_3 3 f_3) cur_3) i = true := fun _ h1 h2 => treeBlockF_at nb_3 h1 h2
theorem lb_3 : LowerBin m_3 s_3 g_3 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_3 kn_3 sub_3 gl_3 rc_3 nc_3

def m_4 : Nat := 0x5500550000000000
def s_4 : List Nat := [0x1100110000000000, 0x500050000000000, 0x550000000000]
def g_4 : Nat := 0x100150000000000
def ep_4 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000000000000000000
theorem epk_4 : ep_4 = edgePack m_4 g_4 := by decide +kernel
def bds_4 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_4 : KnownBin bds_4 := by intro b hb; simp [bds_4] at hb
theorem sub_4 : ∀ b ∈ bds_4, m_4 &&& b.1 = b.1 := by intro b hb; simp [bds_4] at hb
theorem gl_4 : ∀ b ∈ bds_4, canon b.1 g_4 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_4] at hb
def cur_4 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_4 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_4 : dagCheckRootsV4 m_4 g_4 ep_4 1 bds_4 (dagTraceF m_4 s_4 3 f_4) (cur_4 0) s_4 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_4 : treeBlockF 0 1 (dagCheckNodeV4 m_4 g_4 ep_4 bds_4 1 (dagTraceF m_4 s_4 3 f_4) cur_4) = true := by decide +kernel
theorem nc_4 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_4 g_4 ep_4 bds_4 1 (dagTraceF m_4 s_4 3 f_4) cur_4) i = true := fun _ h1 h2 => treeBlockF_at nb_4 h1 h2
theorem lb_4 : LowerBin m_4 s_4 g_4 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_4 kn_4 sub_4 gl_4 rc_4 nc_4

def m_5 : Nat := 0xc000c000c000c0
def s_5 : List Nat := [0x40004000400040, 0xc0000000c0, 0xc000c0]
def g_5 : Nat := 0x40004000c0
def ep_5 : Nat := 0x40008000000040000000800000000000000000000000000000000000000000000000000000004000400000
theorem epk_5 : ep_5 = edgePack m_5 g_5 := by decide +kernel
def bds_5 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_5 : KnownBin bds_5 := by intro b hb; simp [bds_5] at hb
theorem sub_5 : ∀ b ∈ bds_5, m_5 &&& b.1 = b.1 := by intro b hb; simp [bds_5] at hb
theorem gl_5 : ∀ b ∈ bds_5, canon b.1 g_5 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_5] at hb
def cur_5 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_5 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_5 : dagCheckRootsV4 m_5 g_5 ep_5 1 bds_5 (dagTraceF m_5 s_5 3 f_5) (cur_5 0) s_5 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_5 : treeBlockF 0 1 (dagCheckNodeV4 m_5 g_5 ep_5 bds_5 1 (dagTraceF m_5 s_5 3 f_5) cur_5) = true := by decide +kernel
theorem nc_5 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_5 g_5 ep_5 bds_5 1 (dagTraceF m_5 s_5 3 f_5) cur_5) i = true := fun _ h1 h2 => treeBlockF_at nb_5 h1 h2
theorem lb_5 : LowerBin m_5 s_5 g_5 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_5 kn_5 sub_5 gl_5 rc_5 nc_5

def m_6 : Nat := 0x3300330000000000
def s_6 : List Nat := [0x1100110000000000, 0x300030000000000, 0x330000000000]
def g_6 : Nat := 0x100130000000000
def ep_6 : Nat := 0x1200000000000000000000000000010002000000000000000000000000000100100000000000
theorem epk_6 : ep_6 = edgePack m_6 g_6 := by decide +kernel
def bds_6 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_6 : KnownBin bds_6 := by intro b hb; simp [bds_6] at hb
theorem sub_6 : ∀ b ∈ bds_6, m_6 &&& b.1 = b.1 := by intro b hb; simp [bds_6] at hb
theorem gl_6 : ∀ b ∈ bds_6, canon b.1 g_6 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_6] at hb
def cur_6 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_6 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_6 : dagCheckRootsV4 m_6 g_6 ep_6 1 bds_6 (dagTraceF m_6 s_6 3 f_6) (cur_6 0) s_6 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_6 : treeBlockF 0 1 (dagCheckNodeV4 m_6 g_6 ep_6 bds_6 1 (dagTraceF m_6 s_6 3 f_6) cur_6) = true := by decide +kernel
theorem nc_6 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_6 g_6 ep_6 bds_6 1 (dagTraceF m_6 s_6 3 f_6) cur_6) i = true := fun _ h1 h2 => treeBlockF_at nb_6 h1 h2
theorem lb_6 : LowerBin m_6 s_6 g_6 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_6 kn_6 sub_6 gl_6 rc_6 nc_6

def m_7 : Nat := 0xf0f000000000000
def s_7 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_7 : Nat := 0x107000000000000
def ep_7 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
theorem epk_7 : ep_7 = edgePack m_7 g_7 := by decide +kernel
def bds_7 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_7 : KnownBin bds_7 := by intro b hb; simp [bds_7] at hb
theorem sub_7 : ∀ b ∈ bds_7, m_7 &&& b.1 = b.1 := by intro b hb; simp [bds_7] at hb
theorem gl_7 : ∀ b ∈ bds_7, canon b.1 g_7 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_7] at hb
def cur_7 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_7 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_7 : dagCheckRootsV4 m_7 g_7 ep_7 1 bds_7 (dagTraceF m_7 s_7 3 f_7) (cur_7 0) s_7 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_7 : treeBlockF 0 1 (dagCheckNodeV4 m_7 g_7 ep_7 bds_7 1 (dagTraceF m_7 s_7 3 f_7) cur_7) = true := by decide +kernel
theorem nc_7 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_7 g_7 ep_7 bds_7 1 (dagTraceF m_7 s_7 3 f_7) cur_7) i = true := fun _ h1 h2 => treeBlockF_at nb_7 h1 h2
theorem lb_7 : LowerBin m_7 s_7 g_7 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_7 kn_7 sub_7 gl_7 rc_7 nc_7

def m_8 : Nat := 0xf000f0000000000
def s_8 : List Nat := [0x500050000000000, 0x300030000000000, 0xf0000000000]
def g_8 : Nat := 0x100070000000000
def ep_8 : Nat := 0x600000000000000000000000000000000000000000001000200000000000100040000000000
theorem epk_8 : ep_8 = edgePack m_8 g_8 := by decide +kernel
def bds_8 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_8 : KnownBin bds_8 := by intro b hb; simp [bds_8] at hb
theorem sub_8 : ∀ b ∈ bds_8, m_8 &&& b.1 = b.1 := by intro b hb; simp [bds_8] at hb
theorem gl_8 : ∀ b ∈ bds_8, canon b.1 g_8 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_8] at hb
def cur_8 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_8 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_8 : dagCheckRootsV4 m_8 g_8 ep_8 1 bds_8 (dagTraceF m_8 s_8 3 f_8) (cur_8 0) s_8 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_8 : treeBlockF 0 1 (dagCheckNodeV4 m_8 g_8 ep_8 bds_8 1 (dagTraceF m_8 s_8 3 f_8) cur_8) = true := by decide +kernel
theorem nc_8 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_8 g_8 ep_8 bds_8 1 (dagTraceF m_8 s_8 3 f_8) cur_8) i = true := fun _ h1 h2 => treeBlockF_at nb_8 h1 h2
theorem lb_8 : LowerBin m_8 s_8 g_8 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_8 kn_8 sub_8 gl_8 rc_8 nc_8

def m_9 : Nat := 0x2222222200000000
def s_9 : List Nat := [0x202020200000000, 0x22002200000000, 0x222200000000]
def g_9 : Nat := 0x2022200000000
def ep_9 : Nat := 0x220000000000002002000000000000202000000000000000000000000000000000000000000
theorem epk_9 : ep_9 = edgePack m_9 g_9 := by decide +kernel
def bds_9 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_9 : KnownBin bds_9 := by intro b hb; simp [bds_9] at hb
theorem sub_9 : ∀ b ∈ bds_9, m_9 &&& b.1 = b.1 := by intro b hb; simp [bds_9] at hb
theorem gl_9 : ∀ b ∈ bds_9, canon b.1 g_9 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_9] at hb
def cur_9 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_9 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_9 : dagCheckRootsV4 m_9 g_9 ep_9 1 bds_9 (dagTraceF m_9 s_9 3 f_9) (cur_9 0) s_9 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_9 : treeBlockF 0 1 (dagCheckNodeV4 m_9 g_9 ep_9 bds_9 1 (dagTraceF m_9 s_9 3 f_9) cur_9) = true := by decide +kernel
theorem nc_9 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_9 g_9 ep_9 bds_9 1 (dagTraceF m_9 s_9 3 f_9) cur_9) i = true := fun _ h1 h2 => treeBlockF_at nb_9 h1 h2
theorem lb_9 : LowerBin m_9 s_9 g_9 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_9 kn_9 sub_9 gl_9 rc_9 nc_9

def m_10 : Nat := 0x4444444400000000
def s_10 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_10 : Nat := 0x4044400000000
def ep_10 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
theorem epk_10 : ep_10 = edgePack m_10 g_10 := by decide +kernel
def bds_10 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_10 : KnownBin bds_10 := by intro b hb; simp [bds_10] at hb
theorem sub_10 : ∀ b ∈ bds_10, m_10 &&& b.1 = b.1 := by intro b hb; simp [bds_10] at hb
theorem gl_10 : ∀ b ∈ bds_10, canon b.1 g_10 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_10] at hb
def cur_10 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_10 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_10 : dagCheckRootsV4 m_10 g_10 ep_10 1 bds_10 (dagTraceF m_10 s_10 3 f_10) (cur_10 0) s_10 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_10 : treeBlockF 0 1 (dagCheckNodeV4 m_10 g_10 ep_10 bds_10 1 (dagTraceF m_10 s_10 3 f_10) cur_10) = true := by decide +kernel
theorem nc_10 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_10 g_10 ep_10 bds_10 1 (dagTraceF m_10 s_10 3 f_10) cur_10) i = true := fun _ h1 h2 => treeBlockF_at nb_10 h1 h2
theorem lb_10 : LowerBin m_10 s_10 g_10 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_10 kn_10 sub_10 gl_10 rc_10 nc_10

def m_11 : Nat := 0x3030303000000000
def s_11 : List Nat := [0x1010101000000000, 0x30003000000000, 0x303000000000]
def g_11 : Nat := 0x10103000000000
def ep_11 : Nat := 0x1020000000000010002000000000000000000000000000000000000000000010100000000000
theorem epk_11 : ep_11 = edgePack m_11 g_11 := by decide +kernel
def bds_11 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_11 : KnownBin bds_11 := by intro b hb; simp [bds_11] at hb
theorem sub_11 : ∀ b ∈ bds_11, m_11 &&& b.1 = b.1 := by intro b hb; simp [bds_11] at hb
theorem gl_11 : ∀ b ∈ bds_11, canon b.1 g_11 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_11] at hb
def cur_11 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_11 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_11 : dagCheckRootsV4 m_11 g_11 ep_11 1 bds_11 (dagTraceF m_11 s_11 3 f_11) (cur_11 0) s_11 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_11 : treeBlockF 0 1 (dagCheckNodeV4 m_11 g_11 ep_11 bds_11 1 (dagTraceF m_11 s_11 3 f_11) cur_11) = true := by decide +kernel
theorem nc_11 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_11 g_11 ep_11 bds_11 1 (dagTraceF m_11 s_11 3 f_11) cur_11) i = true := fun _ h1 h2 => treeBlockF_at nb_11 h1 h2
theorem lb_11 : LowerBin m_11 s_11 g_11 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_11 kn_11 sub_11 gl_11 rc_11 nc_11

def m_12 : Nat := 0x5050505000000000
def s_12 : List Nat := [0x1010101000000000, 0x50005000000000, 0x505000000000]
def g_12 : Nat := 0x10105000000000
def ep_12 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000000000000000000
theorem epk_12 : ep_12 = edgePack m_12 g_12 := by decide +kernel
def bds_12 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_12 : KnownBin bds_12 := by intro b hb; simp [bds_12] at hb
theorem sub_12 : ∀ b ∈ bds_12, m_12 &&& b.1 = b.1 := by intro b hb; simp [bds_12] at hb
theorem gl_12 : ∀ b ∈ bds_12, canon b.1 g_12 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_12] at hb
def cur_12 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_12 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_12 : dagCheckRootsV4 m_12 g_12 ep_12 1 bds_12 (dagTraceF m_12 s_12 3 f_12) (cur_12 0) s_12 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_12 : treeBlockF 0 1 (dagCheckNodeV4 m_12 g_12 ep_12 bds_12 1 (dagTraceF m_12 s_12 3 f_12) cur_12) = true := by decide +kernel
theorem nc_12 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_12 g_12 ep_12 bds_12 1 (dagTraceF m_12 s_12 3 f_12) cur_12) i = true := fun _ h1 h2 => treeBlockF_at nb_12 h1 h2
theorem lb_12 : LowerBin m_12 s_12 g_12 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_12 kn_12 sub_12 gl_12 rc_12 nc_12

def m_13 : Nat := 0xff000000
def s_13 : List Nat := [0x55000000, 0x33000000, 0xf000000]
def g_13 : Nat := 0x17000000
def ep_13 : Nat := 0x600000000000000120000000000000014000000
theorem epk_13 : ep_13 = edgePack m_13 g_13 := by decide +kernel
def bds_13 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_13 : KnownBin bds_13 := by intro b hb; simp [bds_13] at hb
theorem sub_13 : ∀ b ∈ bds_13, m_13 &&& b.1 = b.1 := by intro b hb; simp [bds_13] at hb
theorem gl_13 : ∀ b ∈ bds_13, canon b.1 g_13 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_13] at hb
def cur_13 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_13 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_13 : dagCheckRootsV4 m_13 g_13 ep_13 1 bds_13 (dagTraceF m_13 s_13 3 f_13) (cur_13 0) s_13 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_13 : treeBlockF 0 1 (dagCheckNodeV4 m_13 g_13 ep_13 bds_13 1 (dagTraceF m_13 s_13 3 f_13) cur_13) = true := by decide +kernel
theorem nc_13 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_13 g_13 ep_13 bds_13 1 (dagTraceF m_13 s_13 3 f_13) cur_13) i = true := fun _ h1 h2 => treeBlockF_at nb_13 h1 h2
theorem lb_13 : LowerBin m_13 s_13 g_13 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_13 kn_13 sub_13 gl_13 rc_13 nc_13

def m_14 : Nat := 0xff000000000000
def s_14 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_14 : Nat := 0x17000000000000
def ep_14 : Nat := 0x600000000000000120000000000000014000000000000
theorem epk_14 : ep_14 = edgePack m_14 g_14 := by decide +kernel
def bds_14 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_14 : KnownBin bds_14 := by intro b hb; simp [bds_14] at hb
theorem sub_14 : ∀ b ∈ bds_14, m_14 &&& b.1 = b.1 := by intro b hb; simp [bds_14] at hb
theorem gl_14 : ∀ b ∈ bds_14, canon b.1 g_14 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_14] at hb
def cur_14 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_14 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_14 : dagCheckRootsV4 m_14 g_14 ep_14 1 bds_14 (dagTraceF m_14 s_14 3 f_14) (cur_14 0) s_14 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_14 : treeBlockF 0 1 (dagCheckNodeV4 m_14 g_14 ep_14 bds_14 1 (dagTraceF m_14 s_14 3 f_14) cur_14) = true := by decide +kernel
theorem nc_14 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_14 g_14 ep_14 bds_14 1 (dagTraceF m_14 s_14 3 f_14) cur_14) i = true := fun _ h1 h2 => treeBlockF_at nb_14 h1 h2
theorem lb_14 : LowerBin m_14 s_14 g_14 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_14 kn_14 sub_14 gl_14 rc_14 nc_14

def m_15 : Nat := 0xcc000000cc0000
def s_15 : List Nat := [0x44000000440000, 0xc0000000c0000, 0xcc0000]
def g_15 : Nat := 0x40000004c0000
def ep_15 : Nat := 0x48000000000000000000000000000000000000000400000008000000000000000000000004000000400000
theorem epk_15 : ep_15 = edgePack m_15 g_15 := by decide +kernel
def bds_15 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_15 : KnownBin bds_15 := by intro b hb; simp [bds_15] at hb
theorem sub_15 : ∀ b ∈ bds_15, m_15 &&& b.1 = b.1 := by intro b hb; simp [bds_15] at hb
theorem gl_15 : ∀ b ∈ bds_15, canon b.1 g_15 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_15] at hb
def cur_15 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_15 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_15 : dagCheckRootsV4 m_15 g_15 ep_15 1 bds_15 (dagTraceF m_15 s_15 3 f_15) (cur_15 0) s_15 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_15 : treeBlockF 0 1 (dagCheckNodeV4 m_15 g_15 ep_15 bds_15 1 (dagTraceF m_15 s_15 3 f_15) cur_15) = true := by decide +kernel
theorem nc_15 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_15 g_15 ep_15 bds_15 1 (dagTraceF m_15 s_15 3 f_15) cur_15) i = true := fun _ h1 h2 => treeBlockF_at nb_15 h1 h2
theorem lb_15 : LowerBin m_15 s_15 g_15 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_15 kn_15 sub_15 gl_15 rc_15 nc_15

def m_16 : Nat := 0x5500000055000000
def s_16 : List Nat := [0x1100000011000000, 0x500000005000000, 0x55000000]
def g_16 : Nat := 0x100000015000000
def ep_16 : Nat := 0x1400000000000000000000000000000000000000010000000400000001000000100000000000000000000000
theorem epk_16 : ep_16 = edgePack m_16 g_16 := by decide +kernel
def bds_16 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_16 : KnownBin bds_16 := by intro b hb; simp [bds_16] at hb
theorem sub_16 : ∀ b ∈ bds_16, m_16 &&& b.1 = b.1 := by intro b hb; simp [bds_16] at hb
theorem gl_16 : ∀ b ∈ bds_16, canon b.1 g_16 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_16] at hb
def cur_16 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_16 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsV4 m_16 g_16 ep_16 1 bds_16 (dagTraceF m_16 s_16 3 f_16) (cur_16 0) s_16 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16 : treeBlockF 0 1 (dagCheckNodeV4 m_16 g_16 ep_16 bds_16 1 (dagTraceF m_16 s_16 3 f_16) cur_16) = true := by decide +kernel
theorem nc_16 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_16 g_16 ep_16 bds_16 1 (dagTraceF m_16 s_16 3 f_16) cur_16) i = true := fun _ h1 h2 => treeBlockF_at nb_16 h1 h2
theorem lb_16 : LowerBin m_16 s_16 g_16 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_16 kn_16 sub_16 gl_16 rc_16 nc_16

def m_17 : Nat := 0x3300000033000000
def s_17 : List Nat := [0x1100000011000000, 0x300000003000000, 0x33000000]
def g_17 : Nat := 0x100000013000000
def ep_17 : Nat := 0x1200000000000000000000000000000000000000010000000200000000000000000000000100000010000000
theorem epk_17 : ep_17 = edgePack m_17 g_17 := by decide +kernel
def bds_17 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_17 : KnownBin bds_17 := by intro b hb; simp [bds_17] at hb
theorem sub_17 : ∀ b ∈ bds_17, m_17 &&& b.1 = b.1 := by intro b hb; simp [bds_17] at hb
theorem gl_17 : ∀ b ∈ bds_17, canon b.1 g_17 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_17] at hb
def cur_17 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_17 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsV4 m_17 g_17 ep_17 1 bds_17 (dagTraceF m_17 s_17 3 f_17) (cur_17 0) s_17 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17 : treeBlockF 0 1 (dagCheckNodeV4 m_17 g_17 ep_17 bds_17 1 (dagTraceF m_17 s_17 3 f_17) cur_17) = true := by decide +kernel
theorem nc_17 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_17 g_17 ep_17 bds_17 1 (dagTraceF m_17 s_17 3 f_17) cur_17) i = true := fun _ h1 h2 => treeBlockF_at nb_17 h1 h2
theorem lb_17 : LowerBin m_17 s_17 g_17 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_17 kn_17 sub_17 gl_17 rc_17 nc_17

def m_18 : Nat := 0xa0a00000a0a0
def s_18 : List Nat := [0x202000002020, 0xa0000000a0, 0xa0a0]
def g_18 : Nat := 0x20000020a0
def ep_18 : Nat := 0x208000000000000000000000002000000080000000000000000000000020000020000000000000000000
theorem epk_18 : ep_18 = edgePack m_18 g_18 := by decide +kernel
def bds_18 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_18 : KnownBin bds_18 := by intro b hb; simp [bds_18] at hb
theorem sub_18 : ∀ b ∈ bds_18, m_18 &&& b.1 = b.1 := by intro b hb; simp [bds_18] at hb
theorem gl_18 : ∀ b ∈ bds_18, canon b.1 g_18 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_18] at hb
def cur_18 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_18 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsV4 m_18 g_18 ep_18 1 bds_18 (dagTraceF m_18 s_18 3 f_18) (cur_18 0) s_18 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_18 : treeBlockF 0 1 (dagCheckNodeV4 m_18 g_18 ep_18 bds_18 1 (dagTraceF m_18 s_18 3 f_18) cur_18) = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_18 g_18 ep_18 bds_18 1 (dagTraceF m_18 s_18 3 f_18) cur_18) i = true := fun _ h1 h2 => treeBlockF_at nb_18 h1 h2
theorem lb_18 : LowerBin m_18 s_18 g_18 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_18 kn_18 sub_18 gl_18 rc_18 nc_18

def m_19 : Nat := 0xf0000000f000000
def s_19 : List Nat := [0x500000005000000, 0x300000003000000, 0xf000000]
def g_19 : Nat := 0x100000007000000
def ep_19 : Nat := 0x600000000000000000000000000000000000000000000000000000001000000020000000100000004000000
theorem epk_19 : ep_19 = edgePack m_19 g_19 := by decide +kernel
def bds_19 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_19 : KnownBin bds_19 := by intro b hb; simp [bds_19] at hb
theorem sub_19 : ∀ b ∈ bds_19, m_19 &&& b.1 = b.1 := by intro b hb; simp [bds_19] at hb
theorem gl_19 : ∀ b ∈ bds_19, canon b.1 g_19 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_19] at hb
def cur_19 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_19 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsV4 m_19 g_19 ep_19 1 bds_19 (dagTraceF m_19 s_19 3 f_19) (cur_19 0) s_19 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19 : treeBlockF 0 1 (dagCheckNodeV4 m_19 g_19 ep_19 bds_19 1 (dagTraceF m_19 s_19 3 f_19) cur_19) = true := by decide +kernel
theorem nc_19 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_19 g_19 ep_19 bds_19 1 (dagTraceF m_19 s_19 3 f_19) cur_19) i = true := fun _ h1 h2 => treeBlockF_at nb_19 h1 h2
theorem lb_19 : LowerBin m_19 s_19 g_19 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_19 kn_19 sub_19 gl_19 rc_19 nc_19

def m_20 : Nat := 0xaa000000aa00
def s_20 : List Nat := [0x220000002200, 0xa0000000a00, 0xaa00]
def g_20 : Nat := 0x20000002a00
def ep_20 : Nat := 0x280000000000000000000000000000000000000002000000080000000200000020000000000000000000
theorem epk_20 : ep_20 = edgePack m_20 g_20 := by decide +kernel
def bds_20 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_20 : KnownBin bds_20 := by intro b hb; simp [bds_20] at hb
theorem sub_20 : ∀ b ∈ bds_20, m_20 &&& b.1 = b.1 := by intro b hb; simp [bds_20] at hb
theorem gl_20 : ∀ b ∈ bds_20, canon b.1 g_20 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_20] at hb
def cur_20 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_20 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV4 m_20 g_20 ep_20 1 bds_20 (dagTraceF m_20 s_20 3 f_20) (cur_20 0) s_20 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_20 : treeBlockF 0 1 (dagCheckNodeV4 m_20 g_20 ep_20 bds_20 1 (dagTraceF m_20 s_20 3 f_20) cur_20) = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_20 g_20 ep_20 bds_20 1 (dagTraceF m_20 s_20 3 f_20) cur_20) i = true := fun _ h1 h2 => treeBlockF_at nb_20 h1 h2
theorem lb_20 : LowerBin m_20 s_20 g_20 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_20 kn_20 sub_20 gl_20 rc_20 nc_20

def m_21 : Nat := 0xff0000000000
def s_21 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_21 : Nat := 0x170000000000
def ep_21 : Nat := 0x6000000000000001200000000000000140000000000
theorem epk_21 : ep_21 = edgePack m_21 g_21 := by decide +kernel
def bds_21 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_21 : KnownBin bds_21 := by intro b hb; simp [bds_21] at hb
theorem sub_21 : ∀ b ∈ bds_21, m_21 &&& b.1 = b.1 := by intro b hb; simp [bds_21] at hb
theorem gl_21 : ∀ b ∈ bds_21, canon b.1 g_21 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_21] at hb
def cur_21 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_21 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV4 m_21 g_21 ep_21 1 bds_21 (dagTraceF m_21 s_21 3 f_21) (cur_21 0) s_21 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21 : treeBlockF 0 1 (dagCheckNodeV4 m_21 g_21 ep_21 bds_21 1 (dagTraceF m_21 s_21 3 f_21) cur_21) = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_21 g_21 ep_21 bds_21 1 (dagTraceF m_21 s_21 3 f_21) cur_21) i = true := fun _ h1 h2 => treeBlockF_at nb_21 h1 h2
theorem lb_21 : LowerBin m_21 s_21 g_21 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_21 kn_21 sub_21 gl_21 rc_21 nc_21

def m_22 : Nat := 0x4444000044440000
def s_22 : List Nat := [0x404000004040000, 0x44000000440000, 0x44440000]
def g_22 : Nat := 0x4000004440000
def ep_22 : Nat := 0x440000000000000000000000004000000400000000400000400000000000000000000000000000000000000
theorem epk_22 : ep_22 = edgePack m_22 g_22 := by decide +kernel
def bds_22 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_22 : KnownBin bds_22 := by intro b hb; simp [bds_22] at hb
theorem sub_22 : ∀ b ∈ bds_22, m_22 &&& b.1 = b.1 := by intro b hb; simp [bds_22] at hb
theorem gl_22 : ∀ b ∈ bds_22, canon b.1 g_22 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_22] at hb
def cur_22 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_22 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV4 m_22 g_22 ep_22 1 bds_22 (dagTraceF m_22 s_22 3 f_22) (cur_22 0) s_22 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_22 : treeBlockF 0 1 (dagCheckNodeV4 m_22 g_22 ep_22 bds_22 1 (dagTraceF m_22 s_22 3 f_22) cur_22) = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_22 g_22 ep_22 bds_22 1 (dagTraceF m_22 s_22 3 f_22) cur_22) i = true := fun _ h1 h2 => treeBlockF_at nb_22 h1 h2
theorem lb_22 : LowerBin m_22 s_22 g_22 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_22 kn_22 sub_22 gl_22 rc_22 nc_22

def m_23 : Nat := 0xa0a00000a0a0000
def s_23 : List Nat := [0x202000002020000, 0xa0000000a0000, 0xa0a0000]
def g_23 : Nat := 0x20000020a0000
def ep_23 : Nat := 0x208000000000000000000000002000000080000000000000000000000020000020000000000000000000000
theorem epk_23 : ep_23 = edgePack m_23 g_23 := by decide +kernel
def bds_23 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_23 : KnownBin bds_23 := by intro b hb; simp [bds_23] at hb
theorem sub_23 : ∀ b ∈ bds_23, m_23 &&& b.1 = b.1 := by intro b hb; simp [bds_23] at hb
theorem gl_23 : ∀ b ∈ bds_23, canon b.1 g_23 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_23] at hb
def cur_23 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_23 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV4 m_23 g_23 ep_23 1 bds_23 (dagTraceF m_23 s_23 3 f_23) (cur_23 0) s_23 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_23 : treeBlockF 0 1 (dagCheckNodeV4 m_23 g_23 ep_23 bds_23 1 (dagTraceF m_23 s_23 3 f_23) cur_23) = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_23 g_23 ep_23 bds_23 1 (dagTraceF m_23 s_23 3 f_23) cur_23) i = true := fun _ h1 h2 => treeBlockF_at nb_23 h1 h2
theorem lb_23 : LowerBin m_23 s_23 g_23 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_23 kn_23 sub_23 gl_23 rc_23 nc_23

def m_24 : Nat := 0xc0c00000c0c0000
def s_24 : List Nat := [0x404000004040000, 0xc0000000c0000, 0xc0c0000]
def g_24 : Nat := 0x40000040c0000
def ep_24 : Nat := 0x408000000000000000000000004000000080000000000000000000000000000000000000004000004000000
theorem epk_24 : ep_24 = edgePack m_24 g_24 := by decide +kernel
def bds_24 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_24 : KnownBin bds_24 := by intro b hb; simp [bds_24] at hb
theorem sub_24 : ∀ b ∈ bds_24, m_24 &&& b.1 = b.1 := by intro b hb; simp [bds_24] at hb
theorem gl_24 : ∀ b ∈ bds_24, canon b.1 g_24 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_24] at hb
def cur_24 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_24 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV4 m_24 g_24 ep_24 1 bds_24 (dagTraceF m_24 s_24 3 f_24) (cur_24 0) s_24 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_24 : treeBlockF 0 1 (dagCheckNodeV4 m_24 g_24 ep_24 bds_24 1 (dagTraceF m_24 s_24 3 f_24) cur_24) = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_24 g_24 ep_24 bds_24 1 (dagTraceF m_24 s_24 3 f_24) cur_24) i = true := fun _ h1 h2 => treeBlockF_at nb_24 h1 h2
theorem lb_24 : LowerBin m_24 s_24 g_24 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_24 kn_24 sub_24 gl_24 rc_24 nc_24

def m_25 : Nat := 0x5050000050500000
def s_25 : List Nat := [0x1010000010100000, 0x50000000500000, 0x50500000]
def g_25 : Nat := 0x10000010500000
def ep_25 : Nat := 0x1040000000000000000000000010000000400000000000000000000000100000100000000000000000000000
theorem epk_25 : ep_25 = edgePack m_25 g_25 := by decide +kernel
def bds_25 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_25 : KnownBin bds_25 := by intro b hb; simp [bds_25] at hb
theorem sub_25 : ∀ b ∈ bds_25, m_25 &&& b.1 = b.1 := by intro b hb; simp [bds_25] at hb
theorem gl_25 : ∀ b ∈ bds_25, canon b.1 g_25 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_25] at hb
def cur_25 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_25 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV4 m_25 g_25 ep_25 1 bds_25 (dagTraceF m_25 s_25 3 f_25) (cur_25 0) s_25 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25 : treeBlockF 0 1 (dagCheckNodeV4 m_25 g_25 ep_25 bds_25 1 (dagTraceF m_25 s_25 3 f_25) cur_25) = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_25 g_25 ep_25 bds_25 1 (dagTraceF m_25 s_25 3 f_25) cur_25) i = true := fun _ h1 h2 => treeBlockF_at nb_25 h1 h2
theorem lb_25 : LowerBin m_25 s_25 g_25 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_25 kn_25 sub_25 gl_25 rc_25 nc_25

def m_26 : Nat := 0xaa00aa00
def s_26 : List Nat := [0x22002200, 0xa000a00, 0xaa00]
def g_26 : Nat := 0x2002a00
def ep_26 : Nat := 0x28000000000000000000000000000200080000000000020020000000000000000000
theorem epk_26 : ep_26 = edgePack m_26 g_26 := by decide +kernel
def bds_26 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_26 : KnownBin bds_26 := by intro b hb; simp [bds_26] at hb
theorem sub_26 : ∀ b ∈ bds_26, m_26 &&& b.1 = b.1 := by intro b hb; simp [bds_26] at hb
theorem gl_26 : ∀ b ∈ bds_26, canon b.1 g_26 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_26] at hb
def cur_26 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_26 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV4 m_26 g_26 ep_26 1 bds_26 (dagTraceF m_26 s_26 3 f_26) (cur_26 0) s_26 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_26 : treeBlockF 0 1 (dagCheckNodeV4 m_26 g_26 ep_26 bds_26 1 (dagTraceF m_26 s_26 3 f_26) cur_26) = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_26 g_26 ep_26 bds_26 1 (dagTraceF m_26 s_26 3 f_26) cur_26) i = true := fun _ h1 h2 => treeBlockF_at nb_26 h1 h2
theorem lb_26 : LowerBin m_26 s_26 g_26 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_26 kn_26 sub_26 gl_26 rc_26 nc_26

def m_27 : Nat := 0x3000300030003000
def s_27 : List Nat := [0x1000100010001000, 0x300000003000, 0x30003000]
def g_27 : Nat := 0x100010003000
def ep_27 : Nat := 0x1000200000001000000020000000000000000000000000000000000000000000000000000000100010000000
theorem epk_27 : ep_27 = edgePack m_27 g_27 := by decide +kernel
def bds_27 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_27 : KnownBin bds_27 := by intro b hb; simp [bds_27] at hb
theorem sub_27 : ∀ b ∈ bds_27, m_27 &&& b.1 = b.1 := by intro b hb; simp [bds_27] at hb
theorem gl_27 : ∀ b ∈ bds_27, canon b.1 g_27 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_27] at hb
def cur_27 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_27 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV4 m_27 g_27 ep_27 1 bds_27 (dagTraceF m_27 s_27 3 f_27) (cur_27 0) s_27 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27 : treeBlockF 0 1 (dagCheckNodeV4 m_27 g_27 ep_27 bds_27 1 (dagTraceF m_27 s_27 3 f_27) cur_27) = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_27 g_27 ep_27 bds_27 1 (dagTraceF m_27 s_27 3 f_27) cur_27) i = true := fun _ h1 h2 => treeBlockF_at nb_27 h1 h2
theorem lb_27 : LowerBin m_27 s_27 g_27 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_27 kn_27 sub_27 gl_27 rc_27 nc_27

def m_28 : Nat := 0xc000c000c000c00
def s_28 : List Nat := [0x400040004000400, 0xc0000000c00, 0xc000c00]
def g_28 : Nat := 0x40004000c00
def ep_28 : Nat := 0x400080000000400000008000000000000000000000000000000000000000000000000000000040004000000
theorem epk_28 : ep_28 = edgePack m_28 g_28 := by decide +kernel
def bds_28 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_28 : KnownBin bds_28 := by intro b hb; simp [bds_28] at hb
theorem sub_28 : ∀ b ∈ bds_28, m_28 &&& b.1 = b.1 := by intro b hb; simp [bds_28] at hb
theorem gl_28 : ∀ b ∈ bds_28, canon b.1 g_28 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_28] at hb
def cur_28 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_28 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV4 m_28 g_28 ep_28 1 bds_28 (dagTraceF m_28 s_28 3 f_28) (cur_28 0) s_28 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28 : treeBlockF 0 1 (dagCheckNodeV4 m_28 g_28 ep_28 bds_28 1 (dagTraceF m_28 s_28 3 f_28) cur_28) = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_28 g_28 ep_28 bds_28 1 (dagTraceF m_28 s_28 3 f_28) cur_28) i = true := fun _ h1 h2 => treeBlockF_at nb_28 h1 h2
theorem lb_28 : LowerBin m_28 s_28 g_28 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_28 kn_28 sub_28 gl_28 rc_28 nc_28

def m_29 : Nat := 0x5555000000000000
def s_29 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_29 : Nat := 0x115000000000000
def ep_29 : Nat := 0x14000000000000010400000000000001100000000000000000000000000000
theorem epk_29 : ep_29 = edgePack m_29 g_29 := by decide +kernel
def bds_29 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_29 : KnownBin bds_29 := by intro b hb; simp [bds_29] at hb
theorem sub_29 : ∀ b ∈ bds_29, m_29 &&& b.1 = b.1 := by intro b hb; simp [bds_29] at hb
theorem gl_29 : ∀ b ∈ bds_29, canon b.1 g_29 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_29] at hb
def cur_29 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_29 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV4 m_29 g_29 ep_29 1 bds_29 (dagTraceF m_29 s_29 3 f_29) (cur_29 0) s_29 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29 : treeBlockF 0 1 (dagCheckNodeV4 m_29 g_29 ep_29 bds_29 1 (dagTraceF m_29 s_29 3 f_29) cur_29) = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_29 g_29 ep_29 bds_29 1 (dagTraceF m_29 s_29 3 f_29) cur_29) i = true := fun _ h1 h2 => treeBlockF_at nb_29 h1 h2
theorem lb_29 : LowerBin m_29 s_29 g_29 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_29 kn_29 sub_29 gl_29 rc_29 nc_29

def m_30 : Nat := 0xf0f000000000
def s_30 : List Nat := [0x505000000000, 0x303000000000, 0xf000000000]
def g_30 : Nat := 0x107000000000
def ep_30 : Nat := 0x6000000000000000000000000000001020000000000000104000000000
theorem epk_30 : ep_30 = edgePack m_30 g_30 := by decide +kernel
def bds_30 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_30 : KnownBin bds_30 := by intro b hb; simp [bds_30] at hb
theorem sub_30 : ∀ b ∈ bds_30, m_30 &&& b.1 = b.1 := by intro b hb; simp [bds_30] at hb
theorem gl_30 : ∀ b ∈ bds_30, canon b.1 g_30 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_30] at hb
def cur_30 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_30 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV4 m_30 g_30 ep_30 1 bds_30 (dagTraceF m_30 s_30 3 f_30) (cur_30 0) s_30 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30 : treeBlockF 0 1 (dagCheckNodeV4 m_30 g_30 ep_30 bds_30 1 (dagTraceF m_30 s_30 3 f_30) cur_30) = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_30 g_30 ep_30 bds_30 1 (dagTraceF m_30 s_30 3 f_30) cur_30) i = true := fun _ h1 h2 => treeBlockF_at nb_30 h1 h2
theorem lb_30 : LowerBin m_30 s_30 g_30 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_30 kn_30 sub_30 gl_30 rc_30 nc_30

def m_31 : Nat := 0x3333000000000000
def s_31 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_31 : Nat := 0x113000000000000
def ep_31 : Nat := 0x12000000000000010200000000000000000000000000000110000000000000
theorem epk_31 : ep_31 = edgePack m_31 g_31 := by decide +kernel
def bds_31 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_31 : KnownBin bds_31 := by intro b hb; simp [bds_31] at hb
theorem sub_31 : ∀ b ∈ bds_31, m_31 &&& b.1 = b.1 := by intro b hb; simp [bds_31] at hb
theorem gl_31 : ∀ b ∈ bds_31, canon b.1 g_31 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_31] at hb
def cur_31 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0x7 2 3 1 1 3 7 4 15
def f_31 : Nat → Nat × Nat := unpackForestF 0x7 1 3
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV4 m_31 g_31 ep_31 1 bds_31 (dagTraceF m_31 s_31 3 f_31) (cur_31 0) s_31 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31 : treeBlockF 0 1 (dagCheckNodeV4 m_31 g_31 ep_31 bds_31 1 (dagTraceF m_31 s_31 3 f_31) cur_31) = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_31 g_31 ep_31 bds_31 1 (dagTraceF m_31 s_31 3 f_31) cur_31) i = true := fun _ h1 h2 => treeBlockF_at nb_31 h1 h2
theorem lb_31 : LowerBin m_31 s_31 g_31 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_31 kn_31 sub_31 gl_31 rc_31 nc_31

def m_32 : Nat := 0xffff000000000000
def s_32 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_32 : Nat := 0x117000000000000
def ep_32 : Nat := 0x16000000000000010600000000000001120000000000000114000000000000
theorem epk_32 : ep_32 = edgePack m_32 g_32 := by decide +kernel
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7), (m_14, s_14, 4, g_14), (m_29, s_29, 4, g_29), (m_31, s_31, 4, g_31)]
theorem kn_32 : KnownBin bds_32 := by
  intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_7
  · exact lb_14
  · exact lb_29
  · exact lb_31
theorem sub_32 : ∀ b ∈ bds_32, m_32 &&& b.1 = b.1 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_32 : ∀ b ∈ bds_32, canon b.1 g_32 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_32_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_32_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_32 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_32_1 (Nat.sub p 32)) (cc_32_0 p) (Nat.blt p 32)
def f_32 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV4 m_32 g_32 ep_32 43 bds_32 (dagTraceF m_32 s_32 6 f_32) (cur_32 0) s_32 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32_0 : treeBlockF 0 32 (dagCheckNodeV4 m_32 g_32 ep_32 bds_32 43 (dagTraceF m_32 s_32 6 f_32) cur_32) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32_1 : treeBlockF 32 43 (dagCheckNodeV4 m_32 g_32 ep_32 bds_32 43 (dagTraceF m_32 s_32 6 f_32) cur_32) = true := by decide +kernel
theorem nj_32_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_32 g_32 ep_32 bds_32 43 (dagTraceF m_32 s_32 6 f_32) cur_32) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_32_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_32_1 h1 h2)
theorem nc_32 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_32 g_32 ep_32 bds_32 43 (dagTraceF m_32 s_32 6 f_32) cur_32) i = true := nj_32_1
theorem lb_32 : LowerBin m_32 s_32 g_32 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_32 kn_32 sub_32 gl_32 rc_32 nc_32

def m_33 : Nat := 0xffff00000000
def s_33 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_33 : Nat := 0x177700000000
def ep_33 : Nat := 0x6000000000000006000000000000001222000000000000144400000000
theorem epk_33 : ep_33 = edgePack m_33 g_33 := by decide +kernel
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_21, s_21, 4, g_21)]
theorem kn_33 : KnownBin bds_33 := by
  intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_21
theorem sub_33 : ∀ b ∈ bds_33, m_33 &&& b.1 = b.1 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_33 : ∀ b ∈ bds_33, canon b.1 g_33 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_33 : Nat → List (Nat × Nat) := fun _ => []
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV4 m_33 g_33 ep_33 0 bds_33 (dagTraceF m_33 s_33 4 f_33) (cur_33 0) s_33 4 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_33 g_33 ep_33 bds_33 0 (dagTraceF m_33 s_33 4 f_33) cur_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_33 kn_33 sub_33 gl_33 rc_33 nc_33

def m_34 : Nat := 0xf0f0f0f000000000
def s_34 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_34 : Nat := 0x10107000000000
def ep_34 : Nat := 0x1060000000000010006000000000000000000000000000101020000000000010104000000000
theorem epk_34 : ep_34 = edgePack m_34 g_34 := by decide +kernel
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3), (m_30, s_30, 4, g_30), (m_12, s_12, 4, g_12), (m_11, s_11, 4, g_11)]
theorem kn_34 : KnownBin bds_34 := by
  intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_3
  · exact lb_30
  · exact lb_12
  · exact lb_11
theorem sub_34 : ∀ b ∈ bds_34, m_34 &&& b.1 = b.1 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_34 : ∀ b ∈ bds_34, canon b.1 g_34 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_34_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_34_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_34 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_34_1 (Nat.sub p 32)) (cc_34_0 p) (Nat.blt p 32)
def f_34 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV4 m_34 g_34 ep_34 43 bds_34 (dagTraceF m_34 s_34 6 f_34) (cur_34 0) s_34 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_0 : treeBlockF 0 32 (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 43 (dagTraceF m_34 s_34 6 f_34) cur_34) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_1 : treeBlockF 32 43 (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 43 (dagTraceF m_34 s_34 6 f_34) cur_34) = true := by decide +kernel
theorem nj_34_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 43 (dagTraceF m_34 s_34 6 f_34) cur_34) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_34_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_34_1 h1 h2)
theorem nc_34 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 43 (dagTraceF m_34 s_34 6 f_34) cur_34) i = true := nj_34_1
theorem lb_34 : LowerBin m_34 s_34 g_34 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_34 kn_34 sub_34 gl_34 rc_34 nc_34

def m_35 : Nat := 0xf0f0f0f00000000
def s_35 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_35 : Nat := 0x107070700000000
def ep_35 : Nat := 0x600000000000006000000000000000000000000000001020202000000000104040400000000
theorem epk_35 : ep_35 = edgePack m_35 g_35 := by decide +kernel
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
theorem kn_35 : KnownBin bds_35 := by
  intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_7
theorem sub_35 : ∀ b ∈ bds_35, m_35 &&& b.1 = b.1 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_35 : ∀ b ∈ bds_35, canon b.1 g_35 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_35 : Nat → List (Nat × Nat) := fun _ => []
def f_35 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV4 m_35 g_35 ep_35 0 bds_35 (dagTraceF m_35 s_35 4 f_35) (cur_35 0) s_35 4 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_35 g_35 ep_35 bds_35 0 (dagTraceF m_35 s_35 4 f_35) cur_35 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_35 : LowerBin m_35 s_35 g_35 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_35 kn_35 sub_35 gl_35 rc_35 nc_35

def m_36 : Nat := 0xcccccccc00000000
def s_36 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_36 : Nat := 0x4044400000000
def ep_36 : Nat := 0x440000000000004004000000000000404000000000000000000000000000004044400000000
theorem epk_36 : ep_36 = edgePack m_36 g_36 := by decide +kernel
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
theorem kn_36 : KnownBin bds_36 := by
  intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_10
theorem sub_36 : ∀ b ∈ bds_36, m_36 &&& b.1 = b.1 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_36 : ∀ b ∈ bds_36, canon b.1 g_36 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_36 : Nat → List (Nat × Nat) := fun _ => []
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV4 m_36 g_36 ep_36 0 bds_36 (dagTraceF m_36 s_36 4 f_36) (cur_36 0) s_36 4 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_36 g_36 ep_36 bds_36 0 (dagTraceF m_36 s_36 4 f_36) cur_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_36 kn_36 sub_36 gl_36 rc_36 nc_36

def m_37 : Nat := 0x3333333300000000
def s_37 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_37 : Nat := 0x113133300000000
def ep_37 : Nat := 0x1220000000000012002000000000010202000000000000000000000000000110100000000000
theorem epk_37 : ep_37 = edgePack m_37 g_37 := by decide +kernel
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6), (m_31, s_31, 4, g_31), (m_11, s_11, 4, g_11), (m_9, s_9, 4, g_9)]
theorem kn_37 : KnownBin bds_37 := by
  intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_6
  · exact lb_31
  · exact lb_11
  · exact lb_9
theorem sub_37 : ∀ b ∈ bds_37, m_37 &&& b.1 = b.1 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_37 : ∀ b ∈ bds_37, canon b.1 g_37 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_37_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8724381de0ee07323981c44b575a02d01642aa4550298940698435b9a80d406623301980c445a429214049844a123109c0064001 0x59003c6015407c9a07d3a36950b460fa10592a048cf1460a9f054b9d07a0c39201a830c4285a8825180a83d002c600c4040120310050280f4e07a6b69342c92a2450b20878f5a46ac94d2ca2874f5826a1c4e0626870f818720c320618830c018547826060d0805952980e400f180310100680c300c0a038c01a6015200b20078c02a8081340fa72cd29468c1f420b25269181c7c0e3d489e904d42a5a892506251e118287c0c3d0a17030a418440c21061003068202c624c0b2012d203e800d400e980310050680d300a90030c030480c300e980a0d0184015200c1207938d4945a460f21058f8a47442360b190e518626c0d2e06250811818741036060c878fc2c7742370b19874fe426e152f7093870fc1876b8370619850bc1856702706118306c102e000f 13 8191 5 31 10 1023 17 131071
def cc_37_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb817017bae0544a80580a014018811001 0x2e9c174d0f27059343c7c16390b19058c42c61514d84a2874f6626a152d8092d21341892a0450620870f5a06a142d4c12858c1f2493a4d0b24c29142c821e3d991a875383a7cf126942683124b08a0c410e1eb00d4702b104c0620078c1f2681520 11 2047 5 31 10 1023 17 131071
def cur_37 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_37_1 (Nat.sub p 32)) (cc_37_0 p) (Nat.blt p 32)
def f_37 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV4 m_37 g_37 ep_37 43 bds_37 (dagTraceF m_37 s_37 6 f_37) (cur_37 0) s_37 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_37_0 : treeBlockF 0 32 (dagCheckNodeV4 m_37 g_37 ep_37 bds_37 43 (dagTraceF m_37 s_37 6 f_37) cur_37) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_37_1 : treeBlockF 32 43 (dagCheckNodeV4 m_37 g_37 ep_37 bds_37 43 (dagTraceF m_37 s_37 6 f_37) cur_37) = true := by decide +kernel
theorem nj_37_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_37 g_37 ep_37 bds_37 43 (dagTraceF m_37 s_37 6 f_37) cur_37) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_37_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_37_1 h1 h2)
theorem nc_37 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_37 g_37 ep_37 bds_37 43 (dagTraceF m_37 s_37 6 f_37) cur_37) i = true := nj_37_1
theorem lb_37 : LowerBin m_37 s_37 g_37 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_37 kn_37 sub_37 gl_37 rc_37 nc_37

def m_38 : Nat := 0xaaaaaaaa00000000
def s_38 : List Nat := [0x2222222200000000, 0xa0a0a0a00000000, 0xaa00aa00000000, 0xaaaa00000000]
def g_38 : Nat := 0x2022200000000
def ep_38 : Nat := 0x220000000000002002000000000000202000000000000020222000000000000000000000000
theorem epk_38 : ep_38 = edgePack m_38 g_38 := by decide +kernel
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_38 : KnownBin bds_38 := by
  intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_38 : ∀ b ∈ bds_38, m_38 &&& b.1 = b.1 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_38 : ∀ b ∈ bds_38, canon b.1 g_38 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV4 m_38 g_38 ep_38 0 bds_38 (dagTraceF m_38 s_38 4 f_38) (cur_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_38 g_38 ep_38 bds_38 0 (dagTraceF m_38 s_38 4 f_38) cur_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_38 kn_38 sub_38 gl_38 rc_38 nc_38

def m_39 : Nat := 0x5555555500000000
def s_39 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_39 : Nat := 0x115155500000000
def ep_39 : Nat := 0x1440000000000014004000000000010404000000000001101000000000000000000000000000
theorem epk_39 : ep_39 = edgePack m_39 g_39 := by decide +kernel
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4), (m_29, s_29, 4, g_29), (m_12, s_12, 4, g_12), (m_10, s_10, 4, g_10)]
theorem kn_39 : KnownBin bds_39 := by
  intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_4
  · exact lb_29
  · exact lb_12
  · exact lb_10
theorem sub_39 : ∀ b ∈ bds_39, m_39 &&& b.1 = b.1 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_39 : ∀ b ∈ bds_39, canon b.1 g_39 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_39_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8724381de0ee07323981c44b575a02d01642aa4550298940698435b9a80d406623301980c445a429214049844a123109c0064001 0x59003c6015407c9a07d3a36950b460fa10592a048cf1460a9f054b9d07a0c39201a830c4285a8825180a83d002c600c4040120310050280f4e07a6b69342c92a2450b20878f5a46ac94d2ca2874f5826a1c4e0626870f818720c320618830c018547826060d0805952980e400f180310100680c300c0a038c01a6015200b20078c02a8081340fa72cd29468c1f420b25269181c7c0e3d489e904d42a5a892506251e118287c0c3d0a17030a418440c21061003068202c624c0b2012d203e800d400e980310050680d300a90030c030480c300e980a0d0184015200c1207938d4945a460f21058f8a47442360b190e518626c0d2e06250811818741036060c878fc2c7742370b19874fe426e152f7093870fc1876b8370619850bc1856702706118306c102e000f 13 8191 5 31 10 1023 17 131071
def cc_39_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb817017bae0544a80580a014018811001 0x2e9c174d0f27059343c7c16390b19058c42c61514d84a2874f6626a152d8092d21341892a0450620870f5a06a142d4c12858c1f2493a4d0b24c29142c821e3d991a875383a7cf126942683124b08a0c410e1eb00d4702b104c0620078c1f2681520 11 2047 5 31 10 1023 17 131071
def cur_39 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_39_1 (Nat.sub p 32)) (cc_39_0 p) (Nat.blt p 32)
def f_39 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV4 m_39 g_39 ep_39 43 bds_39 (dagTraceF m_39 s_39 6 f_39) (cur_39 0) s_39 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_39_0 : treeBlockF 0 32 (dagCheckNodeV4 m_39 g_39 ep_39 bds_39 43 (dagTraceF m_39 s_39 6 f_39) cur_39) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_39_1 : treeBlockF 32 43 (dagCheckNodeV4 m_39 g_39 ep_39 bds_39 43 (dagTraceF m_39 s_39 6 f_39) cur_39) = true := by decide +kernel
theorem nj_39_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_39 g_39 ep_39 bds_39 43 (dagTraceF m_39 s_39 6 f_39) cur_39) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_39_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_39_1 h1 h2)
theorem nc_39 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_39 g_39 ep_39 bds_39 43 (dagTraceF m_39 s_39 6 f_39) cur_39) i = true := nj_39_1
theorem lb_39 : LowerBin m_39 s_39 g_39 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_39 kn_39 sub_39 gl_39 rc_39 nc_39

def m_40 : Nat := 0xaaaa0000aaaa0000
def s_40 : List Nat := [0x2222000022220000, 0xa0a00000a0a0000, 0xaa000000aa0000, 0xaaaa0000]
def g_40 : Nat := 0x20000020a0000
def ep_40 : Nat := 0x20800000000000000000000000200000008000000020000020a000000020000020000000000000000000000
theorem epk_40 : ep_40 = edgePack m_40 g_40 := by decide +kernel
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_23, s_23, 4, g_23)]
theorem kn_40 : KnownBin bds_40 := by
  intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_23
theorem sub_40 : ∀ b ∈ bds_40, m_40 &&& b.1 = b.1 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_40 : ∀ b ∈ bds_40, canon b.1 g_40 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_40 : Nat → List (Nat × Nat) := fun _ => []
def f_40 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV4 m_40 g_40 ep_40 0 bds_40 (dagTraceF m_40 s_40 4 f_40) (cur_40 0) s_40 4 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_40 g_40 ep_40 bds_40 0 (dagTraceF m_40 s_40 4 f_40) cur_40 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_40 : LowerBin m_40 s_40 g_40 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_40 kn_40 sub_40 gl_40 rc_40 nc_40

def m_41 : Nat := 0x5555000055550000
def s_41 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_41 : Nat := 0x115000015550000
def ep_41 : Nat := 0x1440000000000000000000000014000000400000010400000400000001100000100000000000000000000000
theorem epk_41 : ep_41 = edgePack m_41 g_41 := by decide +kernel
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16), (m_29, s_29, 4, g_29), (m_25, s_25, 4, g_25), (m_22, s_22, 4, g_22)]
theorem kn_41 : KnownBin bds_41 := by
  intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_16
  · exact lb_29
  · exact lb_25
  · exact lb_22
theorem sub_41 : ∀ b ∈ bds_41, m_41 &&& b.1 = b.1 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_41 : ∀ b ∈ bds_41, canon b.1 g_41 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_41_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8724381de0ee07323981c44b575a02d01642aa4550298940698435b9a80d406623301980c445a429214049844a123109c0064001 0x59003c6015407c9a07d3a36950b460fa10592a048cf1460a9f054b9d07a0c39201a830c4285a8825180a83d002c600c4040120310050280f4e07a6b69342c92a2450b20878f5a46ac94d2ca2874f5826a1c4e0626870f818720c320618830c018547826060d0805952980e400f180310100680c300c0a038c01a6015200b20078c02a8081340fa72cd29468c1f420b25269181c7c0e3d489e904d42a5a892506251e118287c0c3d0a17030a418440c21061003068202c624c0b2012d203e800d400e980310050680d300a90030c030480c300e980a0d0184015200c1207938d4945a460f21058f8a47442360b190e518626c0d2e06250811818741036060c878fc2c7742370b19874fe426e152f7093870fc1876b8370619850bc1856702706118306c102e000f 13 8191 5 31 10 1023 17 131071
def cc_41_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb817017bae0544a80580a014018811001 0x2e9c174d0f27059343c7c16390b19058c42c61514d84a2874f6626a152d8092d21341892a0450620870f5a06a142d4c12858c1f2493a4d0b24c29142c821e3d991a875383a7cf126942683124b08a0c410e1eb00d4702b104c0620078c1f2681520 11 2047 5 31 10 1023 17 131071
def cur_41 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_41_1 (Nat.sub p 32)) (cc_41_0 p) (Nat.blt p 32)
def f_41 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV4 m_41 g_41 ep_41 43 bds_41 (dagTraceF m_41 s_41 6 f_41) (cur_41 0) s_41 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_0 : treeBlockF 0 32 (dagCheckNodeV4 m_41 g_41 ep_41 bds_41 43 (dagTraceF m_41 s_41 6 f_41) cur_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_1 : treeBlockF 32 43 (dagCheckNodeV4 m_41 g_41 ep_41 bds_41 43 (dagTraceF m_41 s_41 6 f_41) cur_41) = true := by decide +kernel
theorem nj_41_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_41 g_41 ep_41 bds_41 43 (dagTraceF m_41 s_41 6 f_41) cur_41) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_41_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_41_1 h1 h2)
theorem nc_41 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_41 g_41 ep_41 bds_41 43 (dagTraceF m_41 s_41 6 f_41) cur_41) i = true := nj_41_1
theorem lb_41 : LowerBin m_41 s_41 g_41 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_41 kn_41 sub_41 gl_41 rc_41 nc_41

def m_42 : Nat := 0xf0f00000f0f0
def s_42 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_42 : Nat := 0x1070000030f0
def ep_42 : Nat := 0x2080000000000000000000000060000000c0000000000000000000001020000030000000104000000000
theorem epk_42 : ep_42 = edgePack m_42 g_42 := by decide +kernel
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 4, g_18)]
theorem kn_42 : KnownBin bds_42 := by
  intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_18
theorem sub_42 : ∀ b ∈ bds_42, m_42 &&& b.1 = b.1 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_42 : ∀ b ∈ bds_42, canon b.1 g_42 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_42 : Nat → List (Nat × Nat) := fun _ => []
def f_42 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV4 m_42 g_42 ep_42 0 bds_42 (dagTraceF m_42 s_42 4 f_42) (cur_42 0) s_42 4 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_42 g_42 ep_42 bds_42 0 (dagTraceF m_42 s_42 4 f_42) cur_42 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_42 kn_42 sub_42 gl_42 rc_42 nc_42

def m_43 : Nat := 0xcccc0000cccc0000
def s_43 : List Nat := [0x4444000044440000, 0xc0c00000c0c0000, 0xcc000000cc0000, 0xcccc0000]
def g_43 : Nat := 0x40000044c0000
def ep_43 : Nat := 0x448000000000000000000000004000000480000000400000408000000000000000000000004000004400000
theorem epk_43 : ep_43 = edgePack m_43 g_43 := by decide +kernel
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15), (m_2, s_2, 4, g_2), (m_22, s_22, 4, g_22), (m_24, s_24, 4, g_24)]
theorem kn_43 : KnownBin bds_43 := by
  intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_15
  · exact lb_2
  · exact lb_22
  · exact lb_24
theorem sub_43 : ∀ b ∈ bds_43, m_43 &&& b.1 = b.1 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_43 : ∀ b ∈ bds_43, canon b.1 g_43 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_43_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_43_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_43 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_43_1 (Nat.sub p 32)) (cc_43_0 p) (Nat.blt p 32)
def f_43 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV4 m_43 g_43 ep_43 43 bds_43 (dagTraceF m_43 s_43 6 f_43) (cur_43 0) s_43 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_0 : treeBlockF 0 32 (dagCheckNodeV4 m_43 g_43 ep_43 bds_43 43 (dagTraceF m_43 s_43 6 f_43) cur_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_1 : treeBlockF 32 43 (dagCheckNodeV4 m_43 g_43 ep_43 bds_43 43 (dagTraceF m_43 s_43 6 f_43) cur_43) = true := by decide +kernel
theorem nj_43_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_43 g_43 ep_43 bds_43 43 (dagTraceF m_43 s_43 6 f_43) cur_43) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_43_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_43_1 h1 h2)
theorem nc_43 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_43 g_43 ep_43 bds_43 43 (dagTraceF m_43 s_43 6 f_43) cur_43) i = true := nj_43_1
theorem lb_43 : LowerBin m_43 s_43 g_43 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_43 kn_43 sub_43 gl_43 rc_43 nc_43

def m_44 : Nat := 0xaaaa0000aaaa
def s_44 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_44 : Nat := 0x22200002aaa
def ep_44 : Nat := 0x288800000000000000000000002000000080000002000000080000000222000020000000000000000000
theorem epk_44 : ep_44 = edgePack m_44 g_44 := by decide +kernel
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 4, g_18)]
theorem kn_44 : KnownBin bds_44 := by
  intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_18
theorem sub_44 : ∀ b ∈ bds_44, m_44 &&& b.1 = b.1 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_44 : ∀ b ∈ bds_44, canon b.1 g_44 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_44 : Nat → List (Nat × Nat) := fun _ => []
def f_44 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV4 m_44 g_44 ep_44 0 bds_44 (dagTraceF m_44 s_44 4 f_44) (cur_44 0) s_44 4 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_44 g_44 ep_44 bds_44 0 (dagTraceF m_44 s_44 4 f_44) cur_44 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_44 : LowerBin m_44 s_44 g_44 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_44 kn_44 sub_44 gl_44 rc_44 nc_44

def m_45 : Nat := 0xaa00aa00aa00aa00
def s_45 : List Nat := [0x2200220022002200, 0xa000a000a000a00, 0xaa000000aa00, 0xaa00aa00]
def g_45 : Nat := 0x20002002a00
def ep_45 : Nat := 0x200280000000200000028000000000000000000000002000200080000000200020020000000000000000000
theorem epk_45 : ep_45 = edgePack m_45 g_45 := by decide +kernel
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_20, s_20, 4, g_20), (m_26, s_26, 4, g_26), (m_1, s_1, 4, g_1), (m_0, s_0, 4, g_0)]
theorem kn_45 : KnownBin bds_45 := by
  intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_20
  · exact lb_26
  · exact lb_1
  · exact lb_0
theorem sub_45 : ∀ b ∈ bds_45, m_45 &&& b.1 = b.1 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_45 : ∀ b ∈ bds_45, canon b.1 g_45 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_45_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_45_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_45 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_45_1 (Nat.sub p 32)) (cc_45_0 p) (Nat.blt p 32)
def f_45 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV4 m_45 g_45 ep_45 43 bds_45 (dagTraceF m_45 s_45 6 f_45) (cur_45 0) s_45 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_0 : treeBlockF 0 32 (dagCheckNodeV4 m_45 g_45 ep_45 bds_45 43 (dagTraceF m_45 s_45 6 f_45) cur_45) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_1 : treeBlockF 32 43 (dagCheckNodeV4 m_45 g_45 ep_45 bds_45 43 (dagTraceF m_45 s_45 6 f_45) cur_45) = true := by decide +kernel
theorem nj_45_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_45 g_45 ep_45 bds_45 43 (dagTraceF m_45 s_45 6 f_45) cur_45) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_45_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_45_1 h1 h2)
theorem nc_45 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_45 g_45 ep_45 bds_45 43 (dagTraceF m_45 s_45 6 f_45) cur_45) i = true := nj_45_1
theorem lb_45 : LowerBin m_45 s_45 g_45 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_45 kn_45 sub_45 gl_45 rc_45 nc_45

def m_46 : Nat := 0x3300330033003300
def s_46 : List Nat := [0x1100110011001100, 0x300030003000300, 0x330000003300, 0x33003300]
def g_46 : Nat := 0x100130013003300
def ep_46 : Nat := 0x1200200000001200000020000000000000000000010002000200000000000000000000000100100010000000
theorem epk_46 : ep_46 = edgePack m_46 g_46 := by decide +kernel
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6), (m_17, s_17, 4, g_17), (m_27, s_27, 4, g_27), (m_1, s_1, 4, g_1)]
theorem kn_46 : KnownBin bds_46 := by
  intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_6
  · exact lb_17
  · exact lb_27
  · exact lb_1
theorem sub_46 : ∀ b ∈ bds_46, m_46 &&& b.1 = b.1 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_46 : ∀ b ∈ bds_46, canon b.1 g_46 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_46_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_46_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
def cur_46 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_46_1 (Nat.sub p 32)) (cc_46_0 p) (Nat.blt p 32)
def f_46 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV4 m_46 g_46 ep_46 43 bds_46 (dagTraceF m_46 s_46 6 f_46) (cur_46 0) s_46 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_0 : treeBlockF 0 32 (dagCheckNodeV4 m_46 g_46 ep_46 bds_46 43 (dagTraceF m_46 s_46 6 f_46) cur_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_1 : treeBlockF 32 43 (dagCheckNodeV4 m_46 g_46 ep_46 bds_46 43 (dagTraceF m_46 s_46 6 f_46) cur_46) = true := by decide +kernel
theorem nj_46_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_46 g_46 ep_46 bds_46 43 (dagTraceF m_46 s_46 6 f_46) cur_46) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_46_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_46_1 h1 h2)
theorem nc_46 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_46 g_46 ep_46 bds_46 43 (dagTraceF m_46 s_46 6 f_46) cur_46) i = true := nj_46_1
theorem lb_46 : LowerBin m_46 s_46 g_46 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_46 kn_46 sub_46 gl_46 rc_46 nc_46

def m_47 : Nat := 0xcc00cc00cc00cc00
def s_47 : List Nat := [0x4400440044004400, 0xc000c000c000c00, 0xcc000000cc00, 0xcc00cc00]
def g_47 : Nat := 0x40004000c00
def ep_47 : Nat := 0x4000800000004000000080000000000000000000000040004000c0000000000000000000000040004000000
theorem epk_47 : ep_47 = edgePack m_47 g_47 := by decide +kernel
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_28, s_28, 4, g_28)]
theorem kn_47 : KnownBin bds_47 := by
  intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_28
theorem sub_47 : ∀ b ∈ bds_47, m_47 &&& b.1 = b.1 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_47 : ∀ b ∈ bds_47, canon b.1 g_47 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_47 : Nat → List (Nat × Nat) := fun _ => []
def f_47 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV4 m_47 g_47 ep_47 0 bds_47 (dagTraceF m_47 s_47 4 f_47) (cur_47 0) s_47 4 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_47 g_47 ep_47 bds_47 0 (dagTraceF m_47 s_47 4 f_47) cur_47 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_47 : LowerBin m_47 s_47 g_47 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_47 kn_47 sub_47 gl_47 rc_47 nc_47

def m_48 : Nat := 0xf000f000f000f00
def s_48 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_48 : Nat := 0x100070007000f00
def ep_48 : Nat := 0x600080000000600000008000000000000000000000000000000000001000200020000000100040004000000
theorem epk_48 : ep_48 = edgePack m_48 g_48 := by decide +kernel
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8), (m_19, s_19, 4, g_19), (m_28, s_28, 4, g_28), (m_0, s_0, 4, g_0)]
theorem kn_48 : KnownBin bds_48 := by
  intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_8
  · exact lb_19
  · exact lb_28
  · exact lb_0
theorem sub_48 : ∀ b ∈ bds_48, m_48 &&& b.1 = b.1 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_48 : ∀ b ∈ bds_48, canon b.1 g_48 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_48_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_48_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
def cur_48 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_48_1 (Nat.sub p 32)) (cc_48_0 p) (Nat.blt p 32)
def f_48 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV4 m_48 g_48 ep_48 43 bds_48 (dagTraceF m_48 s_48 6 f_48) (cur_48 0) s_48 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_0 : treeBlockF 0 32 (dagCheckNodeV4 m_48 g_48 ep_48 bds_48 43 (dagTraceF m_48 s_48 6 f_48) cur_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_1 : treeBlockF 32 43 (dagCheckNodeV4 m_48 g_48 ep_48 bds_48 43 (dagTraceF m_48 s_48 6 f_48) cur_48) = true := by decide +kernel
theorem nj_48_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_48 g_48 ep_48 bds_48 43 (dagTraceF m_48 s_48 6 f_48) cur_48) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_48_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_48_1 h1 h2)
theorem nc_48 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_48 g_48 ep_48 bds_48 43 (dagTraceF m_48 s_48 6 f_48) cur_48) i = true := nj_48_1
theorem lb_48 : LowerBin m_48 s_48 g_48 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_48 kn_48 sub_48 gl_48 rc_48 nc_48

def m_49 : Nat := 0xcc00cc00cc00cc
def s_49 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_49 : Nat := 0x40044004c00cc
def ep_49 : Nat := 0x48008800000040000000800000000000000000000400000008000000000000000000000004004400400000
theorem epk_49 : ep_49 = edgePack m_49 g_49 := by decide +kernel
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
theorem kn_49 : KnownBin bds_49 := by
  intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_5
theorem sub_49 : ∀ b ∈ bds_49, m_49 &&& b.1 = b.1 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_49 : ∀ b ∈ bds_49, canon b.1 g_49 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_49 : Nat → List (Nat × Nat) := fun _ => []
def f_49 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV4 m_49 g_49 ep_49 0 bds_49 (dagTraceF m_49 s_49 4 f_49) (cur_49 0) s_49 4 = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_49 g_49 ep_49 bds_49 0 (dagTraceF m_49 s_49 4 f_49) cur_49 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_49 : LowerBin m_49 s_49 g_49 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_49 kn_49 sub_49 gl_49 rc_49 nc_49

def m_50 : Nat := 0xcccccccc
def s_50 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_50 : Nat := 0x44c0ccc
def ep_50 : Nat := 0x88000000000004800c00000000004080c0000000000000000000000000004400000
theorem epk_50 : ep_50 = edgePack m_50 g_50 := by decide +kernel
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_50 : KnownBin bds_50 := by
  intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_50 : ∀ b ∈ bds_50, m_50 &&& b.1 = b.1 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_50 : ∀ b ∈ bds_50, canon b.1 g_50 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_50 : Nat → List (Nat × Nat) := fun _ => []
def f_50 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV4 m_50 g_50 ep_50 0 bds_50 (dagTraceF m_50 s_50 4 f_50) (cur_50 0) s_50 4 = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_50 g_50 ep_50 bds_50 0 (dagTraceF m_50 s_50 4 f_50) cur_50 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_50 : LowerBin m_50 s_50 g_50 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_50 kn_50 sub_50 gl_50 rc_50 nc_50

def m_51 : Nat := 0xaaaaaaaa
def s_51 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_51 : Nat := 0x20a2aaa
def ep_51 : Nat := 0x28a0000000000008008000000000020a080000000000020020000000000000000000
theorem epk_51 : ep_51 = edgePack m_51 g_51 := by decide +kernel
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_26, s_26, 4, g_26)]
theorem kn_51 : KnownBin bds_51 := by
  intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_26
theorem sub_51 : ∀ b ∈ bds_51, m_51 &&& b.1 = b.1 := by intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_51 : ∀ b ∈ bds_51, canon b.1 g_51 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_51 : Nat → List (Nat × Nat) := fun _ => []
def f_51 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV4 m_51 g_51 ep_51 0 bds_51 (dagTraceF m_51 s_51 4 f_51) (cur_51 0) s_51 4 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_51 g_51 ep_51 bds_51 0 (dagTraceF m_51 s_51 4 f_51) cur_51 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_51 : LowerBin m_51 s_51 g_51 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_51 kn_51 sub_51 gl_51 rc_51 nc_51

def m_52 : Nat := 0xff000000ff000000
def s_52 : List Nat := [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000]
def g_52 : Nat := 0x100000017000000
def ep_52 : Nat := 0x1600000000000000000000000000000000000000010000000600000001000000120000000100000014000000
theorem epk_52 : ep_52 = edgePack m_52 g_52 := by decide +kernel
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_19, s_19, 4, g_19), (m_13, s_13, 4, g_13), (m_16, s_16, 4, g_16), (m_17, s_17, 4, g_17)]
theorem kn_52 : KnownBin bds_52 := by
  intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_19
  · exact lb_13
  · exact lb_16
  · exact lb_17
theorem sub_52 : ∀ b ∈ bds_52, m_52 &&& b.1 = b.1 := by intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_52 : ∀ b ∈ bds_52, canon b.1 g_52 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_52_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_52_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_52 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_52_1 (Nat.sub p 32)) (cc_52_0 p) (Nat.blt p 32)
def f_52 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV4 m_52 g_52 ep_52 43 bds_52 (dagTraceF m_52 s_52 6 f_52) (cur_52 0) s_52 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_0 : treeBlockF 0 32 (dagCheckNodeV4 m_52 g_52 ep_52 bds_52 43 (dagTraceF m_52 s_52 6 f_52) cur_52) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_1 : treeBlockF 32 43 (dagCheckNodeV4 m_52 g_52 ep_52 bds_52 43 (dagTraceF m_52 s_52 6 f_52) cur_52) = true := by decide +kernel
theorem nj_52_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_52 g_52 ep_52 bds_52 43 (dagTraceF m_52 s_52 6 f_52) cur_52) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_52_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_52_1 h1 h2)
theorem nc_52 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_52 g_52 ep_52 bds_52 43 (dagTraceF m_52 s_52 6 f_52) cur_52) i = true := nj_52_1
theorem lb_52 : LowerBin m_52 s_52 g_52 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_52 kn_52 sub_52 gl_52 rc_52 nc_52

def m_53 : Nat := 0xf000f000f000f0
def s_53 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_53 : Nat := 0x100070005000f0
def ep_53 : Nat := 0x40008000000060000000a00000000000000000000000000000000000100020000000000010004000500000
theorem epk_53 : ep_53 = edgePack m_53 g_53 := by decide +kernel
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_53 : KnownBin bds_53 := by
  intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_53 : ∀ b ∈ bds_53, m_53 &&& b.1 = b.1 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_53 : ∀ b ∈ bds_53, canon b.1 g_53 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_53 : Nat → List (Nat × Nat) := fun _ => []
def f_53 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV4 m_53 g_53 ep_53 0 bds_53 (dagTraceF m_53 s_53 4 f_53) (cur_53 0) s_53 4 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_53 g_53 ep_53 bds_53 0 (dagTraceF m_53 s_53 4 f_53) cur_53 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_53 : LowerBin m_53 s_53 g_53 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_53 kn_53 sub_53 gl_53 rc_53 nc_53

def m_54 : Nat := 0xf0f00000f0f0000
def s_54 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_54 : Nat := 0x1070000070f0000
def ep_54 : Nat := 0x608000000000000000000000006000000080000000000000000000001020000020000000104000004000000
theorem epk_54 : ep_54 = edgePack m_54 g_54 := by decide +kernel
def bds_54 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7), (m_19, s_19, 4, g_19), (m_24, s_24, 4, g_24), (m_23, s_23, 4, g_23)]
theorem kn_54 : KnownBin bds_54 := by
  intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_7
  · exact lb_19
  · exact lb_24
  · exact lb_23
theorem sub_54 : ∀ b ∈ bds_54, m_54 &&& b.1 = b.1 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_54 : ∀ b ∈ bds_54, canon b.1 g_54 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_54_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_54_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
def cur_54 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_54_1 (Nat.sub p 32)) (cc_54_0 p) (Nat.blt p 32)
def f_54 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV4 m_54 g_54 ep_54 43 bds_54 (dagTraceF m_54 s_54 6 f_54) (cur_54 0) s_54 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_0 : treeBlockF 0 32 (dagCheckNodeV4 m_54 g_54 ep_54 bds_54 43 (dagTraceF m_54 s_54 6 f_54) cur_54) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54_1 : treeBlockF 32 43 (dagCheckNodeV4 m_54 g_54 ep_54 bds_54 43 (dagTraceF m_54 s_54 6 f_54) cur_54) = true := by decide +kernel
theorem nj_54_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_54 g_54 ep_54 bds_54 43 (dagTraceF m_54 s_54 6 f_54) cur_54) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_54_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_54_1 h1 h2)
theorem nc_54 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_54 g_54 ep_54 bds_54 43 (dagTraceF m_54 s_54 6 f_54) cur_54) i = true := nj_54_1
theorem lb_54 : LowerBin m_54 s_54 g_54 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_54 kn_54 sub_54 gl_54 rc_54 nc_54

def m_55 : Nat := 0x3333333333333333
def s_55 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_55 : Nat := 0x113133313133333
def ep_55 : Nat := 0x1200200000001220000020200012002000000000010202000202000000000000000000000110100010100000
theorem epk_55 : ep_55 = edgePack m_55 g_55 := by decide +kernel
def bds_55 : List (Nat × List Nat × Nat × Nat) := [(m_46, s_46, 7, g_46)]
theorem kn_55 : KnownBin bds_55 := by
  intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_46
theorem sub_55 : ∀ b ∈ bds_55, m_55 &&& b.1 = b.1 := by intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_55 : ∀ b ∈ bds_55, canon b.1 g_55 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_55 : Nat → List (Nat × Nat) := fun _ => []
def f_55 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV4 m_55 g_55 ep_55 0 bds_55 (dagTraceF m_55 s_55 7 f_55) (cur_55 0) s_55 7 = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_55 g_55 ep_55 bds_55 0 (dagTraceF m_55 s_55 7 f_55) cur_55 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_55 : LowerBin m_55 s_55 g_55 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_55 kn_55 sub_55 gl_55 rc_55 nc_55

def m_56 : Nat := 0xcccccccccccccccc
def s_56 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_56 : Nat := 0x40444044c0ccc
def ep_56 : Nat := 0x4480888000004400000088000040040004800c00004040004080c0000000000000000000004044404400000
theorem epk_56 : ep_56 = edgePack m_56 g_56 := by decide +kernel
def bds_56 : List (Nat × List Nat × Nat × Nat) := [(m_43, s_43, 7, g_43)]
theorem kn_56 : KnownBin bds_56 := by
  intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_43
theorem sub_56 : ∀ b ∈ bds_56, m_56 &&& b.1 = b.1 := by intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_56 : ∀ b ∈ bds_56, canon b.1 g_56 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_56 : Nat → List (Nat × Nat) := fun _ => []
def f_56 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV4 m_56 g_56 ep_56 0 bds_56 (dagTraceF m_56 s_56 7 f_56) (cur_56 0) s_56 7 = true := by decide +kernel
theorem nc_56 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_56 g_56 ep_56 bds_56 0 (dagTraceF m_56 s_56 7 f_56) cur_56 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_56 : LowerBin m_56 s_56 g_56 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_56 kn_56 sub_56 gl_56 rc_56 nc_56

def m_57 : Nat := 0xff00ff00ff00ff
def s_57 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_57 : Nat := 0x170077005f00ff
def ep_57 : Nat := 0x48008800000060000000a0000000000000000000060000000a000000120022000000000014004400500000
theorem epk_57 : ep_57 = edgePack m_57 g_57 := by decide +kernel
def bds_57 : List (Nat × List Nat × Nat × Nat) := [(m_53, s_53, 5, g_53)]
theorem kn_57 : KnownBin bds_57 := by
  intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_53
theorem sub_57 : ∀ b ∈ bds_57, m_57 &&& b.1 = b.1 := by intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_57 : ∀ b ∈ bds_57, canon b.1 g_57 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_57 : Nat → List (Nat × Nat) := fun _ => []
def f_57 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV4 m_57 g_57 ep_57 0 bds_57 (dagTraceF m_57 s_57 5 f_57) (cur_57 0) s_57 5 = true := by decide +kernel
theorem nc_57 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_57 g_57 ep_57 bds_57 0 (dagTraceF m_57 s_57 5 f_57) cur_57 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_57 : LowerBin m_57 s_57 g_57 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_57 kn_57 sub_57 gl_57 rc_57 nc_57

def m_58 : Nat := 0xffffffff
def s_58 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_58 : Nat := 0x175f3fff
def ep_58 : Nat := 0x28a000000000004800c000000000060a0c0000000000120030000000000014500000
theorem epk_58 : ep_58 = edgePack m_58 g_58 := by decide +kernel
def bds_58 : List (Nat × List Nat × Nat × Nat) := [(m_51, s_51, 5, g_51)]
theorem kn_58 : KnownBin bds_58 := by
  intro b hb; simp only [bds_58, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_51
theorem sub_58 : ∀ b ∈ bds_58, m_58 &&& b.1 = b.1 := by intro b hb; simp only [bds_58, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_58 : ∀ b ∈ bds_58, canon b.1 g_58 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_58, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_58 : Nat → List (Nat × Nat) := fun _ => []
def f_58 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV4 m_58 g_58 ep_58 0 bds_58 (dagTraceF m_58 s_58 5 f_58) (cur_58 0) s_58 5 = true := by decide +kernel
theorem nc_58 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_58 g_58 ep_58 bds_58 0 (dagTraceF m_58 s_58 5 f_58) cur_58 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_58 : LowerBin m_58 s_58 g_58 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_58 kn_58 sub_58 gl_58 rc_58 nc_58

def m_59 : Nat := 0xffff0000ffff
def s_59 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_59 : Nat := 0x177700003fff
def ep_59 : Nat := 0x2888000000000000000000000060000000c00000060000000c0000001222000030000000144400000000
theorem epk_59 : ep_59 = edgePack m_59 g_59 := by decide +kernel
def bds_59 : List (Nat × List Nat × Nat × Nat) := [(m_33, s_33, 5, g_33)]
theorem kn_59 : KnownBin bds_59 := by
  intro b hb; simp only [bds_59, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_33
theorem sub_59 : ∀ b ∈ bds_59, m_59 &&& b.1 = b.1 := by intro b hb; simp only [bds_59, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_59 : ∀ b ∈ bds_59, canon b.1 g_59 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_59, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_59 : Nat → List (Nat × Nat) := fun _ => []
def f_59 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_59 : dagCheckRootsV4 m_59 g_59 ep_59 0 bds_59 (dagTraceF m_59 s_59 5 f_59) (cur_59 0) s_59 5 = true := by decide +kernel
theorem nc_59 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_59 g_59 ep_59 bds_59 0 (dagTraceF m_59 s_59 5 f_59) cur_59 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_59 : LowerBin m_59 s_59 g_59 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_59 kn_59 sub_59 gl_59 rc_59 nc_59

def g_60 : Nat := 0x1171777175f3fff
def ep_60 : Nat := 0x1648288800001660000028a000160060004800c001060600060a0c0001121222120030000114144414500000
theorem epk_60 : ep_60 = edgePack fullMask g_60 := by decide +kernel
def bds_60 : List (Nat × List Nat × Nat × Nat) := [(m_54, s_54, 7, g_54), (m_39, s_39, 7, g_39), (m_52, s_52, 7, g_52), (m_55, s_55, 8, g_55), (m_34, s_34, 7, g_34), (m_56, s_56, 8, g_56), (m_45, s_45, 7, g_45), (m_37, s_37, 7, g_37), (m_32, s_32, 7, g_32), (m_43, s_43, 7, g_43), (m_46, s_46, 7, g_46), (m_41, s_41, 7, g_41), (m_48, s_48, 7, g_48), (m_58, s_58, 6, g_58), (m_59, s_59, 6, g_59), (m_5, s_5, 4, g_5), (m_57, s_57, 6, g_57), (m_49, s_49, 5, g_49), (m_36, s_36, 5, g_36), (m_44, s_44, 5, g_44), (m_42, s_42, 5, g_42), (m_38, s_38, 5, g_38), (m_47, s_47, 5, g_47), (m_35, s_35, 5, g_35), (m_51, s_51, 5, g_51), (m_50, s_50, 5, g_50), (m_40, s_40, 5, g_40)]
theorem kn_60 : KnownBin bds_60 := by
  intro b hb; simp only [bds_60, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_54
  · exact lb_39
  · exact lb_52
  · exact lb_55
  · exact lb_34
  · exact lb_56
  · exact lb_45
  · exact lb_37
  · exact lb_32
  · exact lb_43
  · exact lb_46
  · exact lb_41
  · exact lb_48
  · exact lb_58
  · exact lb_59
  · exact lb_5
  · exact lb_57
  · exact lb_49
  · exact lb_36
  · exact lb_44
  · exact lb_42
  · exact lb_38
  · exact lb_47
  · exact lb_35
  · exact lb_51
  · exact lb_50
  · exact lb_40
theorem sub_60 : ∀ b ∈ bds_60, fullMask &&& b.1 = b.1 := by intro b hb; simp only [bds_60, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_60 : ∀ b ∈ bds_60, canon b.1 g_60 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_60, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_60_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x99d63938658d5638478e7a3a47564d713436c84b67d4b5f885582765354d4c76e462654263c3e64038165360213124e2c84a27e4a22d511e54816184121400dc450904c0781805f1903d220013c00001 0x6d6f01d6b01d6706d6306c6f01c6b01c6704c630ac5f04c5b07c5704c5302b6f01b6b01b6702b6302b5f02b5b02b5a02b5707b5602b5302b4f02b4b02b4702b4302a6f06a6e01a6b01a6a01a6701a6602a6302a6202a5f05a5e02a5b02a5a02a5703a5602a5302a5202a4f04a4e02a4b02a4702a4302a4201a3f01a3e01a3d0296f0196b01967029630295f0295b02957029530294f0294b02947029430293f0293b02937029330292f0292d0292b0292702925029230186f0186b01867018630785f0185b07857018530484f0184b04847018430183b0283a018390283702836018330183102827028261d0250281f0181b028170181301d6f01d6b01d6701d6301c6f01c6b01c6701c6304c5f04c5b04c5704c5301b6f01b6e01b6b01b6a01b6701b6601b6301b6207b5f05b5e07b5b03b5a07b5703b5607b5305b5204b4f04b4e04b4b04b4704b4304b4201a6f01a6b01a6701a6302a5f02a5b02a5a02a5707a5602a5302a4f02a4b02a4702a4301a3f01a3e01a3d0196f0196b01967019630295f0295b02957029530294f0294b02947029430293f0293d0293b0293702935029330292f0292b02927029230186f0186b01867018630185f0185b0185a0185707856018530184f0184b01847018430183f0283e0183d0182f0282e0182b018290182301822018210181f0181b018170181301d6f01d6b01d6701d6301c6f01c6b01c6701c6304c5f04c5b04c5704c5301b6f01b6b01b6701b6307b5f02b5b07b5702b5304b4f02b4b04b4702b4301a6f01a6b01a6701a6307a5f02a5b07a5702a5304a4f02a4b04a4702a4302a3f02a3b02a3702a330196f0196b01967019630195f0195b0195a0195707956019530194f0194b01947019430193f0293e0193d019370193501933019320192f0192b01927019230186f0186e0186b0186a018670186601863018620185f0585e0185b0185a018570385601853018520184f0484e0184b018470184301842018371d036018350182f0182b0182a0182708826018230181f0181e0181d03e7f01e7b01e7705e7305d7f06d7e01d7b01d7a01d7701d7605d7305d7205d6f05d6e05d6d06c7f01c7b01c7704c7305c6f03c6b03c6704c6305c5f04c5b04c5905c5704c5304c5106b7f06b7e01b7b01b7a01b7701b7606b7306b7203b6b03b6a07b6907b6803b6703b6605b6305b6205b6105b6003b5703b5603b5503b5404b4f04b4e0cb4b0cb4a0cb470cb4604b4304b4206a7f01a7b01a7702a7305a6f02a6b03a6a03a6703a6602a6305a5705a5607a5507a5404a4f02a4b0aa4702a4301a3f01a3e01a3d0697f0197b01977029730596f0296b03967029630595f0595d0295b0595709955029530494f0294b09947029430993f0993d0293b02939099370993502933029310292f0292b02927029230187f0187b01877018730586f0186b0386a0386703866018630585705856078550a8540484f0184b04847018430283f0283e0283d0282f0282e0182b018290182302822018210281f0181b078170181303e7f01e7b01e7705e7306d7f01d7b01d7704d7305d6f03d6b03d6704d6306c7f06c7e01c7b01c7a01c7701c7606c7306c7205c6f05c6e05c6d05c6c03c6b03c6a03c6703c6607c6507c6404c5f04c5e0cc5b0cc5a0cc570cc5604c5304c5206b7f01b7b01b7702b7305b6f05b6d02b6b03b6a03b6703b6607b6507b6402b6304b5f02b5b0ab5702b5301b4f01b4e01b4d05a7f06a7e01a7b01a7a01a7701a7605a7305a7205a6f05a6e05a6d04a5f04a5e05a5b05a5704a5304a5203a4f03a4e03a4d03a4c02a3f02a3e03a3d02a3c01a3b01a3a05a3701a3605a3501a3402a3302a320697f0197b01977029730596f0296b03967029630495f0295b09957029530994f0994d0294b02949099470994502943029410293f0293b02937029330592f0592d0292b0592709925029230187f0187b01877018730586f0586d0186b0386a0386703866078650a864018630485f0185b04857018530284f0284e0284d0283f0283e0183b018390183302832018310282f0282d0182b0382a01829018280582705826028250282401823018210281f0181b078170181303d6f01d6b01d6705d6301c6b04c6303c5b04c5302b6f01b6b01b6702b6302b5f02b5b02b5702b5302b4f02b4306a6f06a6e01a6b01a6a01a6701a6606a6306a6202a5f02a5b02a5a03a5703a5604a4f04a4e04a4304a4202a3f02a3e01a3b01a3a02a3701a3602a3302a320296f019670295f029570293f029370292f0292d02927029250186f0186b01867018630585f0185b03857018530484f018430283f0183b02837018330282f0282d0182b01829028270282501823018210181b0281706d6f06d6e01d6b01d6a01d6701d6606d6306d6203c6f01c6b01c6705c6303c5f03c5d02c5702c5502c5301b6b04b6304b5b04b5904b5304b5103b4b04b4302a6f01a6b01a6702a6302a5f0da5e02a5d02a4f02a4b02a4702a4302a3f02a330296f019670295f0295d02957029550294f029470292f029270186f0186b01867018630785f0d85e0785d0584f0184b02847018430483f018330282f0182b02827018230181b0281706d6f01d6b01d6706d6303c6f01c6b01c6705c6302c5f02c5d02c5702c5502c5301b6b04b6304b5b04b5303b4b04b4306a6f01a6b01a6706a6305a5f05a5e01a5b01a5905a5705a5305a5201a5101a5005a4f05a4e03a4b03a4705a4305a4204a3f04a330296f019670295f029570294f029470292f0292d02927029250186f0186b01867018630785f0f85e0185b01859058570185307852018510584f0184b0384a0384703846018430483f018330282f0282e0282d0181b0281703d6f01d6b01d6705d6306c6f01c6b01c6706c6301c5b01c5a02c5701c5602c5301b6b04b6303b5b04b5304b4b04b4306a6f01a6b01a6706a6305a5f05a5e03a5b02a5705a5305a5205a4f05a4e02a4b02a4902a4702a4302a4202a4102a4004a3f04a330296f0196b01967029630295f0295b0295a0295703956029530294f0d94e0294b02949029470294302942029410293f029330192f0192e0192d0286f018670285f028570284f028470282f0282d02827028250281f0281703e7f01e7b01e7705e7305d7f06d7e01d7b01d7a01d7701d7605d7305d7201c7b04c7303c6b04c6304c5b04c5904c5304c5106b7f06b7e01b7b01b7a01b7701b7606b7306b7205b6f05b6e03b6b03b6a03b6703b6605b6305b6205b5f05b5e05b5d05b5c05b5b05b5a0fb591935805b5705b560db551835405b5305b5205b5105b5004b4f04b4e04b4304b4202a7f01a7b01a7702a7302a6f02a6b02a6a02a6703a6602a6302a5f02a5d02a5b02a5a02a5902a5802a5705a5602a551725402a5302a5102a4f02a4301a3f01a3e01a3d0297f019770296a02967039660295703956029550293f0293d02937029350292f029270187f0187b01877018730586f0186b0386a0386703866018630585f0585d0185b0585a01859018580585705856078551605401853018510484f018430283f0283e0283d0282f0282e0182b018290182302822018210181b0281706e7f01e7b01e7706e7301d7b04d7304d6b04d6306c7f06c7e01c7b01c7a01c7701c7606c7306c7209c6f09c6e07c6b07c6a07c6707c6609c6309c6204c5f04c5e04c5304c5202b7f01b7b01b7702b7302b6f02b6b02b6a02b6707b6602b6302b5f02b5301b4f01b4e01b4d06a7f06a7e01a7b01a7a01a7701a7606a7306a7209a6f05a6e07a6b03a6a07a6703a6609a6305a6204a5f04a5e04a5304a5201a3b01a3a02a3701a3602a3302a320297f019770296f029670294a02948029470d94602945061440293f0293a0293702936029270d926029250187f0187b01877018730786f0186b0886a078670a866018630485f018530284f0284e0284d0283f0283e0183b018390183302832018310282f0282d028270282501823018210281d0181b028170881506d6f01d6b01d6706d6301c6b04c6304c5b04c5302b6f01b6b01b6702b6302b5f02b5b02b5702b5302b4f02b4306a6f06a6e01a6b01a6a01a6701a6606a6306a6209a5f05a5e07a5b03a5a07a5703a5609a5305a5204a4f04a4e04a4304a4201a3b01a3a02a3701a3602a330296f019670295f029570293f0293a02937029360292706126029250186f0186b01867018630785f0185b07857018530484f018430283f0183b02837018330282f0282d0282702825018230281d0181b028170881506e7f01e7b01e7706e7301d7b04d7304d6b04d6306c7f06c7e01c7b01c7a01c7701c7606c7306c7209c6f05c6e07c6b03c6a07c6703c6609c6305c6204c5f04c5e04c5304c5206b7f06b7e01b7b01b7a01b7701b7606b7306b7209b6f09b6e07b6b07b6a07b6707b6609b6309b6204b5f04b5e04b5304b5202a7f01a7b01a7702a7302a6f02a6b02a6a02a6707a6602a6302a5f02a5302a4f08a4e02a4d08a4c01a3f01a3e01a3d0297f019770296f029670294f0d94e0294d0293f0d93e0293d0613c02932029300292f029270187f0187b01877018730786f0186b0886a078670a866018630485f018530284f0284e0284d0284c0283f0283e0283d0282f0282e0182b018290182302822018210181b0281706d6f01d6b01d6706d6306c6f01c6b01c6704c630cc5f04c5b07c5704c5306b6f06b6e01b6b01b6a01b6701b6606b6306b621b35f05b5e07b5b03b5a07b5703b561a35305b5204b4f04b4e0cb4b0cb4704b4304b4206a6f01a6b01a6702a630aa5f02a5b07a5a07a5707a5602a5304a4f02a4b0ca4702a4301a3f01a3e01a3d0696f0196b01967029631515f0295b07957029530494f0294b0c947029431413f1313d0293b1213705135029330292f0292b02927029230186f0186b01867018630785f0185b0a85a078570a856018530484f0184b04847018430283f0283e0283d0282f0282e0182b018290182302822018210281f0181b088170181301c5f01c5b01c5701c5301b5f01b5b01b5701b5304b4f04b4b04b4704b4301a5f01a5b01a5701a5302a4f02a4b02a4702a4302a3f02a3b02a3702a330195f0195b01957019530294f0294b02947029430293f0293b02937029330292f0292b02927029230185f0185b01857018530184f0184b01847018430183f0183b01837018330182f0182b01827018230181f0181b018170181301c5f01c5b01c5701c5301b5f01b5b01b5701b5303b4f03b4b03b4703b4301a5f01a5b01a5701a5302a4f02a4b02a4702a4302a3f02a3b02a3702a330195f0195b01957019530294f0294b02947029430293f0293b02937029330292f0292b02927029230185f0185b01857018530184f0184b01847018430183f0183b01837018330182f0182d0182b0182a018270282601825018230181f0181b018170181301d6f01d6b01d6701d6301c6f01c6b01c6701c6304c5f04c5b04c5704c5301b6f01b6b01b6701b6302b5f02b5b02b5702b5302b4f02b4b02b4702b4301a6f01a6b01a6701a6302a5f02a5b02a5702a5302a4f02a4b02a4702a4302a3f02a3b02a3702a330196f0196b01967019630195f0195b01957019530194f0194b01947019430193f0193d0193b0193a0193702936019350192f0192b01927019230186f0186e0186b0186a018670186601863018620185f0585e0185d1005c0185b0185a0185703856018550f05401853018520184f0484e0184b0184701843018420183f0283e0183d0182f0182b0182a0182702826018230181f0181e0181d07d6f01d6b01d6709d6302b6f01b6b01b6702b6302b5f02b5b02b5702b5301a660696e019660595e039560293e029360186f0186b01867018630785f0185b07857018530283f0183b0283701833018290881501d6f01d6b01d6701d6301c6b01c6304c5b04c5301b6f01b6e01b6b01b6a01b6701b6601b6301b6207b5f05b5e07b5b03b5a07b5703b5607b5305b5204b4f04b4e04b4304b4201a6f01a6b01a6701a6302a5f02a5b02a5a02a5707a5602a5302a4f02a4301a3f01a3e01a3d0196f019670295f029570293f0293d02937029350292f0292d02927029250186f0186b01867018630185f0185b01857018530184f018430183f0183d0183701835018330182f0182b018290182701823018210181b0181701d6f01d6b01d6701d6301c6b01c6304c5b04c5301b6f01b6b01b6701b6307b5f02b5b07b5702b5304b4f02b4301a6f01a6707a5f07a5702a3f02a370196f0196b0196a0196701966019630195f0195b01957019530194f019430193f0193b01937019330192d01927019250186f0186e0186b0186a018670186601863018620185f0585e0185b0185a018570385601853018520184f0484e01843018420183f0283e0183b0183a018370c036018330183201827088260182501d6f01d6e01d6b01d6a01d6701d6601d6301d6201c6f01c6b01c6701c6307c5f03c5d09c5b05c5907c5703c5509c5305c5101b6b01b6304b5b04b5904b5304b5104b4b04b4301a6f01a6b01a6701a6301a5f01a5d01a5b01a5901a5701a5502a5302a5102a4f02a4b02a4702a4302a3f02a330196f019670295f0d95e0295d0294f029470192f029270186f0186b01867018630185f0d85e0185d0184f0184b01847018430183f018330182f0182b01827018230181b0181701d6f01d6701d6301c6f01c6b01c6701c6307c5f09c5b07c5709c5301b6b01b6304b5b04b5304b4b04b4301a6f01a6b01a6701a6301a5f01a5b01a5702a4f02a4b02a4702a4302a3f02a330196f0196e0196b0196701963019620695f0695e0195b0195901957019530195201951019500894f0794b07947089430493f049330192f0292b0292a0292702926029230186f0186b0186a0186701866018630185f0e85e0185b01859018570185301852018510184f0184b01847018430183f018330182f0182b018270182301d6f01d6b01d6a01d6701d6601d6301c6f01c6b01c6701c6307c5f09c5b07c5709c5301b6b01b6304b5b04b5304b4b04b4301a6f01a6b01a6701a6301a5f01a5b01a5701a5302a4f02a4b02a4702a4302a3f02a330196f0196e0196b0196701963019620695f0695e0295702953029520894f0794b07947089430493f049330292f0292b0292a0292702926029230186f0186a01867018660285f0d85e02857028520284f028470282f028270181f0181e0181d01e7f01e7e02e7d01d7f01d7b01d7701d7306d6f03d6d06d6b05d6906d6703d6506d6305d6101c7b01c7304c6b04c6904c6304c6104c5b04c5301b7b01b7a01b7901b7701b7601b7302b7101b6701b6601b6502b5f02b5b02b5702b5302b4f02b4301a7f01a7e01a7b01a7a01a7701a7601a7301a7206a6f06a6e06a6d06a6c06a6b06a6a08a6908a6806a6706a6608a650a26406a6306a6206a6106a6008a5f05a5e07a5b03a5a07a5703a5608a5305a5204a4f04a4e04a4304a4202a3f02a3e02a3b02a3a02a3702a3602a3302a320197f0197a01977019760296f0296d0296a029670696602965091640295f029570293f029370192f0192e0192d0187f0187b0187a0187701876018730186f0186d0186b0186a01869018680186706866018650806401863018610185f0185b01857018530184f018430183f0183b01837018330181b018190181106d6f01d6b01d6706d6301c6b04c6304c5b04c5306b6f01b6b01b6706b6309b5f07b5b07b5709b5304b4f04b4302a6f01a6b01a6702a6302a5f02a5b02a5702a5302a4f02a4302a3f08a3e02a3d0696f0196b01967069630995f0795b07957099530494f049430192b02927029230186f0186b01867018630785f0185b07857018530484f018430283f0283e0283d0282f0182b02827018230281f028170181306d6f01d6b01d6706d6301c6b04c6304c5b04c5306b6f06b6e01b6b01b6a01b6701b6606b6306b6209b5f05b5e07b5b03b5a07b5703b5609b5305b5204b4f04b4e04b4304b4202a6f01a6b01a6702a6302a5f02a5b02a5702a5302a4f02a4302a3f08a3e02a3d0296f019670295f029570293f0613e0293d0292f029270186f0186b01867018630785f0185b07857018530484f018430283f0283e0283d0282f0182b02827018230181b0281707d6f01d6b01d6709d6301c6b04c6304c5b04c530736f01b6b01b6702b6309b5f02b5b07b5702b5304b4f02b4308a6f06a6e01a6b01a6a01a6701a6608a6306a6208a5f05a5e07a5b03a5a07a5703a5608a5305a5204a4f04a4e04a4304a4202a3f02a3e08a3b08a3a08a370523602a3302a320896f0196a01967019660895f079570293f029370192f0192e0192d0186f0186b0886a018670b866018630785f0185b07857018530484f018430283f0183b08837018330181b018190181101c5f01c5b01c5701c5301a5f01a5b01a5701a5302a4f02a4b02a4702a430185f0185b01857018530184f0184b01847018430182f0182b018270182301c5f01c5b01c5701c5301a5f01a5b01a5701a5302a4f02a4b02a4702a430185f0185b01857018530184f0184b01847018430182f0182b01827018230181501d6f01d6b01d6701d6301b6f01b6b01b6701b6302b5f02b5b02b5702b530196f0196b01967019630195f0195b01957019530193f0193b0193701933019250186e0306c01866020640585e038560283e028360181ec345fc145bc0457be453bc35fba35bb9357b7353b534fb334bb2347b0343a925fa825ba5257a3253a124fa024b9c247982439623f9423b902378d2338b15f8a15b821577f1537514f7414b71147701436b13f6a13b66137631336112f6012b5f1275c1235705f5505b4d0574a0534504f4404b3c047380432503f2403b210371f0331e02f1c02b110270e0230d01f0b01b04017010130003f 20 1048575 8 255 11 2047 20 1048575
def cc_60_1 : Nat → List (Nat × Nat) := unpackCursorV4 0x884570830df732bd03c725f6dcb01a032b19cd5b7f8ad5353c7ca3b7b4583c856b4f7671bfde354565f170b551954ac27666492b488d30f23f182c427520469007e9d0ba8613480122900048 0xf5bc0eb581d6707ac64adbc35b701b6b036d406d9c0db312b630d6c406d6c0dad0aa6f034d60699c153183a5f054b60e95c15298aa3f1547a0a8ec151c8aa371546a0a8cc15188186f030d60619c0c318385f030b60614c241f8483d0505e060ac24138182307cfe0f9f80f3d81e7a03cee079d81f3986e7207afe075ec0ebb83d7303ade075b80eb681c7a0d8e40f1a81e3403c627c8c00f1681e290aa7f034f6069dc153983a6f154da0a9ac153483a67074ca0a98c153083a5f134ba0a96c1d2b83a55054a62a934152084a3d1524c061fc0c3d81877030e60e1bc1c370486d070be0e1780c2d81859030a60e1480c288484d030820a0bc0c158482a0904e2a0980c1183d6f07adc075ac0eb501d6703acc0f58c36b103c6f038d60719c1e3181c5f038bc0717611b781b6b036ce12d8c1daf83b5b076b20ed5c1da984b510769e0ed2c1da383b43154de069ac0d338aa63074be2a9741d2d82a59074ae0e9541d2982a510749e2a9341d2583a470748a0e90c251f8aa3b1546e128ce08b78196b032ce2258c1cafbf15d072b60e55c1caa839530729e0e52c1ca3839430927e224ede89b849331525e224ac549388923030de061ac0c3381863070be0e1782c2e8384f0709c0612c0c24818430708406104241f8183b0906e060cc3c178182b0f0541e09c5413018230f03e0606c3c0b81813038be0716c0e2b81c53036be06d6c0dab81b530969e0ed2c1da384b43034be0696c0d2b81a530549e0a92c152382a430547e0a8ec151b82a33032be0656c0cab819530529e0a52c14a3829430527e0a4ec149b829330525e0a4ac149382923030be0616c0c2b818530309e0612c0c23818430307e060ec0c1b818330305e060ac0c13818230303e0606c0c0b8181303ade075ac0eb381d63038de071ac0e3381c63098be0f16c1e2b84c53036de06db80db581b6a036ce06d980db181b620b6be16d7815ad82b5a076ae0ad582da985b520969e12d3825a584b470968612d080d3781a6e034d6069a80d3381a66034c6069882d2f85a5e054b60e9681d2b83a56054a616948252784a4e0549612928252384a4605486129080d1f81a3e0347a065bc0cb581967032c61657c14ad83957052a61253c14a58494705286224fc449e8293b1126e224d414998292f1125a0a4ac4494829271124a0a48c44908186f030d60619c0c318185f030ba0616c0c2d01857070ac061540c298184f030960611c0c218183f0307a060ec0c1c818370306a060cc0c188182f0305a060ac0c14818270304a0608c0c108181f030360605c0c0981c5f038b60715c0e2981b5f036b606d5c0da984b4f076960ed1c25a181a5f034b60695c0d2985a4f074960e91c2d2184a3f09476128dc25198195f032b60655c0ca98594f072960e51c2ca18493f09276124dc24998892f112562249c44918185f030b60615c0c298184f0309a0612c0c25018470708c061140c218183f03076060dc0c198182f030560609c0c118181f030360605c0c0981d6f03ad60759c0eb181c6f038d60719c0e3184c5f078b60f15c262981b6f036d606d9c0db185b5f076b60ed5c2da984b4f0969612d1c25a181a6f034d60699c0d3185a5f074b60e95c2d2984a4f094961291c252188a3f11476228dc45198196f032d60659c0cb18195f032ba0656c0cad01957072ac065540ca78194b0328e0650c0c9f8193b0326e064cc0c978192b0324e0648c0c378186e030d6061a80c3381866030c6061880c2f8585e030ba0613c24270184b0308e0610c0c210183f0507c060f5d81e0183b03074060ddd01b0183572068060cc0c190182f03056060a80c1388826030460607c0c0f0181d03ade075ac0eb381d63038de071b80e3581c6a038ce071980e3181c62038be071781e2d83c5a038ae071580e2981c52036d606d8c1dad84b530369606d240da181b41034de069ac0d3381a630b4be0e96c1d2b85a530d49e1a934352582a490d48e1a914352182a410947e128cc0cb7819670b2be0e55c4ca78994d1328e26514349786927030de061ac0c3381863030be0616c0c2b818530309e0612c0c248184303082060fc0c198182f030560609c0c118181b0302e079fc1f3e81e7b03cf4079dc0f3b01e7503afe075f81ebe81d6f03adc075b40e3d81c73078d61318c262d84c5a098b2131602e2b04c53098a206dfc0dbf01b7b036f406ddc0dbb01b73036e412dbc2db703b6b076d40ed9c1db304b63096c412d7c2daf04b5d0b6b812d6c25ad04b59096b012d5c2dab04b556e6a812d4c25a904b51096a006d3c0da701b4d034fe069ec0d3b81a730b4de0e9ac1d3385a630b4be169742d2d82a590b4ae1a9542d2982a510949e1290c251f84a3d094760a8e4251b86a35094660a8c40cbf819770b2de0e59c2caf8595d0b2ae26554249f8493d0926e264d4349786927030fe061ec0c3b81873030de061ac0c3381863030be061740c2d81859030ae061540c2981851030920610c0c208182f030560609c0c118181b0302e075bc0eb681d6b03ad20759c0eb281d6303ac21f1bc1e368fc6b0b8d21f19c1e328fc630b8c20717c0e2d81c57038a606dac0db481b63036c206d6c0da984b4b09686069bc0d3681a6b034d20699c0d3282a63054c20697c0d2d81a57034a61a93c152586a4705486128fc15198f96f1d2da3e59c74b28195f032ae3e53c3ca38292f0524e061bc0c3581869030c6061840c2f8185b030ae0614c0c278184b0308e0610c0c1f818330305e060ac0c1381823030360605c0f3f81e7e05cfa075fc0ebd81d7703ae61b5bc1eb686d6b0bad21b59c1eb286d630bac2071ec0e3984c6b098d21318c263084c5b098a606dfc0dbf01b7b036f406ddc0dbb01b73036e412dbc35b704b6d0d6d812dac25b504b69096d012d9c35b304b656a6c812d8c25b104b61096c012d7c2daf04b5b076b412d5c1dab04b53096a406d3c0da701b4d034f6069e80d3c81a77034ec069cc153881a67034cc06994352f82a5b0d4ae0a94c252782a430947e128f4151d82a390946e1a8d4151982a31032fe065dc34b78696d0d2ce525947caf879570927e124f4249b939350525e0a49c0c3f8187b030ee061cc0c378186d030d6061a40c3381865030c6061840c2f8185b030ae0614c0c248184303082060bc0c1581827030460606c0c0b83e7f03cf6079dc2f3985d7f0dafc075ec0ebd01d7703aec175cc2eb902d6f05adc0b5b40e3d84c73078d61318c262d84c59098a61314425bf86b7e036f606de80dbb81b76096e612dc825b785b6e076d60eda81db383b66096c612d8825af85b5e096ba16d7025ad84b5a096b212d6025ab85b56096aa2ad5025a984b52096a212d400da781b4e0369a1a9fc0d3d81a77054e60a9ac1d3502a69074ce0e998153182a61074ae0e9581d2a84a4f05486128fc251e82a3b05472128dc551a82a33054621a5fc0cbb8596f072ce1657c2cae85957132aa124fc249e849371326a0a4bc14938187f030f6061dc0c398486f090da061ac1c3384865030c61217c242e8185b030b21215c242a81853030a2061240c21818410505e060ac241381823030361205c36bf01d7a03aec1b5c84eb707d6a0facc27588363f01c7a038ec1b1c82e3703c6a078cc17188252f02a5d0949c0a93425260f9561d2a83e51814930f924030a2061041416848250dade075ac0eb386d630d8de1b1b80e3581c6a038ce07198363186c62138be171783e2d83c5a0f8ae0f1584e2985c52054de069ac0d3382a63054be0a96c152b82a530549e0a93474a302926030de061ac0c3381863090be0616c242b818530308606104141782827030461b5bc0eb581d670dac61b1bc363701c6b038d40719c0e3306c630d8c43f17c2e2f07c5b078b41f15c1e2b0fc530b8a406dac25b184b5b096a606d2c0da484b43036821a9bc0d3581a67054c62a97c152d87a57054a61293c252704a4d0947e128f8151984a320d2de0659c7caf879576429ec45347ca3a91450525e324b41493a8125030de061ac0c3381863090be0616c242b818530909e0612c0c248184303082120fc0c198282f0905a060ac241384825030460606c240b81d7f03af6075dc0eb986d6f07ada1b5ac2eb486d6707aca1b58c2eb081b7f036fc06dec0dbd01b77036ec06dcc0db904b6f0d6dc12db435b604b6b096d412da425b404b670d6cc12d945db204b63096c412d8425b004b5f0b6bc12d6c1dad04b57076ac12d4c25a901b4d034fe069ec0d3b81a730d4de1a9b4153582a690d4ce1a994153182a610d4be0a96c352b82a530947e128f4151d82a390946e1a8d4151982a31032ec065980c3f8187d030f6061dc0c3a81873030de061b40c3581869030ce061940c3181861030be0616c0c2b8185303082060bc0c1581827030463f5bc36b701d6b03ad40759c0eb30fd630dac40f1bc0e3581c670b8c60f17c1e2e8fa6f034d60699c15318fa5f1f4ba0a96c152c8fa571f4aa0a94c152885a4f054960e91c15218186f030d60619c0c3181853030a21213c1c23818430505e060ac24138182307cfe079ec0f3b85e730bafe1b5f80ebd81d7a03aee075d82eb985d72096fe1adf80dbd81b7a036ee06dd825b984b72096de16db81db583b6a076ce0ed9825b184b62096be16d7825ae85b5c096b612d6825ac84b58096ae16d5825aaae354096a612d4825a884b500369a3e9fc0d3d81a77054e6169bc153583a67054c61697c2d2e82a5b054b21695c7d2a82a53054a2128fc251e82a3b05472128dc7d1a82a33054620e5981cab0187f030f6061dc0c398486f030d60e19c0c318485f090ba0616c0c2c84857090aa0614c0c28818410505e060ac2413818230dafc075e80ebb06d7213adc1f5a83eb309d620d6fc06de80dbb06b720b6dc0eda81db305b62056bc0ad7415ae02a5a054b20a960752b02a551d4a80a944751b02a35092bc124f8249e029261d248120d4240a86d6f03ad60759c36b186b6f0d6dc06dac0db501b67036cc1ad8c35b109b5f0b6bc1ed6c1dad07b57076ac26d4c2da902a6f034d60699c153182a5f054b60a95c152982a371d46c0a8d40c378186b030ce0618c242f8185b090ae0614c241b848350505e060ac0c1187d6f03ad60759c4eb18ec6f0d8dc071ac0e3501c67038cc4f18c363109c5f0b8bc1f16c1e2d07c57078ac2714c2e2913a6f034d60699c153189a5f054b61e95c1529ac24f5649a0a92c15248ea475248a0a90c15208494e4e24c061bc0c3581867030c61217c0c2d84857030a60a0bc0c1584827030461205436b781d6b03ace1b58c363786c6e038d6071a80e3381c660d8c61b1884e2f85c5e0f8b60f1683e2b83c56138a617148153781a6b034ce0a98c152f82a5b054ae0a94c15278ea4e0549a3a5380c378186b030ce0618c242f8185b090ae0614c0c21818410505e0a09c0c1186d6f03ad60759c36b186c6f038d60719c363189c5f0f8b61f15c4e2982a6f034d60699c153182a5f054b60a95c152982a4f0949c3e53814970186f030d60619c0c318485f030b61215c0c29818430505e0a0b4141384825030461b5bc0eb581d670dac61b1bc0e3581c670d8c62717c3e2d87c57138a60a9bc0d3581a67054c60a97c152d82a57054a60a93c252702a4b054920a91c152182a42054820a90014b78196b032ce0a58c14af8295b052ae0a54c14a78e94e052960a52414a382943052840a5040c378186b030ce0618c242f8185b090ae0614c14178282d030560a09c2412818230503e0606c140b818130dcfe079ec0f3b86e73098fe1b1f80e3d81c7a038ee071d8263984c72098de171b8263583c6a098ce0f198263184c62038ba0adfc35bf01b7b036f406ddc0dbb02b73056e40adbc2db702b6b056d40ad9c1db302b63056c40ad3c25a702b4d096980ad2c15a502b49056900ad1c25a302b45526880ad0c15a102b41056800a9fc0d3d81a77054e60a9bc153582a67054c60a93c152682a4b054940a924152402a470948c0a915412202a43054821251938a20293e0525c061fc0c3d81877030e6121bc0c3584867030c606144141f8283d03076060e4141b8483503066060c414178182b0504e0608c3eb781d6b03aced958c0e3584c63098b61314c25b786b6e036d606da80db381b66096c612d8825af85b5e096b60ed6825ab83b56096a612d480da781b4e0369ad09bc0d3581a67194c6cc97c3d2d87a57194a61293c252184a3f0947a128ec151c84a376046a128cc1518af16f032ceb457c3cab8493f0927a124dd509a8c92f4c24e061bc0c3581867030c61217c0c2d84857030a6061240c21818410905e060ac241381823030361205c0eb781d6b03ace0758c0db781b6b036ce06d8c3daf87b5b0f6ae1ed4c0cb78196b032ce0658c0caf8195b032ae0654c0ca68193f03276064dc0c998186e030cc161781c2b0283e1906c060780eb781d6b03ace071bc0e3581c67038c60717c0e2d81c57038a606d8825a904b4209680129080cb78196b032ce0658c2caf8395b072ae1654c34a78694b0d28e1a50c249e81e7f07cfa079ec0f3d01e7703cec079d40ebf81d7e07afa075bc0eb701d6d038f4071c81e3504c62098b413160262904c50096b412d600d3f81a7b034ee069cc2d3783a6b074ce1698c2d2f85a5d0b4b60a9642d2b86a550b4a60a944252682a41030fe061ec0c3b81873030de061ac0c3381863030be061740c2d8185a030b2061600c2b85856030aa8c1500c29818510309a060c40c178182b0304e0608c3eb781d6b03ace8958c0e3504c62078b413148653781a6b034ce3298c652f87a5b0f4ae3294c252682a41030de061ac0c3381863090be0616c242b818530909a060c424178182b0904e0608c0eb781d6b03ace0758c0e3581c63098b61314c0db781b6e036d606da80db381b66036c606d883daf85b5e0f6b60ed683dab83b560f6a616d4825a784b4e0968612d080d3781a6b034d40699c0d3301a630f4be0a96c3d2d07a570f4ac0a94c252784a4e05486129080d1f81a3e0347a065bc0cb38795f0f2ae224fc449e889371126a0a4bc4496829271124a061bc0c3581867030c60617c0c2d81857030a60613c0c218183f0307a060dc0c1a818330305e060ac0c148182703046060840c0d8181703ade075ac0eb381d63038d60718c262d84c53036de06dac0db381b630f6be1ed6c3dab87b530969e12d0c0d3781a670f4be1e95c451f88a37032de065ac0cb381963032be0656c0cab819530329e065340ca28193f03276064dc0c998192b0324e061bc0c370186b030d40619c0c3301863030c40617c2c2f0185b030b40615c1c2b01853030a40613c24270184d0307e0a0f80c1d8183a0306e800d80c198183203056060a80c1388826 19 524287 7 127 11 2047 19 524287
def cc_60_2 : Nat → List (Nat × Nat) := unpackCursorV4 0x9841896b199492290c3d8917b86928828417c56375c696f9636ce2b68f3f626695c462524a04f92b4bc3d4576543f183ff4039a6535b3f2c3982972c256411f363190631652b122430a08204f510004f 0xd8be1b16c362b86c53054be0a96c152b82a530549e0a92c152382a43090be1216c242b848530909e1212c2423848430505e0a0ac1413828230d8be1b16c362b86c53054be0a96c152b82a530549e0a92c152382a430524c1a17c342d868570d0a62213c442588847110860a0bc141582827050461b5bc36b586d670dac60adbc15b582b67056c60ad7c15ad82b57056a60a8d834b7019660b2bc0e55af0a65d1440527c1a1bc3435868670d0c62217c442d88857110a60a0fc141d828370506606064440a81e7f03cfc079f40ebf81d7b03aee075cc0eb783d6d03ad6075a40eb381d6503ac6175840e3f01c76038dc1b1b00e3301c64098bc0ed680d3f81a7b034ee069cc0d3786a6d034d6069a40d3381a65034c60a9842d2f83a5b074ae1694c152486a45030f6061e80c3c81877030ec061cc0c3881867030cc061940c2f8185b030ae0614c0c24818450305e060ac0c138182303cfe079f80f3e81d7f03af6075dc0eb981d6f07ada075ac0eb481d6703aca0758c2eb081c7f038fc071ec0e3d01c77038ec071cc0e3901c6f038dc171b4363601c6b038d4071a40e3401c67038cc071940e3201c63038c4171842e3001b7b036e606dac0db481b63096c20ed6c25a984b4b0969212d0c25a081a7f034f6069dc0d3981a6f0d4da069ac0d3481a67034ca0698c153085a5f054b60e95c152985a4f0b49a0a92c152485a470d48a0a90c152084a3f05466065fc34be81977032ea065bc34b681967032ca0e5681cab839560728e0e5181ca28292f0524e061ec0c3d01879030ee061d80c3981871030ce061980c328185f030b60615c0c298184f0309a0612c0c24818470308a0610c0c208183f03066060bc0c1581827030460606c0c0b81d6f03adc075b40e3781c6b038ce0718c0e2f81c5b038ae0714c0db786b6d036d606da80db381b66036ca06d6c0dad09b4f0f6961ed1c4da18196f032d60659c0cb18195f032b60655c0ca98694f052961a51c14a18693f052761a4dc149981e7f03cfc079f40ebf81d7b03aee075cc0eb783d6d03ad6075a40eb381d6503ac6175840e3d01c72038d4071a00e3106c60078b4171480d3f81a7b034ee069cc0d3786a6d034d6069a40d3381a65034c60a984352f82a5b0d4ae0a94c352682a410947a1a4980c3d8187a030f2061dc0c3b01873030e20619c0c3301865030be0616c0c2b818530309b641300c20818400305e060ac0c138182303ade075b80eb681c6f038d60719c0e3181c5f078ba0716c0e2c81c57038aa0714c2e2881b6f036d606d9c0db181b5f036b606d640dab81b53096a36cd3c25a587b4709686069bc0d3581a67034c60697c352e81a5b034b20695c0d2a81a53054a21a93c352586a470d486128fc351d86a3709466065bc34b68196b032ce065940cb18195f0d2ba0656c0cab81955032a76853c3ca58794711286124fc449dd8137092661a4bc3495869270d246061ac0c3501869030ce061980c3181861030ae061580c2a8184f030960611c0c218183f03076060dc0c198182f030560609c0c118181f030360605c0c0981d6f03ad60759c0eb181c6f038d60719c0e3184c5f098b61315c262981b6f036dc06dac0db501b67036cc06d8c0db107b5f0b6bc1ed6c1dad07b57076ac1ed4c2da904b4f0969c12d2c25a384b4309684069bc0d3581a6a034ce069980d3186a5f054b61a968352b87a56054a61293c152584a4705486068fc0d1f01a3d032de065ac0cb3819630f2be0a56c3cab829530929e0a52c24a3829431127e224f4149d889371126a0a4cc14978292b0524e0a48c0c378186b030ce0618c0c2f8185b030ae0614c0c278184b0308e0610c0c1f8183d03076060e40c1b8183503066060c40c178182b030520609c0c11818210303e0606c0c0b8181303ade075ac0eb381d63038de071ac0e3381c63098be1316c262b84c53036de06dac0db381b630f6be1ad6c3dab86b530969e12d2c25a384b43034de069ac0d3381a630f4be1e96c3d2b87a530949e1292c252384a430d47e228ec451b86a33032de065b80cb681967032ca0658c0cb10195f032b60655c0ca98194f032960651c0ca18193f03276064dc0c998192f03256064a80c9388926032460619c0c3301865030be161780c2d8185a030ae0e1580c29818520309e121380c258184703086061080c1f8283e03076060e80c1bd603603066060c80c178182b030540609c4413018230303e060780c0e81d6b03ad4071bc0e3581c67038c60717c0e2e81c5b038b20715c0e2a84c53098a2069bc0d3581a67034c63297c652e86a5b054b23295c652a86a53054a21693c1d2583a470b486061bc0c3581863030be061740c278184b0308e0610c0c178182b0304e0608c0f3f81e7e03cfa075fc1ebe81d7b03af2075dc0eba81d730bae2075bc0eb581d6703ac6071faa23e01c76038e8071b80e3304c5e036e412dc01dad01a7f194fa069ec0d3c81a77034ea069cc153881a6f034d60699c0d3185a5f074b60e95c2d2982a491948a061fc0c3f0187d030de061b80c3581869030c6061880c308185f030b60615c0c29818490308a060bc0c158182703046075bc0eb701d6b03ad40759c0eb301d6303ac4071bc0e3581c67038c61f17c1e2e8fc5b0b8b21f15c1e2a8fc530b8a206dbc0db581b67036c632d7c25ad84b59196ae12d4c25a88cb4f096961ed1c25a181a6f034d6069a80d3381a66034c60695c0d2b01a550d49f44938152586a47054861a908251f82a3b0d46e0a8cc0cb78196b032ce0658c5caf8b95d052b62e55c5caa829531729e0a52c3ca3829430927e0a4ec5c9b829330525e0a4ac149382923030de061ac0c3381863030be061740c2d81859030ae061540c29818510309e0612c0c23818430307e060ec0c1b818330305e060b40c15818270304a0608c0c0f8181b0302e0604c0eb781d6b03ace0758c0e3781c6b038ce0718c1e2f83c5d0b8b6171681e2b87c56078aa0714c0db781b6b036d406d9c0db301b63076be0ed740dad81b5a036ae06d580daa81b54036a60ad3c15a702b4d034de069ac0d3381a63194be1296c652b84a530b49e0e92c1d2384a430b47e128ec2d1b84a33032de065ac0cb381963132be0a56c4cab829530b29e0a52c1ca3829430b27e0a4ec2c9b829330925e0a4ac4c9382923030de061ac0c3381863030be0616c0c2b818530309e061340c25818470308a0610c0c1f8183d03076060dc0c1a818330305e060ac0c13818230303e0606c0c0b8181303cfe079f80f3e81d7f07afa075ec0ebc81d7703aea075cc2eb881d6f03ad60759c0eb181c7f038fc171f4563e01c7b038f4071e40e3c01c77038ec071d40e3a01c73038e4171c42e3801c6f038dc071ac0e3501c67038cc0718c0e3102c5f058bc0b1740dbf81b7b036f206ddc0db984b71036de06dac0db381b630b6be0ed6c1dab84b530b69e12d2c25a485b470968612d040d3f81a7e0d4fb449f00d3d81a79034ee069d40d3981a72054e20a9c00d3781a6b034ce0698c152d83a5a054b20e95c1d2b02a53054a20e91c1d2303a450947e0a8ec351b82a33032fe265f40cbd81977032ea065cc0cb78696d032d60659c0cb2819630b2be0a56c1cab829530b29e1653414a5859471328a0a50c249f8293b1326e0a4cc14978292b0524e0a48c0c3f8187e030fa061bc0c370186b030d20618c0c3101861030be061740c2d81857030aa0614c0c278184d03096061240c238184503086061040c1f8183b0306e060cc0c178182b0304e0608c0c0f8181b030340605c4c0b0181303ade075ac0eb381d63036d606da8adaf85b5e0f6b60ed683dab83b562b6a616d480d3781a6b034ce0698c352f82a5b0d4ae0a94c251f84a3d03476068e40d1b81a3503466068c40c378186b030c60617c0c2d81857030a6060fc0c1e8182f030560609c0c1181e7f03cfc079f40ebf83d7d03af6075e40ebb81d7503ae6175c40eb781d6b03ace0758c0e3d01c78038e53d1c00e3501c62078b4171480d3f86a7d034f6069e40d3b81a75034e60a9c40d3781a6b034ce0698c352f82a5b0d4ae0a94c252682a31030fe061f80c3e8186f030dc061ac0c3481863030c4061840c2f8185b030ae0614c0c26818410305e060ac0c138182303ade075b80eb681c6f078da071ac0e3481c67038ca0718c2e3081c5f038b60715c0e2981b6f036d606da40db381b63096c206d7c0dad81b57036a74cd3c25a587b4709686069be913681a6b034d20699c0d3281a63054c20697c0d2d81a57034a74093c352587a470d486128fc351dce23709466065bc5cb68196b032ce065940cb18195f172ba0656c0cab81955032a62e53c3ca58794711286124fc449d8b937092661a4bc44958b9270d246061bc0c370186d030be061780c2d81859030a6061480c288184f030960611c0c218183f03076060dc0c198182f030560609c0c118181f03036060680c0b8b816030260717c0e2d81c57038a60697c0d2d81a57034a60a93c152582a47054860617c0c2d81857030a60613c0c258184703086060bc0c1581827030460717c0e2d81c57038a606d7c0dad81b57036a612d3c25a584b47096860697c0d2d81a57034a61a93c352586a470d486128fc251d84a37094660657c0cad81957032a61e53c3ca5879470f286124fc249d84937092661a4bc3495869270d2460617c0c2e8185b030b40615c0c2b01855030a60613c0c258184703086060fc0c1d8183703066060bc0c1581827030460607c0c0d8181703026075bc0eb581d6703ac6071bc0e3581c67038c61317c262d84c57098a606dbc0db581b67036c61ad7c35ad86b570d6a612d3c25a584b4709686069bc0d3581a67034c61e97c3d2d87a570f4a61293c252584a47094861a8fc351d86a370d466065bc0cb68196b032d40659c0cb301965032be0656c0cab819530329e0652c0ca3819430327e064ec0c9b819330325e064ac0c9381923030de061b80c368185f0b0bc0616c0c2d01857070ac0614c0c290184f0909c0612c0c238184303084060fc141f0183b03074060dc341b0183303064060bc0c16cc02c03056060a80c13888260304b2c0900c118181f0303c060740f3f01d7f03af6075dc0eb985d6907aca071fc0e3f01c7b038f4071dc0e3b01c73038e4171a42e3405c650f8c80717c0e2f01c5d036f4069fc0d3d81a77034e60a9a4353285a5f0b4ba0e96c1d2b86a550b4a61693c2d2685a4b054921691c352285a4305482061fc0c3d81877030e6061a40c328185b030b4061640c2b83856030a6061440c23838460308a060bc0c158182703046079fc0f3f02e7d03afe075ec0ebb81d7307ade0f5b42eb585d6907ace0f5942eb185d61038fe071f80e3d81c7a038ee071d80e3981c720b8de1b1b82e3686c6c0b8d6171a82e3485c680b8ce1b1982e3287c640b8c6171882e3085c60038be071780e2e81b7f036f606ddc0db986b6f096d612da435b384b63096c216d7c1dad83b57096a616d3c25a584b490b68e12d0c25a081a7b034f4069e40d3b81a76034e60a9c40d3381a66034ca1697c2d2e82a5b074ae1a954152985a4f0b49a0a92c152485a470d48a0a90c152084a3f054761a8dc15198197f032f6065dc0cb98696f0d2da0a5ac34b389965052c61657c14ad83957052a61653c2ca68294b0b28e1e51414a18493f05276264dc14998292f052560a49c14918187f030f6061dc0c398186f030da061ac0c3481867030ca0618c0c308185b030b4061640c2b83856030a6061440c23838460308a060fc0c1d8183703066060bc0c1581827030460607c0c0d81817030260f5bc0eb581d670bac6171bc0e3581c670b8c60717c0e2f01c5d0d6de06dac0db386b630b6be16d741dad83b5a076ae0ed583daa83b4b076941a5bc0cb581967052c61657c2cae8295b072ae1e55414a98594f0b29a0a52c2ca38794505286124fc0c9d84937052660f9fc0f3d81e770bce6175fc36bf01d7b03af4075dc0ebb05d730bae4075bc0eb701d6d038f41b1c81e3505c620b8b41f1602e2905c500d4fe069ec0d3b82a730b4de169b4153583a670f4ca0a98c2d2f85a5d054b60a9642d2b87a55054a60a944252682a31030fe061ec0c3b81873030d60e1a80c3483867070cc0618c0c3083857070ac0e1542426c704c030820610014178182b0904e0608c1eb781d6b03ace1758c2e3786c6e038d6071a80e3381c660b8c6171880e2f81c5e038bb24dbc0db581b67096c616d7c1dad83b57096a616d3c25a584b490b68e12d0c25a0c826f034d60699c553185a5f0b4ba0e96c1d2b87a550b4a61693c2d2685a4b054921691c3d2285a4305482128fc551dc623709466265bc0cb581967112c61657c1cad839570b2a61653c2ca68594b0b28e1e5142ca18493f11276264dc24998992f112562649c44918186f030d60619c0c318185b070b4061641c2b83856030a6061441c23838460708a120fc0c1d84837030661e0bc0c1587827030461e07c0c0d8781703026075bc0eb581d6703ac6071bc0e3581c67038c60f17c1e2d83c57078a606dbc0db581b67036c60ed7c1dad83b57076a612d3c25a584b4709686069bc0d3581a67034c60e97c1d2d83a57074a61293c252584a4709486228fc451d88a3711466065bc0cb581967032c60657c1caf0195d032ae065540ca9819520329e0652c0ca3819430327e064ec0c9d019371526c064cc0c978192b0324e0648c0c378186e030d6061a80c3381866030c6061880c2b83856030aa0613c24270184b0308e0610c0c210183f0507c060ec0c1d018371506c060cc0c190182f03056060a80c1388826030460607c0c0f0181d03ade075ac0eb381d63038de071b80e3581c6a038ce071980e3181c62038b6071680d3781a6b034ce0698c1d2f83a5b074ae0e94c352786a4d0d4960a924352386a450d4860a9040c378186b030ce0618c0c2f8185b030a60613c0c268182f030560609c0c1181e7e03afe075f80ebd81d7a03aee075d80eb981d7207ad30d5a01eb283d64038fe071ec0e3b81c73078d20f1940e2f81c5e038ba06de81da904b50034fe069ec0d3b81a73054d21a9941d2f86a5d074b60a9641d2b83a55074a60a9441d2786a4d074960e91c1d2283a43030fe061ec0c3b81873030d2061940c2f8385e030ba0613c1c270184b030920610c0c21018410305e060ac0c15018270d04c0608c0ebf81d7e03af6075e80ebb81d7603ae6075c81eb783d6e07ada0f5b01eb586d6a07ad22f5a01eb383d6607aca0f5901eb186d6207ac21b5800e3f81c7b038ee071cc1e3783c6d078d60f1a41e3383c65078c60f1840e2f81c5e038ba06dec0db984b6b096d212d8c25b083b5b076b20ed4c25a883b4b07686069fc0d3d81a77034e61a9bc353682a6b054d21a99c353282a63054c20e97c352e82a5b054b20e95c1d2a82a53054a20e93c352682a4b0748e0e914152184a3f05466065e80cbb81976032ce065980cb28395f072bc2257600ae03957072aa0e5481ca7839470525e0a49c0c3f8187d030f6061dc0c3a81873030de061b40c3581869030ce061940c3181861030be0e1780c2e8184f0709c0612c0c248184303084061040c1f818330305e060ac0c15018270d04c0608c0c0d81817038de071ac0e3381c63078be0f1741e2d83c57078aa0714c0db786b6d036d606da80db381b66036ca06d8c1daf83b5d036b606d680dab81b56036aa06d500da981b4b0368e06d0c0d3581a63094b61294c1d2583a4309476128cc0cb78196b032ce0658c34af8295b0d2ae0a54c1ca78294b0728e0a50c349f8293b0d26e0a4cc249782923030de061b40c3581867030ca0618c0c2f8185d030b60615c0c2a818530309e0612c0c23818430307e060dc0c198182f030460607c0c0d81817030260f5bc0eb581d6707ac64f1bc363701c6b038d40719c0e330ec630d8c40716c0e2d03c57038ac0f14c0db584b63076b60ed4c25a584b490968612d04553781a6b034ce0a98c1d2f82a5b074ae0a94c55278aa4d054960a92455238aa45054860a904251f82a33112df005b80cb388962072be0e5681cab839560728e0e5181ca28292f0524e061bc0c3581867030c60e17c0c2d83857030a61613c2c26878470b08a0610c241f818330505e060ac3c13818230f03a0606c3c0b87815 20 1048575 8 255 11 2047 19 524287
def cc_60_3 : Nat → List (Nat × Nat) := unpackCursorV4 0xeceb383e0d753720f9be936d34ea95727ecd95f3a33c888e82024374589ad48674817e3e57cf94c264a91119a142484f3ab34d04ba322a4889d1824460802216538354809480004a 0x75ac0eb503c6f038d61718c1e2f83c5d0d4de069ac0d3382a630d4be1a974152d82a590d4ae1a954152982a510b49e0a92c1d2382a430728c061bc0c3581867030c61217c242e8185b030b21215c242a81853030a21213c0c2583847030860a0bc0c1584827030460f9fc0f3d81e770bce6175fc36bf01d7b03af4075dc0ebb05d730bae4071e825b785b6e096da16db01db583b6a076ce0ed9825b283b64096c612d8825af85b5e096ba16d7025ad84b5a096b212d6025ab85b56096abf8d5025a984b52096a212d400da686a7f034f6069dc153985a6f054d60e99c153185a5f0b4ba0a96c152c85a570d4aa0a94c152884a3f0947a0a8ec151c84a370d46a0a8cc151883966072ac061fc0c3d81877030e6121bc0c3583867030c61217c242e8185b030b21215c242a81853030a2120fc241e8183b03072120dc241a81833030620a0bc0c158482703046075bc0eb682d6b05ad20759c0eb282d6305ac20f1bc1e3682c67058ca0b18c1e2f81c5b038ae1714c7db584b691f6c612d840dad86b530769616d0c153781a6d054d60a9a40d3381a65054c60a984152f81a5b034ae0a94c152782a4b0548e0a90c151f82a33052de0a5b414b382965052be0655c14a7829470525e0a49c7c378d86d030d6061a47c338d865030c6061840c2f8185b030ae0614c2c278184b0708e0610c7c1f818330505e060ac141381823030360a05c173f82e7e05cfa0f5fc0ebd81d770bae60f5bc1eb685d6b0bad20f59c1eb285d630bac2171fc363f01c7b038f4071dc0e3b05c730b8e4171bc363705c6d0d8d8171ac2e3505c690b8d01719c363305c65f88c81718c2e3105c610b8c006dec35b986b6b096d21ad8c25b083b5b0b6a616d2c25a485b4309682069ec0d3d02a79034ee069d8153982a71034ce069980d3282a5f054b60a95c152982a4f0549a0a92c152482a470548a0a90c152082a3f054660a5fc0cbb8296f052da0a59c14b28295a052ae0e55814a3839460528a0a4bc14938187f030f6061dc0c398686f0d0da061ac0c3486867330ca0618c0c308585f030b60e15c0c298584f0b09a0612c0c24858473108a0610c0c208f83f030660a0bc0c1582827030460606c140b86d6f0dadc075ac0eb501d6703acc1b58c36b103c6f038d60719c2e3182c5f058ba1716c2e2c82c57058aa0b14c162881b6b096c612d6c25ac84b53096a20ed2c25a182a6f034d60699c153182a5f054ba0696c0d2c82a57054aa0a94c0d2882a4f054960a91c152182a3f054660a5bc0cb38295f052ba0a55c14aa8294f0528e0a4bc14938186f030d60619c0c31878571b0ac1e15414278184b0708e0610c241f818330505e060ac1415028270504c0608c0c0d828170dade1b5b85eb581d6a17ace0759836b186d62078de171ac1e3385c63058be0b174162b82c55058a62edac35b18fb5b096b23ed4c25a883b4b0b6860a9bc153582a67054c60a97c2d2f02a5d0549e16938152582a47054860a908151f82a33052de0a59c14af8295d052ae0a55414a7829470525e0a4b41493829250d0de1e1ac5c33868632d0bfe81743c2d818591f0ae601543c29818510b09e0e12c1c23858431f07e1e0cc14178282d050560a09cb81282823050360a05c1f3f85e7b07cee179cc2ebf86d7e0baf6075e82ebb81d760bae6175c825bf86b7e096f606de825bb81b76096e612dc825b785b6e076d60eda81db383b66096c612d8825af85b5e096ba16d7025ad84b5a096b212d6025ab85b56096aa32d5025a984b52096a212d4015a682a7f054f60a9dc153982a6f054d60a99c153182a5f054ba0a96c152c82a57054aa0a94c152882a41072cc0e558243f8487b090ee121cc24378386b070ce1218c242f8485d090b606164242b84855090a606144241f8483d09076060e4241b8483509066060c414178282b0504e0a08c1eb781d6b03ace1758c363786c6e038d6071a80e3381c660d8c61b188162f82c5e038b607168162b81c56058a60b1480db584b63076b612d4c25a584b490968612d04153781a6b034ce0a98c152f82a5b054ae0a94c15238da460548a0a8fc15198296f032ce0a57c14ab8294f0529a0a51c14a28292f0524e061bc0c3581867030c61617c0c2d82857030a61613c2c268184b030920a11c14228184303082120fc0c198282f0505a060ac141387825030460606c140b83d6f03ad60759c2eb18dc6f0d8dc071ac0e3501c67038cc4b18c363101c5b038b40f15c0e2b05c53036d612d8c1dad84b530969612d2425a184b41314de069ac0d3382a630b4be0a96c1d2b82a532549fdc934152582a491b48e60914152182a410947e0a8cc44b7819670b2be0e55c3ca78394d0728e0e514149782927030de061ac0c33818630b0be161780c2d83857030a6161482c278584e0b09a120fc0c198282f030561e0a83c1396026030460606c3c0d078171102c0f5bc2eb583d670bac6171bc363705c6b038d41719c0e3305c630b8c42edafe9b183b5b0b6a616d2c25a485b4309683ec9bc15358ba67054c61697c152d83a57054a61693c2d2682a4b054921691fc92282a4305483e08fc15198996f132ce0e5681cab839560728e0e5181ca28292f0524f681bc3c358b8670f0c61617c1c2d838570b0a61613c2c268584b030921611fb0228584303082b40fc3c198282f0f0565409c14118781b1102e0f5bc1eb583d6707ac60adbc15b582b67056c60ad7c15ad82b57056a60e97834b701966072ac0a4f8149b0786f0f0d61e19c3c318385f070b60e15c1c298283f050760a0dc1419818190f02a0f5bc1eb701d6b03ace0f58c36b103c6f038d60719c1e3183a5f074bc0e96c1d2c83a57074a60e948252884a500749e0e9381d2583a490748e0e90c1d2109a410d2de065ac0cb382963072be1a57414ad83957072aa0a54c1ca78294b0728e0a50c34978292b0d24e0a48c0c378186b030ce0618c1c2f8485d030b60e15c1c2a818530709e0612c1c23818430905e060ac2413818230503e0606c240b8181307cfe0f9f80f3d81e7a03cee079d81f3986e7207afe075ec0ebb83d73038f40edbc1db704b6d136d80edac1db503b69076d00ed9c1db303b65076c80ed8c1db104b61096c00ed7c1daf04b5d0b6b80ed6c1dad03b57076ac0ed541daa03b53076a406d34353f81a7b034ee0a9cc1d3786a6d054d60a9a41d3383a65054c60a9841d2f82a5b074ae0a94c251f84a3d054760a8e4251b86a35054660a8c41cb70395e0926dcc4d00c3f8187b030ee061cc1c378486d030d6061a41c3383865030c6061841c2f8185b070ae0614c241f8483d03076060e4241b8483503066060c414178182b0904e0608c1eb783d6e07ad6075a81eb381d6607ac61b5881e3783c6b078ce0f18c5db5f2363076b60ed641da984b51076960ed0c553782a6b154ce0a98c1d2f89a5d054b60a9641d2b83a55054a60a9441d2782a4b0748e0a90c551f82a33132de2659c1caf8395e0b2ba0e53c1ca7039420525e0a49c3c378786b0f0ce1e18c1c2f8785d070b6061641c2b83855070a6061441c278384b0708e0e10c3c1f878330505e1e0ac3c13828230f0361e05c1eb785d6b07ace1758c15b782b6b056ce0ad8c15af82b5b056ae0ad4c1d2b0696e032cc16578149f02936110de1e1ac4433878630b0be0e16c1c2b858530507e0a0ec141b8283303032220541f3f85e7e07cfa075ec0ebd03d7903aee075d81eb983d7103ace075980eb281b7a096e40eda825b403b62076c00ed681da906a7f034f6069dc153983a6f074da0a9ac153483a670d4ca0a98c153083a5f054b60e95c152984a4d0947a0a8c40c3f8187b030ee061cc1c378386d030d6061a41c3384865030c6061841c2f8185b070ae0614c241e818310505e060ac24138182305cfe0b9f8173e86d7f03af6075dc36b986d6f07ada1b5ac2eb486d6707aca1b58c2eb081b7a096e412da825b404b62096c00ed6825a901a7b034f40a9e40d3b81a76054e60a9c40d3381a66034ca0a97c152d82a57054a60a934151e82a31030fe061ec0c3b81873090de121b40c3581869090ce121940c3181861090be0616c242b818530907a060c414178182b0504e0608c36b78bd6b17ace1b58c1e3783c6b078ce0f18c162f84b5a074b40e92814b78296b052ce0a58c14af8294f052960a50c149e8292d090de121ac243384863090be1216c242b848530709e0e12c1c23838430503e0a06c140b8281307cfe0f9f81f3d81e7a07cee079d81f3986e7207afe0f5ec1ebb83d7305ade0b5b816b681b7a096e40eda81db403b62096c00ed681da902a7f054f60a9dc153982a6f074dc0a9b4152f83a5e054b60a964152982a52054a20a934151e82a31072ddb45b0243f8487b090ee121cc1c378486d070d6061a41c3383865070c6061841c2f8485d070b60e15c1c2a838530907a060c414178282d050560a09c241282823deade275ac5eb389d63036d412d881dad04b52dc4de0a9ac5d3382a63134be0a96f612b82a530949a128f415188486f090d61219c24318485f090b61215c24298483d030620a0bc24158482705046275bc4eb589d6713ac60adbc15b582b67056c60ad7c15ad82b57056a60a8d834b7019660b2bc0e558149f02936110de121ac443384863110be1216c442b848530507e0a0ec141b8283303032220540eb581d6707ac616d8c2db101b5b036b41a9bc0d3581a67054c60e97c152d83a57054a61a8fc351e82a3b054721a8dc351a82a3305462061bc0c3581867030c60e17c0c2d83857030a61e0fc3c1e8183b030721e0dc3c1a81833030620a0bc0c1586827030460f9fc2f3f03e7d03af6075e81ebc81d7703aec0f5cc1eb881d6703acc075940e3d06c72078d5a51a01e3103c60078b40f1601e2905c500d4fe069ec0d3b82a73074de0e9b4153582a69074ce1a994153182a61074be0a96c1d2b82a530d49a0a904351e86926030fe061ec0c3b81873070de0e1b40c3581869070ce1e1940c3181861070be0616c1c2b818530f09a0610414178182b0d04e0608c3eb781d6b03ace2758cbe3786c6e038d6071a80e3381c661b8c61b1884e2f85c5e0f8b60f1683e2b83c56138a617148653781a6b034ce0a98c4d2f82a5b0f4ae0a94c65278ca4d054960a92465238ca45054860a9040c37d906e030d60619c0c3184862090be0616c242b818530505e060ac241381823d0ade275ac5eb389d63038d41b1881e2d05c52194de0a9ac5d3382a63134be0a96c652b82a531949a0a904651e8c926b00de121ac5c3384863130be1216de82b84853ce09a0610414178482b1904e0a08c362f86c5b0d8ae1b14c152f82a5b054ae0a94c152782a4b0548e0a90c242f8485b090ae1214c24278484b0908e1210c14178282b0504e0a08c4e2f89c5b138ae2714c152f82a5b054ae0a94c152782a4b0548e0a90c242f8485b090ae1214c24278484b0908e1210c14178282b0504e0a08c4eb789d6b13ace2758c15b782b6b056ce0ad8c15af82b5b056ae0ad4c34b7019660b2bc0e558149f6513c0526d904d024378486b090ce1218c242f8485b090ae1214c141f8283b0506e0a0cc0c0c848150dade075ac0eb386d63038d61318c262d84c53056de06dac0db382b63056be0ad6c15ab82b530569e0ad0c353786a6e034d6069a80d3381a660d4c61a9884d2f85a5e0f4b60e9683d2b83a56134a616948252784a4e09486129080d1d81a3a0546e068d815198296f032ce0a57c14ab8293f0526e0a4bc1496829270524a061bc0c3581867030c61e17c0c2d8885a0f0ae2a1580c298484f030860a0fc141f0183b0506e060cc14190282f0505c0a0b40c0d8281a0502e0a05836b786d6b0dace1b58c363586c63158b62714c15b782b6b056ce0ad8c15af82b5b056ae0ad4c15a782b43054de1a9b8153581a6a054ce06998153182a62054be16978152d82a5a054ae0e958152982a520549e12938152182a42052de0a59c14af82957052740a4dc149b029270524c0a49434378686b0d0ce1a18c4c2f8885b150ae2214c6427888430507e0a0ec141b828330505e0a0b41415818290504f88094141181821050360a05c36b789d6b13ace1b58c15b782b6b056ce0ad8c15af82b5b056ae0ad4c151f0696e032cc165781cab029360d0de221ac443386863110be2216c442b888530507e0a0ec141b82833030322205436b789d6b15ace1b58c5e3586c63158b62714c15b786b6e056d606da815b381b66056c60ad8815af85b5e056b60ad6815ab83b56056a60ad4815a784b4e056860ad08153782a6b054ce0a98c152f82a5b054ae0a94c152782a43052de0a59c14af829570529432518149f8293e0527a0a4bc1497029220d0de221ac5c3386863130be2216c542b888534c09e2210c141f8283d05076060e4141b8503505066060c414178282b0504e0a08c140d82817 18 262143 7 127 11 2047 19 524287
def cc_60_4 : Nat → List (Nat × Nat) := unpackCursorV4 0x818817c94f764657283c6ad7b66d406086558d7b5434a50f344ef204c42b4853f4513443120419183e73239b4c33d5e2f34a2d2212a72b244631f64e1a94d128811022609f630534c03b180221900022 0x1e7f01e7e01e7b01e7a01e7901e7801e7701e7601e7301e7203e7106e7001d7f01d7b01d7701d7302d6f02d6e02d6d01c7e01c7301c7203c6b03c6903c6304c6103c5b03c5301b6f03b6e01b6d9f36c01b6b01b6a01b6901b6801b6703b6601b6503b6401b6301b6201b6101b6001b5f03b5e01b5b01b5a01b5703b5601b5301b5201b4f04b4e01b4d01a7f01a7b01a7701a7303a6f03a6e05a6d03a5f03a5e02a5b02a5902a5303a5202a5104a4f02a4301a3f01a3d01a3b02a3901a3706a3501a3301a310197f019770396f0b96d03967039650395f039570193f0193d019370b9350292f029270187f0187b01877018730186f0186d0186b01869018670186501863018610185f0185d0185b0185701855018530184f018430183f0183d0183b01839018370183501833018310182f0182d0182b0182701825018230181b0181706d6f06d6e0bd6b01d6a0bd6701d6606d6306d6203c6f03c6b03c6703c6302c5f02c5d02c5702c5502c530bb6b06b6314b5b04b590eb5304b5103b4b03b4302a6f02a6b02a6702a6302a5f02a5d02a5702a5502a5302a4f02a4b02a4702a4302a3f02a330296f029670295703956029550294f0294a02947039466d13e029320292f0292a02927029260686f0786b07867068630785f0785d0785b01859078570785507853018510384f0384b03847038430783f078330282f0282b02827028230281b0281703d6f03d6e03d6b01d6a03d6701d6603d6306d6203c6f03c6b03c6703c6302c5f02c5e02c5d06b6f9e36b0cb6706b6303b5f03b5b03b5903b5703b5304b5103b4f03b4b03b4703b4306a6f02a6b06a6702a6303a5f03a5e05a5d03a4f03a4e02a4b02a4902a4303a4202a410aa3f02a3b0aa3702a330696f0296b85167029630395f9d15d0295b0395703955029530394f0294b03947029436c13f0293b0c937029330292f0292b02927029230686f0786b07867068630385f0785d0385b01859038570385503853018510384f0784d0384b0384703845038430783f0783b07837078330282f0782d0782b0782707825028230281f0781b078170281301c5f01c5b01c5701c5301b5f01b5b01b5701b5304b4f03b4b03b4704b4301a5f01a5b01a5701a5302a4f02a4b02a4702a4302a3f02a3b02a3702a330195f0195b01957019530294f0294b02947029430293f0293b02937029330292f0292b02927029230185f0185b01857018530184f0184b01847018430183f0183b01837018330182f0182b01827018230181f0181b018170181303d6f01d6b01d6705d6306c6f01c6b01c6704c6305c5f03c5b03c5704c5302b6f01b6b01b6702b6302b5f02b5d02b5b02b5a02b5703b5602b5502b5302b4f02b4b02b4702b4306a6f06a6e01a6b01a6a01a6701a6606a6306a6205a5f05a5e01a5b01a5a03a5701a5605a5305a5204a4f04a4e0ca4b0ca4704a4304a4202a3f02a3e01a3b01a3a02a3701a3602a3302a320296f0196b01967029630295f0295b02957029530294f0294b02947029430293f0293b02937029330292f0292d0292b0292702925029230186f0686e0186b0686a018670686601863068620585f0585e0185b0385a038570385601853058520484f0c84e0184b0784a048470c84601843078420283f0283e0183b0283a028370283601833028320282f0282e0282d0281f0281e0181b0281a0281702816018130281203c5f05c5b03c5705c5306b5f06b5b06b5706b5305b4f03b4b03b4705b4302a5f02a5b02a5702a5302a4f02a4d02a4b02a4a02a4703a4602a4502a4302a3f02a3b02a3702a330695f0695b06957069530594f0394b03947059430c93f0c93b0c9370c9330292f0292b02927029230285f0285b02857028530284f0284b02847028430283f0283b02837028330282f0282b02827028230281f0281b028170281303d6f05d6b03d6705d6306c6f06c6b06c6706c6305c5f03c5b03c5705c5302b6f02b6b02b6702b6302b5f02b5d02b5b02b5a02b5703b5602b5502b4f02b4b02b4702b4302a6f06a6e02a6b01a6a02a6701a6602a6302a6202a5f05a5e02a5d02a4f04a4e02a4b02a4702a4302a4202a3f02a3e02a3d0296f0296b02967029630295f0295b02957029530294f0294b02947029430293f0293b02937029330292f0292d0292b0292702925029230686f0686b06867068630585f0385b03857058530c84f0784b0c847078430283f0283b02837028330282f0282d0282b0282a018299b02802827028269a0259902402823018210281f0281b028170281301e7f01e7e03e7d01e7701e7501e7301e7201d7701d7601d7501d6f05d6e01d6d01c7b01c7303c6b04c6301c5b04c5901c5301c5101b7f01b7e01b7b01b7a01b7701b7601b7301b7204b6f05b6e03b6b03b6a03b6703b6604b6304b6201b5f01b5e01b5d01b5c01b5b01b5a04b5904b5801b5701b5604b550cb5401b5301b5201b5101b5002b4f02b4e02b4d01a7f01a7b01a7701a7305a6f02a6b03a6702a6301a5f01a5d01a5b02a5901a5706a5501a5301a5102a4902a4302a410197f019770596f039670195f0195d01957099550494d099450493f0493d04937099350292f029270187f0187b01877018730186f0186b01867018630185f0185d0185b01859018570185501853018510184f018430183f0183d0183b01839018370183501833018310182f0182b01827018230181b0181706d6f9756b0ad6706d6304c6b04c6304c5b04c5304b6f06b6e04b6b01b6a04b6701b6604b6304b6204b5f05b5e04b5b03b5a04b5703b5604b5304b5202b4f02b4e02b4d06a6f02a6b06a6702a630aa5f02a5b0aa5702a5302a4902a4302a410696f831677815f0a9570494d0c9450493f0493d049370c9350292f029270486f0486b04867048630485f0485b04857048530484f048430483f0483d0483b01839048370483504833018310282f0482b04827028230481b0481706d6f01d6b01d6706d6302b6f01b6b01b6702b6302b5f02b5b02b5702b5306a6f06a6e01a6b01a6a01a6701a6606a6306a620aa5f05a5e07a5b03a5a07a5703a560aa5305a5202a3f02a3e01a3b01a3a02a3701a3602a3302a320186f0186b01867018630485f0185b0485a048570a856018530283f0283e0183b02837018330283206d6f06d6b06d6706d6302b6f02b6b02b6702b6302b5f02b5b02b5702b5302b4d06a6e01a6605a5e03a5602a3e0686f0486b06867048630a85f0485b0a857048530283f0283b0283702833018299502501d6f01d6701d6301b6b01b6a05b5305b5201a6f01a6b01a6701a6305a5f02a5b03a5702a5304a3f04a3d01a3b01a3901a3701a3501a3301a310186f0186b01867018630185f0185b01857018530183f0183d0183b01839018370183501833018310182f0182b018270182301e7f01e7e03e7d01e7701e7501e7301e7201d7701d7601d7501d6f05d6e01d6d01c7a01c7801c7206c7003c6a05c6201c5a9345801c5201c5001a7f01a7b01a7701a7305a6f02a6b03a6702a6301a5f01a5d01a5b02a5901a5706a5501a5301a5104a4d02a310187f0187b01877018730186f0186b01867018630185f0185d0185b01859018570185501853018510184d018410182f0182b018270182306d6f01d6b01d6706d6306c6f06c6e01c6b01c6a01c6701c6606c6306c6217c5f05c5e07c5b03c5a07c5703c560dc5305c5206a6f01a6b01a6702a630aa5f02a5b07a5702a5304a4f04a4d01a4b01a4904a4704a4502a4301a410186f0186b01867018630485f4705e0185b0485701853048520282f0182b0482a048270c8260182306d6f9256b0ad6706d6301c6a06c6203c5a05c5206a6f02a6b06a6702a630aa5f02a5b0aa5702a5304a4d02a310686f0486b4e067048634605f0485b0a857048539104d018410282f0482b0c8270282306c5f06c5b06c5706c5302a5f02a5b02a5702a5302a4f02a4b02a4702a430485f0485b04857048530484f0484b04847048430282f0282b028270282306c5f06c5b06c5706c5304b5b04b5304b4b04b4302a5f02a5b02a5702a5302a4f02a4b02a4702a4302a3f02a3d02a3502a330295f0295b02957029530294f0294b02947029430293f0293302927029230485f0485b04857048530484f0484b04847048430483f048330282f0282b02827028230281f0281b028170281306d6f06d6b06d6706d6304c6b04c6304c5b04c5302b6f02b6b02b6702b6302b5f02b5b02b5702b5302b4f02b4d02b4502a6f06a6e02a6b01a6a02a6701a6602a6302a6202a5f05a5e02a5b02a5a02a5703a5602a5302a5202a4f04a4e02a4d0296f029670295f029570293f029370292f0292d0292a8f1280292702926029258e1240486f0486b04867048630485f0485b04857048530484f048430283f0283b02837028330282f0282d0282b01829028270482502823018210281b0281703d7f01d7b01d7703d7303d6f03d6d03d6b03d6903d6703d6503d6303d6103c5203b7f06b7e01b7b01b7a01b7701b7603b7303b7203b6f06b6e03b6d06b6c03b6b03b6a03b6903b6803b6706b6603b650bb6403b6303b6203b6103b6003b4d06a7f01a7b01a7702a7306a6f06a6d02a6b02a6906a6706a6502a6302a6103a5f02a5b03a5702a5303a3f03a3d02a3b02a3903a3706a3502a3302a3101976019660187f0487d0187b0187704875018730486f0486d0186b01869048670486501863018610385f0185b03857018530383f0383d0183b01839038370483501833018310282f0182b048270182306c6f01c6b01c6706c6306c5f03c5d06c5b05c5906c5703c5506c5305c5101b6b06b6306b5b04b5906b5304b518c34b09b4306a6f01a6b01a6702a6306a5f06a5d02a5b02a5906a5706a5502a5302a5106a4f02a4b06a4702a4306a3f02a330196a01967019660195701956019550994f099470292f029270186f0686d0186b018670b865018630685f0685d0185b01859068570b85501853018510984f0184b41047018432f03f018330282f0182b06827018230181b0881701d6f01d6b01d6701d6301b6f01b6b01b6701b6302b5f02b5b02b5702b5301a6e019660595e039560293e029360186f0186b01867018630185f0185b01857018530183f0183b018370183301825018190181501d6f01d6e01c6f01c6b01c6701c5b01c5901a6f01a6b01a6701a630aa5f0aa5d02a5b02a590aa570aa5502a5302a5103a4f02a4b03a4702a430186f0186b01867018630185f0185d0185b01859018570185501853018510184f0184b01847018430182f0182b018270182301d7f01d7e03d7d03d7c01d7b01d7901d7701d7501d7301d7203d7105d7001d6f01d6b01d6701d6303c5201b7f01b7e03b7d8937c01b7b01b7a01b7901b7801b7701b7601b7501b7401b7301b7203b7103b7001b6f01b6e01b6b01b6a01b6701b6601b6301b6203b4d01a7f0aa7d01a7b01a7901a7701a7501a7302a7101a6f01a6b01a6701a6303a5f02a5b03a5702a5303a3f03a3d02a3b02a3903a370aa3502a3302a310197e0196e0187f0187d0187b01879018770187501873018710186f0186d0186b0186701865018630185f0185b01857018530183f0183d0183b01839018370183501833018310182f0182b01827018230181501d6f01d6e01d6701d6301d6201c6f01c6b01c6701c630ac5f03c5d09c5b05c590ac5703c5509c5305c5101b6b01b630fb5b04b590fb5304b510ab4b09b4301a6f01a6b01a6a01a6701a6601a6301a5701a5601a5502a4f02a4b02a4702a4302a3f8423e02a3302a320196f019670295f0295d02957029550294f029470292f0292d02927029250186f0186b01867018630185f0185d0185b01859018570185501853018510184f0184b01847018430183f018330182f0182b01827018230181b0181701d6f01d6b01d6701d6301c6f01c6e01c6701c6301c6201c5f01c5e02c5b02c5a01c5701c5601c5301c5201b6b01b6303b5b03b5316b4b04b4916b4304b4101a6f01a6b01a6701a6302a5f02a5b01a5702a5302a4f02a4d01a4b01a4901a4701a4501a4301a4102a3f02a330196f019670295f029570294f0294d02947029450292f029270186f0186b01867018630185f0185b01857018530184f0184d0184b01849018470184501843018410183f018330182f0182b01827018230181b0181701d7f01d7e03d7d03d7c01d7b01d7a01d7901d7801d7701d7601d7501d7401d7301d7203d718657001d6f01d6e01d6b01d6a01d6701d6601d6301d6201c7f03c7d01c7b01c7901c7701c7501c7303c7101c6f01c6b01c6701c6302c5f02c5e02c5d01b7b01b7901b7304b7101b6b01b6303b5b03b5903b5304b5103b4b03b4301a7f02a7d01a7b01a7901a7701a7501a7302a7101a6f01a6b01a6701a6302a5f03a5e02a5d02a4f03a4e02a4b02a4902a4302a4202a4102a3f02a330197f0197e0297d0196f0196e019620295f0295d02957029550294f029470292f029270187f0187d0187b01879018770187501873018710186f0186d0186b0186701865018630185f0185d0185b01859018570185501853018510184f0184d0184b0184701845018430183f018330182f0182d0182b0182701825018230181d0181b018170181501d6f01c6f01c6b01c6701c630ac5f09c5b0ac5709c5304b5a01a6f01a6b01a6a01a6701a6601a5b01a5a04a4f04a4b04a4704a4302a3d0186f0186b01867018630185f0185b01857018530184f0184b01847018430182f0182b018270182301d7f03d7d01d7b01d7901d7701d7501d7305d7101d6f01d6b01d6701d6301b7f01b7e04b7d0cb7c01b7b01b7a01b7901b7801b7701b7601b7501b7401b7301b7204b7104b7001b6f01b6e01b6b01b6a01b6701b6601b6301b6204b5f05b5e04b5b03b5a04b5703b5604b5304b5202b4d01a7f01a7e02a7d8427c01a7b01a7901a7701a7501a7301a7202a7102a7001a6f01a6b01a6701a6302a5f02a5b02a5702a5302a410197e0196e0187f0187d0187b01879018770187501873018710186f0186d0186b0186701865018630185f0185b01857018530183f0183d0183b01839018370183501833018310182f0182b01827018230181501c6f03c6d01c6b01c6901c6701c6501c6305c6101c5f01c5b01c5701c5301b6b01b6901b6304b6101b5b01b538834b09b4301a6f8726d01a6b01a6901a6701a6501a6302a6101a5f01a5b01a5701a5309a4f02a4b8524702a438323f02a330196f0196e0696d0195f0195e019520994f099470292f029270186f0186d0186b01869018670186501863018610185f0185d0185b0185701855018530184f0184b01847018430183f018330182f0182b01827018230181d0181b018170181501c5f01c5b01c5701c5301a5f01a5b01a5701a5302a4f02a4b02a4702a430185f0185b01857018530184f0184b01847018430182f0182b018270182306c5f01c5b01c5706c5302a5f01a5b01a5702a5302a4f02a4b02a4702a43019560685f0185b01857068530884f0884b08847088430282f0282b028270282306d6f01d6b01d6706d6302b6f01b6b01b6702b6302b5f02b5b02b5702b5301a660696e0595e039560293e029360186f0186b01867018630885f0185b08857018530283f0183b028370183301819810180881580014 20 1048575 8 255 11 2047 20 1048575
def cc_60_5 : Nat → List (Nat × Nat) := unpackCursorV4 0x9726194032920208d24e88a4886a20835357ed487b934799207663371e486fe206ac52664486154f5987d551475024f4b44e44b693ea613896133e4b2bd8125c611ef6d18e611137b0b06304d630004d 0x3d6f03d6d01d6b01d6a01d6701d6603d6503c6f03c6e03c6d01c5f01c5e01c5d06b6f01b6b01b6706b6305b5f03b5b03b5705b5305b4f05b4b04b4905b4705b4304b4106a6f01a6b01a6706a6305a5f03a5b03a5705a5305a4f05a4d05a4b02a4905a4706a4505a4302a4106a3f06a3b06a3706a330696f0196b01967069630595f0395b03957059530594f0594d0594b0594709945059430993f0993b09937099330692f0692b06927069230186f0186b01867018630585f0185b03857018530584f0584d0184b0184905847bf04501843018413603f0183b22037018330682f0182b06827018230981f0181b098170181301d6f01d6e01d6b01d6a01d6701d6601d6301d6201c6f01c6b01c6701c6307c5f03c5d0dc5b05c5907c5703c5515c5305c5101a6f01a6b01a6701a6306a5f06a5d06a5b02a5906a5706a5506a5302a5106a4f06a4b06a4706a430186f0186e0186b0186701863018620184f0184b01847018430182f0182b018270182304d6e06c6f01c6b01c6706c6305c5903c5501b6a06a6f01a6b01a6706a6302a5906a5506a4f06a4b06a4706a430186f0186b018670186301859bd0554904f0184b42047018430682f0182b068270182301d6f01d6b01d6701d6301c6b01c6304c5b04c5301b6f01b6e01b6b01b6301b620fb5f05b5e0ab5b03b5a0ab5703b560fb5305b5204b4f04b4e04b4304b4201a6f01a6b01a6a01a6701a6601a6306a5f02a5b06a5702a5304a4f04a4e02a4304a4201a3f01a3e01a3d0196f019670b95f0a9570b93f0b93d0b9370b9350292f0692d029270b9250186f0186b01867018630185f0185b01857018530184f018430183f0183d0183b01839018370183501833018310182f0182b01827018230181b0181701d6f01d6b01d6701d6301c6e01c6301c6204c5b04c5301b5f05b5e01b5b01b5a01b5703b5601b5301b5201b4f04b4e01b4d01a6f01a6b01a6701a63a225f06a5b9e25706a5304a4f04a4301a3f01a3d01a3b02a3901a37bb23501a3301a310196f019670b95f0b9570193f0193d019370b9350692f0b9270186f0186b01867018630185f0185b01857018530184f018430183f0183d0183b01839018370183501833018310182f0182b01827018230181b0181701d6d03c6d05c6101c5f01c5b01c5701c5301b520ca6d02a6101a5f01a5b01a5701a530ca4f06a4b0ca4706a430186d018610185f0185b01857018530184f0184b01847018430182f0182b018270182306d6f01d6b01d6706d6309b5f05b5e1ab5b03b5a0eb5703b5609b5305b5206a6f01a6b01a6702a6306a5f02a5b06a5702a5306a3f06a3d02a3b02a3906a3706a3502a3302a310696e731560493e069260186f0186b01867018630485f0185b04857018530483f0483d0183b01839048370483501833018310282f0182b04827018230481506d6f01d6b01d6706d6301c6b01c6a01c6604c5b04c5304b5f05b5e04b5b03b5a04b5703b5604b5304b5201b4f01b4e01b4d06a6f01a6b01a6706a6306a5f06a5b06a5706a5304a4f04a4304a3f04a3d04a3b02a3904a3706a3504a3302a310696f019677d15f721570493f0493d04937b81350692f069270186f0186b01867018630485f0185b04857018530484f018430483f0483d0183b01839048370483501833018310482f0182b04827018230181b0481703d6f01d6b01d6705d630dc6f06c6e01c6b01c6a01c6701c6612c6306c6204c5f04c5e01c5b01c5a03c5701c5604c5304c520ca6f01a6b01a670aa6305a5f03a5b03a5705a530ca4f0ca4d0aa4b02a490ca470ca450aa4302a410186f0186b01867018630485f0585e0185b0385701853048520482f0182b0482a048270c8260182303d6f05d6b03d6705d6306c6e01c6604c5e03b5a0ca6f0aa6b0ca670aa6305a5f03a5b03a5705a5302a490ca455b06f0486b53067048630585f0385b038570485301849b60450a82f0482b0c8270482303d6f03d6b03d6703d630eb6f06b6e0bb6b01b6a0bb6701b6613b6306b620aa6f02a6b0aa6702a6303a5f02a5b03a5702a530aa3f0aa3d02a3b02a390aa370aa3502a3302a31039560393e0a9260486f0486b04867048630385f0385b03857038530483f0483d0483b01839048370483504833018310282f0482b048270282303d6f03d6b03d6703d6304c6b04c6303c5e03c5303c5203b6f06b6e03b6b01b6a03b6701b6603b6303b6203b4f04b4e03b4d0aa6f0aa6b0aa670aa6303a5f03a5b03a5703a5304a4f04a4303a3f03a3d03a3b02a3903a370aa3503a3302a318c16f881670395f039570393f0393d03937b41350a92f0a9270486f0486b04867048630385f0385b03857038530484f048430383f0383d0383b01839038370483503833018310482f0482b04827048230481b0481701d6a06d6203c6f03c6b03c6703c6303c5d03b420aa6f0aa6b0aa670aa630aa5d02a5103a4f03a4b03a4703a430786f0486b07867048630785d018510384f0384b03847038430782f0482b078270482303d6f05d6b03d6705d6304c6b04c6303c5b04c5306b6f06b6e16b6b01b6a0fb6701b6606b6306b6202b5b02b5a03b5702b5605b5303b4f03b4e04b4303b4206a6f02a6b0aa6a06a67a726602a6305a5f05a5e02a5b03a5702a5305a5204a4f04a4e02a4304a4204a3f04a3e04a3d0696f099670595f039570993f0993d09937099350292f0992d02927099250486f0486b04867048630485f0385b03857048530484f048430483f0483d0483b01839048370483504833018310282f0482d0482b0482704825028230481b0481703d6f05d6b03d6705d6304c6b04c6303c5b03c5a03c5604b6f06b6e04b6b01b6a04b6701b6604b6304b6203b4f03b4e03b4dae26f0aa6ba62670aa6305a5f03a5b03a5705a5304a4f04a4304a3f04a3d04a3b02a3904a37b123504a3302a310996f099670595f039570493f0493d04937099350992f099270486f0486b04867048630485f0385b03857048530484f048430483f0483d0483b01839048370483504833018310482f0482b04827048230481b0481701d6f01d6d02d6b02d6901d6701d6504d6302d6103c6f03c6d03c6703c6505c6303c5f01c5b01c5705c5303b6b03b6904b6303b6101b5b04b5303b4b04b4304a6f01a6d02a6b02a6901a6701a6502a6302a6104a5f01a5b01a5a01a5701a5602a5305a4f02a4b03a4702a4304a3f02a330996f0996d09967099650695f019570594f039470292f029270486f0486d0186b01869048670486501863018610185f0185b01857018530484f0184b03847018430483f018330282f0182b04827018230181b0481702e7f02e7e02e7d03d7f01d7b01d7705d7303d6f03d6d05d6b05d6903d6703d6505d6305d6101c7b04c7304c6b04c6904c6304c6103c5b03c5a03c5604b7f06b7e04b7d06b7c01b7b01b7a01b7701b7604b7501b7404b7304b7204b6f06b6e04b6d06b6c04b6b04b6a04b6904b6804b6706b6604b65af36404b6304b6204b6104b6003b4f03b4e03b4d01a7b01a7a02a7901a7701a7602a7302a7101a6701a6601a6505a5f02a5b03a5702a5304a4f02a4304a3f04a3d02a3b02a3904a3706a3502a3302a310697f019770696f0696d06967099650595f039570493f0493d04937099350292f029270187f0187b01877018730486f0486d0186b01869048670486501863018610485f0185b03857018530484f018430483f0483d0183b01839048370483501833018310282f0182b04827018230181b0481701d6f01d6e01d6701d6301d6201c6f01c6b01c6701c6307c5f03c5d09c5b05c5907c5703c5509c5305c5101b6b01b6304b5b04b5904b5304b5104b4b04b4301a6f01a6b01a6701a6301a5f01a5d01a5b01a5701a5502a4f02a4b02a4702a4302a3f02a330196f019670295f0295d01957019550294f029470192f029270186f0186b0186701863018570d856018550184f0184b01847018430183f018330182f0182b01827018230181b0181a018170281602d6f02d6e01d6702d6302d6206c6f01c6b01c6706c630ac5f03c5d09c5b05c590ac5703c5509c5305c5101b6b06b630eb5b04b5914b5304b510ab4b09b4302a6f01a6b01a6702a6302a5f01a5d02a5b01a5701a5502a4f02a4b02a4702a4302a3f02a330296f0696e01967029620295f0695e0295d0294f029470292f0292a02927029260186f0186b01867018631a85fad05d0185b018590e8570a05501853018510984f0184b0a847018431483f018330282f0182b02827018230281d0181b028170901501d6f01d6e01d6b01d6a01d6701d6601d6301d6201c6f01c6b01c6701c6307c5f03c5d09c5b05c5907c5703c5509c5305c5101b6b01b6304b5b04b5904b5304b5104b4b04b4301a6f01a6b01a6701a6301a5f01a5d01a5b01a5902a5702a5501a5301a5102a4f02a4b02a4702a4302a3f02a330196f01967029570d956029550294f029470292f019270186f0186b01867018630185f0185d0185701855018530184f0184b01847018430183f018330182f0182b01827018230181d0181b018170181501d6f01d6e01d6b01d6a01d6701d6601d6301d6201c6f01c6b01c6701c6307c5f03c5d0dc5b05c5907c5703c5515c5305c5101b6f01b6b01b6701b630cb5f04b5b04b590cb5704b5304b510cb4f04b4b07b4704b4301a6f01a6b01a6701a6301a5f01a5d01a5b01a5901a5701a5501a5301a5106a4f02a4b06a4702a4304a3f02a3b06a3702a330196f0196b01967019631595fab15d0295b0d9570a155029531994f0294b07947029430493f0293b0c937029330292f0292b02927029230186f0186e0186b0186701863018620185f0685e0185d0184f0184b01847018430183f0183b01837018330182f0182b0182a0182706826018230181f0181b0181a01817080160181302d6f02d6e02d6d06c6f01c6b01c6706c6306c5f03c5d06c5b05c5906c5703c5506c5305c5106b6f01b6b01b6706b6306b5f06b5b04b5906b5706b5304b510cb4f0ab4b0ab47ae34301a6b01a6a02a6901a6701a6602a6302a6101a5701a5601a5506a4f02a4b06a4702a4306a3f02a3b06a3702a330696f0196b01967029630695f0695d0295b06957ac155029537b14f0294b0a947029436e13f0293b0c937029330292f0292b02927029230186f0186b01867018630685f0685d0185b0185906857aa05501853018514804f0184b0a847018433403f0183b0c837018330282f0182b06827018230281f0181b070170181301d6f01d6b01d6701d6301c6f01c6b01c6701c630ac5f0ac5b0ac570ac5301b6f01b6e02b6d01b6701b6501b6301b6202b5f02b5b02b5702b5302b4f02b4b02b4702b4301a6701a6601a6501a5f05a5e01a5b01a5a01a5703a5601a5301a5201a4f04a4e01a4b01a4701a4301a4201a3f02a3e01a3d0196f0196b01967019630295f0295b02957029530294f0294b02947029430293f0293b02937029330192f0192d0192b0192702925019230186f0186b01867018630185f0185b01857018530184f0184b01847018430183f0183b01837018330182f0182d0182b01829018270182501823018210181f0181b018170181301d6f01d6e01d6d01c6f01c6b01c6901c6701c6305c6101c5f01c5b01c5701c5301b6b01b6901b6304b6101b5b01b5303b4b01b4301a6f01a6e01a6b01a6901a6701a6301a6204a6104a6001a5f01a5e01a5b01a5901a5701a5301a5206a5102a4b03a4705a4303a3f04a330196f0696d01967019650195f019570594f039470992f099270186f0186d0186b0186701865018630185f0185b01857018530184f0184b01847018430183f018330182f0182b01827018230181b0181701e7f01e7e01e7d01d7f03d7d01d7b01d7901d7701d7501d7305d7101d6f01d6b01d6701d6301c7b01c7901c7304c7101c6b01c6303c5b03c5a03c5601b7f01b7e04b7d06b7c01b7b01b7a01b7901b7801b7701b7601b7501b7401b7301b7204b7104b7001b6f01b6e04b6d06b6c01b6b01b6a01b6701b6601b6501b6401b6301b6203b4f03b4e03b4d01a7f01a7e06a7d01a6f01a6e01a6b01a6901a6301a6202a6105a5f02a5b03a5702a5304a4f02a4304a3f04a3d02a3b04a3a02a3902a3804a3704a3606a35a723402a3302a310197f0697d01977019750196f019670595f039570493f0493d04937099350292f029270187f0187d0187b01879018770187501873018710186f0186b01867018630185f0185b01857018530184f018430183f0183d0183b01839018370183501833018310182f0182b01827018230181b0181701d6f01d6e01d6d01c6f03c6d01c6b01c6901c6701c6501c6305c6101c5f01c5b01c5701c5301b6f01b6b01b6901b6701b6304b6101b5f01b5b01b5701b530cb4f0ab4b0ab47a634301a6f01a6e06a6d01a5f01a5e01a5b01a5901a5301a5202a5106a4f02a4b06a4702a4306a3f02a3b06a3702a330196f0696d0196b0196701965019630195f0195b01957019530b94f0294b0a947029430b93f0293b0b937029330292f0292b02927029230186f0186d0186b01869018670186501863018610185f0185b01857018530184f0184b01847018430183f0183b01837018330182f0182b01827018230181f0181b018170181301d6f01d6b01d6701d6301c6f01c6b01c6701c630ac5f04c5b07c5704c5301b6f01b6b01b6701b6302b5f02b5b02b5702b5302b4f02b4b02b4702b4301a6f01a6e01a6b01a6a01a6701a6601a6301a620aa5f05a5e07a5b03a5a07a5703a560aa5305a5204a4f04a4e0ca4b0ca4704a4304a4201a3f01a3e01a3b01a3a01a3701a3601a3301a320196f0196b01967019630295f0295b02957029530294f0294b02947029430293f0293b02937029330292f0292d0292b0292702925029230186f0186e0186b0186701863018620185f0185b0185a018570a856018530184f0184b0184a018470c846018430183f0283e0183b0183701833018320182f0282e0182d0181f0181b0181a01817028160181306d6f01d6b01d6706d6306c6f01c6b01c6706c630ac5f0ac5b0ac570ac5302b6f02b6d01b6b01b6a01b6701b6602b6502b5f02b5b02b5702b5302b4f02b4b02b4702b4302a6f06a6e02a6d02a5f05a5e02a5b02a5a02a5703a5602a5302a5202a4f04a4e02a4b02a4702a4302a4201a3f01a3e01a3d0296f0196b01967029630295f0295b02957029530294f0294b02947029430293f0293b02937029330292f0292d0292b0292702925029230186f0186b01867018630a85f0185b0a857018530c84f0184b0c847018430283f0183b02837018330282f0282d0182b0182902827a402501823018210281f0181b028170181301e7f01e7b01e7701e7301d7f01d7e01d7b01d7a01d7701d7601d7301d7202d6f02d6e02d6d01c7e01c7301c7203c6b04c6304c5b04c5904c5304c5101b6f05b6e01b6b01b6a01b6703b6601b6301b6201b5f05b5e01b5d05b5c01b5b01b5a01b5901b5801b5705b5601b550ab5401b5301b5201b5101b5001b4f04b4e01b4d01a7f01a7b01a7701a7302a6b03a6a02a6903a6703a6602a6302a6103a5703a5603a5504a4f02a4301a3f01a3d01a3b02a3901a3706a3501a3301a310197f019770596f039670595f0595d05957099550193f0193d01937099350292f029270187f0187b01877018730186f0186d0186b0186701865018630185f0185d0185b01859018570185501853018510184f018430183f0183d0183b01839018370183501833018310182f0182b01827018230181b0181703d6f05d6b03d6705d6305c6f06c6e05c6b01c6a05c6701c6605c6305c6202c5f02c5e02c5d06b6fa236b0cb6706b6305b5f03b5b03b5705b5305b4f05b4b04b4905b4705b4304b4106a6f02a6b06a6702a6302a5b03a5a02a5903a5703a5602a5302a5103a4703a4603a450aa3f02a3b0aa3702a330696f0296b09967029630595f0295b03957029530594f0594d0294b0594709945029430993f0293b09937029330292f0292b02927029230686f0786b50067068630585f0585d0385b038570a855058530584f0584d0584b01849058470a84505843018413303f0783b0c837078330282f0782b0a827028230281f0781b098170281303d6f03d6b03d6703d6306c6f06c6b06c6706c6303c5f03c5b03c5703c5302b6f02b6b02b6702b6302b5f03b5e02b5d02b5702b5502b5302b5202b4f02b4b02b4702b4302a6f06a6e02a6b01a6a02a6701a6602a6302a6202a5703a5602a5502a4f04a4e02a4b02a4702a4302a4202a3f02a3e02a3d0296f0296b02967029630295f0295b02957029530294f0294b02947029430293f0293b02937029330292f0292d0292b0292702925029230686f0686b06867068630385f0385b03857038530784f0784b07847078430283f0283d0283b0283707835028330282f0282d0282b01829028270782502823018210281f0281b028170281301d6f01d6b01d6701d6301c6f01c6e01c6701c6301c6201c5f01c5e02c5b02c5a01c5701c5601c5301c5201b6b01b6303b5b03b5303b4b03b4904b4304b4101a6f01a6b01a6701a6303a5f02a5b01a5702a5305a4f05a4d01a4b01a4901a4701a4501a4301a4104a3f02a330196f019670395f039570b94f0b94d0b9470b9450292f029270186f0186b01867018630185f0185b01857018530184f0184d0184b01849018470184501843018410183f018330182f0182b01827018230181b01817 20 1048575 8 255 11 2047 20 1048575
def cc_60_6 : Nat → List (Nat × Nat) := unpackCursorV4 0x1f99ecc614bf499d846dc2006d 0x5d6f05d6e01d6706d6305d6203c6f01c6b01c6703c6303c5f01c5d03c5b01c5701c5501b6b06b630eb5b04b5914b5304b5103b4b03b4306a6f01a6b01a6702a6306a5f06a5d02a5b02a5906a5706a5502a5302a5103a4f02a4b03a4702a4306a3f02a330696f0696e01967069620395f0395e0395d0394f0394a03947039460292f029270186f0186b01867018630785f0785d0185b01859078570785501853018510384f0184b03847018430783f018330282f0182b06827018230781d0181b078170781503d6f05d6e03d6d01c6b01c6a03c6901c6701c6603c6303c6101c5701c5601c5506b6f01b6b01b6706b6303b5f03b5b04b5903b5703b5303b5103b4f03b4b03b4703b4306a6f01a6b01a6706a6303a5f03a5d03a5b02a5903a5706a5503a5302a5103a4f03a4b03a4703a4306a3f06a3b06a3706a330696f0196b01967069630395f0395d0395b03957c4155039530394f0394b03947039436f13f0993b68137099330692f0692b06927069230186f0186b01867018630385f0385d0185b01859038570785501853018510384f0184b03847018430783f0183b07837018330682f0182b06827018230781f0181b078170181301d6f01d6b01d6701d6301c6f01c6e01c6b01c6a01c6701c6601c6301c6205c5f05c5e02c5b02c5a03c5702c5605c5305c5201b6f01b6b01b6701b6305b5f03b5b03b5705b530cb4f0fb4b04b490cb470fb4304b4101a6f01a6b01a6a01a6701a6601a6305a5f05a5e02a5b03a5702a5305a5201a4f01a4e01a4d06a3f02a3b06a3702a330196f0196b01967019630595f0295b03957029530994f0994d0294b0994709945029430993f0293b09937029330292f0292b02927029230186f0186b01867018630185f0185b01857018530184f0184d0184b01849018470184501843018410183f0183b01837018330182f0182d0182b0182701825018230181f0181b018170181301d6f01d6e03d6d01d6701d6501d6301d6201c6701c6601c6501c5f05c5e01c5d01b6f01b6b01b6701b6305b5f03b5b03b5705b5301b4f01b4b04b4901b4701b4301b4101a6f01a6b01a6701a6305a5f03a5b03a5705a5301a4f01a4d01a4b02a4901a47c224501a4301a419723f06a3b9223706a330196f0196b01967019630595f0395b03957059530194f0194d0194b0194709945019430993f0993b09937099330692f0992b09927069230186f0186b01867018630185f0185b01857018530184f0184d0184b01849018470184501843018410183f0183b01837018330182f0182b01827018230181f0181b018170181301d6f01d6e01d6d01c6f01c6e03c6d01c5f01c5e01c5b01c5901c5301c5203c5101b6f01b6b01b6901b6701b6304b6101b5f01b5b01b5701b5303b4f03b4b03b4703b4301a6f0aa6d01a6b01a6901a6701a6501a6302a6101a5f01a5b01a5701a5303a4f03a4b03a4703a430aa3f06a3b0aa3706a330196f0b96d0196b0196701965019630195f0195b01957019530394f0394b03947039430b93f0993b0b937099330692f0992b0a927069230186f0186d0186b01869018670186501863018610185f0185b01857018530184f0184b01847018430183f0183b01837018330182f0182b01827018230181f0181b018170181301d6f01d6b01d6701d6301c6f01c6e01c6b01c6a01c6701c6601c6301c6201c5f01c5e01c5b01c5a01c5701c5601c5301c5201b6f01b6b01b6701b6305b5f03b5b03b5704b5312b4f04b4b04b490db4704b4304b4101a6f01a6b01a6701a6305a5f03a5b03a5705a5306a4f06a4d06a4b02a4906a4706a4506a4302a4104a3f06a3b06a3704a330196f0196b01967019630595f0395b03957059530994f0994d0894b0994709945089430493f0893b09937049330692f0692b06927069230186f0186e0186b0186701863018620185f0585e0185b0185701853018520184f0584e0184d0183f0183b0183a0183723036018330182f0182b0182a0182706826018230181f0181b0181a018170981601813 17 131071 7 127 11 2047 20 1048575
def cur_60 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (cc_60_6 (Nat.sub p 192)) (cc_60_5 (Nat.sub p 160)) (Nat.blt p 192)) (Bool.rec (cc_60_4 (Nat.sub p 128)) (cc_60_3 (Nat.sub p 96)) (Nat.blt p 128)) (Nat.blt p 160)) (Bool.rec (Bool.rec (cc_60_2 (Nat.sub p 64)) (cc_60_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_60_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def f_60 : Nat → Nat × Nat := unpackForestF 0x62155018bf84914062d80c57bf08a0314ef42a80b5fbb46a02d6c05abdc135016a76c11405a7da1350169602d1ec51a80b43af6c954d0eb42ed5155ab2bb54154052f80a5ba74694cd0c052bd2025014a744dac052780a4b9f6d93adae74ae80a479905132096641200a4397ad6028fe541280a3b938b1235ae442680a378e2511c4900519c634b012be0256e25be41b4b834db0d5c20d23c227c8347e0255e000c40014012a6fcd51d9b1be464764def4175d922bb23f7749aec11404a78094b73268e4d8c04a3809436caded89bdb4b6362570127e024eda63433d6f6709a024dd909e3213401266c409404978092b0124eba53174a2009235869eb053d64262c137010beac0d8042daa47c4e69e9c9b5453e2724f4f8e09c8dc042ba582c4b0480214d19b7a326f470988c8dc04278084b43ad07adbcf4b7a016e3d2ba7d180f49b8084739078720d8e41a00843376a84d58cd5b21326f264be6253cc4a693235262de5cd5098af95a4f2b49a4c4d49da213a44272884c49c041f8083b230a84558c041b9003601066020bc741b0082b126be24d4c59ac0b354164a82c15048af8913f1227a244dc04138785c0f0a80208c040f86036010361099020b204064056de0c4f8151b00817020d80419004098003f 8 11
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsV4 fullMask g_60 ep_60 197 bds_60 (dagTraceF fullMask rootStock 11 f_60) (cur_60 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_0 : treeBlockF 0 32 (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 197 (dagTraceF fullMask rootStock 11 f_60) cur_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_1 : treeBlockF 32 64 (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 197 (dagTraceF fullMask rootStock 11 f_60) cur_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_2 : treeBlockF 64 96 (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 197 (dagTraceF fullMask rootStock 11 f_60) cur_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_3 : treeBlockF 96 128 (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 197 (dagTraceF fullMask rootStock 11 f_60) cur_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_4 : treeBlockF 128 160 (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 197 (dagTraceF fullMask rootStock 11 f_60) cur_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_5 : treeBlockF 160 192 (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 197 (dagTraceF fullMask rootStock 11 f_60) cur_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_6 : treeBlockF 192 197 (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 197 (dagTraceF fullMask rootStock 11 f_60) cur_60) = true := by decide +kernel
theorem nj_60_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 197 (dagTraceF fullMask rootStock 11 f_60) cur_60) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_60_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_60_1 h1 h2)
theorem nj_60_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 197 (dagTraceF fullMask rootStock 11 f_60) cur_60) i = true := block_join nj_60_1 (fun _ h1 h2 => treeBlockF_at nb_60_2 h1 h2)
theorem nj_60_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 197 (dagTraceF fullMask rootStock 11 f_60) cur_60) i = true := block_join nj_60_2 (fun _ h1 h2 => treeBlockF_at nb_60_3 h1 h2)
theorem nj_60_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 197 (dagTraceF fullMask rootStock 11 f_60) cur_60) i = true := block_join nj_60_3 (fun _ h1 h2 => treeBlockF_at nb_60_4 h1 h2)
theorem nj_60_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 197 (dagTraceF fullMask rootStock 11 f_60) cur_60) i = true := block_join nj_60_4 (fun _ h1 h2 => treeBlockF_at nb_60_5 h1 h2)
theorem nj_60_6 : ∀ i, 0 ≤ i → i < 197 → (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 197 (dagTraceF fullMask rootStock 11 f_60) cur_60) i = true := block_join nj_60_5 (fun _ h1 h2 => treeBlockF_at nb_60_6 h1 h2)
theorem nc_60 : ∀ i, 0 ≤ i → i < 197 → (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 197 (dagTraceF fullMask rootStock 11 f_60) cur_60) i = true := nj_60_6
theorem lb_60 : LowerBin fullMask rootStock g_60 12 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_60 kn_60 sub_60 gl_60 rc_60 nc_60

def wg : List Gate := [⟨GateOp.and, [0, 4]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.and, [5, 7]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [1, 8]⟩, ⟨GateOp.or, [2, 10]⟩, ⟨GateOp.and, [3, 11]⟩, ⟨GateOp.and, [2, 13]⟩, ⟨GateOp.or, [6, 9]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [14, 15]⟩, ⟨GateOp.and, [16, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276676744 * 2 ^ 32 + 3902849024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276676744 * 2 ^ 32 + 3902849024)) (13 - 1) := by
  rw [show canon fullMask (4276676744 * 2 ^ 32 + 3902849024) = g_60 by decide]
  exact lb_60

end PEqualNP.Outside.L_meta_49121

theorem PEqualNP.Outside.L_meta_49121 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676744 * 2 ^ 32 + 3902849024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676744 * 2 ^ 32 + 3902849024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_49121.table2_from_lowerBin (4276676744 * 2 ^ 32 + 3902849024) 13 PEqualNP.Outside.L_meta_49121.root_lb PEqualNP.Outside.L_meta_49121.wg 18 rfl PEqualNP.Outside.L_meta_49121.wfits PEqualNP.Outside.L_meta_49121.weval
