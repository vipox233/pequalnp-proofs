import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_49273

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

def m_0 : Nat := 0xcccc00000000
def s_0 : List Nat := [0x444400000000, 0xc0c00000000, 0xcc00000000]
def g_0 : Nat := 0x44c00000000
def ep_0 : Nat := 0x4800000000000004080000000000000000000000000000044000000000
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

def m_1 : Nat := 0xf0000000f000000
def s_1 : List Nat := [0x500000005000000, 0x300000003000000, 0xf000000]
def g_1 : Nat := 0x100000007000000
def ep_1 : Nat := 0x600000000000000000000000000000000000000000000000000000001000000020000000100000004000000
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

def m_2 : Nat := 0xff000000
def s_2 : List Nat := [0x55000000, 0x33000000, 0xf000000]
def g_2 : Nat := 0x17000000
def ep_2 : Nat := 0x600000000000000120000000000000014000000
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

def m_3 : Nat := 0xf000f0000000000
def s_3 : List Nat := [0x500050000000000, 0x300030000000000, 0xf0000000000]
def g_3 : Nat := 0x100070000000000
def ep_3 : Nat := 0x600000000000000000000000000000000000000000001000200000000000100040000000000
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

def m_4 : Nat := 0xc0c0c0c00000000
def s_4 : List Nat := [0x404040400000000, 0xc000c00000000, 0xc0c00000000]
def g_4 : Nat := 0x4040c00000000
def ep_4 : Nat := 0x408000000000004000800000000000000000000000000000000000000000004040000000000
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

def m_5 : Nat := 0xaa00aa00000000
def s_5 : List Nat := [0x22002200000000, 0xa000a00000000, 0xaa00000000]
def g_5 : Nat := 0x2002a00000000
def ep_5 : Nat := 0x28000000000000000000000000000200080000000000020020000000000000000000000000
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

def m_6 : Nat := 0xa0a0a0a00000000
def s_6 : List Nat := [0x202020200000000, 0xa000a00000000, 0xa0a00000000]
def g_6 : Nat := 0x2020a00000000
def ep_6 : Nat := 0x208000000000002000800000000000000000000000000020200000000000000000000000000
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

def m_7 : Nat := 0xcc00cc00000000
def s_7 : List Nat := [0x44004400000000, 0xc000c00000000, 0xcc00000000]
def g_7 : Nat := 0x4004c00000000
def ep_7 : Nat := 0x48000000000000000000000000000400080000000000000000000000000004004000000000
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

def m_8 : Nat := 0x4444444400000000
def s_8 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_8 : Nat := 0x4044400000000
def ep_8 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
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

def m_10 : Nat := 0xaaaa00000000
def s_10 : List Nat := [0x222200000000, 0xa0a00000000, 0xaa00000000]
def g_10 : Nat := 0x22a00000000
def ep_10 : Nat := 0x2800000000000002080000000000000220000000000000000000000000
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

def m_11 : Nat := 0xf000f000000000
def s_11 : List Nat := [0x50005000000000, 0x30003000000000, 0xf000000000]
def g_11 : Nat := 0x10007000000000
def ep_11 : Nat := 0x60000000000000000000000000000000000000000000100020000000000010004000000000
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

def m_12 : Nat := 0xcccc0000
def s_12 : List Nat := [0x44440000, 0xc0c0000, 0xcc0000]
def g_12 : Nat := 0x44c0000
def ep_12 : Nat := 0x480000000000000408000000000000000000000000000004400000
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

def m_13 : Nat := 0xc0c00000c0c0
def s_13 : List Nat := [0x404000004040, 0xc0000000c0, 0xc0c0]
def g_13 : Nat := 0x40000040c0
def ep_13 : Nat := 0x408000000000000000000000004000000080000000000000000000000000000000000000004000004000
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

def m_14 : Nat := 0x4040404040404040
def s_14 : List Nat := [0x40004000400040, 0x404000004040, 0x40404040]
def g_14 : Nat := 0x4000404040
def ep_14 : Nat := 0x40400000000040000040000000004000400000000000000000000000000000000000000000000000000000
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

def m_15 : Nat := 0xff000000000000
def s_15 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_15 : Nat := 0x17000000000000
def ep_15 : Nat := 0x600000000000000120000000000000014000000000000
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

def m_16 : Nat := 0x88008800880088
def s_16 : List Nat := [0x8000800080008, 0x8800000088, 0x880088]
def g_16 : Nat := 0x800080088
def ep_16 : Nat := 0x8008000000008000000800000000000000000000000080008000000000000000000000000000000000000
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

def m_17 : Nat := 0xc000c000c000c0
def s_17 : List Nat := [0x40004000400040, 0xc0000000c0, 0xc000c0]
def g_17 : Nat := 0x40004000c0
def ep_17 : Nat := 0x40008000000040000000800000000000000000000000000000000000000000000000000000004000400000
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

def m_18 : Nat := 0x4400440044004400
def s_18 : List Nat := [0x400040004000400, 0x440000004400, 0x44004400]
def g_18 : Nat := 0x40004004400
def ep_18 : Nat := 0x400400000000400000040000000000000000000000004000400000000000000000000000000000000000000
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

def m_19 : Nat := 0xf0f000000000000
def s_19 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_19 : Nat := 0x107000000000000
def ep_19 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
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

def m_20 : Nat := 0xf0f000000000
def s_20 : List Nat := [0x505000000000, 0x303000000000, 0xf000000000]
def g_20 : Nat := 0x107000000000
def ep_20 : Nat := 0x6000000000000000000000000000001020000000000000104000000000
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

def m_21 : Nat := 0xc0c0c0c0
def s_21 : List Nat := [0x40404040, 0xc000c0, 0xc0c0]
def g_21 : Nat := 0x4040c0
def ep_21 : Nat := 0x40800000000000400080000000000000000000000000000000000000000000404000
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

def m_22 : Nat := 0xff0000000000
def s_22 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_22 : Nat := 0x170000000000
def ep_22 : Nat := 0x6000000000000001200000000000000140000000000
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

def m_23 : Nat := 0x4444000044440000
def s_23 : List Nat := [0x404000004040000, 0x44000000440000, 0x44440000]
def g_23 : Nat := 0x4000004440000
def ep_23 : Nat := 0x440000000000000000000000004000000400000000400000400000000000000000000000000000000000000
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

def m_24 : Nat := 0xa0a00000a0a0000
def s_24 : List Nat := [0x202000002020000, 0xa0000000a0000, 0xa0a0000]
def g_24 : Nat := 0x20000020a0000
def ep_24 : Nat := 0x208000000000000000000000002000000080000000000000000000000020000020000000000000000000000
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

def m_25 : Nat := 0xc0c00000c0c0000
def s_25 : List Nat := [0x404000004040000, 0xc0000000c0000, 0xc0c0000]
def g_25 : Nat := 0x40000040c0000
def ep_25 : Nat := 0x408000000000000000000000004000000080000000000000000000000000000000000000004000004000000
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

def m_26 : Nat := 0xcc000000cc0000
def s_26 : List Nat := [0x44000000440000, 0xc0000000c0000, 0xcc0000]
def g_26 : Nat := 0x40000004c0000
def ep_26 : Nat := 0x48000000000000000000000000000000000000000400000008000000000000000000000004000000400000
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

def m_27 : Nat := 0xc300c300c300c300
def s_27 : List Nat := [0x4100410041004100, 0x300030003000300, 0xc3000000c300, 0xc300c300]
def g_27 : Nat := 0x100030003004300
def ep_27 : Nat := 0x200400000000200000040000000000000000000000000000000000000000000000000000100000000004000
theorem epk_27 : ep_27 = edgePack m_27 g_27 := by decide +kernel
def bds_27 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_27 : KnownBin bds_27 := by intro b hb; simp [bds_27] at hb
theorem sub_27 : ∀ b ∈ bds_27, m_27 &&& b.1 = b.1 := by intro b hb; simp [bds_27] at hb
theorem gl_27 : ∀ b ∈ bds_27, canon b.1 g_27 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_27] at hb
def cc_27_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xb41682b1560ac148a80d009c3382704e09c1382704648c1182304607c8f81f03a2740e81b1341680c841c001 0xf138749a360b1a048b8305ca226d212680893c40981c130d088602c2c12125308288304c1422040402249fa3ff91df28df4467893fb89dda4deb267512fa495c849df246e03f641db00dd6066a82f50159e09ca046381f100d8605c1026000f 11 2047 5 31 10 1023 17 131071
def cc_27_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb0b0b0b0b0949090909074707062606052494841404040404040242020202004 0x3d299e140ec26741038251b924d8146a09330719034c00c5e052c2616244a1a44ed02607928308ca64451210310014 8 255 3 7 10 1023 17 131071
def cur_27 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_27_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_27_0 p) (Nat.blt p 32)
def f_27 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c838c834053fbc18bc14053b0537b2440533052f052b97489740943c94300527814c814480188014052375387534043f682c6824043b04375d440433042f042b43484340413c413004272c4c2c442c2c2c240423214c2144041f144c1444041b041709240413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV4 m_27 g_27 ep_27 64 bds_27 (dagTraceF m_27 s_27 5 f_27) (cur_27 0) s_27 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_0 : treeBlockF 0 32 (dagCheckNodeV4 m_27 g_27 ep_27 bds_27 64 (dagTraceF m_27 s_27 5 f_27) cur_27) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_1 : treeBlockF 32 64 (dagCheckNodeV4 m_27 g_27 ep_27 bds_27 64 (dagTraceF m_27 s_27 5 f_27) cur_27) = true := by decide +kernel
theorem nj_27_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_27 g_27 ep_27 bds_27 64 (dagTraceF m_27 s_27 5 f_27) cur_27) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_27_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_27_1 h1 h2)
theorem nc_27 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_27 g_27 ep_27 bds_27 64 (dagTraceF m_27 s_27 5 f_27) cur_27) i = true := nj_27_1
theorem lb_27 : LowerBin m_27 s_27 g_27 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_27 kn_27 sub_27 gl_27 rc_27 nc_27

def m_28 : Nat := 0x3333000000003333
def s_28 : List Nat := [0x1111000000001111, 0x303000000000303, 0x33000000000033, 0x3333]
def g_28 : Nat := 0x1113000000001333
def ep_28 : Nat := 0x2000000000020000200000000020000000000000000001110000000001000
theorem epk_28 : ep_28 = edgePack m_28 g_28 := by decide +kernel
def bds_28 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_28 : KnownBin bds_28 := by intro b hb; simp [bds_28] at hb
theorem sub_28 : ∀ b ∈ bds_28, m_28 &&& b.1 = b.1 := by intro b hb; simp [bds_28] at hb
theorem gl_28 : ∀ b ∈ bds_28, canon b.1 g_28 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_28] at hb
def cur_28 : Nat → List (Nat × Nat) := unpackCursorV4 0x1a2d58b12a44890e8701 0x31243048c4908121924204928ea11b393a526c80e841b000f 7 127 3 7 10 1023 15 32767
def f_28 : Nat → Nat × Nat := unpackForestF 0xc7463629d6490a6c43a492209086c00f 3 10
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV4 m_28 g_28 ep_28 10 bds_28 (dagTraceF m_28 s_28 4 f_28) (cur_28 0) s_28 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28 : treeBlockF 0 10 (dagCheckNodeV4 m_28 g_28 ep_28 bds_28 10 (dagTraceF m_28 s_28 4 f_28) cur_28) = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 10 → (dagCheckNodeV4 m_28 g_28 ep_28 bds_28 10 (dagTraceF m_28 s_28 4 f_28) cur_28) i = true := fun _ h1 h2 => treeBlockF_at nb_28 h1 h2
theorem lb_28 : LowerBin m_28 s_28 g_28 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_28 kn_28 sub_28 gl_28 rc_28 nc_28

def m_29 : Nat := 0xffff00000000
def s_29 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_29 : Nat := 0x177f00000000
def ep_29 : Nat := 0x6800000000000006080000000000001220000000000000144000000000
theorem epk_29 : ep_29 = edgePack m_29 g_29 := by decide +kernel
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_20, s_20, 4, g_20), (m_22, s_22, 4, g_22), (m_0, s_0, 4, g_0), (m_10, s_10, 4, g_10)]
theorem kn_29 : KnownBin bds_29 := by
  intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_20
  · exact lb_22
  · exact lb_0
  · exact lb_10
theorem sub_29 : ∀ b ∈ bds_29, m_29 &&& b.1 = b.1 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_29 : ∀ b ∈ bds_29, canon b.1 g_29 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_29_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8724381de0ee07323981c44b575a02d01642aa4550298940698435b9a80d406623301980c445a429214049844a123109c0064001 0x59003c6015407c9a07d3a36950b460fa10592a048cf1460a9f054b9d07a0c39201a830c4285a8825180a83d002c600c4040120310050280f4e07a6b69342c92a2450b20878f5a46ac94d2ca2874f5826a1c4e0626870f818720c320618830c018547826060d0805952980e400f180310100680c300c0a038c01a6015200b20078c02a8081340fa72cd29468c1f420b25269181c7c0e3d489e904d42a5a892506251e118287c0c3d0a17030a418440c21061003068202c624c0b2012d203e800d400e980310050680d300a90030c030480c300e980a0d0184015200c1207938d4945a460f21058f8a47442360b190e518626c0d2e06250811818741036060c878fc2c7742370b19874fe426e152f7093870fc1876b8370619850bc1856702706118306c102e000f 13 8191 5 31 10 1023 17 131071
def cc_29_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb817017bae0544a80580a014018811001 0x2e9c174d0f27059343c7c16390b19058c42c61514d84a2874f6626a152d8092d21341892a0450620870f5a06a142d4c12858c1f2493a4d0b24c29142c821e3d991a875383a7cf126942683124b08a0c410e1eb00d4702b104c0620078c1f2681520 11 2047 5 31 10 1023 17 131071
def cur_29 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_29_1 (Nat.sub p 32)) (cc_29_0 p) (Nat.blt p 32)
def f_29 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV4 m_29 g_29 ep_29 43 bds_29 (dagTraceF m_29 s_29 6 f_29) (cur_29 0) s_29 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_0 : treeBlockF 0 32 (dagCheckNodeV4 m_29 g_29 ep_29 bds_29 43 (dagTraceF m_29 s_29 6 f_29) cur_29) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_1 : treeBlockF 32 43 (dagCheckNodeV4 m_29 g_29 ep_29 bds_29 43 (dagTraceF m_29 s_29 6 f_29) cur_29) = true := by decide +kernel
theorem nj_29_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_29 g_29 ep_29 bds_29 43 (dagTraceF m_29 s_29 6 f_29) cur_29) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_29_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_29_1 h1 h2)
theorem nc_29 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_29 g_29 ep_29 bds_29 43 (dagTraceF m_29 s_29 6 f_29) cur_29) i = true := nj_29_1
theorem lb_29 : LowerBin m_29 s_29 g_29 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_29 kn_29 sub_29 gl_29 rc_29 nc_29

def m_30 : Nat := 0xff00ff0000000000
def s_30 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_30 : Nat := 0x1100170000000000
def ep_30 : Nat := 0x600000000000000000000000000000006000000000011001200000000001100140000000000
theorem epk_30 : ep_30 = edgePack m_30 g_30 := by decide +kernel
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_30 : KnownBin bds_30 := by
  intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_30 : ∀ b ∈ bds_30, m_30 &&& b.1 = b.1 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_30 : ∀ b ∈ bds_30, canon b.1 g_30 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_30 : Nat → List (Nat × Nat) := fun _ => []
def f_30 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV4 m_30 g_30 ep_30 0 bds_30 (dagTraceF m_30 s_30 4 f_30) (cur_30 0) s_30 4 = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_30 g_30 ep_30 bds_30 0 (dagTraceF m_30 s_30 4 f_30) cur_30 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_30 : LowerBin m_30 s_30 g_30 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_30 kn_30 sub_30 gl_30 rc_30 nc_30

def m_31 : Nat := 0xff00ff00000000
def s_31 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_31 : Nat := 0x17007f00000000
def ep_31 : Nat := 0x68000000000000000000000000000600080000000000120020000000000014004000000000
theorem epk_31 : ep_31 = edgePack m_31 g_31 := by decide +kernel
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11), (m_15, s_15, 4, g_15), (m_7, s_7, 4, g_7), (m_5, s_5, 4, g_5)]
theorem kn_31 : KnownBin bds_31 := by
  intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_11
  · exact lb_15
  · exact lb_7
  · exact lb_5
theorem sub_31 : ∀ b ∈ bds_31, m_31 &&& b.1 = b.1 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_31 : ∀ b ∈ bds_31, canon b.1 g_31 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_31_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8724381de0ee07323981c44b575a02d01642aa4550298940698435b9a80d406623301980c445a429214049844a123109c0064001 0x59003c6015407c9a07d3a36950b460fa10592a048cf1460a9f054b9d07a0c39201a830c4285a8825180a83d002c600c4040120310050280f4e07a6b69342c92a2450b20878f5a46ac94d2ca2874f5826a1c4e0626870f818720c320618830c018547826060d0805952980e400f180310100680c300c0a038c01a6015200b20078c02a8081340fa72cd29468c1f420b25269181c7c0e3d489e904d42a5a892506251e118287c0c3d0a17030a418440c21061003068202c624c0b2012d203e800d400e980310050680d300a90030c030480c300e980a0d0184015200c1207938d4945a460f21058f8a47442360b190e518626c0d2e06250811818741036060c878fc2c7742370b19874fe426e152f7093870fc1876b8370619850bc1856702706118306c102e000f 13 8191 5 31 10 1023 17 131071
def cc_31_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb817017bae0544a80580a014018811001 0x2e9c174d0f27059343c7c16390b19058c42c61514d84a2874f6626a152d8092d21341892a0450620870f5a06a142d4c12858c1f2493a4d0b24c29142c821e3d991a875383a7cf126942683124b08a0c410e1eb00d4702b104c0620078c1f2681520 11 2047 5 31 10 1023 17 131071
def cur_31 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_31_1 (Nat.sub p 32)) (cc_31_0 p) (Nat.blt p 32)
def f_31 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV4 m_31 g_31 ep_31 43 bds_31 (dagTraceF m_31 s_31 6 f_31) (cur_31 0) s_31 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_0 : treeBlockF 0 32 (dagCheckNodeV4 m_31 g_31 ep_31 bds_31 43 (dagTraceF m_31 s_31 6 f_31) cur_31) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_1 : treeBlockF 32 43 (dagCheckNodeV4 m_31 g_31 ep_31 bds_31 43 (dagTraceF m_31 s_31 6 f_31) cur_31) = true := by decide +kernel
theorem nj_31_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_31 g_31 ep_31 bds_31 43 (dagTraceF m_31 s_31 6 f_31) cur_31) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_31_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_31_1 h1 h2)
theorem nc_31 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_31 g_31 ep_31 bds_31 43 (dagTraceF m_31 s_31 6 f_31) cur_31) i = true := nj_31_1
theorem lb_31 : LowerBin m_31 s_31 g_31 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_31 kn_31 sub_31 gl_31 rc_31 nc_31

def m_32 : Nat := 0xf0f0f0f000000000
def s_32 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_32 : Nat := 0x1010107000000000
def ep_32 : Nat := 0x60000000000000006000000000000000000000000010101020000000001010104000000000
theorem epk_32 : ep_32 = edgePack m_32 g_32 := by decide +kernel
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
theorem kn_32 : KnownBin bds_32 := by
  intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_11
theorem sub_32 : ∀ b ∈ bds_32, m_32 &&& b.1 = b.1 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_32 : ∀ b ∈ bds_32, canon b.1 g_32 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_32 : Nat → List (Nat × Nat) := fun _ => []
def f_32 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV4 m_32 g_32 ep_32 0 bds_32 (dagTraceF m_32 s_32 4 f_32) (cur_32 0) s_32 4 = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_32 g_32 ep_32 bds_32 0 (dagTraceF m_32 s_32 4 f_32) cur_32 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_32 : LowerBin m_32 s_32 g_32 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_32 kn_32 sub_32 gl_32 rc_32 nc_32

def m_33 : Nat := 0xf0f0f0f00000000
def s_33 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_33 : Nat := 0x107070f00000000
def ep_33 : Nat := 0x608000000000006000800000000000000000000000001020200000000000104040000000000
theorem epk_33 : ep_33 = edgePack m_33 g_33 := by decide +kernel
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3), (m_19, s_19, 4, g_19), (m_4, s_4, 4, g_4), (m_6, s_6, 4, g_6)]
theorem kn_33 : KnownBin bds_33 := by
  intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_3
  · exact lb_19
  · exact lb_4
  · exact lb_6
theorem sub_33 : ∀ b ∈ bds_33, m_33 &&& b.1 = b.1 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_33 : ∀ b ∈ bds_33, canon b.1 g_33 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_33_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8724381de0ee07323981c44b575a02d01642aa4550298940698435b9a80d406623301980c445a429214049844a123109c0064001 0x59003c6015407c9a07d3a36950b460fa10592a048cf1460a9f054b9d07a0c39201a830c4285a8825180a83d002c600c4040120310050280f4e07a6b69342c92a2450b20878f5a46ac94d2ca2874f5826a1c4e0626870f818720c320618830c018547826060d0805952980e400f180310100680c300c0a038c01a6015200b20078c02a8081340fa72cd29468c1f420b25269181c7c0e3d489e904d42a5a892506251e118287c0c3d0a17030a418440c21061003068202c624c0b2012d203e800d400e980310050680d300a90030c030480c300e980a0d0184015200c1207938d4945a460f21058f8a47442360b190e518626c0d2e06250811818741036060c878fc2c7742370b19874fe426e152f7093870fc1876b8370619850bc1856702706118306c102e000f 13 8191 5 31 10 1023 17 131071
def cc_33_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb817017bae0544a80580a014018811001 0x2e9c174d0f27059343c7c16390b19058c42c61514d84a2874f6626a152d8092d21341892a0450620870f5a06a142d4c12858c1f2493a4d0b24c29142c821e3d991a875383a7cf126942683124b08a0c410e1eb00d4702b104c0620078c1f2681520 11 2047 5 31 10 1023 17 131071
def cur_33 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_33_1 (Nat.sub p 32)) (cc_33_0 p) (Nat.blt p 32)
def f_33 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV4 m_33 g_33 ep_33 43 bds_33 (dagTraceF m_33 s_33 6 f_33) (cur_33 0) s_33 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_0 : treeBlockF 0 32 (dagCheckNodeV4 m_33 g_33 ep_33 bds_33 43 (dagTraceF m_33 s_33 6 f_33) cur_33) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_1 : treeBlockF 32 43 (dagCheckNodeV4 m_33 g_33 ep_33 bds_33 43 (dagTraceF m_33 s_33 6 f_33) cur_33) = true := by decide +kernel
theorem nj_33_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_33 g_33 ep_33 bds_33 43 (dagTraceF m_33 s_33 6 f_33) cur_33) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_33_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_33_1 h1 h2)
theorem nc_33 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_33 g_33 ep_33 bds_33 43 (dagTraceF m_33 s_33 6 f_33) cur_33) i = true := nj_33_1
theorem lb_33 : LowerBin m_33 s_33 g_33 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_33 kn_33 sub_33 gl_33 rc_33 nc_33

def m_34 : Nat := 0xcccccccc00000000
def s_34 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_34 : Nat := 0x4044c00000000
def ep_34 : Nat := 0x448000000000004004800000000000404080000000000000000000000000004044000000000
theorem epk_34 : ep_34 = edgePack m_34 g_34 := by decide +kernel
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7), (m_0, s_0, 4, g_0), (m_8, s_8, 4, g_8), (m_4, s_4, 4, g_4)]
theorem kn_34 : KnownBin bds_34 := by
  intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_7
  · exact lb_0
  · exact lb_8
  · exact lb_4
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

def m_35 : Nat := 0xcc00cc00cc00cc
def s_35 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_35 : Nat := 0x4004c004c00cc
def ep_35 : Nat := 0x48008000000048000000800000000000000000000400080008000000000000000000000004004000400000
theorem epk_35 : ep_35 = edgePack m_35 g_35 := by decide +kernel
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7), (m_26, s_26, 4, g_26), (m_17, s_17, 4, g_17), (m_16, s_16, 4, g_16)]
theorem kn_35 : KnownBin bds_35 := by
  intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_7
  · exact lb_26
  · exact lb_17
  · exact lb_16
theorem sub_35 : ∀ b ∈ bds_35, m_35 &&& b.1 = b.1 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_35 : ∀ b ∈ bds_35, canon b.1 g_35 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_35_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_35_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
def cur_35 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_35_1 (Nat.sub p 32)) (cc_35_0 p) (Nat.blt p 32)
def f_35 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV4 m_35 g_35 ep_35 43 bds_35 (dagTraceF m_35 s_35 6 f_35) (cur_35 0) s_35 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_0 : treeBlockF 0 32 (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 43 (dagTraceF m_35 s_35 6 f_35) cur_35) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_1 : treeBlockF 32 43 (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 43 (dagTraceF m_35 s_35 6 f_35) cur_35) = true := by decide +kernel
theorem nj_35_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 43 (dagTraceF m_35 s_35 6 f_35) cur_35) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_35_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_35_1 h1 h2)
theorem nc_35 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 43 (dagTraceF m_35 s_35 6 f_35) cur_35) i = true := nj_35_1
theorem lb_35 : LowerBin m_35 s_35 g_35 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_35 kn_35 sub_35 gl_35 rc_35 nc_35

def m_36 : Nat := 0x3333333300000000
def s_36 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_36 : Nat := 0x1113133300000000
def ep_36 : Nat := 0x220000000000002002000000000000202000000000000000000000000001110100000000000
theorem epk_36 : ep_36 = edgePack m_36 g_36 := by decide +kernel
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_36 : KnownBin bds_36 := by
  intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_36 : ∀ b ∈ bds_36, m_36 &&& b.1 = b.1 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_36 : ∀ b ∈ bds_36, canon b.1 g_36 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_36 : Nat → List (Nat × Nat) := fun _ => []
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV4 m_36 g_36 ep_36 0 bds_36 (dagTraceF m_36 s_36 4 f_36) (cur_36 0) s_36 4 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_36 g_36 ep_36 bds_36 0 (dagTraceF m_36 s_36 4 f_36) cur_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_36 kn_36 sub_36 gl_36 rc_36 nc_36

def m_37 : Nat := 0xaaaaaaaa00000000
def s_37 : List Nat := [0x2222222200000000, 0xa0a0a0a00000000, 0xaa00aa00000000, 0xaaaa00000000]
def g_37 : Nat := 0x2022a00000000
def ep_37 : Nat := 0x228000000000002002800000000000202080000000000020220000000000000000000000000
theorem epk_37 : ep_37 = edgePack m_37 g_37 := by decide +kernel
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5), (m_10, s_10, 4, g_10), (m_9, s_9, 4, g_9), (m_6, s_6, 4, g_6)]
theorem kn_37 : KnownBin bds_37 := by
  intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_5
  · exact lb_10
  · exact lb_9
  · exact lb_6
theorem sub_37 : ∀ b ∈ bds_37, m_37 &&& b.1 = b.1 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_37 : ∀ b ∈ bds_37, canon b.1 g_37 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_37_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_37_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_37 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_37_1 (Nat.sub p 32)) (cc_37_0 p) (Nat.blt p 32)
def f_37 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
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

def m_38 : Nat := 0xc0c0c0c0c0c0c0c0
def s_38 : List Nat := [0x4040404040404040, 0xc000c000c000c0, 0xc0c00000c0c0, 0xc0c0c0c0]
def g_38 : Nat := 0x40004040c0
def ep_38 : Nat := 0x40408000000040000040800000004000400080000000000000000000000000000000000000004000404000
theorem epk_38 : ep_38 = edgePack m_38 g_38 := by decide +kernel
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13), (m_21, s_21, 4, g_21), (m_14, s_14, 4, g_14), (m_17, s_17, 4, g_17)]
theorem kn_38 : KnownBin bds_38 := by
  intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_13
  · exact lb_21
  · exact lb_14
  · exact lb_17
theorem sub_38 : ∀ b ∈ bds_38, m_38 &&& b.1 = b.1 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_38 : ∀ b ∈ bds_38, canon b.1 g_38 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_38_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_38_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_38 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_38_1 (Nat.sub p 32)) (cc_38_0 p) (Nat.blt p 32)
def f_38 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV4 m_38 g_38 ep_38 43 bds_38 (dagTraceF m_38 s_38 6 f_38) (cur_38 0) s_38 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_0 : treeBlockF 0 32 (dagCheckNodeV4 m_38 g_38 ep_38 bds_38 43 (dagTraceF m_38 s_38 6 f_38) cur_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_1 : treeBlockF 32 43 (dagCheckNodeV4 m_38 g_38 ep_38 bds_38 43 (dagTraceF m_38 s_38 6 f_38) cur_38) = true := by decide +kernel
theorem nj_38_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_38 g_38 ep_38 bds_38 43 (dagTraceF m_38 s_38 6 f_38) cur_38) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_38_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_38_1 h1 h2)
theorem nc_38 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_38 g_38 ep_38 bds_38 43 (dagTraceF m_38 s_38 6 f_38) cur_38) i = true := nj_38_1
theorem lb_38 : LowerBin m_38 s_38 g_38 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_38 kn_38 sub_38 gl_38 rc_38 nc_38

def m_39 : Nat := 0xcccc0000cccc0000
def s_39 : List Nat := [0x4444000044440000, 0xc0c00000c0c0000, 0xcc000000cc0000, 0xcccc0000]
def g_39 : Nat := 0x40000044c0000
def ep_39 : Nat := 0x448000000000000000000000004000000480000000400000408000000000000000000000004000004400000
theorem epk_39 : ep_39 = edgePack m_39 g_39 := by decide +kernel
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_26, s_26, 4, g_26), (m_12, s_12, 4, g_12), (m_23, s_23, 4, g_23), (m_25, s_25, 4, g_25)]
theorem kn_39 : KnownBin bds_39 := by
  intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_26
  · exact lb_12
  · exact lb_23
  · exact lb_25
theorem sub_39 : ∀ b ∈ bds_39, m_39 &&& b.1 = b.1 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_39 : ∀ b ∈ bds_39, canon b.1 g_39 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_39_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_39_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_39 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_39_1 (Nat.sub p 32)) (cc_39_0 p) (Nat.blt p 32)
def f_39 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
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

def m_40 : Nat := 0xff000000ff00
def s_40 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_40 : Nat := 0x170000005700
def ep_40 : Nat := 0x400000000000000000000000000000000000000006000000020000001200000002000000140000005400
theorem epk_40 : ep_40 = edgePack m_40 g_40 := by decide +kernel
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_22, s_22, 4, g_22)]
theorem kn_40 : KnownBin bds_40 := by
  intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_22
theorem sub_40 : ∀ b ∈ bds_40, m_40 &&& b.1 = b.1 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_40 : ∀ b ∈ bds_40, canon b.1 g_40 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_40 : Nat → List (Nat × Nat) := fun _ => []
def f_40 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV4 m_40 g_40 ep_40 0 bds_40 (dagTraceF m_40 s_40 4 f_40) (cur_40 0) s_40 4 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_40 g_40 ep_40 bds_40 0 (dagTraceF m_40 s_40 4 f_40) cur_40 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_40 : LowerBin m_40 s_40 g_40 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_40 kn_40 sub_40 gl_40 rc_40 nc_40

def m_41 : Nat := 0xf0f00000f0f0000
def s_41 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_41 : Nat := 0x1070000070f0000
def ep_41 : Nat := 0x608000000000000000000000006000000080000000000000000000001020000020000000104000004000000
theorem epk_41 : ep_41 = edgePack m_41 g_41 := by decide +kernel
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1), (m_19, s_19, 4, g_19), (m_25, s_25, 4, g_25), (m_24, s_24, 4, g_24)]
theorem kn_41 : KnownBin bds_41 := by
  intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_1
  · exact lb_19
  · exact lb_25
  · exact lb_24
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

def m_42 : Nat := 0xcccc0000cccc
def s_42 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_42 : Nat := 0x44c000044cc
def ep_42 : Nat := 0x408000000000000000000000004800000088000004080000000000000000000000000000044000004400
theorem epk_42 : ep_42 = edgePack m_42 g_42 := by decide +kernel
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_42 : KnownBin bds_42 := by
  intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_42 : ∀ b ∈ bds_42, m_42 &&& b.1 = b.1 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_42 : ∀ b ∈ bds_42, canon b.1 g_42 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_42 : Nat → List (Nat × Nat) := fun _ => []
def f_42 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV4 m_42 g_42 ep_42 0 bds_42 (dagTraceF m_42 s_42 4 f_42) (cur_42 0) s_42 4 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_42 g_42 ep_42 bds_42 0 (dagTraceF m_42 s_42 4 f_42) cur_42 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_42 kn_42 sub_42 gl_42 rc_42 nc_42

def m_43 : Nat := 0xcc00cc00cc00cc00
def s_43 : List Nat := [0x4400440044004400, 0xc000c000c000c00, 0xcc000000cc00, 0xcc00cc00]
def g_43 : Nat := 0x40004004400
def ep_43 : Nat := 0x400400000000400000040000000000000000000000004000400000000000000000000000000040004004400
theorem epk_43 : ep_43 = edgePack m_43 g_43 := by decide +kernel
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 4, g_18)]
theorem kn_43 : KnownBin bds_43 := by
  intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_18
theorem sub_43 : ∀ b ∈ bds_43, m_43 &&& b.1 = b.1 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_43 : ∀ b ∈ bds_43, canon b.1 g_43 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_43 : Nat → List (Nat × Nat) := fun _ => []
def f_43 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV4 m_43 g_43 ep_43 0 bds_43 (dagTraceF m_43 s_43 4 f_43) (cur_43 0) s_43 4 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_43 g_43 ep_43 bds_43 0 (dagTraceF m_43 s_43 4 f_43) cur_43 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_43 : LowerBin m_43 s_43 g_43 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_43 kn_43 sub_43 gl_43 rc_43 nc_43

def m_44 : Nat := 0xf000f000f000f00
def s_44 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_44 : Nat := 0x100070007000700
def ep_44 : Nat := 0x600000000000600000000000000000000000000000000000000000001000200020002000100040004000400
theorem epk_44 : ep_44 = edgePack m_44 g_44 := by decide +kernel
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_44 : KnownBin bds_44 := by
  intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_44 : ∀ b ∈ bds_44, m_44 &&& b.1 = b.1 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_44 : ∀ b ∈ bds_44, canon b.1 g_44 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_44 : Nat → List (Nat × Nat) := fun _ => []
def f_44 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV4 m_44 g_44 ep_44 0 bds_44 (dagTraceF m_44 s_44 4 f_44) (cur_44 0) s_44 4 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_44 g_44 ep_44 bds_44 0 (dagTraceF m_44 s_44 4 f_44) cur_44 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_44 : LowerBin m_44 s_44 g_44 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_44 kn_44 sub_44 gl_44 rc_44 nc_44

def m_45 : Nat := 0xcccccccc
def s_45 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_45 : Nat := 0x44c44cc
def ep_45 : Nat := 0x40800000000000480088000000000408000000000000000000000000000004404400
theorem epk_45 : ep_45 = edgePack m_45 g_45 := by decide +kernel
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
theorem kn_45 : KnownBin bds_45 := by
  intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_12
theorem sub_45 : ∀ b ∈ bds_45, m_45 &&& b.1 = b.1 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_45 : ∀ b ∈ bds_45, canon b.1 g_45 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_45 : Nat → List (Nat × Nat) := fun _ => []
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV4 m_45 g_45 ep_45 0 bds_45 (dagTraceF m_45 s_45 4 f_45) (cur_45 0) s_45 4 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_45 g_45 ep_45 bds_45 0 (dagTraceF m_45 s_45 4 f_45) cur_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin m_45 s_45 g_45 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_45 kn_45 sub_45 gl_45 rc_45 nc_45

def m_46 : Nat := 0xff00ff00
def s_46 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_46 : Nat := 0x17005700
def ep_46 : Nat := 0x40000000000000000000000000000600020000000000120002000000000014005400
theorem epk_46 : ep_46 = edgePack m_46 g_46 := by decide +kernel
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_46 : KnownBin bds_46 := by
  intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_46 : ∀ b ∈ bds_46, m_46 &&& b.1 = b.1 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_46 : ∀ b ∈ bds_46, canon b.1 g_46 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_46 : Nat → List (Nat × Nat) := fun _ => []
def f_46 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV4 m_46 g_46 ep_46 0 bds_46 (dagTraceF m_46 s_46 4 f_46) (cur_46 0) s_46 4 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_46 g_46 ep_46 bds_46 0 (dagTraceF m_46 s_46 4 f_46) cur_46 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_46 : LowerBin m_46 s_46 g_46 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_46 kn_46 sub_46 gl_46 rc_46 nc_46

def m_47 : Nat := 0xf0f0f0f0
def s_47 : List Nat := [0x50505050, 0x30303030, 0xf000f0, 0xf0f0]
def g_47 : Nat := 0x105050f0
def ep_47 : Nat := 0x40a000000000004000a0000000000000000000000000100000000000000010505000
theorem epk_47 : ep_47 = edgePack m_47 g_47 := by decide +kernel
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_21, s_21, 4, g_21)]
theorem kn_47 : KnownBin bds_47 := by
  intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_21
theorem sub_47 : ∀ b ∈ bds_47, m_47 &&& b.1 = b.1 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_47 : ∀ b ∈ bds_47, canon b.1 g_47 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_47 : Nat → List (Nat × Nat) := fun _ => []
def f_47 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV4 m_47 g_47 ep_47 0 bds_47 (dagTraceF m_47 s_47 4 f_47) (cur_47 0) s_47 4 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_47 g_47 ep_47 bds_47 0 (dagTraceF m_47 s_47 4 f_47) cur_47 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_47 : LowerBin m_47 s_47 g_47 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_47 kn_47 sub_47 gl_47 rc_47 nc_47

def m_48 : Nat := 0xff000000ff000000
def s_48 : List Nat := [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000]
def g_48 : Nat := 0x1100000017000000
def ep_48 : Nat := 0x600000000000000000000000000000000000000000000000600000011000000120000001100000014000000
theorem epk_48 : ep_48 = edgePack m_48 g_48 := by decide +kernel
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_48 : KnownBin bds_48 := by
  intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_48 : ∀ b ∈ bds_48, m_48 &&& b.1 = b.1 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_48 : ∀ b ∈ bds_48, canon b.1 g_48 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_48 : Nat → List (Nat × Nat) := fun _ => []
def f_48 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV4 m_48 g_48 ep_48 0 bds_48 (dagTraceF m_48 s_48 4 f_48) (cur_48 0) s_48 4 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_48 g_48 ep_48 bds_48 0 (dagTraceF m_48 s_48 4 f_48) cur_48 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_48 : LowerBin m_48 s_48 g_48 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_48 kn_48 sub_48 gl_48 rc_48 nc_48

def m_49 : Nat := 0x5500550055005500
def s_49 : List Nat := [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500]
def g_49 : Nat := 0x1100150015005500
def ep_49 : Nat := 0x400400000000400000040000000000000000000000004000400000011001000100000000000000000000000
theorem epk_49 : ep_49 = edgePack m_49 g_49 := by decide +kernel
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 4, g_18)]
theorem kn_49 : KnownBin bds_49 := by
  intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_18
theorem sub_49 : ∀ b ∈ bds_49, m_49 &&& b.1 = b.1 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_49 : ∀ b ∈ bds_49, canon b.1 g_49 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_49 : Nat → List (Nat × Nat) := fun _ => []
def f_49 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV4 m_49 g_49 ep_49 0 bds_49 (dagTraceF m_49 s_49 4 f_49) (cur_49 0) s_49 4 = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_49 g_49 ep_49 bds_49 0 (dagTraceF m_49 s_49 4 f_49) cur_49 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_49 : LowerBin m_49 s_49 g_49 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_49 kn_49 sub_49 gl_49 rc_49 nc_49

def m_50 : Nat := 0x4444444444444444
def s_50 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_50 : Nat := 0x4044404444444
def ep_50 : Nat := 0x440400000000440000040000004004000400000000404000400000000000000000000000000000000000000
theorem epk_50 : ep_50 = edgePack m_50 g_50 := by decide +kernel
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8), (m_23, s_23, 4, g_23), (m_18, s_18, 4, g_18), (m_14, s_14, 4, g_14)]
theorem kn_50 : KnownBin bds_50 := by
  intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_8
  · exact lb_23
  · exact lb_18
  · exact lb_14
theorem sub_50 : ∀ b ∈ bds_50, m_50 &&& b.1 = b.1 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_50 : ∀ b ∈ bds_50, canon b.1 g_50 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_50_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_50_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
def cur_50 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_50_1 (Nat.sub p 32)) (cc_50_0 p) (Nat.blt p 32)
def f_50 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV4 m_50 g_50 ep_50 43 bds_50 (dagTraceF m_50 s_50 6 f_50) (cur_50 0) s_50 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_0 : treeBlockF 0 32 (dagCheckNodeV4 m_50 g_50 ep_50 bds_50 43 (dagTraceF m_50 s_50 6 f_50) cur_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_1 : treeBlockF 32 43 (dagCheckNodeV4 m_50 g_50 ep_50 bds_50 43 (dagTraceF m_50 s_50 6 f_50) cur_50) = true := by decide +kernel
theorem nj_50_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_50 g_50 ep_50 bds_50 43 (dagTraceF m_50 s_50 6 f_50) cur_50) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_50_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_50_1 h1 h2)
theorem nc_50 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_50 g_50 ep_50 bds_50 43 (dagTraceF m_50 s_50 6 f_50) cur_50) i = true := nj_50_1
theorem lb_50 : LowerBin m_50 s_50 g_50 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_50 kn_50 sub_50 gl_50 rc_50 nc_50

def m_51 : Nat := 0x8888888888888888
def s_51 : List Nat := [0x808080808080808, 0x88008800880088, 0x888800008888, 0x88888888]
def g_51 : Nat := 0x800080088
def ep_51 : Nat := 0x8008000000008000000800000000800080088000000080008000000000000000000000000000000000000
theorem epk_51 : ep_51 = edgePack m_51 g_51 := by decide +kernel
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16)]
theorem kn_51 : KnownBin bds_51 := by
  intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_16
theorem sub_51 : ∀ b ∈ bds_51, m_51 &&& b.1 = b.1 := by intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_51 : ∀ b ∈ bds_51, canon b.1 g_51 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_51 : Nat → List (Nat × Nat) := fun _ => []
def f_51 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV4 m_51 g_51 ep_51 0 bds_51 (dagTraceF m_51 s_51 4 f_51) (cur_51 0) s_51 4 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_51 g_51 ep_51 bds_51 0 (dagTraceF m_51 s_51 4 f_51) cur_51 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_51 : LowerBin m_51 s_51 g_51 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_51 kn_51 sub_51 gl_51 rc_51 nc_51

def m_52 : Nat := 0x2222222222222222
def s_52 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_52 : Nat := 0x2022202020222
def ep_52 : Nat := 0x200000000000220000000200002002000000020000202000202020000000000000000000000000000000000
theorem epk_52 : ep_52 = edgePack m_52 g_52 := by decide +kernel
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_52 : KnownBin bds_52 := by
  intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_52 : ∀ b ∈ bds_52, m_52 &&& b.1 = b.1 := by intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_52 : ∀ b ∈ bds_52, canon b.1 g_52 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_52 : Nat → List (Nat × Nat) := fun _ => []
def f_52 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV4 m_52 g_52 ep_52 0 bds_52 (dagTraceF m_52 s_52 4 f_52) (cur_52 0) s_52 4 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_52 g_52 ep_52 bds_52 0 (dagTraceF m_52 s_52 4 f_52) cur_52 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_52 : LowerBin m_52 s_52 g_52 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_52 kn_52 sub_52 gl_52 rc_52 nc_52

def m_53 : Nat := 0x5a005a005a005a00
def s_53 : List Nat := [0xa000a000a000a00, 0x1200120012001200, 0x5a0000005a00, 0x5a005a00]
def g_53 : Nat := 0x1000120012005200
def ep_53 : Nat := 0x200400000000200000040000000000000000000000000000000000010001200120002000000000000000000
theorem epk_53 : ep_53 = edgePack m_53 g_53 := by decide +kernel
def bds_53 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_53 : KnownBin bds_53 := by intro b hb; simp [bds_53] at hb
theorem sub_53 : ∀ b ∈ bds_53, m_53 &&& b.1 = b.1 := by intro b hb; simp [bds_53] at hb
theorem gl_53 : ∀ b ∈ bds_53, canon b.1 g_53 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_53] at hb
def cc_53_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xb41682d05a0b4168292520a41482904a490320230c608c108a104207c4f81f03a2740e81b1341680c841c001 0xe24c6d20345319280b83c581a2a0b140488838449e1e4f0e260602c2c12124f08268303c141a040402249da3fd91dea8df4467993fc89dda4de8267392f9495c449df246f03f741db00dd3066902f40159a09ca046381f100d8605c1026000f 11 2047 5 31 10 1023 17 131071
def cc_53_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb0b0b09490909090747070707070707070545050505034292821202012101002 0x3f271f134f41c780d3a251c924e0146e09314998240bc265c102c2795934a80c520526271323c901e460c210310014 8 255 3 7 10 1023 17 131071
def cur_53 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_53_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_53_0 p) (Nat.blt p 32)
def f_53 : Nat → Nat × Nat := unpackForestF 0xf138f134f038f034063fdd28dd24dc28dc24063b06370633053f053bba4cba40b84cb8400537a53ca534a418a4140533052f9a3c052b8c3c8c300527801880140523043f043b664c6640654c65400437503c5034502c50240433042f453c042b393c393004272c2c2c240423213c2134041f143c1434041b041709240413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV4 m_53 g_53 ep_53 64 bds_53 (dagTraceF m_53 s_53 5 f_53) (cur_53 0) s_53 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53_0 : treeBlockF 0 32 (dagCheckNodeV4 m_53 g_53 ep_53 bds_53 64 (dagTraceF m_53 s_53 5 f_53) cur_53) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53_1 : treeBlockF 32 64 (dagCheckNodeV4 m_53 g_53 ep_53 bds_53 64 (dagTraceF m_53 s_53 5 f_53) cur_53) = true := by decide +kernel
theorem nj_53_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_53 g_53 ep_53 bds_53 64 (dagTraceF m_53 s_53 5 f_53) cur_53) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_53_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_53_1 h1 h2)
theorem nc_53 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_53 g_53 ep_53 bds_53 64 (dagTraceF m_53 s_53 5 f_53) cur_53) i = true := nj_53_1
theorem lb_53 : LowerBin m_53 s_53 g_53 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_53 kn_53 sub_53 gl_53 rc_53 nc_53

def m_54 : Nat := 0xf0f0f0f0f0f0f0f0
def s_54 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_54 : Nat := 0x10101070105050f0
def ep_54 : Nat := 0x40408000000060000040a000000060004000a0000000000000000010101020100000001010104010505000
theorem epk_54 : ep_54 = edgePack m_54 g_54 := by decide +kernel
def bds_54 : List (Nat × List Nat × Nat × Nat) := [(m_38, s_38, 7, g_38)]
theorem kn_54 : KnownBin bds_54 := by
  intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_38
theorem sub_54 : ∀ b ∈ bds_54, m_54 &&& b.1 = b.1 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_54 : ∀ b ∈ bds_54, canon b.1 g_54 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_54 : Nat → List (Nat × Nat) := fun _ => []
def f_54 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV4 m_54 g_54 ep_54 0 bds_54 (dagTraceF m_54 s_54 7 f_54) (cur_54 0) s_54 7 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_54 g_54 ep_54 bds_54 0 (dagTraceF m_54 s_54 7 f_54) cur_54 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_54 : LowerBin m_54 s_54 g_54 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_54 kn_54 sub_54 gl_54 rc_54 nc_54

def m_55 : Nat := 0x3333333333333333
def s_55 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_55 : Nat := 0x1113133313131333
def ep_55 : Nat := 0x200000000000220000000200002002000000020000202000202020000000000000000001110100010101000
theorem epk_55 : ep_55 = edgePack m_55 g_55 := by decide +kernel
def bds_55 : List (Nat × List Nat × Nat × Nat) := [(m_36, s_36, 5, g_36)]
theorem kn_55 : KnownBin bds_55 := by
  intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_36
theorem sub_55 : ∀ b ∈ bds_55, m_55 &&& b.1 = b.1 := by intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_55 : ∀ b ∈ bds_55, canon b.1 g_55 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_55 : Nat → List (Nat × Nat) := fun _ => []
def f_55 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV4 m_55 g_55 ep_55 0 bds_55 (dagTraceF m_55 s_55 5 f_55) (cur_55 0) s_55 5 = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_55 g_55 ep_55 bds_55 0 (dagTraceF m_55 s_55 5 f_55) cur_55 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_55 : LowerBin m_55 s_55 g_55 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_55 kn_55 sub_55 gl_55 rc_55 nc_55

def m_56 : Nat := 0xff00ff00ff00ff00
def s_56 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_56 : Nat := 0x1100170017005700
def ep_56 : Nat := 0x600400000000600000040000000000000000000000006000600020011001200120002001100140014005400
theorem epk_56 : ep_56 = edgePack m_56 g_56 := by decide +kernel
def bds_56 : List (Nat × List Nat × Nat × Nat) := [(m_30, s_30, 5, g_30), (m_40, s_40, 5, g_40), (m_48, s_48, 5, g_48), (m_44, s_44, 5, g_44), (m_46, s_46, 5, g_46), (m_43, s_43, 5, g_43), (m_49, s_49, 5, g_49), (m_27, s_27, 6, g_27), (m_53, s_53, 6, g_53), (m_18, s_18, 4, g_18)]
theorem kn_56 : KnownBin bds_56 := by
  intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_30
  · exact lb_40
  · exact lb_48
  · exact lb_44
  · exact lb_46
  · exact lb_43
  · exact lb_49
  · exact lb_27
  · exact lb_53
  · exact lb_18
theorem sub_56 : ∀ b ∈ bds_56, m_56 &&& b.1 = b.1 := by intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_56 : ∀ b ∈ bds_56, canon b.1 g_56 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_56 : Nat → List (Nat × Nat) := unpackCursorV4 0x60001 0x4f4f5e96dd1d7a19e4f6c96791e3219e3f7c7678dd7198d4f2a96351caa18d3f2a7634dca998d2f2a56349ca91a44f488e90fd21ba42f384e507c60b801f 12 4095 6 63 10 1023 15 32767
def f_56 : Nat → Nat × Nat := unpackForestF 0x1f 1 5
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV4 m_56 g_56 ep_56 1 bds_56 (dagTraceF m_56 s_56 7 f_56) (cur_56 0) s_56 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56 : treeBlockF 0 1 (dagCheckNodeV4 m_56 g_56 ep_56 bds_56 1 (dagTraceF m_56 s_56 7 f_56) cur_56) = true := by decide +kernel
theorem nc_56 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_56 g_56 ep_56 bds_56 1 (dagTraceF m_56 s_56 7 f_56) cur_56) i = true := fun _ h1 h2 => treeBlockF_at nb_56 h1 h2
theorem lb_56 : LowerBin m_56 s_56 g_56 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_56 kn_56 sub_56 gl_56 rc_56 nc_56

def m_57 : Nat := 0xf0f0f0f0f0f0f0f
def s_57 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_57 : Nat := 0x107070f070f070f
def ep_57 : Nat := 0x608000000000608000000000006000800080008000000000000000001020200020002000104040004000400
theorem epk_57 : ep_57 = edgePack m_57 g_57 := by decide +kernel
def bds_57 : List (Nat × List Nat × Nat × Nat) := [(m_41, s_41, 7, g_41)]
theorem kn_57 : KnownBin bds_57 := by
  intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_41
theorem sub_57 : ∀ b ∈ bds_57, m_57 &&& b.1 = b.1 := by intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_57 : ∀ b ∈ bds_57, canon b.1 g_57 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_57 : Nat → List (Nat × Nat) := fun _ => []
def f_57 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV4 m_57 g_57 ep_57 0 bds_57 (dagTraceF m_57 s_57 7 f_57) (cur_57 0) s_57 7 = true := by decide +kernel
theorem nc_57 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_57 g_57 ep_57 bds_57 0 (dagTraceF m_57 s_57 7 f_57) cur_57 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_57 : LowerBin m_57 s_57 g_57 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_57 kn_57 sub_57 gl_57 rc_57 nc_57

def m_58 : Nat := 0x5555555555555555
def s_58 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_58 : Nat := 0x1115155515555555
def ep_58 : Nat := 0x440400000000440000040000004004000400000000404000400000011101000100000000000000000000000
theorem epk_58 : ep_58 = edgePack m_58 g_58 := by decide +kernel
def bds_58 : List (Nat × List Nat × Nat × Nat) := [(m_50, s_50, 7, g_50)]
theorem kn_58 : KnownBin bds_58 := by
  intro b hb; simp only [bds_58, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_50
theorem sub_58 : ∀ b ∈ bds_58, m_58 &&& b.1 = b.1 := by intro b hb; simp only [bds_58, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_58 : ∀ b ∈ bds_58, canon b.1 g_58 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_58, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_58 : Nat → List (Nat × Nat) := fun _ => []
def f_58 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV4 m_58 g_58 ep_58 0 bds_58 (dagTraceF m_58 s_58 7 f_58) (cur_58 0) s_58 7 = true := by decide +kernel
theorem nc_58 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_58 g_58 ep_58 bds_58 0 (dagTraceF m_58 s_58 7 f_58) cur_58 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_58 : LowerBin m_58 s_58 g_58 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_58 kn_58 sub_58 gl_58 rc_58 nc_58

def m_59 : Nat := 0xff00ff00ff00ff
def s_59 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_59 : Nat := 0x17007f005f00ff
def ep_59 : Nat := 0x48008000000068000000a0000000000000000000060008000a000000120020000000000014004000500000
theorem epk_59 : ep_59 = edgePack m_59 g_59 := by decide +kernel
def bds_59 : List (Nat × List Nat × Nat × Nat) := [(m_31, s_31, 7, g_31)]
theorem kn_59 : KnownBin bds_59 := by
  intro b hb; simp only [bds_59, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_31
theorem sub_59 : ∀ b ∈ bds_59, m_59 &&& b.1 = b.1 := by intro b hb; simp only [bds_59, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_59 : ∀ b ∈ bds_59, canon b.1 g_59 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_59, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_59 : Nat → List (Nat × Nat) := fun _ => []
def f_59 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_59 : dagCheckRootsV4 m_59 g_59 ep_59 0 bds_59 (dagTraceF m_59 s_59 7 f_59) (cur_59 0) s_59 7 = true := by decide +kernel
theorem nc_59 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_59 g_59 ep_59 bds_59 0 (dagTraceF m_59 s_59 7 f_59) cur_59 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_59 : LowerBin m_59 s_59 g_59 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_59 kn_59 sub_59 gl_59 rc_59 nc_59

def m_60 : Nat := 0xffff0000ffff
def s_60 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_60 : Nat := 0x177f000057ff
def ep_60 : Nat := 0x4080000000000000000000000068000000a8000006080000020000001220000002000000144000005400
theorem epk_60 : ep_60 = edgePack m_60 g_60 := by decide +kernel
def bds_60 : List (Nat × List Nat × Nat × Nat) := [(m_29, s_29, 7, g_29)]
theorem kn_60 : KnownBin bds_60 := by
  intro b hb; simp only [bds_60, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_29
theorem sub_60 : ∀ b ∈ bds_60, m_60 &&& b.1 = b.1 := by intro b hb; simp only [bds_60, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_60 : ∀ b ∈ bds_60, canon b.1 g_60 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_60, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_60 : Nat → List (Nat × Nat) := fun _ => []
def f_60 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsV4 m_60 g_60 ep_60 0 bds_60 (dagTraceF m_60 s_60 7 f_60) (cur_60 0) s_60 7 = true := by decide +kernel
theorem nc_60 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_60 g_60 ep_60 bds_60 0 (dagTraceF m_60 s_60 7 f_60) cur_60 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_60 : LowerBin m_60 s_60 g_60 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_60 kn_60 sub_60 gl_60 rc_60 nc_60

def m_61 : Nat := 0xffff0000ffff0000
def s_61 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_61 : Nat := 0x11170000175f0000
def ep_61 : Nat := 0x64800000000000000000000000600000048000000060000060a000011120000120000001114000014500000
theorem epk_61 : ep_61 = edgePack m_61 g_61 := by decide +kernel
def bds_61 : List (Nat × List Nat × Nat × Nat) := [(m_41, s_41, 7, g_41)]
theorem kn_61 : KnownBin bds_61 := by
  intro b hb; simp only [bds_61, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_41
theorem sub_61 : ∀ b ∈ bds_61, m_61 &&& b.1 = b.1 := by intro b hb; simp only [bds_61, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_61 : ∀ b ∈ bds_61, canon b.1 g_61 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_61, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_61 : Nat → List (Nat × Nat) := fun _ => []
def f_61 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_61 : dagCheckRootsV4 m_61 g_61 ep_61 0 bds_61 (dagTraceF m_61 s_61 7 f_61) (cur_61 0) s_61 7 = true := by decide +kernel
theorem nc_61 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_61 g_61 ep_61 bds_61 0 (dagTraceF m_61 s_61 7 f_61) cur_61 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_61 : LowerBin m_61 s_61 g_61 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_61 kn_61 sub_61 gl_61 rc_61 nc_61

def g_62 : Nat := 0x1117177f175f57ff
def ep_62 : Nat := 0x648408000000668000040a000060068004800a800060608060a020011121220120002001114144014505400
theorem epk_62 : ep_62 = edgePack fullMask g_62 := by decide +kernel
def bds_62 : List (Nat × List Nat × Nat × Nat) := [(m_34, s_34, 7, g_34), (m_61, s_61, 8, g_61), (m_60, s_60, 8, g_60), (m_59, s_59, 8, g_59), (m_56, s_56, 8, g_56), (m_57, s_57, 8, g_57), (m_58, s_58, 8, g_58), (m_37, s_37, 7, g_37), (m_38, s_38, 7, g_38), (m_54, s_54, 8, g_54), (m_33, s_33, 7, g_33), (m_41, s_41, 7, g_41), (m_50, s_50, 7, g_50), (m_31, s_31, 7, g_31), (m_35, s_35, 7, g_35), (m_29, s_29, 7, g_29), (m_45, s_45, 5, g_45), (m_39, s_39, 7, g_39), (m_46, s_46, 5, g_46), (m_55, s_55, 6, g_55), (m_47, s_47, 5, g_47), (m_51, s_51, 5, g_51), (m_52, s_52, 5, g_52), (m_32, s_32, 5, g_32), (m_40, s_40, 5, g_40), (m_30, s_30, 5, g_30), (m_27, s_27, 6, g_27), (m_28, s_28, 5, g_28), (m_43, s_43, 5, g_43), (m_42, s_42, 5, g_42)]
theorem kn_62 : KnownBin bds_62 := by
  intro b hb; simp only [bds_62, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_34
  · exact lb_61
  · exact lb_60
  · exact lb_59
  · exact lb_56
  · exact lb_57
  · exact lb_58
  · exact lb_37
  · exact lb_38
  · exact lb_54
  · exact lb_33
  · exact lb_41
  · exact lb_50
  · exact lb_31
  · exact lb_35
  · exact lb_29
  · exact lb_45
  · exact lb_39
  · exact lb_46
  · exact lb_55
  · exact lb_47
  · exact lb_51
  · exact lb_52
  · exact lb_32
  · exact lb_40
  · exact lb_30
  · exact lb_27
  · exact lb_28
  · exact lb_43
  · exact lb_42
theorem sub_62 : ∀ b ∈ bds_62, fullMask &&& b.1 = b.1 := by intro b hb; simp only [bds_62, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_62 : ∀ b ∈ bds_62, canon b.1 g_62 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_62, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_62_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x93e518c17d86e5380866782867384a72018707196e5226687d61e4a5fd215d22b5735f5264d4d35344b884202b3df41378673294f2a881247611f84f19c5c10e8e0dc320ab3105d4e03d200013c00001 0x6d6f06d6706c6f06c6b06c6706c630bc5b0ac5703b6f03b6b03b6703b6303b5b03b5703b4f03b4b03b4703b4303a6f03a6e02a6b02a6a03a6702a6603a6303a620ca5b0ca5a0ca570ca560ba4f08a4e0aa4b05a4a0aa4705a460ba4308a4201a3f01a3e01a3701a3301a320196f0196b01967019630195b019570194f0194b01947019430193f0193b01937019330192f0192d0192b01929019270192501923019210686f068670785a0c8560784f078470383f0383e01837038320482f0482d01827018250181f0181706e7f06e7706d7f06d7b06d7706d730bd6b0ad6703c7f03c7e03c7b06c7a03c7703c7603c7306c7203c6b0cc6a03c6703c6603c5f03c5e03c5b05c5a03c5703c5603c5308c5203b7f03b7b03b7703b7303b6b03b6703b5f03b5b03b5703b5301a7f06a7e01a7d01a7701a7501a7301a7201a6b01a6a01a670ca6601a5f01a5b01a5701a5301a4f01a4d01a4b01a4901a4701a4501a4301a4101a3f01a3b01a3701a330197702976019750196b0196a019670c9660195f0895e0195b0195a019570595601953019520194f0394e0194d1e14c0194b0194a019490194801947039460194503944019430194201941019400193f0393e0193b0193a019370393601933019320192f0192e0192d0687f068770786a0c8660785f078570384f0384e0484d0383f0383e038320182f018270181f0181d018170781507d6f08d6705c6f08c6b05c6707c6308c5b05c5703b6f03b6b03b6703b6303b5b03b5703b4f03b4b03b4703b4307a6f07a6e14a6b06a6a14a6706a6607a6307a6208a5b08a5a08a5708a5603a4f02a4e03a4b03a4a03a4703a4602a4302a4201a3f01a3e01a3701a3301a320196f0196b01967019630195b019570194f0194b01947019430193f0193b01937019330192f0192d0192b01929019270192501923019210786f078670885a088560884f058470383f0383e01837038320482f0482e0482d0182701825018220181f0181707d6f08d6705c6f08c6b05c6707c6308c5b05c5703b6f03b6e03b6b06b6a03b6703b6603b6307b6203b5b08b5a03b5703b5603b4f03b4e03b4b05b4a03b4905b4803b4703b4603b4308b4203b4103a6f03a6b03a6703a6303a5b03a5703a4f03a4b03a4703a430196f0196b01967019630195b019570194f0194b0194a0194705946019430193f0393e0193d0293c0193b019390193701935019330193201931019300192f0192b01927019230786f1086b10867078630885b0885a08857088560284f05847088430383f0383e0483d0183b018390183701835018330183201831018300382f0382e0382b03829018270382303822108210181f018170181307e7f08e7705d7f08d7b05d7707d7308d6b05d6703c7f03c7e03c7b06c7a03c7703c7603c7307c7203c6b08c6a03c6703c6603c5f03c5e03c5b05c5a03c5905c5803c5703c5603c5308c5203c5108c5003b7f03b7b03b7703b7303b6b03b6703b5f03b5b03b5703b5301a7f01a7b01a7701a7301a6b01a6701a5f01a5d01a5b01a5a01a5705a5601a5501a4f03a4e01a4d02a4c01a4b01a4901a4701a4501a4301a4201a4101a4001a3f01a3b01a3701a330197f0797e0197b0197a019770697601973019720196b0196a01967089660195f0295e0195d0194f0394e0194d1c14c0194b0194a019490194801947039460194503944019430194201941019400193f0393e0193b0193a019370393601933019320192f0192e0192d0787f078770886a088660885f058570384f0384e0484d0383f0383e038320182f018270181f0181d0181a01817018160a8151b01407d6f0ed6707c6f1f46b0ac6707c630ec5b0ac5703b6f03b6e03b6b06b6a03b6703b6603b6307b6203b5b0eb5a03b5703b5603b4f03b4e03b4b05b4a03b4703b4603b4308b4203a6f03a6b03a6703a6303a5b03a5703a4f03a4b03a4703a430796f1d16b0f967079630e95b0e9570f94f0a94b0a9471a1430393f0293d0393b01939039370293503933019310392f0392b03927039230786f078670d85a0e8560a84f0a8470383f0383e0483d0382f0382e038220d81f0d81707b5f07b5b07b5707b5303a5f04a5b03a5704a5303a3f04a3b03a3704a330795f0795b07957079530893f0893b08937089330492f0392b039270492307b5f07b5b07b5707b5303a5f04a5b03a5704a5303a3f04a3b03a3704a330795f0795b07957079530a93f0a93b0a9370a9330492f0392b03927049230382607c6f07c6b07c6707c6303b6f04b6b03b6704b6303b4f04b4b03b4704b4307a6f07a6b07a6707a630aa4f0aa4b0aa470aa4304a3f03a3b03a3704a33039360786e068661805c170540884e058460483e0182e0282606e7f06e7706d7f06d7b06d7706d730bd6b0ad6703c7f06c7e03c7d03c7703c7504c7304c7204c6b04c6a03c670cc6603c5f04c5b03c5704c5303b7703b7603b7504b6b04b6a04b670cb6604b5f08b5e04b5b04b5a04b5705b5604b5304b5204b4f04b4e04b4d01a7f01a7b01a7701a7301a6b01a6701a5f01a5b01a5a01a570aa5601a5301a4f01a4b01a4701a4301a3f01a3d01a3b01a3901a3701a3501a3301a310197f0697e0197b0197a019770697601973019720196b0196a019670c9660195f0895e0195b0195a019570595601953019520194f0494e0194b0194a019470394601943019420193f0493e0193d0493c0193b0193a01939019380193704936019350f934019330193201931019300687f068770785f078570484f038470483f0483d04837078350182a018270182601817018160281507d6f11d6707c6f0bc6b0ac6707c630bc5b0ac5707b6f1536b0db6707b6311b5b0db570bb4f0ab4b0ab470bb4301a6f01a6b01a6701a6301a5b01a5701a4f01a4b01a4a01a470aa4601a4301a3f01a3b01a3701a330196f0796e0196b0196a019670696601963019620195b0195a019570f9560194f0894e0194b0194a019470594601943019420193f0493e0193b0193a019370393601933019320786f078670a84f0a8470d83f0d8370182a018270182601817018160281507c6f07c6b07c6707c6307b6f07b6b07b6707b630ab4f0ab4b0ab470ab4302a6f01a6b02a6701a6302a4f01a4b02a4701a4302a3f01a3b02a3701a330a9460192e0786e068660884e058460483e038360282606c6f06c6b06c6706c6306b6f06b6b06b6706b6308b4f0ab4b0ab4708b4302a6f01a6b02a6702a4f01a4b02a4701a4302a3f01a3b02a3701a330296f0296e0894f0894e0a94b0594a0a9470594608943089421593f0493e0d93b0393a0d9370393615933049320192f0192e06d7e06d6e06c7f05c7d06c7b06c7906c7705c7506c7308c7106c6f06c6b06c6706c6306b7f03b7d06b7b04b7906b7703b7506b7304b7106b6f06b6b06b6706b6308b4f0ab4b0ab4708b4302a7f02a7e02a7d02a7c02a7b06a7a02a7906a7802a7702a7602a7502a7402a7306a7202a711227002a6f02a6e02a6b06a6a02a6702a6602a6306a6202a4f02a4e02a4b05a4a02a4702a4602a4308a4202a3f02a3e02a3b03a3a02a3702a3602a3304a320297f0297d0197b01979029770297501973019710296f0196b02967019630294f0194b0a94a0294702946019430293f0193b02937019330b8460182e0181e06d6f06d6705c6f02c6b05c6706c6308c5b05c5706b6f06b6b06b6706b6308b5b08b5708b4f05b4b05b4708b4302a6f01a6b02a6701a6301a5b02a5702a4f01a4b02a4701a4302a3f01a3b02a3701a330296f0296e0596b0596a029670296602963029620895b0895a08957089560294f0294e0294b0294a029470294607943079421493f0493e0d93b0393a0d9370393614933049320192f0192e0292701923019220686f068670784f058470783f078370182f028270181f0181d068170181506d6f06d6705c6f02c6b05c6706c6308c5b05c5706b6f06b6b05b6708b5b08b5a08b5708b5607b4f05b4707b4306a6f06a6b06a6706a6308a5b08a5708a4f05a4b05a4708a430da3f10a3b0da3710a330296f0296b0696a0296702966029630295b029570294f0294e0294b0294702943089420293f0293e0193b0193902937029330693201931019300292f0292b02927029230286f0186b02867018630185b028570284f0184b0584a0284702846018430283f0283e0183b0183902837018330b832018310282f0182b028270182306e7f06e7705d7f06d7e05d7d05d7705d7506d7306d7208d6b08d6a05d6708d6605c7705c7605c7506c6b06c6a06c6708c6606c5f07c5e06c5d06b7f06b7b06b7706b7308b6b08b6708b5f05b5b05b5708b5306b4f03b4d06b4b04b4906b4703b4506b4304b4102a7f02a7e02a7b06a7a02a7702a7602a7306a7202a6b08a6a02a6702a6602a5f02a5e02a5b05a5a02a5702a5602a5308a5202a4f02a4e02a4d02a4c02a4b06a4a02a491024802a4702a4602a4502a4402a4306a4202a4106a4002a3f02a3e02a3b03a3a02a3702a3602a3304a320297f0197b02977019730196b029670295f0195b0595a0295702956019530294f0294d0194b0694a01949019480294702946029450294401943019410293f0193b02937019330687f068770786a088660785f0585a05857058560684f0684d0684a0684706846078450f0440783f078370182f0182e0182d0181f0181e0181205c6f08c6b05c6707c6307b6f0cb6b0cb6707b6308b4f05b4b05b4708b4302a6f01a6b02a6701a6302a4f02a4701a4302a3f01a3b02a3701a330796f0796e0c96b0696a0c96706966079630796202947029461493f0493e0d93b0393a0d9370393614933049320192f0192e05c6f08c6b05c6707c6307b6f0cb6b0cb6707b6307a6f0ca6b0ca6707a6308a4f05a4b05a4708a430da3f10a3b0da3710a330296f0296b02967029630294f0294e0294b0294702943089420293f0293e0193b0193902937029330893201931019300292f0292b02927029230286f0186b02867018630284f0184b0584a0284702846018430283f0283e0183b0183902837018330b832018310282f0182b028270182305d7f08d7b08d7a05d770ad7607d7305d6507c7f07c7e08c7b06c7a08c7706c7607c7307c7205c6507b7f0cb7b0cb7707b7308b5f05b5b05b5708b5308b4f03b4d08b4b04b4908b4703b4508b4304b4102a7f02a7e02a7b06a7a02a7702a7602a7307a7202a5f02a5e02a5b05a5a02a5702a5602a5308a5202a4f02a4e02a4d02a4c02a4b08a4a02a490d24802a4702a4602a4502a4402a4308a4202a4108a4002a3f02a3e02a3b03a3a02a3702a3602a3304a320297f0197b02977019730295f0195b0595a0295702956019530294f0294d0194b0894a01949019480294702946029450294401943019410293f0193b029370193305856088460c0440182e0181e06d6f06d6706c6f06c6b06c6706c630cc5b0ac5703b6f02b6b03b6704b6304b5b03b5703b4f04b4b03b4704b4302a6f01a6b02a6701a6301a5b02a5702a4f01a4b02a4701a4302a3f01a3b02a3701a330296f0296e0396b0396a029670296602963029620c95b0c95a0c9570c9561294f0894e0a94b0594a0a9470594612943089420293f0293e0293b0293a029370293604933049320192f0192e0292701923019220686f068670785a0c8560784f078470483f038370182f028270181f0181d048170181506e7f06e7706d7f06d7b06d7706d730cd6b0ad6703c7f06c7e03c7d03c7703c7504c7304c7204c6b04c6a03c670cc6603c5f04c5b03c5704c5303b7703b7603b7504b6b04b6a04b670cb6604b5f08b5e04b5b04b5a04b5705b5604b5304b5204b4f04b4e04b4d02a7f02a7e02a7b06a7a02a7702a7602a7306a7202a6b0ca6a02a6702a6602a5f02a5e02a5b05a5a02a5702a5602a5308a5202a4f02a4e02a4b03a4a02a4702a4602a4304a4202a3f02a3e02a3d02a3c02a3b04a3a02a390a23802a3702a3602a3502a3402a3304a3202a3104a300297f0197b02977019730196b029670295f0195b0a95a0295702956019530294f0194b02947019430293f0293d0193b01939029370293501933019310687f068770786a0c8660785f0785a078570b8560484f038470483f0483d04837078350182f0182e0182d0181f0181e0181207d7f08d7b0ad7707d7303c7f04c7b04c7a03c770cc7604c7303c6503c5f04c5b03c5704c5304b7f07b7e04b7b04b7a04b7706b7604b7304b7203b6504b5f08b5e04b5b04b5a04b5705b5604b5304b5202a7f02a7e02a7b06a7a02a7702a7602a7307a7202a5f02a5e02a5b05a5a02a5702a5602a5308a5202a4f02a4e02a4b03a4a02a4702a4602a4304a4202a3f02a3e02a3d02a3c02a3b04a3a02a390ea3802a3702a3602a3502a3402a3304a3202a3104a300297f0197b02977019730295f0195b0a95a0295702956019530294f0194b02947019430293f0293d0193b01939029370293501933019310b8560182e0181e07d6f08d6705c6f08c6b05c6707c6308c5b05c5703b6f04b6b03b6704b6304b5b03b5703b4f04b4b03b4702b4302a6f01a6b02a6701a6301a5b02a5702a4f01a4b02a4701a4302a3f01a3b02a3701a330796f0796e1296b0696a129670696607963079620895b0895a08957089560294f0294e0294b0294a029470294603943039420293f0293e0293b0293a029370293604933049320192f0192e0292701923019220786f078670885a088560884f058470483f038370182f028270181f0181d048170181507d6f08d6705c6f08c6b05c6707c6308c5b05c5703b6f04b6b03b6704b6304b5b03b5703b4f04b4b03b4702b4307a6f10a6b10a6707a6308a5b08a5a08a5708a5603a4f05a4708a4304a3f03a3704a330296f0296b0696a0296702966029630295b0895a02957029560294f0294e0294b02949029470294308942029410293f0293e0293b0293902937029330493202931049300292f0292e0192b0192902927029230492201921019200286f0186b02867018630185b028570284f0184b0584a0284702846018430283f0183b02837018330282f0282e0182b0182902827018230b8220182107e7f08e7705d7f08d7b05d7707d7308d6b05d6703c7f04c7b03c7704c7304c6b03c6703c5f03c5d04c5b04c5a03c5705c5603c5504b7f07b7e04b7b04b7a04b7706b7604b7304b7204b6b04b6a04b6708b6603b5f03b5e03b5d04b4f04b4e04b4d02a7f02a7e02a7b06a7a02a7702a7602a7307a7202a6b08a6a02a6702a6602a5f02a5e02a5b05a5a02a5905a5802a5702a5602a5308a5202a5108a5002a4f02a4e02a4b03a4a02a4903a4802a4702a4602a4304a4202a4104a4002a3f02a3e02a3d02a3c02a3b04a3a02a390723802a3702a3602a3502a3402a3304a3202a3104a300297f0197b02977019730196b029670295f0195b0595a0295702956019530294f0194b02947019430293f0293d0193b0493a01939019380293702936029350293401933019310787f078770886a088660885f0585a05857058560484f038470483f0483d0483a04837048360a835060340182f0182e0182d0181f0181e0181207c6f08c6b0ac6707c6307b6f0cb6b0cb6707b6308b4f0ab4b0ab4708b4302a6f01a6b02a6701a6302a5502a4f01a4b02a4701a4302a3f01a3b02a3701a330796f0796e0c96b0696a0c967069660796307962029550894f0894e0a94b0594a0a9470594608943089421093f0493e0d93b0393a0d93703936139330493207b6f08b6b0ab6707b6305b5507a6f0ca6b0ca6707a630da4508a3f0aa3b0aa3708a330296f0296b0696a02967029660296301959029490293f0293e0293b0293702933089320292f0292b0392a0292702926029230286f0186b0286701863018590283f0183b0a83a0283702836018330282f0182b028270182307d6f1156707c6f0e46b0ac6707c630b45b0ac5707b6f0936b0db6707b630835b0db570db4f0ab4b0ab470534302a6f02a6e02a6b06a6a02a6702a6602a6307a6202a5b0425a02a5702a5602a4f02a4e02a4b05a4a02a4702a4602a4308a4202a3f02a3e02a3b03a3a02a3702a3602a3304a320296f0196b02967019630195b029570294f0194b0a94a0294702946019430293f0193b02937019330786f078670f85a030560a84f0b84a0a8470b8460d83f0d8370182f0182e0182d0181f0181e0181207c6f07c6b07c6707c6307b6f07b6b07b6707b630ab4f0ab4b0ab470ab4301a6f01a6b01a6701a6301a4f01a4b01a4701a4301a3f01a3b01a3701a33019260786e068660884e058460483e038360182ef745ff645bf4457eb453e935fe735be6357e5353e234fe034bdf347de343dd25fdb25bda257d4253d324fd124bce247cb243ca23fc523bc4237c2233b715fb515bb0157af153ae14faa14ba7147a41439f13f9613b84137671335c12f5b12b56127541234605f4505b3e0573d0533c04f3b04b3a047390433703f3603b2f0372c0332202f2102b19027160231401f1301b02017010130003f 20 1048575 8 255 11 2047 20 1048575
def cc_62_1 : Nat → List (Nat × Nat) := unpackCursorV4 0x8c4951488220d0c2fa483a4b03481e77eba9ca73242e0eadaaaeb3b346299ab59f5536fa81ca4eb309a4652c11238bf413bc731ecceaf173d3269fc417786bae8997c0ea90194801f668007d 0x363787c6d0d8ce1b194362f86c570d6de16db435b586b690d6ce16d9435b187b610d6be1ad6c35ab86b53196962ad1c353783a6d0d4d6129a4353383a650d4c612984352f86a5b0d4ae1a94c65258ca471b47e2a8ec551bc32330d2de0a5b434b5819690d2ce0a59434b1819610d2be1a56c34ab86953192963251c7c9f8a93b1526f044cc7c978d92b1b24efc48c34378686e0f0da1a17c342f068520f094321183c1f878370f05e1e09c3c0f878170f8de1b1ac363387c630f6de1adac35b387b631569e2ad2c55a38ab430f4de1a9ac353387a631549e2a92c55238aa431b47e368ec6d1b8da330d2cc1e1b84427058460907c0e0d80c17028260f8dc1b1983db788b6b116ce1ed8c45a485b450f4de329ac653387a631b4aa129241d2288a3f11476228dc45198796f192d63259c3cb1819490528a224fc449d88937112663a4bc6c958d9271d2461f1bc3e3587c670f8c61edbc3db587b670f6c622d3c55a58ab47116861e9bc3d3587a670f4c62293c55258aa4711486368fc6d1d8da371b4661e59844a70d9361f24c1e1b834330884e0b08c120f81c1b0182e0504c1f5b836b307b6f116d62ad9c3db188b590b6aa1e9bc65358ca670f4c6129641d2a8da451147e2a8ec551b88a330f2de325ac64b387963032b20a554449f8a93b1526e224cc7c978d92b1b24e4648c64330883e1d04c0c0583e3787c6b0f8ce1f18c3db787b6b0f6ce1ed8c45a788b4b1168e22d0c3d3787a6b0f4ce1e98c452788a4b1148e2290c6d1f8da3b1b46e368cc3c37068661109c16118241f038360305c0a098373f86e770bafe1b5ec2ebb86d7311ad61759c363f86c7e0d8f61b1e8363b86c760d8e61b1c8463588c6a118ce231981dbf86b7e076fa0eddc1dba84b73096e412dac25b503b67116cc0ed7c25ad83b57096a60ed3c1da684b4b096920ed1c1da284b43096820e9dc1d3b03a75094d6129a8253388a66094be22978252d84a5a094ae16958252984a520949e22938252688a4c0949612928252484a480948e2291825228aa440948612908252084a400947e128f8251e8697f0d2f61a5dc34b98896b112ce2257c2cad85957112a62253c14a68894b032922251c14a28894303282124fc1c9d8393709266124bc14968492b032521249c149284923032421a1fc343b8786a110cc161682c2b858560b08e161182c228483f0706e120bc2416848270f04a1e07c3c0b87d6f11ace171bc463585c670f8c62316c2e2b87b6f0f6dc22dac35b508b670d6cc1ed8c3db108b5b116b422d5c45ab07a6f704d63699c3d3188a5b114ae2293c2d2585a4711486228fc1d1e88a3b09472228dc1d1a88a33094621e5bc5cb58f9670f2c62256c44ab8894f0b2961651c44a18893f0527a224ec0c9c889370526a224cc0c988f92f172563649c5c918786f0f0ce22168442b0584a0b08e161182c1b858360b06a2a0bc54138a81f1502e171bc2e3585c670b8c61edbc3db587b670f6c616d3c2da585b470b6861e9bc3d3587a670f4c61693c2d2585a470b4862e8fc5d1d8ba3717466165385c930786e0d0cc16118241f038360305c0a0982e3785c6b0b8ce16dbc2db705b4f0b69c1a9bc353586a670d4c61693c2d2585a470b486368fc1d1e95a3b09472368dc1d1a95a33094621a5bc34b5869670d2c61653c2ca5859470b2862e4fc149e8b93b032722e4dc149a8b933032622e4bc5c958b927172461b5f836b705c7f0b8fc171f42e3e05c7b0d8f4171e4363c05c770b8ec171d42e3a05c730d8e4171c5aa3805c6f0b8dc171ac363505c670b8cc1718c363105b7f0b6fa16dec2dbc85b770b6ea16dcc2db885b6f0b6d616d9c2db186a7f074fa1a9ec253c86a77074ea1a9cc253886a6f0d4d61a99c353185a4f0749a1692c252485a470748a1690c252085a3f0b476168dc2d198697f052fa1a5ec0cbc86977052ea1a5cc0cb88696f0d2d61a59c34b18594f0529a1652c0ca4859470528a1650c0ca08593f0b276164dc2c998b92f172562e49c5c918584e0b07c2e0582e3785c6b0b8ce1718c2e2a87b6f0f6dc32dac35b50cb670d6cc1ed8c3db105b550f4de329ac653387a630b49e1692c2d2385a431b47e0e8f4851d84a391b46e0e8d49d1984a310f2de2e5ac5cb3879630b29e1652c2ca3859431727e0a4f45c9d819391726e0a4d45c99819311725e2e4ac5c938b9230b09c2e05836b786d670b8de171ac2e3385c630b8b61715c2db785b6e076d60eda82db383b660b6c616d8865ad8cb5a196ae32d5825a784b4e0968e12d0c25a103a6f094d60e99c253184a5b074ae0e93c252583a47094860e8fc1d1e84a3b094720e8dc1d1a84a33094621a5bc34b5869670d2c62e56c5cab8594f0b2961651c2ca18b93f0527a2e4ec0c9c8b9370526a2e4cc0c988492f072560e49c24918686f0d0ce1613c24238783f0f07a120dc241a8482f0704e1e07c3c0b86e7f0dcee175fc2ebf05d7b0daf4175dc2ebb05d730dae4175ac66b505d670bacc171fc2e3d85c770b8e6171ac2e3383b7f0d6fc0edf41dbb83b75096e612dc825b584b6a076ce32d981daf83b5d096b612d641dab83b55096a612d441da784b4b0768e12d0c1d3b83a76074ea129ac253504a67194cc1297c2d2f04a5d644b81296c252d04a59094b01295c2d2b04a550b4a81294c252904a51094a01293c2d2704a4b094941291c2d2304a4309484128fc251f04a3d0d2fe1a5ec34bb86973172d62e59c2caf8295d0b2b6065642cab829550b2a6065442ca78594b0b28e1650c249f8393b0726e124cc24978292d09256064a42493829250924606484343f868770b0be161783c2e8584f0b09c16108241f838370905e120b42413878250f03e1e0683c0b8b8160bafe175f82ebd86d7a0baee175d82eb987d720b8fe171ec2e3b85c73076fe12dec25bd03b77196ec12dcc1db283b5f076ba12d6c25ac83b57076aa12d4c25a883b4f096960ed1c25a184a7f0f4fc129ec253d04a770d4ec129cc253903a65094be16978252e8ea5c094b612968252c84a58094ae16958252a85a54094a612948252884a500949e16938252584a4a0948e16918252184a420f2fe2e5ec5cbb879730b2be0a5742cad819590b2ae0a5542ca9819510b29e1652c2ca3859430927e0e4ec1c9b849330925e0a4b42495819290924e0a4942491819210b0bc161385c0b07d6f68ace171bc2e3705c6b0d8d41719c2e3305c630f8c41716d9a2d05c570b8ac16dbc2db585b670b6c616d6c2dab87a6f624d63699c3d31b025b1b4ae1693c1d2685a4b094921691c1d2285a4309482168fc2d1d85a370b4661e5bc5cb58b9670f2c62e56c5cab8594f0529a1652c0ca4859470528a1650c0ca08593f0b276164dc2c998b92f172562e49c5c918786f0f0ce1613c2c270884d0b07e160f82c190a82f1504e2a07c540d0a8171702c16d7c3dad85b570f6a61e97c3d2d87a570f4a6228fc2d1d85a37114660657c0cad81957032a6064fc0c9d8193703266064bc0c95819270324616d7c3dad85b570f6a61e97c3d2d87a570f4a6228fc2d1d85a37114660a57c14ad82957052a60a4fc149d82937052660a4bc14958292705246160d82e3787c6b0b8ce1f18c3db787b6b0f6ce1ed8c45a785b4b0b68e22d0c3d3787a6b0f4ce1e98c452785a4b0b48e2290c6d1f8ba3b1b46e2e8cc2ca30786e0d0cc22138241f038360305cb80b014132d024156de22dac55b388b630d6be1ad6c35ab86b53074de0e9b4253584a6a074ce369981d3284a63074be1296c1d2b84a530747e128ec1d1b84a33072de0e5b424b58496a092ce1a5981cb283964092c61257c24ad8495a092ae1a55824a98493f09276124dc24998f86f210d63e19c84318685f0d0b61a15c34298883f150762a0dc44198482f070560e09c24118481f090361205c240986d7e0dadc1b1fc2e3e86c7b0d8f21b1dc2e3a86c73118e21b1bc363586c670d8c60edfc1dbe84b7b096f20eddc1dba84b73096e20edbc25b583b67096c60ed3c25a583b4709686129fc353f04a7d1b4f8129ec253d04a79094f0129dc353b04a750d4e8129cc253904a71094e0129bc353704a6b094d41299c353304a63094c41293c452704a4b094941291c2d2304a43094841a5fc14be8697b032f21a5dc14ba86973032e21a5bc34b5869670d2c62253c54a58a94711286124fc1c9d8393709266124bc14968492b032521249c149284923032421a1f9583e038360704c1b9fc373b85d7f0dafc175f42ebb85d750dae61b5c846b588d6a0bace235982e3b85c760b8ea1b1ac363506c67118cc1b17c3e2f06c5d076fe12dec1dbb84b73096d60ed9c1daf84b5b076ae12d4c1da783b4d0969612d241da383b450968612d04253f86a7e094f6129e8253b86a76094e6129c8253584a6a094ce22998252f88a5e094b612968252b85a56094a612948252786a4e0949a1a930252584a4a0949212920252386a460948a36910252184a42094821290034bf8697b0d2ee1a5cc44b588967112be1656c2cab889530d29e0a53434a5819490d28e0a51434a1819410927e0e4ec1c9b849330925e0a4b42495819290924e0a4942491819210d0fe1a1dc3c2f858570d09e1a134342387845070740e0dc1c1b038270704c0e0943c0f878170bafe235ec46bd05d7715aec1f5cc2eb287c7f0f8fc231ec363d08c770d8ec1f1cc3e3905c65076fe12dec1dbb84b73076be12d6c1dab84b530769e0ed3425a584b490768e0ed1425a184b41094fe1e9f8253d84a7a094ee1a9d8253984a72094be22978252d84a5a094ae16958252984a520949e22938252688a4c0949612928252484a480948e2291825228da440948612908252084a400f2fe2e5ec64bb87973112be1656c2cab889531129e0a53444a5819491128e0a51444a1819410927e0e4ec1c9b849330925e0a4b42495819290924e0a4942491819210706c0e09836b786d670d8de1b1ac363386c63178b62b15c1db784b6b076ce12d8c25ad83b570769e12d2c1da384b43094de129ac253504a670d4cc1298c252d84a5a094ae32958252784a4b094941291c2d2304a43032de065ac0cb381963032b60655c0ca78194b0328e0650c0c9f8193b0326e064cc0c978192b032520649c0c91819210d0de1a1ac14338c85b190ae2e13c54258a84717086060fc1c1d8383a1b0720e0dc1c1b0483309062060bc0c158182a03052060a01c138382603046060840c0f81817030261b9fc373b86d7f0daf61b5dc36b98bd6b15ace0f1fc263d83c77098e6131ac1e3383c5f098b60f15c262984b7f0d6fc12dec25bd04b770d6ec12dcc25b904b6b096d412d9c65b304b5f116bc12d6c25ad04b570b6ac12d4c25a901a7f0d4fc069f40d3b81a75034e6069c80d3581a6a034ce329980d2f81a5b034ae0694c0d2781a4b0348e0690c0d1f81a3d03476068e40d1b81a3503466068c40cbb82976032ea065ac0cb501967192cc0657c44af0195b032b40655c2cab01953032a40653c24a70194b032940651c1ca30194303284064fc249f0193d09278064ec0c9d0193903270064dc249b019351b268064cc0c990193103260064bc0c970192d0d0fe1a1dc3c2f87857070940e11c1c23038370706c0e0d40c17818270303e060740c0d018170302c1e055380a07d7f11af62b5dc3eb983c7f098f60f1dc263983c5f098b60f15c262984b7f0f6fc12dec25bd04b770d6ec12dcc25b904b5f116bc12d6c25ad04b570b6ac12d4c25a901a7f034f6069e80d3b8ca76034e6069940d2f81a5b034ae0694c0d2781a4b0348e0690c0d1f81a3d03476068e40d1b81a3503466068c40cbf8797e032f6065e80cbb86976032e6065c80cb28195f112bc0656c0cad019570b2ac0654c0ca90194f0929c0652c0ca5019470728c0650c0ca10193f0927c064f4249e0193b03274064e40c9c019370926c064d46c9a0193303264064c40c98038460706c1f5bc46b385c6f118d61719c3e3188c5b0b8ae0edbc25b583b67096c612d6c1dab83b4f096960ed1c25a184a6f0f4dc129ac253504a670d4cc1298c253104a5b094b41295c452b04a4f1149c1292c252504a470b48c1290c25210196f032d60659c0cb18195b032ae0653c0ca58194a0328e165180ca18193f03276064dc0c998192f0325a064ac0c94819270324a0648c0c908786f210d64219c3c318885b110ae0a13c2c23888430307e0e0ec1c1d0d8390706e0e0d82419848310305e060b40c158182a03052060a01c13838260704a0608c0c108181f0302e0604c3f3f88e770bafe235ec2ebb87d7311ad61759c1e3f84c7b078ee131cc263583c67078be1316c1e2b84c53096fe1edf825bd84b7a096ee1add825b984b72096d612da825b388b66096be22d7825ad84b5a096ae16d5825a984b52034fe069ec0d3b81a73034d60699c0d2f81a5d034b6069680d2b85a56034aa0693c0d2581a4703486068fc0d1e81a3b03472068dc0d1a81a3303462065fc3cbf0197b032f4065dc34bb01973032e4065ac0cb501967112cc0657c14af0195d0329e125380ca58194a0328e0e5180ca1819420327e124f80c9e8493c03276064e80c9c819380326e124d80c9a8d93403266064c80c98819300325e064b80c968787f0f0ee2217c2c2b8384a0708e0e1181c1b838360706a060bc0c138181f0303a060680c0b818161502a900503eb7aa5670f8dea51ac563387c63508b62b15c1db784b6b076ce12d8c25ad83b570769e12d2c1da384b43094de1e9b8253584a6a094ce1a998253184a62094b612968252b8da560949e22938252584a4a0948e16918252184a420f2de985ac7cb3879634a2b63e55c7ca78a94b1528e8c50c249f8393b0726e124cc24978292d09256064a424938292509246064843c37878671509e2a11c1c1d038370706c0e09c1c13038251b03e3605c3e3787c6b0f8ce1f18c1db783b6b076ce0ed8c1da783b4b0768e0ed0c3d3787a6b0f4ce1e98c55278aa4b1548e2a90c1d1f83a3b0746e0e8cc1c9f0786e0d0cc221382c23038360305c0a09836b786d670b8de0f1ac2e3386c63118b61715c1db783b6b076ce0ed8c1dad83b570769e0ed2c1da383b43074de0e9b82d3585a6a074ce0e9981d3183a62114b622968452b88a560749e0e9381d2583a4a0748e0e9183d2187a420747e0e8f81d1b83a33074641a5bc34b5869670d2c62256c44ab8894f0b2961651c44a18393f072760e4dc1c998f92f0525a2e4ac0c948f9270524a2e48c0c908686f0d0ce1e13c2c238383f0706e120bc2416868270904a1e07c3c0b86e7f0dcee175fc36bf05d7d0baee175d436b986d7211ad6235a82eb388d660b8ee171d82e3a86c6b0d8d41b19c463306c5f0f8bc1b1741dbf83b7e076f61ade81dbb83b76076e61adc81db588b6a076ce0ed981daf83b5e076b616d681dab83b56076a622d481da783b4e0769a0ed301da586b4a0769280d201da383b460768a0ed101da186b42076821ad001d3f83a7b074ee0e9cc1d3583a67074be0e96c1d2b83a530749e0e9341d2583a490748e0e9141d2183a410d2fe1a5ec34bb86973112d62259c44af8595b0b2ae2254c34a78294d0d2960652434a3829450d286065041c9f8293d07276064e41c9b8293507266064c41c978392b0724e0e48c343f868770f0d4221983c2f858570d09e1a1343423878450707e0e0f8241e8382f0705c0e0883c0f87817 19 524287 7 127 11 2047 19 524287
def cc_62_2 : Nat → List (Nat × Nat) := unpackCursorV4 0xb907bb414fae061a7f61a176897f98917688799e818617c55376461731337062b6a462642625f34f5767d54b2b4e9624985143b5d3bf7c3704f2f37d2ab4828b20236551b4821555f0d77e0825500082 0x239fc473b85d7f11af6235e82ebb8bd7611ae6175b42eb385d65118fe1f1f8463d86c7a118ee1b1d8463987c720b8ce171982e3283b7f096f60eddc25b984b6b076ce0ed7c25ad83b57096a60ed3c1da684b4b096920ed1c1da284b43096820a9fc3d3f02a7b054f40a9dc353b02a73054e40a9ac153502a67114cc0a97c452f02a5b054b40a95c2d2b02a53054a40a93c452702a4d114980a92c152502a49054900a91c452302a45be4880a90c152102a4105480068fc0d1f01a3d052fe065ec14bb81973032d60a59c14af8195b052ae0654c14a78294d032960652414a38294503286065040c9d8393a032720a4dc149b01933032620a49c1493029251f0fe321dc442f858571109e2213444238f8450907e0e0dc14178282d0504e3e0940c0f8281727ade1f5b866b586d6a19ace1b598b6b187d62198de3319c162f82c5e058ba2edbc45b58bb67116c62ed7c2dae88b5b116b22ed5c2daa88b53116a222d2c45a383a6f094d60e99c253181a5b034b20e95c252981a5109496129241d2384a410747e128ec1d1b84a33052de065ac14b381963052be0a5740cad82957052aa0a5340ca5829470528a0a4fc0c9d82937032660a4bc0c9582927032463e1bc64338f85f1f0ba3e15c7c2a8e84d1f08a220fc5c1b8482f0704e0607c140be656f1dad79159c76b18bc6fc48d62f19f02318bc5fbc8b62f15c762983b6f096d60ed9c25b183b5f096b60ed5c25a983b4f096960ed1c25a182a6f0f4dc0a9ac153502a670d4cc0a98c153102a5f054b60a968152bdd256054a60a93c452702a4b054940a91c2d2302a4305484068fc0d1f01a3d052de065ac14b381963052be0656c14ab819530529e0652c14a381943032760e4e80c9c829370526c064cc0c98829270524c0a4947c378d86b1f0ce3618c742f8d85b1f0ae3614c7c278b84b1708e3610c241f8383b0706e120cc14178282d050560a09c7c12828230303e0a06c140b818131dade3b5ac76b38ed63178de2f1ac5e338bc63178be2f16c5e2b8bc53076de0edac1db383b63076be0ed6c1dab83b530769e0ed2c1da383b43034de069ac0d3381a63034be0696c0d2b81a530349e0692c0d2381a430347e0e8f80d1e81a370346a068cc0d190196f0f2dc065ac0cb5019670d2cc0658c0cb10195f032b6065680cab8e956032a60653c44a70194b032940651c2ca30194303284064dc149b019350325e064b80c968d86f1b0d63619c6c318d85f1b0b63615c6c298b84f170962e11c5c218383f070760e0dc1c198182f030560609c0c118181f0303a0606c0c0b8d815030261b5bc36b586d670dac6171bc163585c670d8c61717c462d85c57118a60edbc1db583b67076c60ed7c1dad83b57076a60ed3c1da583b47076860a9bc153705a6b0b4d40a99c153302a63054c42297c452d88a5a114ae22958452982a4f0549c0a92c152502a470548c1e90c3d2103a3f0747c068ec0d1d03a370346c0e8cc1d190296f032d60a59c0cb18295f032b60a55c0ca98294f032960a51c0ca18293f032760a4dc0c998292f0525a064ac0c94829270524a0648c0c908686f0d0d61a19c34318885f0f0b62215c3c298884f0b0961611c3c218383f070760e0dc1c198d82f1b05a1e0ac6c138d8250f0460607c140d82817030261b9fc373d86e770dce6175fc36bf05d7d0baee175d436b986d720bade235ac46b505d6711acc2358c2e3b85c760b8ea1b1bc363586c6a0d8ce23198363186c5f0f8bc1b17415bf82b7e056f61ade815bb82b76056e61adc815b782b6b116d40ad9c15b302b63056be0ad7815ad85b5a056ae0ad5815a988b520569e0ad3815a682b4c056961ad2815a4da3480568e0ad1815a282b44056861ad0815a086b40074fe0e9ec1d3b83a73074de0e9ac1d3383a63074be0e96c1d2b83a530749e0e9341d2583a490748e0e9141d2183a410347e068f80d1e8297f032f60a5dc0cb98296f032d60a59c0cb18295f032b60a55c0ca98294f0529a0652c0ca4829470528a0650c0ca08293f0527c0a4f414978292e03256064a40c9183922032421a1fc343d868770d0e6221bc3c35888670f0c62217c2c2d858570f0a61a13c34268684b0d08e3611434218283f1b07a0a0ec141b82835050660e0bc1c1583827070460607c140d82817030261f5bc36b586d670fac6171bc363585c67058c61717c462d85c57118a60edbc1db583b67076c60ed7c1dad83b57076a60ed3c1da583b47076860a9bc153702a6b054d40a99c153305a630b4c42297c452d88a5a114ae22958452982a4f0549c0a92c152502a470548c1a90c352103a3f0747c068ec0d1d03a370346c0e8cc1d190296f032d60a59c0cb18295f032b60a55c0ca98294f032960a51c0ca18293f032760a4dc0c998292f0525a064ac0c94829270524a0648c0c908786f0d0d61a19c3c318785f0f0b61e15c3c298784f0b0961611c3c218383f070760e0dc1c198782f0f05a1e0ac3c13878250f0460607c140d82817030261f9fc373d86e770fce6175fc2ebe86d7b0daf4175dc36bb05d750bade235ac2eb388d630b8fe171f82e3e87c6f0f8d61f1a83e3388c660f8c61b17c362f06c5d056fe0adf815bd86b7a056ee0add815b987b72056de0adac45b502b67056cc0ad8c15af82b5e056b616d6815ab82b56056a622d4815a782b4e0569a0ad3015a587b4a0569360d2015a382b460568a0ad1015a187b42056821ed001d3f83a7b074ee0e9cc1d3783a6b074ce0e98c1d2f83a5b074ae0e94c1d2783a4d074961e9281d2484a480748e0e9181d2283a44074860e9040d1f81a3e0347a0a5fc0cbd82977032e60a5bc0cb582967032c60a57c0cad82957032a60a53c14a68194b0f294065240ca4029470528c0a51414a201943032820a4fc149f0293d0525e0a4b80c9581929032460e4880c908787f0d0f61a1dc3c398786f0f0d61e19c3c318785f0b0b61615c3c298784f0f09a1e12c3c23878450f0860a0fc3c1e8283b0506e0a0d414198382f070560e09c1c118181f050360a05c0c098ed6f1dad63b59c76b18bc6fb28d62f19eba318bc5f1d8b62f15c762982b6f056dc0adac35b502b67056cc0ad8c3db102b5f056b63ad6815ab82b56056a60ad3c15a702b4b0b6940ad1c15a302b43116840e9bc1d3583a67074c60e97c1d2d83a57074a60e93c1d2583a4707486068fc0d1f01a3d052de065ac14b381963052be0656c14ab819530529e0652c14a3819430527e0a4f8149e8292f0525c064ac0c948192307244064846c378d86b1b0ce3618c6c2f8d85b1b0ae3614c6c278b84b1708e3610c141f8d83d050760a0dc141a828330705e0e0ac1c13838230303e0a06c140b818130fade4759c3e378bc6b158ce1f18c5e2d8ac57076de12dac1db384b63096b60ed5c1da784b4b0768e12d0c0d3781a6b034ce0698c0d2d81a570349e0692c0d2381a430347e068ec0d1b81a330f2de1e5b8ccb58696a212ce1a5983cb187962212b64656884ab919561729e2253854a58594a1528e165185ca1889420527e0a4f81c9b8493305264064bc0c970192703246064883c378d86a0f0cf001986c2d118561509e2e12854238b8460907e120f81c1b848320305e060b80c13818220303e060780c0e91d6f1dad64759c76b18bc6f178d62f19c5e318bc5f178b62f15c5e2983b6f096d60ed9c25b183b5f096b60ed5c25a983b4f096960ed1c25a181a6f034d60699c0d3181a5f034b60695c0d2981a4f034960691c0d2181a3f0347a068ec0d1d01a370746c068d40cb78796e032d6065a80cb386966032c6065880caf8195b032b40655c8cab019530329e225380ca58194a0328e165180ca1819420327e0a4f80c9e8192f0325c064b638378d86b7e0ce3618c742f8d85b230ae3614c5c278b84b1708e2e10c241f8383b0706e120cc0c178182b0304e0608c0c0f8181d030360605ea80a818130f8dc1f17855b785b6d116d622da455b385b65116c622d843daf86b5b0d6ae1ed4c6d3783a6d274d6129a46d3383a65214c6129843d2f86a5b0d4ae1e94c451f8aa3b1546e228cc7cb78296d232d6065a47cb382965212c6065843caf8695b0d2ae1e54c449f8a93b1526e224cc7c978d92b1b24e4648c342b06d6f0dada16dbc2db685b5f0d6b61ed4c6d3783a6d294d6129a46d3383a65294c6129843d2f86a5b0d4ae1e94c451f85a3b0b46e228cc7cb78296d172d6065a47cb382965172c6065843caf8695b0d2ae1e54c449f8593b0b26e224cc7c978b92b1b24e2e48c2e3f86c7b0d8f4171dc363b07c730b8de171b43e3587c6a118d2231a02e3387c660b8ca171903e3187c610b8aa1edfc3dbf06b7b0d6f41addc35bb07b730f6e41edbc3db707b6d0f6d81edac3db508b69116d01ed9c3db308b65a46c81ed8c3db107b610f6c016d543d3f86a7b0d4ee1e9cc3d3783a6d0f4d6129a43d3383a650f4c612984452785a4b0b48e2290c451f83a3d11476128e4451b83a3511466128c43cbf8697b0d2ee1e5cc3cb78296d0f2d6065a43cb3829650f2c60658444a78594b0b28e2250c449f8293d11276064e4449b8293511266064c47c978b92b1b24e2e48c343b068660f8fe1b1ec363b87c730f8de171b43e3588c690f8ce171943e3187c61076fe12dec25bd03b770d6ec12dcc1db783b6d096d612da825b484b68076ce1ed981db283b64096c612d841daa83b4f096960ed1c25a184a7f0f4fc129ec253d04a770d4ec129cc253904a6f0f4dc129b43d3604a6b094d4129a4253404a670f4cc12994753204a63094c412984253003a550949e22938252584a4a0948e16918252184a420f2fe1a5ec34bb879730f2de0a5b43cb5819690f2ce0a5943cb1819611129e2a52c54a3889430927e0e4ec1c9b849330925e0a4b42495819290924e0a4942491819210d0ec1a19826b784d6d09ace1359426b188c6f118da2319c463287c5f0d8ae16dbc2db683b6b076d216d9c2db287b63076c216d7c35ad85b570f6a622d2c2da383a6f074da129ac253483a67074ca1298c253083a5f094b60e95c252984a4b0748e0e8fc251d83a37094663e5bc14b68b96b032d23e59c14b28b963032c21e57c34ad869570f2a62252c44a38893f0b276164dc44998492f072560e49c24918486f090da1a19c34328485f0d0b41a15c342b0783f0b06e120bc1c138781f0f02e1f5fc36bb87d6f0fada1f59c46b285c7f0d8f6171dc3e3985c6f0b8da1f1ac463485c670b8ca1f18c3e3088c5b0b8ae0edfc25bd83b77096e60edbc1db684b6b096d20ed9c1db284b63096c212d6c1dab83b4f0769a12d2c25a503b470b68c0ed14253f87a7e094fa1e9f0253d84a7a094ee1a9d8253a86a74094e6129c8253787a6e094da1e9b0253584a6a094d2129a0253387a66094cb3c990253184a62094c212980252d84a5a094ae229581d2783a4e0749a128fc251f04a3d0f2fe1a5ec34bb879730f2de0a5b43cb5819690f2ce0a5943cb181961112b62255c44a78594b0b28e2250c249f8393b0726e124cc24978292d09256064a42493829250924606484343d068770d0ec1a19c3433068650f09e1611c241f838370905e120b42413878250f03e1e05c0eb781d6d156de16db445b588b69156ce16d9445b188b610f6be1ad6c35ab87b531b4de0e9b4b53584a691b4ce0e994b53184a610f4be1a96c352b87a531147e2a8ec551b88a33032de065b40caf8195b032a6064fc0c9d8193703266064bc0c9581927032461f1fc363d86c770f8e61f1bc2e3687c6b118d21f19c2e3287c630f8c21edfc35bd86b770f6e61edbc1db687b6b096d21ed9c1db287b63096c222d3c55a58ab4711686069fc0d3d81a7a034ee1a9d80d3981a6f034da069ac0d3501a69034d00699c3d3301a65054c80698c0d3081a550349e0692c0d2381a430347e068ec0d1b81a33032fe1e5f80cbd8197a032ee1a5d80cb981972032de1e5b80cb68796c032d6065a80cb481968032ce1e5980cb2cd164032c6065880cb081960032aa0653c44a70194b032940651c2ca30194303284064fc249f0193b03274064dc1c9b01933032641a1d8343301d6f03ada0759c0eb281d63118de231b4463388c650f8be1b15c2db785b6d056d60ada42db385b650f6c60ad842daf86b5b0b6ae1ed4c45a585b471b4de0e9b4a53584a691b4ce0e994a53184a610f4be1a96c352b87a53114962291c451f85a3b0b46e228cc0cb78196d032d6065a40cb381965032c6065840caf8195b032ae0654c0ca5819470327e064ec0c9b819330325e064ac0c9381923030de061b40c35068670d0cc1a1940c2f8685a0d0ae1a1583c1f858370f05e1e09c0c0f818170f8de1b19c3e2f87c5d0f8ae231542db786b6b0b6ce1ed8c2daf85b5d0f6b622d642dab85b550f6a61ed4445a585b470f4de1a9ac353387a630f4be0e9743d2d84a590f4ae0e9543d2984a51114962291c451f85a3b0b46e228cc0cb78196b032ce0658c0caf8195d032b6065640cab81955032a6065440ca5819470327e064ec0c9d019370b26c064cc0c978192b0324e0648c0c378686b0d0d4421a43433868660f0c61e1840c2f8185d030b6061680c2c818580d0ae1a158342a81853030a22212c44238283f0b06e1e0cc84178d82b1b04e4208c0c0f81817030261f5fc36bb87d6f0fada1f59c46b285c7f0d8f6171dc3e3985c6f0b8da1f1ac463485c670b8ca1f18c3e3088c5b0b8ae1edfc35bd86b770f6e61edbc1db687b6b096d21ed9c1db287b63096c222d6c45ab88b4f0b69616d1c45a181a7f034f6069dc0d3981a6f034da069ac0d3481a67034ca0698c0d3081a5b034ae0693c0d2681a4b034940691c2d2301a450347e068ec0d1b81a33032fe1e5f80cbd8197a032ee1a5d80cb981972032de1e5b80cb68796c032d6065a80cb481968032ce1e5980cb2cb164032c6065880cb081960032b6065680cab889560329e0a5380ca68193f0927c064ec0c9d019370726c064cc0c990192f0325c064b4343d068770d0ec1a19c3433068650f09e1611c3c1f878370305e0609c0c0f8181d030340605c0c0b0781594028075bc0eb681d6703aca0758c8e3791c6d238ce471943e2f86c57156de16db45db588b69156ce16d945db188b610f6be1ad6c35ab87b53176962ad1c1d3783a6d054d60a9a41d3383a65094c60a9841d2f84a5b074ae1294c252583a470747e128ec1d1b84a33032de065b40cb581969032ce065940cb181961032be0656c0cab81953032960651c0c9f8193b0326e064cc0c978192b0324e0648c0c378186d0d0ce1a1940c2f8685a0d0ae1a1583c1f878370905e0e09c0c0f818170fafe1b5dc3eb787d6d0face475943e3f86c7b0d8ee1f1cc3e3785c6d0f8d6231a43e3385c650f8c61f1845e2d8ac57076fe12dec1dbb84b73076de0edb425b584b69076ce0ed9425b184b61096b60ed5c1da784b4b0768e12d0c0d3f81a7b034ee069cc0d3781a6d034d6069a40d3381a65034c6069840d2d81a570349e0692c0d2381a430347e068f40d1d81a3a0346e0e8d80d1a8197f0f2fc065f43cbe0197b032f4065dc34bb019750d2e8065cc0cb90196f0f2dc065b43cb60196b032d4065a40cb4019670f2cc0659640b201963032c4065840cb00195b032b40655c8cab0194f1129c0652c0ca5019470b28c0650c0ca10193f0527c064f40c978192e0325a1a1e8343b868760d0ce1a19834328784f0f08e120fc1c1b8182f0304e0607c0c0e818170f02a1f1bc363387c5f0f8ba1f15e9a2a87b6f0d6d61ad9c3db187b5f0b6ba1ed6c45ac87b570b6aa1ed4c3da8d134b1568e1e9bc353586a670f4c61e97c1d2e87a5b094b21e95c1d2a87a53094a34092c6d238da3f154762a8de71198796f0d2d61a59c3cb18795f052ba1e56c0cac87957052aa1e54c0ca8cc14b1f28e3e4fc549d8a937922663e4bc6c958d9278e2461a1a83433868660d0ae1a158342a8783f0f06e1e0bc3c138781f0f02e1b1bc363586c670d8c61adbc35b586b670d6c62ad3c55a58ab47156861a9bc353586a670d4c62a93c55258aa4715486368fc6d1d8da371b4661a5b834330884e0b08c120f81c1b0182e0504c1b1bc3e3686c670d8ca1b17c362b85b6f0d6d61ada42db386b630f6c216d7c35ad85b570d6a622d2c2da383a6f094d6129a41d3384a63094c20e97c252d83a57094a61292c1d2383a3f094760e8dc25198696f0d2dc125ac24b484967092c61258824b0849600d2be1a57834ad86959092ae1a54c34a907951112962252844a3889460727e164dc3c998492f0724e1248c34378286d0d0d61a19c1432868630d0be1a16c342b86853110962211c441f8583b0b06e220cc24178382b0704e1208c7c0f8b81b1f02e2e04c36bf87d7d0daee1b5d436b786d670b8fe171f4363d86c790b8ee171d4363987c710b8de1b1ac2e3386c63118b61715c1dbf83b7d096f612de41dbb83b75096e612dc41db784b6b076ce12d8c25ad83b570769e0ed3425a584b4a0768e16d181da284a7f0d4fc129f43d3e04a7b094f4129e4253c04a770d4ec129d4353a04a73094e4129c4253804a6f0d4dc129b43d3604a6b094d41299c353304a650d4c81298c253104a5b094b41295c452b03a4f0749c0e934251f84a3e0947a1a5fc14be8697b032f21a5dc14ba86973032e21a5bc34b5869670d2c62256c44ab8894f0b2961651c44a18493f072760e4dc24998492f0525a124ac0c94849270524a1248c0c908687f0d0fc1e1f434378686e0d0c41e168442b0784f0b08e120fc1c1b8482f0905a120a82413848260f04b100903c0f878170d8de1f1b4363386c650d8be1b15c2db785b6d0d6d61ada42db385b650d6c61ed842daf86b5b0b6ae1ad4c45a585b470d4de0e9b4353584a690d4ce0e994353184a610d4be1a96c352b86a53114962291c451f85a3b0b46e228cc0cb78196d032d6065a40cb381965032c6065840caf8195b032ae0654c0ca5819470327e064ec0c9d019370b26c064cc0c978192b0324e0648c34378686e0f0da061ac0c3481867030ca0618c0c3101861030c01a17c342f0685b0d0b20615c3429868520f0a22212c4425088471108c0a0fc2c1b878332105e360ac6c13908230303e0605c0c0986d7f0fafa1b5dc36ba86d6f0dace171fc2e3e86c7b0d8f2171dc2e3a86c730f8e2171bc363585c670d8c62316c2e2b86b7f076fa1adec25bc86b77076ea1adcc25b886b6f0d6d61ad9c35b188b5b116ae22d3c2da585b4711686069fc0d3e81a7b034f2069dc0d3a81a73034e2069bc0d3581a67034c60696c0d2b81a4f0349a0692c0d2501a470b48c069140d1f81a3b0346e068cc0cbf8697e032fa1e5f00cbd8197a032f2065e00cbb86976032ea1a5d00cb981972032e2065c00cb78696e032d6065a80cb386966032c6065880cad8195a032ae225580ca78294e0329a064fc249f0193b03274064dc1c9b0193303264064bc0c970192d0d0fe1a1f83c3e8686f0d0dc1a1883c2d088560f09e1611c3c1f878370305e0609c0c0f8181d030340605c0c0b07815840281b1bc3e3686c670d8ca1b17c362b86b6f0b6da1adac35b385b650d6c61ad7c35ad86b570d6a62ed2c55a383a6f094d6129a41d3384a63094c20e97c252d83a57094a61292c1d2383a3f094760e8dc25198196f032d6065a40cb381963032c20657c0cad81957032a60652c0ca38193f03276064dc0c998192f032560649c0c918686f0d0dc061ac0c3481867030c6061880c30818600d0be1a178342d86859030ae1a14c342907851190963212864238c8461707e2a0ec541b8b8330505e0e09c24118181f0302e0604c36bf87d7d0daee1b5d436b786d670d8fe171f4363d86c790d8ee171d4363987c710d8de1b1ac363386c63178b62b15c1dbf83b7d096f612de41dbb83b75096e612dc41db784b6b076ce12d8c25ad83b570769e12d2c1da384b43034fe069f40d3d81a79034ee069d40d3981a71034de069ac0d3381a63034b60695c0d2781a4b0348e0690c0d1f81a3d03476068e80d1b83a360346a065fc34bf0197d0f2f8065ec0cbd01979032f0065dc34bb019750d2e8065cc0cb901971032e0065bc34b70196d0f2d8065ac0cb5019670d2cc0659434b201963032c40656c0cad01957192ac0653c44a70194b032940651c2ca30194303284064fc149f0193d0325e064b80c968687f0d0fc1e1f434378686e0d0c41e168642b0784f0f08e120fc1c1b8182f0304e0607c0c0e8181a0302e060583c0ac0014 20 1048575 8 255 11 2047 19 524287
def cc_62_3 : Nat → List (Nat × Nat) := unpackCursorV4 0xbe2a0b786aad0a8a60709c69a9ae1894f5f8ea65883678186b7b36574e656e9656826761f635ba65555654e66f4e6004de0849e40437673f93e3946531b792ce4d2517d1e968151980e76a04d9a0004d 0x6e7f06e7b06e7706e7305d7f06d7b05d7706d7305d6f08d6b05d6708d6303c7f06c7e03c7d03c7703c7504c7304c7203c6f04c6b04c6a03c6708c6604c6303c5f04c5b03c5704c5303b7703b7603b7504b6f04b6b04b6a04b6708b6604b6304b5f08b5e04b5b04b5a04b5705b5604b5304b5204b4f04b4e04b4d01a7f01a7b01a7701a7301a6f01a6b01a6701a6301a5f01a5d01a5b01a5a01a5705a5601a5501a4f01a4b01a4701a4301a3f01a3d01a3b01a3901a3701a3501a3301a310197f0697e0197b0197a019770697601973019720196f0196b0196a0196708966019630195f0295e0195d0194f0494e0194d0494c0194b0194a0194703946019450394401943019420193f0493e0193d0493c0193b0193a01939019380193704936019357f134019330193201931019300192f0192e0192d0687f0687b06877068730886f0786b08867078630885f0585b05857078530484f0384b03847048430483f0483d0483b0483714835048330182f0182b01827018230181f0181d0181b0181a07818018170181612815760140181304d6f04d6d01d6b01d6901d6701d6501d6301d6108c6f08c6d08c6b08c6708c6508c6306c5f06c5b06c5706c5303b6f03b6d03b6b02b6903b6703b6502b6302b6105b5f06b5b05b5706b5305b4f08b4b05b4708b4303a6f03a6d01a6b01a6901a6701a6501a6301a6103a5f03a5b01a5703a5303a4f03a4b08a4a03a4703a4603a4303a3f03a3b03a3703a330196f0196d0196b01969019670196501963019610195f0195b01957019530194f0194b01947019430193f0193b01937019330192f0192b01927019230d86f0d86d0786b0d8670d865078630685f0685b06857068530884f0784b08847078430883f0583b05837078330382f0382b03827038230181f0181b018170181303e7f03e7e04e7d03d7f08d7d03d7b03d7703d7503d7306d6f06d6b06d6706d6303c7f05c7d03c7b03c7903c7703c7503c7308c7105c6f06c6b05c6706c6305c5f08c5b05c5708c5303b7f03b7e03b7d03b6f03b6e03b6b03b6903b6306b6203b6103b5f03b5b08b5a03b5703b5603b5303b4f03b4b03b4703b4301a7f03a7e01a7d02a7c01a7b01a7901a7701a7501a7301a7201a7101a7001a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4d01a4b01a4a01a4705a4601a4501a3f01a3b01a3701a330197f0397e0197d7d17c0197b0197a019790197801977039760197503974019730197201971019700196f0696e0196d0796c0196b0196a0196706966019650696401963019620195f0195b0195a0195708956019530194f0294e0194d0193f0393e0193d0493c0193b0193a0193703936019350393401933019320192f0192e0192d0387f0d87d0387b0387703875038730686f0686b06867068630885f0785b08857078530884f0584b05847078430383f0383b03837038330182f0182b01827018230181f0181d0181b0181a0781801817018160d815750140181307d6f06d6b06d6707d6305c6f06c6b05c6707c6305c5f08c5b05c5708c5303b6f03b6d04b6b04b6a03b6706b6603b6501b6303b5f04b5b03b5704b5303b4f04b4b03b4704b4303a6f03a6e01a6b01a6a01a6701a6601a6301a6208a5f08a5b08a5a08a5708a5608a5302a4f02a4e04a4b04a4a04a4704a4604a4302a4204a3f04a3e01a3b01a3a01a3701a3601a3301a320196f0196b01967019630195f0195b01957019530194f0194d0194b0194a019470594601945019430193f0193b01937019330192f0192d0192b01929019270192501923019210786f0686b06867078630785f0785b07857078530784f0584b05847078430483f0383b03837048330782f0782d0782b0782707825078230181f0181b018170181307e7f06e7b06e7707e7305d7f06d7b05d7707d7305d6f08d6b05d6708d6303c7f03c7d04c7b04c7a03c7706c7603c7503c6f04c6b03c6704c6303c5f04c5b03c5704c5303b7f03b7e03b7d04b6f04b6b04b6a04b6708b6604b6304b5f08b5e04b5b04b5a04b5705b5604b5304b5204b4f04b4e04b4d01a7f01a7b01a7701a7301a6f01a6b01a6701a6301a5f01a5d01a5b01a5a01a5705a5601a5501a4f01a4b01a4701a4301a3f01a3d01a3b01a3901a3701a3501a3301a310197f0797e0197b0197a019770697601973019720196f0196b0196a0196708966019630195f0295e0195d0194f0494e0194b0194a019470394601943019420193f0493e0193d0493c0193b0193a01939019380193704936019357b134019330193201931019300192f0192e0192d0787f0687b06877078730786f0786b07867078630785f0585b05857078530484f0384b03847048430483f0483d0483b0483707835048330182f0182b01827018230181f0181d0181b0181a07818018170181607815740140181305b5f07b5b05b5707b5307a5f07a5b07a5707a5308a3f05a3b05a3708a330195f0195b01957019530193f0193b01937019330192f0192b019270192307d6f08d6705c6f08c6b05c6707c6308c5b05c5707b6f12b6b0db6707b6308b5b08b5708b4f05b4b05b4708b4301a6f01a6b01a6701a6301a5b01a5701a4f01a4b01a4a01a4705a4601a4301a3f01a3b01a3701a330796f0796e1796b0696a109670696607963079620895b0895a08957089560294f0294e0594708943029421093f0493e0d93b0393a0d9370393612933049320192f0192e0192701923019220786f4a06e0a86a07867420660a8620885e0885a08856088520884f0884e0584a0584705846088420a83f2403e0a83a0a8371b0360a8320182f0182e0182a0182701826018220181f0181e0181d03d6f04d6e03d6d07c6f06c6b06c6707c6303c5f03c5d03c5b03c5708c5503c5305b6f06b6b05b6707b6303b5f03b5d03b5b08b5903b5705b5503b5303b5105b4f08b4b05b4708b4303a6b06a6a03a6903a6703a6603a6303a6103a5703a5603a5503a4f03a4b03a4703a4303a3f03a3b03a3703a330196f0196b01967019630195f0195d0195b01959019570195501953019510194f0194b01947019430193f0193b0193a0193705936019330192f0192b01927019230786f0686b06867078630385f0385d0385b17859038571085503853038510884f0884b08847088430283f0583b05837078330382f0382b03827038230181f0181b018170181306d6f06d6b06d6706d6305c6f06c6b05c6706c6305c5f08c5b05c5708c5303b6f06b6e03b6d03b6703b6504b6304b6203b5f04b5b04b5a03b5708b5604b5303b4f04b4b03b4704b4303a6703a6603a6504a5f04a5b04a5a04a5708a5604a5304a4f08a4e04a4b04a4a04a4705a4604a4304a4204a3f04a3e04a3d0196f0196b01967019630195f0195b01957019530194f0194b0194a0194705946019430193f0193b01937019330192f0192d0192b01929019270192501923019210686f0686b06867068630885f0885b08857088530284f0584b05847088430483f0383b03837048330482f0482d0482b12829048271082504823048210181f0181b018170181303d6f03d6e04d6d03c6f08c6d03c6b03c6703c6503c6306c5f06c5b06c5706c5303b6f05b6d03b6b03b6903b6703b6503b6308b6105b5f06b5b05b5706b5305b4f08b4b05b4708b4303a6f03a6e03a6d03a5f03a5e03a5b03a5903a5306a5203a5103a4f03a4b08a4a03a4703a4603a4303a3f03a3b03a3703a330196f0396e0196d0296c0196b019690196701965019630196201961019600195f0195b01957019530194f0194b01947019430193f0193b0193a0193705936019330192f0192b01927019230386f1086d0386b03869038670386503863178610685f0685b06857068530884f0884b08847088430283f0583b05837088330382f0382b03827038230181f0181b018170181307d6f06d6b06d6707d6305c6f06c6b05c6707c6305c5f08c5b05c5708c5303b6f03b6d04b6b04b6a03b6706b6603b6503b5f04b5b03b5704b5303b4f04b4b03b4704b4303a6f03a6e03a6d04a5f04a5b04a5a04a5708a5604a5304a4f08a4e04a4b04a4a04a4705a4604a4304a4204a3f04a3e04a3d0196f0196b01967019630195f0195b01957019530194f0194b0194a0194705946019430193f0193b01937019330192f0192d0192b01929019270192501923019210786f0686b06867078630885f0885b08857088530284f0584b05847078430483f0383b03837048330482f0482d0482b12829048271082504823048210181f0181b018170181307d6f07d6e07d6d07c6f06c6b06c6707c6307c5f07c5d07c5b07c5708c5507c5305b6f06b6b05b6707b6305b5f05b5d07b5b02b5905b5705b5502b5302b5105b4f08b4b05b4708b4307a6f06a6b06a6707a6307a5f03a5d07a5b04a5907a5703a5507a5304a5108a4f08a4b08a4708a4308a3f05a3b05a3708a330196f0196b01967019630195f0195d0195b01959019570195501953019510194f0194b01947019430193f0193b0193a0193705936019330192f0192b01927019230686b0686a10869068670686607863078610685706856068550884f0884b08847088430283f0583b05837078331082f1082b10827108230181f0181b018170181306d6f06d6b06d6706d6305c6f06c6b05c6706c6305c5f08c5b05c5708c5306b6f06b6b06b6706b6308b5f08b5b08b5708b5308b4f05b4b05b4708b4301a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4b01a4a01a4705a4601a4301a3f01a3b01a3701a330696f0696e1096d069670696506963069620895f0895b0895a0895708956089530294f0594b05947089431093f1293b10937129330192f0192b01927019230686706866068650685f0685b0685a0685708856068530684f0884e0584b058470584606843068420683f0483e0683b0383a068370383606833048320182f0182e0182b018270182601823018220681f0781e0681d06d6f06d6e06d6d06c6f08c6d06c6b06c6706c6506c6306c5f06c5b06c5706c5305b6f05b6d02b6b02b6905b6705b6506b6302b6105b5f06b5b05b5706b5305b4f08b4b05b4708b4306a6f03a6d06a6b04a6906a6703a6506a6304a6106a5f06a5b06a5706a5308a4f08a4b08a4708a4308a3f05a3b05a3708a330196f0196d0196b01969019670196501963019610195f0195b01957019530194f0194b01947019430193f0193b0193a0193705936019330192f0192b01927019230686f0686e0786d0685f0685e0685b068590685306852108510884f0884b0884a0884708846088430283f0583b05837088331082f1082b10827108230181f0181b018170181307d6f06d6b06d6707d6305c6f06c6b05c6707c6305c5f08c5b05c5708c5307b6f06b6b06b6707b6308b5f08b5b08b5708b5308b4f05b4b05b4708b4301a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4b01a4a01a4705a4601a4301a3f01a3b01a3701a330796f0796d0696b0696a0696706966109650895f0895b08957089530294f0594b05947079431093f1293b10937129330192f0192b01927019230786f0786e0786d0785f0785b0785a0785708856078530784f0884e0584b058470584607843078420783f0483e0783b0383a078370383607833048320182f0182e0182b018270182601823018220681f0681e0681d08d6f08d6b08d6708d6305c6f08c6b05c6708c6305c5f08c5b05c5708c5303b6f04b6b03b6704b6303b5f04b5b03b5704b5303b4f04b4b03b4704b4304a6f07a6e04a6b04a6a04a6706a6604a6304a6204a5f04a5b04a5a04a5708a5604a5304a4f02a4e04a4b04a4a04a4705a4602a4302a4204a3f04a3e04a3d0196f0196b01967019630195f0195b01957019530194f0194b0194a0194705946019430193f0193b01937019330192f0192d0192b01929019270192501923019211086f1086b10867108630885f0885b08857088530284f0584b05847088430383b0383a10839038370383604833048310382703826038250181f0181b018170181308d6f08d6b08d6708d6305c6f08c6b05c6708c6305c5f08c5b05c5708c5303b6f03b6b03b6703b6303b5f03b5b03b5703b5303b4f03b4b03b4703b4301a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4b01a4a01a4705a4601a4301a3f01a3b01a3701a331096f1296b10967129630895f0895b0895a0895708956089530294f0594b05947089430393f0393e1093d039370393503933039320192f0192b01927019230386f0786e0386b0386a038670686603863038620385f0385b0385a0385708856038530384f0884e0384b038470584603843038420383703836038350182f0182e0182b018270182601823018220381f0481e0381d08d6f08d6b08d6708d6305c6f08c6b05c6708c6305c5f08c5b05c5708c5303b6f03b6e03b6b06b6a03b6703b6603b6307b6203b5f03b5b08b5a03b5703b5603b5302b4f02b4e03b4b05b4a03b4905b4803b4703b4603b4302b4203b4102b4003a6f03a6b03a6703a6303a5f03a5b03a5703a5303a4f03a4b03a4703a4303a3f03a3e03a3d0196f0196b01967019630195f0195b01957019530194f0194b0194a0194705946019430193f0393e0193d0293c0193b019390193701935019330193201931019300192f0192b01927019231086f1086b10867108630885f0885b0885a0885708856088530284f0584b05847088430383f0383e0483d0382f0382e0382b038290382303822108210181f0181b018170181308b4805b4404a4803a44019480294417848088441bc5f6c45b1bc576b45305b5f08b5b05b5708b5305b4f08b4b05b4708b4303a5f04a5b03a5704a5303a4f04a4b03a4704a4303a3f04a3b03a3704a330195f0195b01957019530194f0194b01947019430193f0193b0193a0193705936019330192f0192b01927019231085f1285b10857128530884f0384b08847088430283f0583b05837088330482f0382b0382a0382703826018230181f0181b018170181308d6f08d6b08d6708d6305c6f08c6b05c6708c6305c5f08c5b05c5708c5303b6f04b6b03b6704b6303b5f04b5b03b5704b5303b4f04b4b03b4704b4301a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4b01a4a01a4705a4601a4301a3f01a3b01a3701a331096f1296b10967129630895f0895b08957089530294f0594b05947089430493f0493d0393b0393a0393703936109350192f0192b01927019230486f0786e0486b0486a048670686604863048620485f0485d0885c0485b0485a0485708856048556a054048530484f0884e0484b048470584604843048420483f0483e0483d0182f0182e0182b018270182601823018220381f0381e0381d08c5f08c5b08c5708c5305b5f08b5b05b5708b5305b4f08b4b05b4708b437725f7625b752577425308a4f08a4b08a4708a4308a3f05a3b05a3708a330195f0195b01957019530194f0194b01947019430193f0193b0193a0193705936019330192f0192b01927019237305f7205b71057700530884f0884b08847088430283f0583b05837088336f02f6e02b6d027690230181f0181b018170181308d6f08d6b08d6708d6305c6f08c6b05c6708c6305c5f08c5b05c5708c538236f7e36b7c3677a36308b5f08b5b08b5708b5308b4f05b4b05b4708b4301a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4d01a4b01a4a01a4705a4601a4501a3f01a3b01a3701a330196f0796e0196b0196a019670696601963019620195f0195b0195a0195708956019530194f0294e0194d0193f0493e0193b0193a019370393601933019320192f0192e0192d4906f0a86b410670a8630885f0885b08857088530884f0584b05847088432303f0a83b1a0370a8330182f0182b01827018230181f0181d0181b0181a79018018170181678015680140181306d7a06d7706d7606d6706d6606d6507c7f06c7b06c7707c7307c6f05c6d07c6b08c6907c6705c6507c6307c6108c5b08c5703b7f04b7b03b7704b7303b6f03b6d04b6b04b6903b6703b6504b6304b6104b5b03b5703b4f04b4b03b4704b4302a7f07a7e02a7b02a7a02a7706a7602a7302a7202a6f07a6e02a6d07a6c02a6b02a6a02a6902a6802a6707a6602a650ca6402a6302a6202a6102a6002a5b02a5a02a570ca5602a4f08a4e02a4b02a4a02a4705a4602a4302a4201a3f01a3e01a3d0297f0197b02977019730296f0296d0196b01969029670296501963019610195b029570294f0194b02947019430193b0393a01939029370293601933019310292702926029250787f068770786f0786d07867078650784f078470483f038370282f0282d02827078250181f0281702d6b02d6902d6702d6302d6107c6f07c6d02c6702c6506c5f02c570bb6f05b6d08b6b08b690bb6705b6508b6308b6106b5f06b5b06b5706b5308b4b08b4703a6f03a6d04a6b01a6903a6703a6501a6301a6103a5f04a5b03a5704a5304a4b03a4703a3f04a3b03a3704a330296f0296d0196b01969029670296501963019610295f0195b02957019530194b029470293f0193b02937019330292f0192b02927019230f86f0f86d0f8670f8650685f068570883f0b8370482f038270181f0281706d7f06d7e07d7d06d6f06d6e06d6206c7f05c7d06c7b06c7906c7705c7506c7308c7106c6f06c6b06c6706c6308c5b08c5703b7f03b7d04b7b04b7903b7703b7504b7304b7103b6f04b6b03b6704b6304b5b03b5703b4f04b4b03b4704b4302a7f06a7e02a7d6527c02a7b02a7a02a7902a7802a7706a7602a7506a7402a7302a7202a7102a7002a6f06a6e02a6b02a6a02a6706a6602a6302a6202a5b02a5a02a570ca5602a4f08a4e02a4b02a4a02a4705a4602a4302a4201a3f01a3e01a3d0297f0297e0297d0297c0197b019790297702975019730697201971019700296f0196b02967019630195b029570294f0194b02947019430193b0393a01939029370293601933019310292702926029250687f0f87d06877068750686f068670884f0b8470483f038370282f0282d028270f8250181f0281706d6f06d6b06d6706d6305c6f02c6b05c6706c6305c5f08c5b05c5708c5302b6f02b6e02b6b02b6a05b6705b6602b6302b6208b5f08b5b08b5a08b5708b5608b5307b4f07b4e02b4b02b4a02b4702b4602b4302b4203a6f04a6b03a6704a6303a5f04a5b03a5704a5303a4f04a4b03a4704a4303a3f03a3d01a3b01a3903a3703a3504a3301a310296f0196b02967019630295f0195b02957019530294f0194b02947019430293f0293d0193b01939029370293501933019310292f0192b02927019230686f0686b06867068630885f0785b08857078530884f0584b05847078430f83f0f83d0783b0f8370f835078330482f0382b03827048230181f0281b028170181306e7f06e7b06e7706e7305d7f06d7e05d7d05d7705d7506d7306d7205d6f08d6b08d6a05d6708d6608d6305c7705c7605c7506c6f06c6b06c6a06c6708c6606c6306c5f07c5e06c5d03b7f04b7b03b7704b7303b6f04b6b03b6704b6303b5f04b5b03b5704b5303b4f03b4d04b4b04b4903b4703b4504b4304b4102a7f06a7e02a7b02a7a02a7706a7602a7302a7202a6f02a6b02a6a02a6708a6602a6302a5f08a5e02a5b02a5a02a5705a5602a5302a5202a4f06a4e02a4d06a4c02a4b02a4a02a4902a4802a4706a4602a456324402a4302a4202a4102a4001a3f01a3e01a3d0297f0197b02977019730296f0196b02967019630295f0195b02957019530294f0294d0194b01949029470294501943019410193b0393a01939029370293601933019310292702926029250687f0687b06877068730886f0786b08867078630885f0585b05857078530684f0684d0684b068470f845068430483f0383b03837048330282f0282d0282b028270f825028230181f0281b028170181307d6f06d6b06d6707d6305c6f06c6b05c6702c6305c5f08c5b05c5708c5305b6f05b6e02b6b02b6a02b6702b6602b6302b6208b5f08b5b08b5a08b5708b5608b5306b4f06b4e02b4b02b4a02b4702b4602b4302b4203a6f04a6b03a6704a6303a5f04a5b03a5704a5303a4f04a4b03a4704a4303a3f03a3d01a3b01a3903a3703a3504a3301a310296f0196b02967019630295f0195b02957019530294f0194b02947019430293f0293d0193b01939029370293501933019310292f0192b0392a0292702926019230786f0686b06867078630785f0785b07857078530784f0584b05847078430783f0783d0783b0783707835078330482f0382b03827048230181f0281b028170181307e7f06e7b06e7707e7305d7f05d7d06d7b06d7a05d7706d7605d7505d6f08d6b05d6708d6305c7f05c7e05c7d07c6f07c6b07c6a07c6708c6607c6306c5f06c5e06c5d03b7f04b7b03b7704b7303b6f04b6b03b6704b6303b5f04b5b03b5704b5303b4f03b4d04b4b04b4a04b4904b4803b4707b4603b4503b4404b4304b4102a7f07a7e02a7b02a7a02a7706a7602a7302a7202a6f02a6b02a6a02a6708a6602a6302a5f08a5e02a5b02a5a02a5705a5602a5302a5202a4f07a4e02a4d07a4c02a4b02a4a02a4902a4802a4707a4602a456124402a4302a4202a4102a4001a3f01a3e01a3d0297f0197b02977019730296f0196b02967019630295f0195b02957019530294f0294d0194b01949029470294501943019410193b0393a01939029370293601933019310292702926029250787f0687b06877078730786f0786b07867078630785f0585b05857078530784f0784d0784b0784707845078430483f0383b03837048330282f0282d0282b0282707825028230181f0281b028170181308d6f08d6705c6f08c6b05c6708c6302c5b05c571ab6f07b6e0cb6b06b6a0cb6706b661ab6307b6202b5b02b5a05b5705b5602b4b02b4a02b4702b4602b4303a6f04a6b03a6704a6304a5b03a5703a4f04a4b03a4704a4303a3f03a3d01a3b01a3903a3703a3504a3301a310296f0196b02967019630195b029570294f0194b02947019430293f0293d0193b01939029370293501933019310292f0192b02927019230f86f0c8670884f058470f83f0f83d0f8370f8350482f038270181f02817 20 1048575 8 255 11 2047 20 1048575
def cc_62_4 : Nat → List (Nat × Nat) := unpackCursorV4 0xd8468cec98c8468bea9ab7e6cae49aa786c9dc9c979638fb7e8ac4f8317b7e24f7934f72b6868f9c6236c5899a5197047f9a43a453d06a32ca42ab8125e4d1db831786310e6a0709e06e0206c020006c 0x4d6f04d6e01d6b01d6a01d6701d6601d6301d6207c6f06c6b06c6707c630ec5f0ec5d08c5b0ec570ec5508c5305b6f05b6b05b6705b6303b5f02b5d03b5b03b5902b5702b5503b5303b5105b4f05b4b05b4705b4301a6f03a6b03a6703a6301a5f01a5d01a5b01a5903a5703a5501a5301a5103a4f03a4b03a4703a4303a3f03a3b03a3703a330196f0196b01967019630195f0195d0195b01959019570195501953019510194f0194b01947019430193f0193b01937019330192f0192b01927019230786f0686b06867078630785f0785d0785b0785707855078530784f0784b07847078430583f0583b05837058330382f0382b03827038230181f0181b018170181303e7f04e7e03e7d07d7f06d7b06d7707d7303d6f03d6d03d6b03d670ed6503d6305c7f05c7b05c7705c7303c6f03c6d03c6b05c6903c6705c6503c6303c6105c5f05c5b05c5705c5303b7b06b7a03b7903b7703b7603b7303b7103b6703b6603b6503b5f03b5b03b5703b5303b4f03b4b03b4703b4301a7f01a7b01a7701a7301a6f01a6d01a6b01a6901a6701a6501a6301a6101a5f01a5b01a5701a5301a4f05a4e01a4d01a4701a4501a4301a4201a3f01a3b01a3701a330197f0797e0197b0197a019770697601973019720196f0396e0196d0396c0196b0196a01969019680196703966019659e164019630196201961019600195f0195b0195a019570e956019530194702946019450193f0393e0193b0193a019370393601933019320192f0192e0192d0787f0687b06877078730386f0386d0386b0386707865038630785f0785b07857078530584f0584b05847058430383f0383b03837038330182f0182d0182b0182707825018230181f0181d0181b01817078150181306d6f06d6b06d6706d6305c6f05c6b05c6705c6305c5f05c5b05c5705c5303b6f01b6b03b6704b6303b5f04b5b03b5704b5303b4f04b4b03b4704b4301a6f01a6e01a6b01a6a03a6703a6601a6301a6208a5f0ca5b0ca5a0ca570ca5608a5304a4f04a4e04a4b02a4a02a4702a4604a4304a4204a3f04a3e01a3b01a3a01a3701a3601a3301a320196f0196b01967019630195f0195b01957019530194f0194b01947019430193f0193b01937019330192f0192d0192b01929019270192501923019210686f0686b06867068630885f0785b0a857078530584f0584b05847058430483f0383b03837048330a82f0a82d0782b0a8270a825078230181f0181b018170181306e7f06e7b06e7706e7305d7f05d7b05d7705d7305d6f05d6b05d6705d6303c7f06c7e03c7d03c7703c7504c7304c7203c6f04c6b04c6a03c670cc6604c6303c5f04c5b03c5704c5303b7703b7603b7504b6f04b6b04b6a04b670cb6604b6304b5f05b5e04b5b04b5a04b5705b5604b5304b5204b4f04b4e04b4d01a7f01a7b01a7701a7301a6f01a6b01a6701a6301a5f05a5e01a5d01a5701a5501a5301a5201a4f01a4b01a4701a4301a3f01a3d01a3b01a3901a3701a3501a3301a310197f0697e0197b0197a019770697601973019720196f0196b0196a019670c966019630195702956019550194f0494e0194b0194a019470394601943019420193f0493e0193d0493c0193b0193a01939019380193704936019359c134019330193201931019300192f0192e0192d0687f0687b06877068730886f0786b0a867078630585f0585b05857058530484f0384b03847048430483f0483d0483b048370a835048330182f0182d0182b018270a825018230181f0181d0181b018170a8150181304d6f04d6d01d6b01d6901d6701d6501d6301d610cc6f0cc6d08c6b0cc670cc6508c6306c5f06c5b06c5706c5302b6f02b6d03b6b03b6903b6702b6503b6303b6105b5f05b5b05b5705b5305b4f05b4b05b4705b4303a6f03a6d01a6b01a6901a6701a6501a6301a6103a5f03a5b01a5703a5303a4f03a4b03a4703a4303a3f03a3b03a3703a330196f0196d0196b01969019670196501963019610195f0195b01957019530194f0194b01947019430193f0593e0193b0193701933019320192f0192b01927019230a86f0a86d0786b0a8670a865078630685f0685b06857068530884f0784b0a847078430583f0583b05837058330382f0382b03827038230181f0181d0181b018170a8150181303e7f03e7e04e7d03d7f0cd7d03d7b03d7703d7503d7306d6f06d6b06d6706d6303c7f05c7d03c7b03c7903c7703c7503c7305c7105c6f05c6b05c6705c6305c5f05c5b05c5705c5303b7f03b7e03b7d03b6f03b6e03b6b03b6903b6306b6203b6103b5f03b5b0cb5a03b5703b5603b5303b4f03b4b03b4703b4301a7f01a7d01a7b01a7901a7701a7501a7301a7101a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f05a4e01a4d01a4701a4501a4301a4201a3f01a3b01a3701a330197f0397e0197d9a17c0197b0197a019790197801977039760197503974019730197201971019700196f0696e0196b0196a019670696601963019620195f0195b0195a019570c956019530194702946019450193f0393e0193b0193a019370393601933019320192f0192e0192d0387f0a87d0387b0387703875038730686f0686b06867068630885f0785b0a857078530584f0584b05847058430383f0383b03837038330182f0182d0182b018270a825018230181f0181d0181b018170a8150181307d6f06d6b06d6707d6305c6f05c6b05c6705c6305c5f05c5b05c5705c5303b6f04b6b03b6701b6303b5f04b5b03b5704b5303b4f04b4b03b4704b4303a6f03a6e01a6b01a6a01a6701a6601a6301a6208a5f11a5b11a5a11a5711a5608a5304a4f04a4e04a4b02a4a02a4702a4604a4304a4204a3f04a3e01a3b01a3a01a3701a3601a3301a320196f0196b01967019630195f0195b01957019530194f0194d0194b0194701945019430193f0193b01937019330192f0192d0192b01929019270192501923019210786f0686b06867078630785f0785b07857078530584f0584b05847058430483f0383b03837048330782f0782d0782b0782707825078230181f0181d0181b01817078150181307e7f06e7b06e7707e7305d7f05d7b05d7705d7305d6f05d6b05d6705d6303c7f03c7d04c7b04c7a03c7706c7603c7503c6f04c6b03c6704c6303c5f04c5b03c5704c5303b7f03b7e03b7d04b6f04b6b04b6a04b6711b6604b6304b5f05b5e04b5b04b5a04b5705b5604b5304b5204b4f04b4e04b4d01a7f01a7b01a7701a7301a6f01a6b01a6701a6301a5f05a5e01a5d01a5701a5501a5301a5201a4f01a4b01a4701a4301a3f01a3d01a3b01a3a01a3901a3801a3704a3601a3502a3401a3301a310197f0797e0197b0197a019770697601973019720196f0196b0196a0196711966019630195702956019550194f0494e0194b0194a019470394601943019420193f0493e0193d0493c0193b0193a019390193801937049360193598134019330193201931019300192f0192e0192d0787f0687b06877078730786f0786b07867078630585f0585b05857058530484f0384b03847048430483f0483d0483b0483707835048330182f0182d0182b0182707825018230181f0181d0181b01817078150181311d6f08d6b11d6708d6305c6f05c6b05c6705c6305c5f05c5b05c5705c539d36f9b36b993679736308b5f11b5b11b5708b5305b4f05b4b05b4705b4301a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f05a4e01a4d01a4701a4501a4301a4201a3f01a3b01a3701a330196f0796e0196b0196a019670696601963019620195f0195b0195a0195711956019530194702946019450193f0493e0193b0193a019370393601933019320192f0192e0192d0a86f0a86b0a8670a8630885f0a85b0a857088530584f0584b05847058430a83f0a83b0a8370a8330182f0182d0182b018270a825018230181f0181d0181b018170a8150181306d7a06d7706d7606d6706d6606d6502c7f02c7e02c7b06c7a02c7702c7602c7307c7202c6f02c6e02c6d02c6c02c6b07c6a02c690cc6802c6702c6602c6502c6402c6307c6202c6107c6002c5b08c5a02c599245802c5702c5602c5105b7f05b7b05b7705b7305b6f05b6d05b6b05b6905b6705b6505b6305b6105b5b05b5701b4f01b4e01b4d07a7f06a7b06a7707a7307a6f03a6d07a6b04a6907a6703a6507a6304a6108a5b08a5702a4f03a4d02a4b02a4902a4702a4502a4304a4105a3f05a3b05a3705a330297f0197b02977019730296f0296d0196b01969029670296501963019610195b029570294f0294e0294d0293f0293e0193b019390193305932019310292f0192b02927019230787f068770786f0786d07867078650284f0784d02847028450583f058370782f078270181f0781d028170281506d6f06d6e02d6706d6205c6f05c6b05c6705c6305c5b05c5702b6f02b6e02b6702b6302b6207b5b07b5a02b5702b5605b4f05b4e01b4b01b4a05b4701b4605b4305b4206a6f06a6b06a6706a6308a5b08a5705a4f05a4b05a4705a430ea3f03a3d15a3b04a390ea3703a3515a3304a310296f0196b02967019630195b029570294f0194b02947019430293f0293d0193b01939029370293501933019310292f0192b02927019230686f068670584f058470a83f0a83d0a8370a8350a82f0a8270181f0281706d7f06d7e07d7d06d6f06d6e06d6202c7f02c7e02c7d02c7c02c7b06c7a02c7906c7802c7702c7602c7502c7402c7306c7202c719447002c6f02c6e02c6b06c6a02c6702c6602c6306c6202c5b08c5a02c5702c5605b7f05b7d05b7b05b7905b7705b7505b7305b7105b6f05b6b05b6705b6305b5b05b5701b4f01b4e01b4d06a7f03a7d06a7b04a7906a7703a7506a7304a7106a6f06a6b06a6706a6308a5b08a5702a4f03a4d02a4b02a4902a4702a4502a4304a4105a3f05a3b05a3705a330297f0297d0197b01979029770297501973019710296f0196b02967019630195b029570294f0294e0294d0293f0293e0193b019390193305932019310292f0192b02927019230687f0a87d06877068750686f068670284f0a84d02847028450583f058370a82f0a8270181f0a81d028170281505c6f05c6b05c6705c6305c5f05c5d05c5b05c5705c5505c5307b6f07b6d06b6b06b6a06b6706b660cb6502b6302b5f02b5d06b5b06b5a02b5702b5602b5502b5402b5301b4b05b4705b4307a6f06a6b06a6707a6307a5f07a5b07a5707a5305a4f05a4b05a4705a430ea3f13a3b0ea3713a330296f0196b02967019630295f0295d0195b0295702955019530294f0194b02947019430293f02937019330292f0192b02927019230786f068670785f078570584f058470783f078370782f078270181f0281708d6f9256e08d6708d6205c6f05c6b05c6705c6305c5d05c5b05c5705c5516b6f07b6e0cb6b06b6a0cb6706b6613b6307b6202b5702b5602b5501b4b01b4a05b4701b4605b430ea6f0ca6b0ca6716a6308a5b08a5705a4f05a4b05a4705a430ea3f03a3d1da3b04a390ea3703a3513a3304a310296f0196b02967019630295d0195b02957029550294f0194b02947019430293f0293d0293702935019330292f0192b02927019230a86f0a8670584f058470a83f0a83d0a8370a8350a82f0a8270181f0281707d6f06d6b06d6707d6305c6f05c6b05c6705c6305c5f05c5b05c5705c5302b6f02b6e02b6b02b6a02b6702b6604b6304b6208b5f0eb5b0eb5a0eb570eb5608b5303b4f03b4e01b4b01b4a03b4701b4603b4303b4202a6f03a6b03a6703a6303a5f03a5b03a5703a5303a4f03a4b03a4703a4303a3f03a3d02a3b02a3902a3702a3502a3302a310296f0196b02967019630295f0195b02957019530294f0194b02947019430293f0293d0193b01939029370293501933019310292f0192b02927019230786f0686b06867078630785f0785b07857078530584f0584b05847058430783f0783d0783b0783707835078330382f0382b03827038230181f0281b028170181303e7f04e7e03e7d07d7f06d7b06d7707d7303d6f03d6d03d6b03d670ed6503d6302c7f02c7e02c7b06c7a02c7702c7602c7307c7202c6f02c6e02c6d02c6c02c6b03c6a02c699046802c6702c6602c6502c6402c6303c6202c6103c6002c5f02c5b0ec5a02c5702c5602c5305b7f05b7b05b7705b7303b6f03b6d03b6b05b6903b6705b6503b6303b6105b5f05b5b05b5705b5301b4f01b4e01b4d03a7b06a7a03a7903a7703a7603a7303a7103a6703a6603a6503a5f03a5b03a5703a5302a4f02a4e03a4d03a4c02a4b02a4902a4702a4502a4302a4203a4104a4003a3f03a3b03a3703a330297f0197b02977019730296f0296d0196b01969029670296501963019610295f0195b02957019530294f0294e0294d0293f0293e0193b019390193305932019310292f0192b02927019230787f0687b06877078730386f0386d0386b0386707865038630785f0785b07857078530284f0784d0284b0284702845028430583f0583b05837058330382f0382b03827038230181f0781d0281b02817028150181306d6f06d6b06d6706d6305c6f05c6b05c6705c6305c5f05c5b05c5705c5302b6f02b6e03b6b03b6a02b6702b6602b6302b6208b5f0cb5b0cb5a0cb570cb5608b5304b4f04b4e01b4b01b4a04b4701b4604b4304b4203a6f06a6e02a6b03a6704a6304a6203a5f04a5b04a5a03a570ca5604a5303a4f04a4b03a4704a4302a3f02a3d02a3b02a3902a3702a3504a3304a310296f0196b02967019630295f0195b02957019530294f0194b02947019430293f0293d0193b01939029370293501933019310292f0192b02927019230686f0686b06867068630885f0785b0a857078530584f0584b05847058430a83f0a83d0783b0a8370a835078330482f0382b03827048230181f0281b028170181306e7f06e7b06e7706e7302d7f02d7e02d7b06d7a02d7702d7602d7306d7202d6f02d6b0cd6a02d6702d6602d6305c7f05c7b05c7705c7305c6f05c6b05c6705c6301c5f01c5e01c5d03b7f06b7e03b7d03b7703b7504b7304b7203b6f04b6b04b6a03b670cb6604b6302b5f03b5d02b5b02b5902b5702b5502b5304b5103b4f04b4b03b4704b4303a7703a7603a7504a6f04a6b04a6a04a670ca6604a6302a5f02a5e04a5d8e25c02a5b02a5a02a5902a5802a5702a5602a5502a5402a5302a5204a5104a5004a4f05a4e04a4b04a4a04a4705a4604a4304a4204a3f04a3e04a3d0297f0197b02977019730296f0196b02967019630295f0295e0295d0294f0294e0194b019490194305942019410293f0193b02937019330292f0292d0192b01929029270292501923019210687f0687b06877068730886f0786b0a867078630285f0a85d0285b0285702855028530584f0584b05847058430483f0383b03837048330482f0482d0482b048270a825048230181f0a81d0281b02817028150181306d6f06d6b06d6706d6305c6f05c6b05c6705c6305c5f05c5b05c5705c5302b6f02b6e04b6b04b6a02b6702b6602b6302b6208b5f0cb5b0cb5a0cb570cb5608b5303b4f03b4e01b4b01b4a03b4701b4603b4303b4203a6f03a6e03a6b02a6703a6306a6203a5f03a5b0ca5a03a5703a5603a5303a4f03a4b03a4703a4303a3f03a3d02a3b02a3902a3702a3502a3302a310296f0196b02967019630295f0195b02957019530294f0294e0194b0294701943059420293f0293d0193b01939029370293501933019310292f0192b02927019230686f0686b06867068630885f0785b0a857078530584f0584b05847058430a83f0a83d0783b0a8370a835078330382f0382b03827038230181f0a81d0281b02817028150181303e7f03e7e04e7d03d7f0cd7d03d7b03d7703d7503d7306d6f06d6b06d6706d6302c7f02c7e02c7d02c7c02c7b03c7a02c7903c7802c7702c7602c7502c7402c7303c7202c718c47002c6f02c6e02c6b06c6a02c6702c6602c6306c6202c5f02c5b0cc5a02c5702c5602c5303b7f05b7d03b7b03b7903b7703b7503b7305b7105b6f05b6b05b6705b6305b5f05b5b05b5705b5301b4f01b4e01b4d03a7f03a7e03a7d03a6f03a6e03a6b03a6903a6306a6203a6103a5f03a5b0ca5a03a5703a5603a5302a4f03a4d02a4b02a4902a4702a4502a4303a4103a3f03a3b03a3703a330297f0297d0197b01979029770297501973019710296f0196b02967019630295f0195b02957019530294f0294e0294d0293f0293e0193b019390193305932019310292f0192b02927019230387f0a87d0387b0387703875038730686f0686b06867068630885f0785b0a857078530284f0a84d0284b0284702845028430583f0583b05837058330382f0382b03827038230181f0a81d0281b02817028150181303e7e03e7207d7e07d7204d6e04d6d02c7e06c7a02c7607c7202c6e02c6d02c6c13c6a02c6913c6802c6602c6502c6415c6202c6115c6002c5d08c5a02c5602c5502c5405b6d05b6905b6505b6105b5d05b5501b4e01b4d04a7a06a7604a6904a6104a5904a5102a4e03a4d03a4c02a4902a4502a4204a4104a400296d0196902965019610295d029550294e0294d0293e0193905932019310786d078650785d078550784d028450781d0281507d6f06d6b06d6707d6305c6f05c6b05c6705c6305c5f05c5b05c5705c5302b6f02b6e02b6b02b6a02b6702b6603b6303b6208b5f18b5b13b5a18b5713b5608b5304b4f04b4e01b4b01b4a04b4701b4604b4304b4203a6f04a6b03a6702a6303a5f04a5b03a5704a5303a4f04a4b03a4704a4302a3f02a3d02a3b02a3902a3702a3504a3304a310296f0196b02967019630295f0195b02957019530294f0194b02947019430293f0293d0193b01939029370293501933019310292f0192b02927019230786f0686b06867078630785f0785b07857078530584f0584b05847058430783f0783d0783b0783707835078330482f0382b03827048230181f0781d0281b02817028150181307e7f06e7b06e7707e7302d7f02d7e02d7b06d7a02d7702d7602d7307d7202d6f02d6b16d6a02d6702d6602d6305c7f05c7b05c7705c7305c6f05c6b05c6705c6301c5f01c5e01c5d03b7f03b7d04b7b04b7a03b7706b7603b7503b6f04b6b03b6704b6302b5f02b5e03b5d03b5c02b5b02b5902b5702b5502b5302b5204b5104b5003b4f04b4b03b4704b4303a7f03a7e03a7d04a6f04a6b04a6a04a678a26604a6302a5f02a5e04a5d8925c02a5b02a5a02a5902a5802a5702a5602a5502a5402a5302a5204a5104a5004a4f05a4e04a4d08a4c04a4b04a4a04a4705a4604a4505a4404a4304a4204a3f04a3e04a3d0297f0197b02977019730296f0196b02967019630295f0295e0295d0294f0294e0194b019490194305942019410293f0193b02937019330292f0292d0192b0492a01929019280292702926029250292401923019210787f0687b06877078730786f0786b07867078630285f0785d0285b0285702855028530584f0584b05847058430483f0383b03837048330482f0482d0482b0482707825048230181f0781d0281b02817028150181308e7f08e7702d7f02d7e02d7b06d7a02d7702d7602d7307d7202d6b08d6a02d6702d6605c7f05c7b05c7705c7305c6b05c6701c5f01c5e01c5d03b7f04b7b04b7a03b770cb7604b7303b6d03b6703b6502b5f02b5e03b5d03b5c02b5b02b5902b5702b5502b5302b5204b5104b5003b4f04b4b03b4704b4304a7f07a7e04a7b04a7a04a7706a7604a7304a7203a6703a6603a6502a5f02a5e04a5d0ea5c02a5b02a5a02a5902a5802a5702a5602a5502a5402a5302a5204a5104a5004a4f05a4e04a4b04a4a04a4705a4604a4304a420297f0197b02977019730196b029670295f0295e0295d0294f0294e0194b019490194305942019410293f0193b02937019330292f0292d0192b01929029270292501923019210a87f0a8770285f0a85d02857028550584f058470483f038370482f0482d048270a8250181f0a81d028170281508d6f08d6705c6f05c6b05c6705c6305c5b05c571cb6f07b6e0cb6b06b6a0cb6706b661cb6307b6204b5b04b5a02b5702b5603b4f03b4e01b4b01b4a03b4701b4603b4303b4203a6f03a6b03a6703a6303a5b02a5703a4f03a4b03a4703a4302a3b02a3902a3702a3302a310296f0196b02967019630195b029570294f0194b02947019430293f0293d0193b01939029370293501933019310292f0192b02927019230a86f0a8670584f058470a83f0a83d0a8370a8350382f038270181f0281703e7f03e7e03e7b06e7a03e7703e7603e7307e7208d7f08d7703d6f03d6e04d6d02c7f02c7e02c7b06c7a02c7702c7602c7307c7202c6f02c6e02c6d02c6c02c6b03c6a02c6903c6802c6702c6602c6502c6402c6303c6202c618646002c5b08c5a02c5702c5605b7f05b7b05b7705b7303b6f05b6d03b6b03b6903b6703b6503b6305b6105b5b05b5701b4f01b4e01b4d03a7f03a7b0ca7a03a7703a7603a7303a5b03a5903a5102a4f02a4e03a4d03a4c02a4b02a4902a4702a4502a4302a4203a4104a4003a3f03a3b03a3703a330297f0197b02977019730296f0296d0196b01969029670296501963019610195b029570294f0294e0294d0293f0293e0193b019390193305932019310292f0192b02927019230a87f0a8770386f0a86d03867038650885d0a8550284f0a84d02847028450583f058370382f038270181f0a81d02817028159556f08d6b9356708d6302c6f02c6e02c6b06c6a02c6702c6602c6307c6202c5f02c5b9145a02c5702c5602c5305b6f05b6b05b6705b6305b5f05b5b05b5705b5301b4f01b4e01b4d8f26f8d26b8b2678826308a5f8725b8525708a5302a4f03a4d02a4b02a4902a4702a4502a4304a4105a3f05a3b05a3705a330296f0196b02967019630295f0195b02957019530294f0294e0294d0293f0293e0193b019390193305932019310292f0192b02927019230a86f0a86b0a8670a8630885f0a85b0a857088530284f0a84d0284b0284702845028430583f0583b05837058330a82f0a82b0a8270a8230181f0a81d0281b02817028150181304d6f04d6e01d6b01d6a01d6701d6601d6301d6207c6f06c6b06c6707c6308c5f08c5d08c5b08c5708c5508c5305b6f06b6b05b6707b6303b5f03b5d02b5b02b5903b5703b5503b5302b5105b4f08b4b05b4708b4301a6f03a6b06a6a03a6703a6603a6301a5f01a5d01a5b01a5903a5703a5501a5301a5103a4f03a4b03a4703a4303a3f03a3b03a3703a330196f0196b01967019630195f0195d0195b01959019570195501953019510194f0194b01947019430193f0193b01937019330192f0192b01927019230786f0686b06867078630785f0785d0785b0785707855078530784f0784b07847078430783f0583b05837078330382f0382b03827038230181f0181b018170181303e7f04e7e03e7d07d7f06d7b06d7707d7303d6f03d6d03d6b03d6708d6503d6305c7f06c7b05c7707c7303c6f03c6d03c6b08c6903c6705c6503c6303c6105c5f08c5b05c5708c5303b7b06b7a03b7903b7703b7603b7303b7103b6703b6603b6503b5f03b5b03b5703b5303b4f03b4b03b4703b4301a7f01a7b01a7701a7301a6f01a6d01a6b01a6901a6701a6501a6301a6101a5f01a5b01a5701a5301a4f01a4d01a4b01a4a01a4705a4601a4501a3f01a3b01a3701a330197f0797e0197d0797c0197b0197a0197706976019750697401973019720196f0396e0196d0396c0196b0196a019690196801967039660196583164019630196201961019600195f0195b0195a0195708956019530194f0294e0194d0193f0393e0193b0193a019370393601933019320192f0192e0192d0787f0687b06877078730386f0386d0386b0386707865038630785f0785b07857078530784f0584b05847078430383f0383b03837038330182f0182b01827018230181f0181d0181b0181a07818018170181607815770140181307838108341082c0782006d6f06d6b06d6706d6305c6f06c6b05c6706c6305c5f08c5b05c5708c5303b6f03b6d01b6b03b6703b6504b6303b5f04b5b04b5a03b5708b5604b5303b4f04b4b03b4704b4301a6f01a6e01a6b01a6a03a6703a6601a6301a6208a5f08a5b08a5a08a5708a5608a5302a4f02a4e04a4b04a4a04a4704a4604a4302a4204a3f04a3e01a3b01a3a01a3701a3601a3301a320196f0196b01967019630195f0195b01957019530194f0194b01947019430193f0193b01937019330192f0192d0192b01929019270192501923019210686f0686b06867068630885f0785b08857078530884f0584b05847078430483f0383b03837048338102f1082d0782b8002710825078230181f0181b0181701813 20 1048575 8 255 11 2047 20 1048575
def cc_62_5 : Nat → List (Nat × Nat) := unpackCursorV4 0xc667fc194db9485b2c68a9696a2c6a9929a931618de5387b63813687779c70d6a669a4606635a561585205364f4b77f4843343a4a3e357361823174a2ff182e7182c52222f96197980fb9c0619a00061 0x1e7f01e7e01e7d07d7f06d7702d6f02d6d02d670cd6507c7f06c7b06c7707c7302c6f02c6d02c6b08c6902c6705c6502c6302c6108c5b08c5703b7f04b7b04b7a03b7706b7604b7302b6f02b6d02b6b02b6a04b6904b6802b6702b6603b6503b6402b6302b6103b5d03b5703b5503b4f04b4b03b4704b4304a7f07a7e04a7b04a7a04a7706a7604a7304a7202a6f02a6e02a6d02a6c02a6b02a6a04a6904a6802a6702a6604a650ea6402a6302a6202a6102a6003a5703a5603a5504a4f08a4e04a4b04a4a04a4705a4604a4304a420197b0697a01979029770297601973019710296702966029650195b029570294f0194b02947019430293f0193b02937019330292f0292d0192b01929029270292501923019210787f068770286f0286d02867078650784f078470483f038370482f0482d04827078250181f0281707d6f06d6703c6f01c6e03c6b03c6a03c6703c6601c6301c6204c5b04c5a02c5702c5607b6f06b6b06b6707b6308b5b08b570bb4f05b4d08b4b08b490bb4705b4508b4308b4103a6f03a6b03a6703a6303a5b02a5702a4b02a4902a4702a4302a4103a3f03a3b03a3703a330296f0196b02967019630195b029570294f0294d0194b01949029470294501943019410293f0193b02937019330292f0192b02927019230786f068670784f0784d07847078450783f078370382f038270181f0281701e7f01e7e01e7d03d7f03d7e03d7b06d7a03d7703d7603d7307d7202d6f02d6e02d6d02d6c02d6b02d6a03d69bd56802d6702d6603d6503d6402d6302d6202d6102d6007c7f06c7702c6f02c6d02c670cc6503c5f03c5e04c5d07b7f06b7b06b7707b7302b6f02b6d02b6b08b6902b6705b6502b6302b6103b5f05b5d03b5b03b5903b5703b5503b5308b5108b4b08b4703a7f03a7b06a7a03a7703a7603a7302a6f02a6d02a6b02a6a03a6904a6802a6702a6603a6503a6402a6302a6103a4b03a4903a4103a3f03a3b03a3703a330197b0697a01979029770297601973019710296702966029650295f0295e0295d0295c0195b019590295702955019530395201951019500194b029470293f0193b02937019330292f0192b02927019230787f068770286f0286d02867078650385f0785d03857038550784d078450783f078370382f038270181f0281703d6f03d6d01d6b01d6903d6703d6503d6301d6108c6f08c6d08c6b08c6708c6508c6307c5f06c5b06c5707c5302b6f02b6d04b6b04b6902b6702b6502b6302b6105b5f06b5b05b5707b5305b4f08b4b05b4708b4302a6f02a6d02a6b02a6903a6703a6502a6302a6103a5f03a5b03a5703a5303a4f03a4b03a4703a4302a3f03a3b03a3703a330296f0296d0196b01969029670296501963019610295f0195b02957019530294f0194b02947019430293f0193b02937019330292f0192b02927019230786f0786d0786b0786707865078630785f0685b06857078530784f0784b07847078430783f0583b05837078330382f0382b03827038230181f0281b028170181301e7f01e7e01e7d07d7f06d7b06d7707d7302d6f02d6d02d6b02d6708d6502d6305c7f06c7b05c7707c7302c6f02c6d02c6b08c6902c6705c6502c6302c6105c5f08c5b05c5708c5303b7f07b7e03b7b03b7a03b7706b7603b7303b7202b6f02b6e02b6d02b6c02b6b02b6a03b6903b6802b6702b6603b65bb36402b6302b6202b6102b6003b5f03b5b03b5a03b5708b5603b5303b4f04b4e03b4d03a7f03a7b03a7703a7302a6f02a6d02a6b03a6902a6703a6502a6302a6103a5f03a5b03a5703a5303a4b05a4a03a4903a4703a4603a4303a4103a3703a3603a350197b0697a01979029770297601973019710296702966029650295f0195b02957019530294f0194b02947019430293f0293d0193b01939029370293501933019310292f0192b02927019230787f0687b06877078730286f0286d0286b0286707865028630785f0785b07857078530784f0584b05847078430383f0383d0383b0383707835038330382f0382b03827038230181f0281b028170181304d6f04d6d01d6b01d6904d6704d6504d6301d6108c6f08c6d08c6b08c6708c6508c6307c5f06c5b06c5707c5302b6f02b6d03b6b03b6902b6702b6502b6302b6105b5f06b5b05b5707b5305b4f08b4b05b4708b4302a6f02a6d04a6b04a6902a6702a6502a6302a6103a5f04a5b03a5704a5303a4f04a4b03a4704a4303a3f04a3b03a3702a330296f0296d0196b01969029670296501963019610295f0195b0695a0295702956019530294f0194b02947019430293f0193b02937019330292f0192b02927019230786f0786d0786b0786707865078630785f0685b06857078530784f0784b07847078430783f0583b05837078330482f0382b03827048230181f0281b028170181301e7f01e7e01e7d07d7f06d7b06d7707d7302d6f02d6d02d6b02d6708d6502d6305c7f06c7b05c7707c7302c6f02c6d02c6b08c6902c6705c6502c6302c6105c5f08c5b05c5708c5303b7f04b7b03b7704b7302b6f02b6d02b6b04b6902b6703b6502b6302b6103b5f04b5b03b5704b5303b4f03b4d04b4b04b4a03b4705b4603b4504a7f07a7e04a7d07a7c04a7b04a7a04a7706a7604a7506a7404a7304a7202a6f02a6e02a6d02a6c02a6b02a6a04a6904a6802a6702a6604a65b926402a6302a6202a6102a6004a5f04a5b04a5a04a5708a5604a5303a4f03a4e03a4d04a3f04a3e04a3d0197b0697a01979029770297601973019710296702966029650295f0195b02957019530294f0194b02947019430293f0193b02937019330292f0292d0192b01929029270292501923019210787f0687b06877078730286f0286d0286b0286707865028630785f0785b07857078530784f0584b05847078430483f0383b03837048330482f0482d0482b0482707825048230181f0281b028170181301d6f01d6e01d6d07c6f06c6b06c6707c6302c5f02c5d02c5b02c57c145502c5307b6f06b6b06b6707b6302b5f02b5d02b5b08b5902b5705b5502b5302b510bb4fbf34b0bb470cb4307a6f06a6b06a6707a6302a5f02a5d02a5b04a5902a5703a5502a5302a510ca4fbe24bbc2470ca43ba23f0ba3b0ba37b82330196b0696a01969029670296601963019610295702956029550294f0194b02947019430293f0193b02937019330292f0192b02927019230786f0686b06867078630285f0285d0285b0285707855028530784f0784b07847078430783f0783b07837078330782f0782b07827078230181f0281b028170181306d6f06d6706c6f06c6b06c6706c630bc5b0ac5706b6f06b6b06b6706b630cb5b0cb570bb4f0ab4b0ab470bb4301a6f01a6b01a6701a6301a5b01a5701a4f01a4b01a4701a4301a3f01a3b01a3701a330696f0696b0296a02967029660c95b0c95a0c9570c9560b94f0894e0a94b0594a0a947059460b943089421093f0493e0d93b0393a0d9370393612933049320192f0192e0192701923019220686f0686a06867068660785a0c8560784f0784a078470b8460783f2703e07837078320182f0182e01827018220181f0181e0181d06d6f06d6b06d6706d6306c6f06c6b06c6706c630bc5f0bc5b0bc570bc5306b6f06b6b06b6706b630cb5f0cb5b0cb570cb530bb4f0bb4b0bb470bb4301a6f06a6e01a6d01a6701a6501a6301a6201a5f01a5b01a5a01a570ca5601a5301a4f01a4b01a4701a4301a3f01a3b01a3701a330196702966019650195f0195b0195a019570c956019530194f0894e0194b0194a019470594601943019420193f0493e0193b0193a019370393601933019320192f0192e0192d0686f0686b06867068630c85f0785b0c857078530b84f0784b0b847078432603f0783b1d037078330182f0182b01827018230181f0181d0181b01817b60150181303d6f03d6e01d6b01d6a03d6701d6603d6303d6206c6f06c6b06c6706c6308c5f08c5d08c5b08c5708c5508c5305b6f06b6b05b6706b6302b5f02b5d02b5b02b5902b5702b5504b5304b5105b4f08b4b05b4708b4303a6f03a6b03a6703a6303a5f03a5d02a5b02a5902a5702a5502a5302a5103a4f03a4b03a4703a4302a3f03a3b03a3703a330296f0196b02967019630295f0295d0195b01959029570295501953019510294f0194b02947019430293f0193b02937019330292f0192b02927019230686f0686b06867068630d85f0d85d0785b0d8570d855078530884f0784b08847078430883f0583b05837078330382f0382b03827038230181f0281b028170181301e7f01e7e01e7d02d7f08d7d02d7b02d7702d7502d7306d6f06d6b06d6706d6302c7f05c7d02c7b02c7902c7702c7502c7308c7105c6f06c6b05c6706c6305c5f08c5b05c5708c5302b7f02b7e03b7db437c02b7b02b7a02b7902b7802b7702b7602b7502b7402b7302b7203b7103b7003b6f06b6e03b6b03b6a03b6706b6603b6303b6203b5f03b5b03b5a03b5708b5603b5303b4f04b4e03b4d02a7f02a7e03a7d03a7c02a7b02a7902a7702a7502a7302a7203a7104a7003a6f03a6b03a6703a6303a5f03a5b03a5703a5303a4b05a4a03a4903a4703a4603a4303a4103a3703a3603a350297f0297e0297d0296f0296e0196b019690196306962019610295f0195b0895a0295702956019530294f0194b02947019430293f0293d0193b01939029370293501933019310292f0192b02927019230287f0d87d0287b0287702875028730686f0686b06867068630885f0785b08857078530884f0584b05847078430383f0383d0383b038370d835038330382f0382b03827038230181f0281b028170181304d6f04d6e01d6b01d6a04d6701d6604d6304d6206c6f06c6b06c6706c6308c5f08c5d08c5b08c5708c5508c5305b6f06b6b05b6706b6302b5f02b5d02b5b02b5902b5702b5503b5303b5105b4f08b4b05b4708b4303a6f04a6b03a6704a6302a5f02a5d02a5b02a5902a5702a5504a5304a5103a4f04a4b03a4704a4303a3f04a3b03a3702a330296f0196b02967019630295f0295d0195b01959029570295501953019510294f0194b0894a0294702946019430293f0193b02937019330292f0192b02927019230686f0686b06867068630f85f0f85d0785b0f8570f855078530884f0784b08847078430883f0583b05837078330482f0382b03827048230181f0281b028170181301e7f01e7e01e7d02d7f08d7d02d7b02d7702d7502d7306d6f06d6b06d6706d6302c7f05c7d02c7b02c7902c7702c7502c7308c7105c6f06c6b05c6706c6305c5f08c5b05c5708c5302b7f02b7e03b7d03b7c02b7b02b7902b7702b7502b7302b7204b7104b7003b6f04b6b03b6704b6303b5f04b5b03b5704b5303b4f03b4d04b4b04b4a03b4705b4603b4502a7f02a7e04a7db227c02a7b02a7a02a7902a7802a7702a7602a7502a7402a7302a7204a7104a7004a6f06a6e04a6d07a6c04a6b04a6a04a6706a6604a6506a6404a6304a6204a5f04a5b04a5a04a5708a5604a5303a4f03a4e03a4d04a3f04a3e04a3d0297f0297e0297d0296f0296e0196b019690196306962019610295f0195b0895a0295702956019530294f0194b02947019430293f0193b02937019330292f0292d0192b0492a01929019280292702926029250292401923019210287f0f87d0287b0287702875028730686f0686b06867068630885f0785b08857078530884f0584b05847078430483f0383b03837048330482f0482d0482b048270f825048230181f0281b028170181301d6f01d6e01d6d02c6f0cc6d02c6b02c6702c6502c6306c5f06c5b06c5706c5302b6f05b6d02b6b02b6902b6702b6502b6308b6106b5f06b5b06b5706b530bb4f0cb4b0bb470cb4302a6f03a6d02a6b02a6902a6702a6502a6304a6106a5f06a5b06a5706a530ca4f0ca4b0ca470ca43b323f0ba3b0ba37b12330296f0296e0296d0295f0295e0195b019590195306952019510294f0194b0c94a0294702946019430293f0193b02937019330292f0192b02927019230286f0f86d0286b0286702865028630685f0685b06857068530c84f0784b0c847078430f83f0783b0b837078330f82f0782b0f827078230181f0281b028170181307d6f06d6b06d6707d6307c6f06c6b06c6707c630bc5f0bc5b0bc570bc5307b6f06b6b06b6707b630cb5f11b5b11b570cb530bb4f0bb4b0bb470bb4301a6f01a6d01a6b01a6a01a6706a6601a6501a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3b01a3701a330196f0296e0196d0195f0195b0195a0195711956019530194f0894e0194b0194a019470594601943019420193f0493e0193b0193a019370393601933019320192f0192e0192d0786f0686b06867078630785f0785b07857078530784f0784b07847078430783f0783b07837078330182f0182b01827018230181f0181d0181b01817078150181307c6e06c6608b6f08b6b08b6708b6308b4905b450ca6f0ca6b0ca670ca6304a4903a4508a3f08a3b08a3708a330296f0196b029670196301959029450293f0193b02937019330292f0192b029270192307d6f06d6707c6f06c6b06c6707c6308c5b08c5703b6f04b6b03b6701b6304b5b03b5703b4f04b4b03b4704b4303a6f03a6e01a6b01a6a01a6701a6601a6301a6204a5b02a5a02a5702a5608a4f08a4e0ba4b05a4a0ba4705a4608a4308a4204a3f04a3e01a3b01a3a01a3701a3601a3301a320196f0196b01967019630195d0195b01957019550194f0194b01947019430193f0193b01937019330192f0192d0192701925019230786f068670784f078470483f038370782f0782d07827078250181f0181707e7f06e7707d7f06d7b06d7707d7308d6b08d6703c7f03c7d04c7b04c7a03c7706c7603c7504c6b03c6703c5f04c5b03c5704c5303b7f03b7e03b7d04b6b04b6a04b670cb6604b5f08b5e04b5b04b5a04b5705b5604b5304b5204b4f04b4e04b4d01a7f01a7b01a7a01a7706a7601a7301a6d01a6701a6501a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3d01a3b01a3a01a3901a3801a3704a3601a3502a3401a3301a310197f0797e0197b0197a019770697601973019720196702966019650195f0895e0195b0195a019570595601953019520194f0494e0194b0194a019470394601943019420193f0493e0193d0493c0193b0193a0193901938019370493601935ad134019330193201931019300787f068770785f078570484f038470483f0483d04837078350182f018270181f0181d018170781507c6f08c6b0ac6707c6307b6f0cb6b0cb6707b6308b4f0ab4b0ab4708b4301a6f01a6b01a6701a6301a4f01a4b01a4701a4301a3f01a3b01a3701a330796f0796e0c96b0696a0c9670696607963079620894f0894e0a94b0594a0a9470594608943089421093f0493e0d93b0393a0d9370393612933049320b8460182e0181e0cd6f0cd670bc6f08c6b0bc6708c6308c5b08c570eb6f0cb6b0cb67ac3630eb5b0eb5708b4f0bb4b0bb4708b4301a6f01a6b01a6a01a670ca6601a6301a5d01a5701a5501a4f01a4b01a4701a4301a3f01a3b01a3701a330196f0796e0196b0196a019670696601963019620195702956019550194f0894e0194b0194a019470594601943019420193f0493e0193b0193a019370393601933019324c06f0c8670884f0b8472503f0e8370182f018270181f0181d01817ab01503d6f06d6707d6302c6f02c6e02c6b02c6702c6307c6202c5f02c5e01c5b01c5902c5702c5304c5201c5101c5007b6f06b6b06b6707b630bb5f08b5b0bb5708b5302b4f05b4d02b4b02b4702b4502b4303a6f04a6b04a6a03a6706a6602a6304a5b03a5704a5302a4f02a4b02a4902a4702a4304a4103a3f04a3b03a3704a330296f0196b0696a0296702966019630295f0295e0195b01959029570195311952019510293f0193b02937019330292f0192b02927019230786f068670785f078570284f0784d02847028450783f078370482f038270181f0281702e7f02e7e02e7b06e7a02e7702e7602e7307e7207d7f06d7701d6f01d6e01d6d07c7f06c7b06c7707c7302c6f05c6d02c6b02c6902c6702c6502c6308c6108c5b08c5703b7f03b7d04b7b04b7a03b7706b7603b7502b6f03b6d02b6b02b6902b6702b6502b6304b6104b5b03b5703b4f04b4b03b4704b4303a7f03a7e03a7d02a6f02a6e04a6d11a6c02a6b02a6a02a6902a6802a6702a6602a6502a6402a6302a6204a6104a6004a5d04a5b04a5a04a570ca5604a55a925404a4f08a4e04a4b04a4a04a4705a4604a4304a4204a3f04a3e04a3d0297f0197b0697a0297702976019730195b01959019510294f0194b02947019430293f0193b02937019330292f0292d0192b0492a01929019280292702926029250292401923019210787f068770286f0786d02867028650784f078470483f038370482f0482d04827078250181f0281702d6f02d6e02d6b06d6a02d6702d6602d6307d620cc6f0cc6701c5f01c5e01c5d0bb6f08b6b0bb6708b6302b5f05b5d02b5b02b5902b5702b5502b5308b5108b4b08b470ea6f0ca6b0ca67a826302a5f03a5d02a5b02a5902a5702a5502a5304a510ea4b0ea4708a3f0ba3b0ba3708a330296f0196b0c96a0296702966019630194b01949019410293f0193b02937019330292f0192b02927019230f86f0c8670285f0f85d02857028550883f0b8370f82f0e8270181f0281707b5f07b5b07b5707b5307a5f07a5b07a5707a5308a3f08a3b08a3708a330195f0195b01957019530193f0193b01937019330192f0192b019270192308b5f08b5b08b5708b530ca5f0ca5b0ca570ca5308a3f08a3b08a3708a330195f0195b01957019530193f0193b01937019330192f0192b019270192308c6f08c6b08c6708c630cb6f0cb6b0cb670cb6308b4f08b4b08b4708b4301a6f01a6b01a6701a6301a5501a4f01a4b01a4701a4301a3f01a3b01a3701a330796e069660894e059460493e039360192ea6018a501403e7f04e7e03e7d07d7f06d7b06d7707d7303d6f03d6d03d6b03d6708d6503d6305c7f06c7b05c7707c7303c6f03c6d03c6b08c6903c6705c6503c6303c6105c5f08c5b05c5708c5302b7f07b7e02b7b02b7a02b7706b7602b7302b7202b6f03b6e02b6d03b6c02b6b02b6a02b6902b6802b6703b6602b650bb6402b6302b6202b6102b6002b5f02b5b02b5a02b5708b5602b5301b4f01b4e01b4d03a7b06a7a03a7903a7703a7603a7303a7103a6703a6603a6503a5f03a5b03a5703a5303a4f03a4b03a4703a4302a3f02a3d02a3b03a3902a3703a3502a3302a310297f0197b02977019730296f0296d0196b01969029670296501963019610295f0195b02957019530194b0594a01949029470294601943019410293702936029350292f0192b02927019230787f0687b06877078730386f0386d0386b0386707865038630785f0785b07857078530784f0584b05847078430283f0283d0283b0283707835028330382f0382b03827038230181f0281b028170181306e7f06e7b06e7706e7305d7f06d7b05d7706d7305d6f08d6b05d6708d6302c7f06c7e02c7b02c7a02c7706c7602c7302c7202c6f02c6b02c6a02c6708c6602c6301c5f01c5e01c5d03b7f06b7e03b7d03b7703b7504b7304b7203b6f04b6b04b6a03b6708b6604b6303b5f04b5b03b5704b5302b4f02b4d02b4b04b4902b4703b4502b4302b4103a7703a7603a7504a6f04a6b04a6a04a6708a6604a6304a5f08a5e04a5b04a5a04a5705a5604a5304a5202a4f02a4e02a4d02a4c02a4b02a4a04a4904a4802a4702a4604a450ba4402a4302a4202a4102a4004a3f04a3e04a3d0297f0197b02977019730296f0196b02967019630195b0595a01959029570295601953019510294702946029450293f0193b02937019330292f0292d0192b01929029270292501923019210687f0687b06877068730886f0786b08867078630885f0585b05857078530284f0284d0284b028470b845028430483f0383b03837048330482f0482d0482b048270f825048230181f0281b028170181303e7f03e7e04e7d03d7f08d7d03d7b03d7703d7503d7306d6f06d6b06d6706d6303c7f05c7d03c7b03c7903c7703c7503c7308c7105c6f06c6b05c6706c6305c5f08c5b05c5708c5302b7f03b7e02b7d0bb7c02b7b02b7a02b7902b7802b7703b7602b7503b7402b7302b7202b7102b7002b6f06b6e02b6b02b6a02b6706b6602b6302b6202b5f02b5b02b5a02b5708b5602b5301b4f01b4e01b4d03a7f03a7e03a7d03a6f03a6e03a6b03a6903a6306a6203a6103a5f03a5b08a5a03a5703a5603a5303a4f03a4b03a4703a4302a3f02a3d02a3b03a3902a3703a3502a3302a310297f0297e0297d0297c0197b019790297702975019730397201971019700296f0196b02967019630295f0195b02957019530194b0594a01949029470294601943019410293702936029350292f0192b02927019230387f0d87d0387b0387703875038730686f0686b06867068630885f0785b08857078530884f0584b05847078430283f0283d0283b028370b835028330382f0382b03827038230181f0281b028170181307e7f06e7b06e7707e7305d7f06d7b05d7707d7305d6f08d6b05d6708d6302c7f07c7e02c7b02c7a02c7706c7602c7302c7202c6f02c6b02c6a02c6708c6602c6301c5f01c5e01c5d03b7f03b7d04b7b04b7a03b7706b7603b7503b6f04b6b03b6704b6303b5f04b5b03b5704b5302b4f02b4d02b4b04b4902b4703b4502b4302b4103a7f03a7e03a7d04a6f04a6b04a6a04a6708a6604a6304a5f08a5e04a5d08a5c04a5b04a5a04a5705a5604a5505a5404a5304a5202a4f02a4e02a4d02a4c02a4b02a4a04a4904a4802a4702a4604a450ba4402a4302a4202a4102a4004a3f04a3e04a3d0297f0197b02977019730296f0196b02967019630195b0595a01959029570295601953019510294702946029450293f0193b02937019330292f0292d0192b01929029270292501923019210787f0687b06877078730786f0786b07867078630785f0585b05857078530284f0284d0284b0284707845028430483f0383b03837048330482f0482d0482b0482707825048230181f0281b028170181308d6f08d6b08d6708d6305c6f08c6b05c6708c6305c5f08c5b05c5708c5302b6f07b6e02b6b02b6a02b6706b6602b6302b6202b5f02b5b02b5a02b5708b5602b5301b4f01b4e01b4da326fa226ba1267a026308a5f08a5b08a5708a5308a4f05a4b05a4708a4302a3f02a3d02a3b04a3902a3703a3502a3302a310296f0196b02967019630295f0195b02957019530194b0594a01949029470294601943019410293702936029350292f0192b02927019230f86f0a86b0f8670a8630885f0885b08857088530884f0584b05847088430283f0283d0283b028370b835028330f82f0a82b0f8270a8230181f0281b0281701813 20 1048575 8 255 11 2047 20 1048575
def cc_62_6 : Nat → List (Nat × Nat) := unpackCursorV4 0xab120a5061a014f99e6393b638ec4f86d7f7eb827945773f556de616be2063f7f5f54a5a84d523854d74c4bf184a61948422423613aa7935d4d2e07d2914f230611cf6117c5311b610cc4f07f4d0007f 0x5c6f08c6b05c6708c6305c5507b6e06b6608b4e0ca6f0ca6b0ca670ca6308a4f05a4b05a4708a4304a3903a350c96f0b96b0c9670b9630894f0594b059470894301939029350e92f0b92b0e9270b92303d6f04d6e03d6d07c6f06c6b06c6707c6303c5f03c5d03c5b03c570ec5503c5307b6f06b6b06b6707b6303b5f03b5d03b5b08b5903b5705b5503b5303b510cb4f0eb4b0eb470cb4303a6b06a6a03a6903a6703a6603a6303a6103a5703a5603a5503a4f03a4b03a4703a4303a3f03a3b03a3703a330796f0696b06967079630395f0295d0395b01959039570295503953019510c94f0e94b0e9470c943a313f9d13b8f137821330392f0392b03927039230786f0686b06867078630385f0385d0385b0385707855038530784f0784b07847078430783f0783b07837078330382f0382b03827038230781f0781b078170781306d6f06d6706c6f06c6b06c6706c630cc5b0ac5703b6f04b6b03b6704b6304b5b03b5703b4f04b4b03b4704b4306a6f06a6b03a6a03a6703a660ca5b0ca5a0ca570ca5610a4f08a4e0aa4b05a4a0aa4705a4614a4308a4204a3f04a3e03a3704a3304a320696f0696b06967069630c95b0c9570f94f0a94b0a947149430493f0393b03937049330f92f0292d1092b019290f9270292519923019210686f0686a06867068660785a0c8560784f078470483f0483e03837048320482f0482e0482d0781f0781706d6f06d6b06d6706d6306c6f06c6b06c6706c630cc5f0cc5b0cc570cc5303b6f06b6e03b6d03b6703b6504b6304b6203b5f04b5b04b5a03b570cb5604b5303b4f04b4b03b4704b4303a6703a6603a6504a5f04a5b04a5a04a570ca5604a5304a4f08a4e04a4b04a4a04a4705a4604a4304a4204a3f04a3e04a3d0696f0696b06967069630c95f0c95b0c9570c953a214f9b14b8d1477e1430493f0393b03937049330492f0292d0492b01929049270292504923019210686f0686b06867068630c85f0785b0c857078533804f0784b31047078430483f0383b03837048330482f0482d0482b04827dc025048231501f0781b090170781303d6f03d6e04d6d03c6f0cc6d03c6b03c6703c6503c6306c5f06c5b06c5706c5303b6f05b6d03b6b03b6903b6703b6503b6308b6106b5f06b5b06b5706b530cb4f0cb4b0cb470cb4303a6f03a6e03a6d03a5f03a5e03a5b03a5903a5306a5203a5103a4f03a4b0ca4a03a4703a4603a4303a3f03a3b03a3703a330396f0296d0396b01969039670296503963019610695f0695b06957069530c94f0c94b0c9470c943a113f9913b8b1377c1330392f0392b03927039230386f0d86d0386b0386703865038630685f0685b06857068530c84f0784b0c847078430d83f0783b0d837078330382f0382b03827038230d81f0781b0d8170781307d6f06d6705c6f06c6b05c6707c6305c5d04c5b05c5705c5503b6f03b6e06b6b06b6a06b6706b6607b6303b6204b5b04b5a05b5705b5604b4b04b4a04b4704b4604b4303a6f04a6b03a6704a6304a5b03a5703a4f04a4b03a4704a4303a3f03a3d04a3b04a3903a3703a3504a3304a310796f0696b06967079630895b089570894f0594b05947089431693f0293d0b93b0193916937029350b933019310492f0392b03927049230786f068670784f058470783f0783d07837078350482f038270781f0781707e7f06e7705d7f06d7b06d7a05d7706d7607d7305d6d05d6705d6507c7f07c7e06c7b06c7a06c7706c7607c7307c7205c6705c6605c6503b7f03b7d04b7b04b7a03b7706b7603b7504b6b03b6703b5f04b5b03b5704b5303b4f03b4d04b4b04b4903b4703b4504b4304b4103a7f03a7e03a7d04a6b04a6a04a6708a6604a5f08a5e04a5d08a5c04a5b04a5a04a5705a5604a5505a5404a5304a5204a4f08a4e04a4d08a4c04a4b04a4a04a4904a4804a4708a4604a45d924404a4304a4204a4104a4004a3f04a3e04a3d0797f0697b06977079730896b089670895f0595b05957089530894f0294d0894b01949089470294508943019410493f0393b03937049330492f0292d0492b01929049270292504923019210787f068770785f058570784f0784d07847078450483f038370482f0482d04827078250781f0781705e7f05e7e05e7b06e7a05e7705e7605e7307e7207d7f06d7705d6f05d6e08d6d05c7f05c7b06c7a05c7705c7605c7305c5b05c5905c5103b7f03b7d04b7b04b7a03b7706b7603b7503b6f03b6d04b6b04b6903b6703b6504b6304b6104b5b03b5703b4f04b4b03b4704b4303a7f03a7e03a7d04a6f05a6e04a6d08a6c04a6b04a6a04a6904a6804a6705a6604a6505a6404a6304a6204a6104a6004a5d04a5b04a5a04a5708a5604a55d625404a4f05a4e04a4d08a4c04a4b04a4a04a4705a4604a4505a4404a4304a4204a3f04a3e04a3d0797f0697b06977079730596f0296d0596b01969059670296505963019610895b089570594f0594b05947059430493f0393b03937049330492f0292d0492b01929049270292504923019210787f068770586f0786d05867058650584f058470483f038370482f0482d04827078250781f0781705d6f05d6e05d6b05d6705d6307d6203c6f06c6707c6305c5f05c5e04c5b04c5904c5704c5304c5204c5104c5005b6f05b6b06b6a05b6705b6605b6305b4f05b4e05b4b05b4904b4705b4308b4205b4103a6f04a6b04a6a03a6706a6604a6303a5f04a5b04a5903a5704a5304a5104a4b03a4704a4303a3f04a3b03a3704a330796f0696b06967079630595f0295d0595b0595702955059530b94f0b94b0b9470b9430593f0593b05937059330492f0392b03927049230786f068670585f0785d05857058550784f078470583f058370482f038270781f0781703d6f03d6e06d6707d6303d6207c6f07c6e06c6707c6204c5f04c5e04c5d07b6f06b6b06b6707b6315b5f05b5d08b5b08b5913b5705b5508b5308b510cb4d08b4b08b47d634503a6f04a6b04a6a03a6706a6604a6304a5b04a5903a5704a5304a5104a4b04a4903a4704a4103a3f04a3b03a3704a330796f0696b06967079631595f0295d1195b01959139570295511953019510c94d0c94b0c947a91450893f1193b8a137089330492f0392b03927049230786f068670785f0785d07857078550784d078450783f078370482f038270781f0781707d6f06d6b06d6707d6307c6f06c6b06c6707c630cc5fd845bd74570cc5303b6f03b6d04b6b04b6a03b6706b6603b6503b5f04b5b03b5704b5303b4f04b4b03b4704b4303a6f03a6e03a6d04a5f04a5b04a5a04a57d525604a5304a4f08a4e04a4b04a4a04a4705a4604a4304a4204a3f04a3e04a3d0796f0696b06967079630c95fac15ba81570c953a014f9714b881477a1430493f0393b03937049330492f0292d0492b01929049270292504923019210786f0686b06867078630785f0785b07857078530784f0784b07847078430483f0383b03837048330482f0482d0482b0482707825048230781f0781b078170781307c6e06c6608b6f08b6b08b6708b6308b4905b4503a6f03a6b03a6703a6303a5903a4503a3f03a3b03a3703a330c96f0c96b0c9670c96301949029450893f0893b08937089330392f0392b039270392305e7f07e7e05e7d07d7f06d7705d6f05d6d05d6708d6505c7b06c7a05c7905c7705c7605c7305c7105c6705c6605c6505c5b05c5703b7f04b7b04b7a03b7706b7604b7303b6f03b6d04b6b04b6a04b6904b6803b6705b6603b6503b6404b6304b6103b5d03b5703b5503b4f04b4b03b4704b4304a7f07a7e04a7b04a7a04a7706a7604a7304a7204a6f05a6e04a6d05a6c04a6b04a6a04a6904a6804a6705a6604a650ea6404a6304a6204a6104a6003a5703a5603a5504a4f05a4e04a4b04a4a04a4705a4604a4304a420797f0697b06977079730596f0296d0596b01969059670296505963019610895b089570594f0594b05947059430493f0393b03937049330492f0292d0492b01929049270292504923019210787f068770586f0586d05867078650584f058470483f038370482f0482d04827078250781f078170cd6f0cd67d246f08c6b0cc6708c6308c5b08c5703b6f04b6b04b6a03b670cb6604b6303b5d03b5703b5503b4f04b4b03b4704b4304a6f07a6e04a6b04a6a04a6706a6604a6304a6203a5703a5603a5504a4f08a4e04a4b04a4a04a4705a4604a4304a42be16f0c96b0c967119630e95b0e9570894f1194b87147089430493f0393b03937049330492f0292d0492b01929049270292504923019215006f0c8670884f300470483f038370482f0482d048270e8251181f0801707d6f06d6703c6f03c6e03c6b03c6a03c6703c6607c6307c6204c5b04c5a05c5704c5603b6f05b6b05b6705b6305b5b05b5705b4f05b4d03b4b03b4903b4703b4503b4303b4103a6f03a6b03a6703a6303a5b03a5703a4b03a4903a4703a4303a4103a3f03a3b03a3703a330796f0696b06967079630895b089570b94f0294d0b94b019490b947029450b943019410593f0593b05937059330392f0392b03927039230786f068670784f0784d07847078450583f058370382f038270781f0781705e7f07e7e05e7d03d7f03d7e03d7b06d7a03d7703d7603d7307d7203d6f03d6e03d6d03d6c03d6b05d6a03d69d056803d6703d6603d6503d6403d6305d6203d6105d6007c7f06c7705c6f05c6d05c6708c6503c5f03c5e04c5d05b7b06b7a05b7905b7705b7605b7305b7105b6705b6605b6503b5f03b5e05b5d05b5c03b5b03b5903b5703b5503b5303b5205b5108b5005b4b05b4703a7f03a7b06a7a03a7703a7603a7303a6f03a6d03a6b05a6a03a6904a6803a6703a6603a6503a6403a6303a6103a4b03a4903a4103a3f03a3b03a3703a330797f0697b06977079730596f0296d0596b01969059670296505963019610395f0295d0395b01959039570295503953019510894b089470593f0593b05937059330392f0392b03927039230787f068770586f0586d05867078650385f0785d03857038550784d078450583f058370382f038270781f0781703d6f03d6e03d6b06d6a03d6703d6603d6307d620cc6f0cc6703c5f03c5e04c5dcf36f08b6b0cb6708b6303b5f05b5d03b5b03b5903b5703b5503b5308b5108b4b08b4703a6f03a6b0ca6a03a6703a6603a6303a4b03a4903a4103a3f03a3b03a3703a33bc16f0c96b0c967119630395f0295d0395b01959039570295503953019510e94b0e9470893f1193b85137089330392f0392b03927039230d86f0c8670385f0d85d03857038550d84d0d8450883f0d8370382f038270d81f0d81707b5f07b5b07b5707b5303a5f04a5b03a5704a5303a3f04a3b03a3704a330795f0795b07957079530893f0893b08937089330492f0392b039270492308b5f08b5b08b5708b5303a5f04a5b03a5704a5303a4503a3f04a3b03a3704a330c85f0c85b0c8570c8530883f0883b08837088330482f0382b038270482308c6f08c6b08c6708c6303b6f04b6b03b6704b6303b5503b4f04b4b03b4704b4307a6e06a6608a4e05a4604a3e0c96f0c96b0c9670c9630894f0894b08947089430493f0393b03937049330192902925cd028cc02408d6f08d6b08d6708d6305c6f08c6b05c6708c6305c5f08c5b05c5708c5303b6f07b6e03b6b03b6a03b6706b6603b6303b6203b5f03b5b03b5a03b5708b5603b5303b4f04b4e03b4d03a6f03a6b03a6703a6303a5f03a5b03a5703a5303a4b05a4a03a4903a4703a4603a4303a4103a3703a3603a35ba16f0b96bb31670b9630895f0895b08957089530894f0594b05947089430393f0293d0393b01939039370293503933019310392f0392b03927039230d86f0a86b0d8670a8630885f0885b08857088530884f0584b05847088430383f0383d0383b038370d835038330382f0382b03827038230b81f0a81b0d8170a81306d7a06d7706d7606d6706d6606d6505c7f05c7b05c7705c7305c6f05c6d05c6b05c6905c6705c6505c6305c6105c5b05c5703b7f04b7b03b7704b7303b6f03b6d04b6b04b6903b6703b6504b6304b6104b5b03b5703b4f05b4e03b4d03b4703b4504b4304b4204a7f07a7e04a7b04a7a04a7706a7604a7304a7204a6f07a6e04a6d07a6c04a6b04a6a04a6904a6804a6707a6604a650ca6404a6304a6204a6104a6004a5b04a5a04a5708a5603a4703a4603a4504a3f04a3e04a3d0797f0697b06977079730796f0296d0796b01969079670296507963019610895b089570594f0594b05947059430493f0393b03937049330492f0292d0492b01929049270292504923019210787f068770786f0786d07867078650584f058470483f038370482f0482d04827078250781f0781704d6b04d6904d6704d6304d6107c6f07c6d04c6704c6506c5f04c5703b6f03b6d05b6b05b6905b6703b6505b6305b6105b5f05b5b05b5705b5305b4b05b4703a6f03a6d04a6b04a6903a6703a6504a6304a6103a5f04a5b03a5704a5304a4b03a4703a3f04a3b03a3704a330b96f0296d0b96b019690b967029650b963019610695f0695b06957069530894b089470593f0593b05937059330492f0392b03927049230a86f0a86d0a8670a8650685f068570583f058370482f038270a81f0a81706d7f06d7e07d7d06d6f06d6e06d6205c7f05c7e05c7d05c7c05c7b05c7905c7705c7505c7306c7205c7108c7005c6f05c6b05c6705c6305c5b05c5703b7f03b7d04b7b04b7903b7703b7504b7304b7103b6f04b6b03b6704b6304b5b03b5703b4f05b4e03b4d03b4703b4504b4304b4204a7f06a7e04a7dc827c04a7b04a7a04a7904a7804a7706a7604a7506a7404a7304a7204a7104a7004a6f06a6e04a6b04a6a04a6706a6604a6304a6204a5b04a5a04a5708a5603a4703a4603a4504a3f04a3e04a3d0697f0297d0697b01979069770297506973019710696f0696b06967069630895b089570594f0594b05947059430493f0393b03937049330492f0292d0492b01929049270292504923019210687f0a87d06877068750686f068670584f058470483f038370482f0482d048270a8250a81f0a81713d6f07d6e0cd6b06d6a0cd6706d6616d6307d6208c6f08c6704c5f04c5e04c5d05b6f05b6b05b6705b6305b5f03b5d05b5b03b5703b5505b4d05b4b05b4705b4503a6f04a6b03a6704a6304a5b04a5903a5704a5304a5104a4b04a4903a4704a4103a3f04a3b03a3704a330b96f0b96b0b9670b9630b95f0295d0b95b019590b957029550b953019510894b089470593f0593b05937059330492f0392b03927049230a86f0a8670a85f0a85d0a8570a8550884d0a8450583f058370482f038270a81f0a817c956f08d6bc756708d6305c6f05c6b05c6705c6305c5f05c5b05c5705c5303b6f04b6b03b6704b6303b5f04b5b03b5704b5303b4f05b4e03b4d03b4703b4504b4304b4204a6f07a6e04a6b04a6a04a6706a6604a6304a6204a5f04a5b04a5a04a57c625604a5303a4703a4603a4504a3f04a3e04a3d0b96f0b96b0b9670b9630895f0b95b0b957089530594f0594b05947059430493f0393b03937049330492f0292d0492b01929049270292504923019210a86f0a86b0a8670a8630885f0a85b0a857088530584f0584b05847058430483f0383b03837048330482f0482d0482b048270a825048230a81f0a81b0a8170a8130ed6f08d6b0ed6708d6303c6f03c6e03c6b06c6a03c6703c6603c6307c6203c5f03c5b0ec5a03c5703c5603c5305b6f05b6b05b6705b6305b5f05b5b05b5705b5303b4f03b4e04b4d03a6f03a6b03a6703a6303a5f03a5b03a5703a5303a4f03a4e03a4d03a3f03a3e03a3b03a3903a3305a3203a310b96f0b96b0b9670b9630895f0b95b0b957089530394f0294d0394b01949039470294503943019410593f0593b05937059330392f0392b03927039230a86f0a86b0a8670a8630885f0a85b0a857088530384f0a84d0384b0384703845038430583f0583b05837058330382f0382b03827038230a81f0a81b0a8170a81307d6f08d6705c6f08c6b05c6707c6308c5b05c5703b6f04b6b03b6704b6304b5b03b5703b4f04b4b03b4704b4307a6f07a6e17a6b06a6a10a6706a6607a6307a6208a5b08a5a08a5708a5603a4f03a4e05a4708a4303a4204a3f04a3e03a3704a3304a320796f0b96b0f967079630895b089570894f0594b05947089430493f0393b03937049330f92f0292d0b92b019290f927029250b923019210786f0a86a07867440660885a088560884f0884e05847088420483f0483e03837048320482f0482e0482d0a81f0a81a0a8170601608d6f08d6b08d6708d6305c6f08c6b05c6708c6305c5f08c5b05c5708c5303b6f04b6b03b6704b6303b5f04b5b03b5704b5303b4f03b4d04b4b04b4a03b4705b4603b4504a6f07a6e04a6b04a6a04a6706a6604a6304a6204a5f04a5b04a5a04a5708a5604a5303a4f03a4e03a4d04a3f04a3e04a3db816f0b96bb11670b9630895f0895b08957089530894f0594b05947089430493f0393b03937049330492f0292d0492b01929049270292504923019214e06f0a86b430670a8630885f0885b08857088530884f0584b05847088430483f0383b03837048330482f0482d0482b04827c3025048230b81f0a81b050170a81301d6b01d6906d6707d6301d6102c6f02c6e02c6d07c5f07c5e06c5707c520bb6f05b6d08b6b08b690bb6705b6508b6308b6107b5f06b5b06b5707b5308b4b08b470ea6f03a6d13a6b04a690ea6703a6515a6304a6107a5f06a5b06a5707a530ca4b0ca4708a3f0ba3b0ba3708a330296f0296d0196b02967029650295f0195b0695a0295702956019530294d0194b02947029450293f0193b02937019330292f0192b02927019230786f0786d07867078650785f068570783f078370782f078270181f0281706d6f06d6d01d6b01d6906d6706d6507d6301d6102c6f02c6d05c6705c6507c5f06c5702b6f02b6d02b6702b6502b6305b5f06b5b05b5707b5302b4b05b470ea6f03a6d16a6b04a690ea6703a6516a6304a6107a5f06a5b06a5707a5308a4b08a4708a3f05a3b05a3708a330296f0296d0196b01969029670296501963019610295f0195b02957019530194b029470293f0193b02937019330292f0192b02927019230786f0786d07867078650785f068570783f058370782f078270181f0281701e7f01e7e01e7d07d7f06d7702d6f02d6d02d6708d6505c7f06c7b06c7a05c7706c7607c7302c6f02c6d02c6b02c6a08c6908c6802c6702c6605c6505c6402c6302c6105c5d05c5705c5507b7f07b7e06b7b06b7a06b7706b7607b7307b7202b6f02b6e02b6d02b6c02b6b02b6a08b6908b6802b6702b6608b65c036402b6302b6202b6102b6005b5705b5605b5507a7f06a7b06a7707a7302a6f02a6d02a6b04a6902a6703a6502a6302a6108a5b08a5708a4f05a4b05a4708a4308a3f03a3d08a3b04a3908a3703a3508a3304a310197b0697a01979029770297601973019710296702966029650195b029570294f0194b02947019430293f0293d0193b01939029370293501933019310292f0192b02927019230787f068770286f0286d02867078650784f058470783f0783d07837078350782f078270181f02817 20 1048575 8 255 11 2047 20 1048575
def cc_62_7 : Nat → List (Nat × Nat) := unpackCursorV4 0x261489448237b384f2207987ee61ef9878e61d79872e61bf986ce619fa85e13d47e14813ceee32f58c8ce120260749818e884a3309528004a 0x6c6a06c6706c6606c5706c5606c5507b6f06b6b06b6707b6307b5f05b5d07b5b08b5907b5705b5507b5307b5108b4b08b4707a6f06a6b06a6707a6307a5f03a5d07a5b04a5907a5703a5507a5304a510ca4b0ca4708a3fc923b0ea3708a330796f0696b06967079630795f0295d0795b01959079570295507953019510c94b0c9470893f1193b95137089336612f0e92b0e927119230786f068670785f0785d07857078550783f078370782f078270781f0781706d6e06c6606b6f06b6b06b6706b6308b4905b4506a6f06a6b06a6706a6304a4903a4508a3f08a3b08a3708a330696f0696b069670696301949029450893f0893b08937089330e92f0e92b0e9270e9230ab6f05b6d08b6b08b690ab6705b6508b6308b6106b5f06b5b06b5706b530da6f03a6d12a6b04a690da6703a6510a6304a6106a5f06a5b06a5706a5308a3f0aa3b0aa3708a330f96f0296d1196b019690f9670296510963019610695f0695b06957069530893f0a93b0a937089330f92f0d92b0d9271192306866068562b02e06c6f06c6e07c6d06c5f06c5e06c5206b6f05b6d06b6b06b6906b6705b6506b6308b6106b5f06b5b06b5706b5308b4b08b4706a6f03a6d06a6b04a6906a6703a6506a6304a6106a5f06a5b06a5706a530ca4b0ca4708a3fc723b0ea3708a330696f0296d0696b01969069670296506963019610695f0695b06957069530c94b0c9470893f1193b93137089336412f0e92b0e927119230686ff506d06867068650685f068570883f340372a02f0e8271181f1101707b5f06b5b06b5707b5307a5f06a5b06a5707a5308a3f08a3b08a3708a330795f0695b06957079530893f0893b08937089330e92f0e92b0e9270e92305b5f05b5b05b5705b5307a5f06a5b06a5707a5305a3f05a3b05a3705a330795f0695b06957079530593f0593b05937059330b92f0b92b0b9270b92307b5f06b5b06b5707b5304a5f04a5b04a5704a5304a3f04a3b04a3704a330795f0695b06957079530893f0893b08937089330492f0492b049270492303b5f03b5b03b5703b5307a5f06a5b06a5707a5303a3f03a3b03a3703a330795f0695b06957079530393f0393b03937039330892f0892b089270892307b5f06b5b06b5707b5307a5f06a5b06a5707a5308a3f08a3b08a3708a330195f0195b01957019530193f0193b01937019330192f0192b019270192302b5f02b5b02b5702b5307a5f06a5b06a5707a5302a3f02a3b02a3702a330795f0695b06957079530293f0293b02937029330892f0892b089270892307b5f06b5b06b5707b5307a5f06a5b06a5707a5308a3f08a3b08a3708a330795f0695b06957079530893f0893b08937089330d92f0d92b0d9270d92307a5f06a5b06a5707a530795f0695b06957079530892f0892b08927089230785f0685b06857078530882f0882b08827088230e81f0e81b0e8170e81306d6607c6e07b6f06b6b06b6707b6308b49f334805b45f234407a6f06a6b06a6707a6304a49f124803a45f024408a3f08a3b08a3708a330796f0696b069670796301949ef14802945ee1440893f0893b08937089330e92f0e92b0e9270e923ed048ec04407d6b07d6906d6707d6307d6105c6f05c6e05c6d07c5f07c5e06c5707c5205b6f05b6d05b6b05b6705b6505b5f05b5b06b5a05b5705b5605b5305b4d05b4b05b4705b450ea6f03a6d13a6b04a690ea6703a6515a6304a6107a5f06a5b06a5707a5308a4b08a4705a3f05a3b05a3705a330b96f0296d0b96b019690b967029650b963019610795f0695b06957079530894b089470593f0593b05937059330b92f0b92b0b9270b9230786f0786d07867078650785f068570583f058370782f078270781f0781705d6f07d6e05d6d07c6f06c6b06c6707c6305c5f05c5d05c5b05c57ea45505c5305b6b06b6a05b6905b6705b6605b6305b6105b5705b5605b5505b4f05b4b05b4705b4307a6f06a6b06a6707a6305a5f03a5d05a5b04a5905a5703a5505a5304a5108a4fd224bcf24708a4305a3f05a3b05a3705a330796f0696b06967079630595f0295d0595b01959059570295505953019510894f0b94b0b947089430593f0593b05937059330b92f0b92b0b9270b9230786f0686b06867078630585f0585d0585b0585707855058530784f0784b07847078430583f0583b05837058330782f0782b07827078230781f0781b078170781306d6f06d6705c6f06c6b05c6706c6308c5b05c5706b6f06b6b05b6a05b6705b6608b5b08b5a08b5708b5607b4f07b4e05b4707b4307b4206a6f06a6b06a6706a6308a5b08a5708a4f05a4b05a4708a430da3f03a3d10a3b04a390da3703a3512a3304a310696f0696b06967069630895b089570894f0594b05947089430f93f0293d0b93b019390f937029350b933019310f92f0b92b0d9270b9230686f0686a06867068660784f0884e05847078420683f0683e0683d0782f078270781f0781a078170f01606d6f06d6b06d6706d6305c6f06c6e05c6d05c6705c6506c6306c6205c5f08c5b08c5a05c5708c5608c5305b6705b6605b6506b5f06b5b06b5a06b5708b5606b5306b4f07b4e06b4d06a6f06a6b06a6706a6308a5f08a5b08a5708a5308a4f05a4b05a4708a4306a3f03a3d06a3b04a3906a3703a3506a3304a310696f0696b06967069630895f0895b08957089530894f0594b05947089430693f0293d0693b01939069370293506933019316212f0b92b591270b9230686f0686b06867068630885f0785b08857078530884f0584b05847078430683f0683d0683b06837e8035068332902f0782b1f027078230b81f0781b0e0170781305d6f05d6e06d6d05c6f0cc6d05c6b05c6705c6505c6306c5f06c5b06c5706c5305b6f05b6e05b6d05b5f05b5e05b5b05b5905b5306b5205b5105b4f05b4b0cb4a05b4705b4605b4305a6f03a6d05a6b04a6905a6703a6505a6304a6106a5f06a5b06a5706a5308a4f0ca4b0ca4708a4305a3f05a3b05a3705a330596f0296d0596b01969059670296505963019610695f0695b06957069530894f0b94b0b947089430593f0593b05937059330b92f0b92b0b9270b9230586f0a86d0586b0586705865058630685f0685b06857068530884f0784b0a847078430583f0583b05837058330a82f0782b0a827078230a81f0781b0a8170781307d6f06d6b06d6707d6305c6f05c6d06c6b06c6a05c6706c6605c6505c5f08c5b05c5708c5305b6f05b6e05b6d07b5f07b5b07b5a07b5708b5607b5306b4f06b4e06b4d07a6f06a6b06a6707a6308a5f08a5b08a5708a5308a4f05a4b05a4708a4307a3f03a3d07a3b04a3907a3703a3507a3304a310796f0696b06967079630895f0895b08957089530894f0594b05947089430793f0293d0793b01939079370293507933019316012f0b92b571270b9230786f0686b06867078630785f0785b07857078530784f0584b05847078430783f0783d0783b0783707835078330782f0782b07827078230781f0781b078170781305b5f05b5b05b5705b5307a5f07a5b07a5707a5305a3f05a3b05a3705a330795f0795b07957079530593f0593b05937059330b92f0b92b0b9270b92305a5f05a5b05a5705a530c95f0c95b0c9570c9530592f0592b05927059230b85f0b85b0b8570b8530582f0582b05827058230b81f0b81b0b8170b81307c6e06c6605b6f05b6b05b6705b6305b5905b450ca6f0ca6b0ca670ca6304a4903a4505a3f05a3b05a3705a330b96f0b96b0b9670b96301949029450593f0593b05937059330b92f0b92b0b9270b923e4048e304405c6f08c6b05c6707c6307b6f07b6e0cb6b06b6a0cb6706b6607b6307b6207a6f0ca6b0ca6707a6308a4f05a4b05a4708a430da3f03a3d10a3b04a390da3703a3512a3304a310796f0b96b0c967079630894f0594b05947089430f93f0293d0b93b019390f937029350b933019310f92f0b92b0d9270b9230884e0883e0c01608d6f08d6705c6f08c6b08c6a05c670cc6608c6305c5d05c5705c5508b6f07b6e08b6b06b6a08b6706b6608b6307b6205b5705b5605b550ea6f0ca6b0ca67d826308a5b08a5708a4f05a4b05a4708a4308a3f03a3d08a3b04a3908a3703a3508a3304a31bf16f0b96b0c9670b9630895b089570894f0594b05947089430893f0293d0893b01939089370293508933019315e12f0b92b0e9270b9235106f0c8670884f058470883f0883d08837e10352802f0e8270b81f0b01705d6f05d6e05d6b06d6a05d6705d6605d6307d6208c6f08c6705c5f05c5e08c5d05b6f05b6b08b6a05b6705b6605b6305b4b05b4905b410ea6f0ca6b0ca67d726305a5f03a5d05a5b04a5905a5703a5505a5304a5108a4b08a4705a3f05a3b05a3705a330b96f0b96b0b9670b9630595f0295d0595b01959059570295505953019510894b089470593f0593b05937059330b92f0b92b0b9270b9230a86f0a8670585f0885d05857058550583f058370a82f0a8270a81f0a817 18 262143 7 127 11 2047 20 1048575
def cur_62 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (cc_62_7 (Nat.sub p 224)) (cc_62_6 (Nat.sub p 192)) (Nat.blt p 224)) (Bool.rec (cc_62_5 (Nat.sub p 160)) (cc_62_4 (Nat.sub p 128)) (Nat.blt p 160)) (Nat.blt p 192)) (Bool.rec (Bool.rec (cc_62_3 (Nat.sub p 96)) (cc_62_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (cc_62_1 (Nat.sub p 32)) (cc_62_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 128)
def f_62 : Nat → Nat × Nat := unpackForestF 0x18be0316fd43680c57ec691d8d13b12476244ec291d8513b02476044018a7d515405aff4035016b602d5c05a9f1848e308802d3f841a80b4b0168e02d0c052fee025014b60295f65226ac5bd58afacd17552b00a530149fa51bc0525e8568cf6de0291f30146602401486028ff1ab7e427cc6acf8c958051d80a37c304a028cee22ae0364b86977092ef6b45c247bb6c9708fee5325c233012bf6c05404adda37cb147f649f2c51980957012a60253eb49a55b63ab02a0252ea52a542630128f4a062940a00943a04df409ae8133d02630127f3c5925db7ce134976d7345f25db3cc134976c6024ee16b7ca47085acf255ba162d48468854df1c9721535c6470854cf1299a252e42a63854b70d182152b80937832c8d0dbe0017c00277f268d0dadf4be343677b268d0d8da00c34015694bed296da52bb4a53690bed216da42bb48536905ed20ada413b5c5b6b8a6d4151a411b401401266bb5bd953e2ed6763488bb1ad85222ec635f488bb16d752b0092f01256b4d215e35ac348578c60249d540a80923478aaa4d911da5a3a4b4f4c88e8cd34b22394b4a2c8940511c99a4164472460217c042da20243f46684050fc99a00143f2460215c04298084f010960211c04219c26b0107e020ecd63818567308b464970c1359825b0106e5a0b0b412008332b0f84759c8e3591c5b27028465ac8cad9201423286020bc0415903481a8d63c53068b58d94c1b0283450c04138b85c170a80208c55b58081f01036249c00eb387a480f088071ac312406044038b6148e00db581b5b064700c0d00da181a5a030ac0205c04098003f 8 11
set_option maxHeartbeats 0 in
theorem rc_62 : dagCheckRootsV4 fullMask g_62 ep_62 248 bds_62 (dagTraceF fullMask rootStock 11 f_62) (cur_62 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_0 : treeBlockF 0 32 (dagCheckNodeV4 fullMask g_62 ep_62 bds_62 248 (dagTraceF fullMask rootStock 11 f_62) cur_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_1 : treeBlockF 32 64 (dagCheckNodeV4 fullMask g_62 ep_62 bds_62 248 (dagTraceF fullMask rootStock 11 f_62) cur_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_2 : treeBlockF 64 96 (dagCheckNodeV4 fullMask g_62 ep_62 bds_62 248 (dagTraceF fullMask rootStock 11 f_62) cur_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_3 : treeBlockF 96 128 (dagCheckNodeV4 fullMask g_62 ep_62 bds_62 248 (dagTraceF fullMask rootStock 11 f_62) cur_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_4 : treeBlockF 128 160 (dagCheckNodeV4 fullMask g_62 ep_62 bds_62 248 (dagTraceF fullMask rootStock 11 f_62) cur_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_5 : treeBlockF 160 192 (dagCheckNodeV4 fullMask g_62 ep_62 bds_62 248 (dagTraceF fullMask rootStock 11 f_62) cur_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_6 : treeBlockF 192 224 (dagCheckNodeV4 fullMask g_62 ep_62 bds_62 248 (dagTraceF fullMask rootStock 11 f_62) cur_62) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_7 : treeBlockF 224 248 (dagCheckNodeV4 fullMask g_62 ep_62 bds_62 248 (dagTraceF fullMask rootStock 11 f_62) cur_62) = true := by decide +kernel
theorem nj_62_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 fullMask g_62 ep_62 bds_62 248 (dagTraceF fullMask rootStock 11 f_62) cur_62) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_62_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_62_1 h1 h2)
theorem nj_62_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeV4 fullMask g_62 ep_62 bds_62 248 (dagTraceF fullMask rootStock 11 f_62) cur_62) i = true := block_join nj_62_1 (fun _ h1 h2 => treeBlockF_at nb_62_2 h1 h2)
theorem nj_62_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeV4 fullMask g_62 ep_62 bds_62 248 (dagTraceF fullMask rootStock 11 f_62) cur_62) i = true := block_join nj_62_2 (fun _ h1 h2 => treeBlockF_at nb_62_3 h1 h2)
theorem nj_62_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeV4 fullMask g_62 ep_62 bds_62 248 (dagTraceF fullMask rootStock 11 f_62) cur_62) i = true := block_join nj_62_3 (fun _ h1 h2 => treeBlockF_at nb_62_4 h1 h2)
theorem nj_62_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeV4 fullMask g_62 ep_62 bds_62 248 (dagTraceF fullMask rootStock 11 f_62) cur_62) i = true := block_join nj_62_4 (fun _ h1 h2 => treeBlockF_at nb_62_5 h1 h2)
theorem nj_62_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeV4 fullMask g_62 ep_62 bds_62 248 (dagTraceF fullMask rootStock 11 f_62) cur_62) i = true := block_join nj_62_5 (fun _ h1 h2 => treeBlockF_at nb_62_6 h1 h2)
theorem nj_62_7 : ∀ i, 0 ≤ i → i < 248 → (dagCheckNodeV4 fullMask g_62 ep_62 bds_62 248 (dagTraceF fullMask rootStock 11 f_62) cur_62) i = true := block_join nj_62_6 (fun _ h1 h2 => treeBlockF_at nb_62_7 h1 h2)
theorem nc_62 : ∀ i, 0 ≤ i → i < 248 → (dagCheckNodeV4 fullMask g_62 ep_62 bds_62 248 (dagTraceF fullMask rootStock 11 f_62) cur_62) i = true := nj_62_7
theorem lb_62 : LowerBin fullMask rootStock g_62 12 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_62 kn_62 sub_62 gl_62 rc_62 nc_62

def wg : List Gate := [⟨GateOp.and, [0, 2]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [5, 8]⟩, ⟨GateOp.or, [3, 9]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.and, [0, 11]⟩, ⟨GateOp.or, [0, 11]⟩, ⟨GateOp.or, [6, 9]⟩, ⟨GateOp.and, [3, 14]⟩, ⟨GateOp.or, [7, 12]⟩, ⟨GateOp.or, [15, 16]⟩, ⟨GateOp.and, [13, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4008241280 * 2 ^ 32 + 3902842880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4008241280 * 2 ^ 32 + 3902842880)) (13 - 1) := by
  rw [show canon fullMask (4008241280 * 2 ^ 32 + 3902842880) = g_62 by decide]
  exact lb_62

end PEqualNP.Outside.L_meta_49273

theorem PEqualNP.Outside.L_meta_49273 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241280 * 2 ^ 32 + 3902842880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241280 * 2 ^ 32 + 3902842880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_49273.table2_from_lowerBin (4008241280 * 2 ^ 32 + 3902842880) 13 PEqualNP.Outside.L_meta_49273.root_lb PEqualNP.Outside.L_meta_49273.wg 18 rfl PEqualNP.Outside.L_meta_49273.wfits PEqualNP.Outside.L_meta_49273.weval
