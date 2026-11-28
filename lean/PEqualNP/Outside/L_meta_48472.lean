import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48472

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

def m_0 : Nat := 0xaaaa
def s_0 : List Nat := [0x2222, 0xa0a, 0xaa]
def g_0 : Nat := 0x22a
def ep_0 : Nat := 0x28000000000000020800000000000002200000000000000000
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

def m_1 : Nat := 0x5050505000000000
def s_1 : List Nat := [0x1010101000000000, 0x50005000000000, 0x505000000000]
def g_1 : Nat := 0x10105000000000
def ep_1 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000000000000000000
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

def m_2 : Nat := 0x5500550000000000
def s_2 : List Nat := [0x1100110000000000, 0x500050000000000, 0x550000000000]
def g_2 : Nat := 0x100150000000000
def ep_2 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000000000000000000
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

def m_3 : Nat := 0xff0000
def s_3 : List Nat := [0x550000, 0x330000, 0xf0000]
def g_3 : Nat := 0x170000
def ep_3 : Nat := 0x6000000000000001200000000000000140000
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

def m_4 : Nat := 0x4444444400000000
def s_4 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_4 : Nat := 0x4044400000000
def ep_4 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
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

def m_5 : Nat := 0x5000500050005000
def s_5 : List Nat := [0x1000100010001000, 0x500000005000, 0x50005000]
def g_5 : Nat := 0x100010005000
def ep_5 : Nat := 0x1000400000001000000040000000000000000000000000000000000000001000100000000000000000000000
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

def m_6 : Nat := 0x3333000000000000
def s_6 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_6 : Nat := 0x113000000000000
def ep_6 : Nat := 0x12000000000000010200000000000000000000000000000110000000000000
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

def m_7 : Nat := 0x5555000000000000
def s_7 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_7 : Nat := 0x115000000000000
def ep_7 : Nat := 0x14000000000000010400000000000001100000000000000000000000000000
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

def m_8 : Nat := 0x222200002222
def s_8 : List Nat := [0x20200000202, 0x2200000022, 0x2222]
def g_8 : Nat := 0x200000222
def ep_8 : Nat := 0x22000000000000000000000000200000020000000020000020000000000000000000000000000000000
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

def m_9 : Nat := 0xa0a00000a0a
def s_9 : List Nat := [0x20200000202, 0xa0000000a, 0xa0a]
def g_9 : Nat := 0x20000020a
def ep_9 : Nat := 0x20800000000000000000000000200000008000000000000000000000002000002000000000000000000
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

def m_10 : Nat := 0xaa000000aa
def s_10 : List Nat := [0x2200000022, 0xa0000000a, 0xaa]
def g_10 : Nat := 0x20000002a
def ep_10 : Nat := 0x2800000000000000000000000000000000000000020000000800000002000000200000000000000000
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

def m_11 : Nat := 0xff000000000000
def s_11 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_11 : Nat := 0x17000000000000
def ep_11 : Nat := 0x600000000000000120000000000000014000000000000
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

def m_12 : Nat := 0xf000f0
def s_12 : List Nat := [0x500050, 0x300030, 0xf0]
def g_12 : Nat := 0x100070
def ep_12 : Nat := 0x600000000000000000000000000000000000000000001000200000000000100040
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

def m_13 : Nat := 0xf0f000000000000
def s_13 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_13 : Nat := 0x107000000000000
def ep_13 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
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

def m_14 : Nat := 0x4400440044004400
def s_14 : List Nat := [0x400040004000400, 0x440000004400, 0x44004400]
def g_14 : Nat := 0x40004004400
def ep_14 : Nat := 0x400400000000400000040000000000000000000000004000400000000000000000000000000000000000000
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

def m_15 : Nat := 0x5500000055000000
def s_15 : List Nat := [0x1100000011000000, 0x500000005000000, 0x55000000]
def g_15 : Nat := 0x100000015000000
def ep_15 : Nat := 0x1400000000000000000000000000000000000000010000000400000001000000100000000000000000000000
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

def m_16 : Nat := 0x22222222
def s_16 : List Nat := [0x2020202, 0x220022, 0x2222]
def g_16 : Nat := 0x20222
def ep_16 : Nat := 0x2200000000000020020000000000002020000000000000000000000000000000000
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

def m_17 : Nat := 0xa0a0a0a
def s_17 : List Nat := [0x2020202, 0xa000a, 0xa0a]
def g_17 : Nat := 0x2020a
def ep_17 : Nat := 0x2080000000000020008000000000000000000000000000202000000000000000000
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

def m_18 : Nat := 0xaa00aa
def s_18 : List Nat := [0x220022, 0xa000a, 0xaa]
def g_18 : Nat := 0x2002a
def ep_18 : Nat := 0x280000000000000000000000000002000800000000000200200000000000000000
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

def m_19 : Nat := 0xcc00cc
def s_19 : List Nat := [0x440044, 0xc000c, 0xcc]
def g_19 : Nat := 0x4004c
def ep_19 : Nat := 0x480000000000000000000000000004000800000000000000000000000000040040
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

def m_20 : Nat := 0xf00ff00f00000000
def s_20 : List Nat := [0x5005500500000000, 0x3003300300000000, 0xf000f00000000, 0xf00f00000000]
def g_20 : Nat := 0x7100700000000
def ep_20 : Nat := 0x1000000000000000000000000000000000000000000000021002000000000004100400000000
theorem epk_20 : ep_20 = edgePack m_20 g_20 := by decide +kernel
def bds_20 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_20 : KnownBin bds_20 := by intro b hb; simp [bds_20] at hb
theorem sub_20 : ∀ b ∈ bds_20, m_20 &&& b.1 = b.1 := by intro b hb; simp [bds_20] at hb
theorem gl_20 : ∀ b ∈ bds_20, canon b.1 g_20 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_20] at hb
def cur_20 : Nat → List (Nat × Nat) := unpackCursorV4 0xb146850932244890e8701 0x292874f0d30248243e80c982e508901a105800f 7 127 3 7 9 511 14 16383
def f_20 : Nat → Nat × Nat := unpackForestF 0x54a047c23279e08b844421a298148042c00f 4 9
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV4 m_20 g_20 ep_20 11 bds_20 (dagTraceF m_20 s_20 4 f_20) (cur_20 0) s_20 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_20 : treeBlockF 0 11 (dagCheckNodeV4 m_20 g_20 ep_20 bds_20 11 (dagTraceF m_20 s_20 4 f_20) cur_20) = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 11 → (dagCheckNodeV4 m_20 g_20 ep_20 bds_20 11 (dagTraceF m_20 s_20 4 f_20) cur_20) i = true := fun _ h1 h2 => treeBlockF_at nb_20 h1 h2
theorem lb_20 : LowerBin m_20 s_20 g_20 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_20 kn_20 sub_20 gl_20 rc_20 nc_20

def m_21 : Nat := 0xf00ff00f
def s_21 : List Nat := [0x50055005, 0x30033003, 0xf000f, 0xf00f]
def g_21 : Nat := 0x1007500f
def ep_21 : Nat := 0x40080000000000000000000000000000000000000000100200000000000010045000
theorem epk_21 : ep_21 = edgePack m_21 g_21 := by decide +kernel
def bds_21 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_21 : KnownBin bds_21 := by intro b hb; simp [bds_21] at hb
theorem sub_21 : ∀ b ∈ bds_21, m_21 &&& b.1 = b.1 := by intro b hb; simp [bds_21] at hb
theorem gl_21 : ∀ b ∈ bds_21, canon b.1 g_21 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_21] at hb
def cur_21 : Nat → List (Nat × Nat) := unpackCursorV4 0x72e18b060c0681 0xa92a4cb62a699252900f 7 127 3 7 6 63 10 1023
def f_21 : Nat → Nat × Nat := unpackForestF 0x1b6c86a33194c80f 3 6
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV4 m_21 g_21 ep_21 7 bds_21 (dagTraceF m_21 s_21 4 f_21) (cur_21 0) s_21 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21 : treeBlockF 0 7 (dagCheckNodeV4 m_21 g_21 ep_21 bds_21 7 (dagTraceF m_21 s_21 4 f_21) cur_21) = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 7 → (dagCheckNodeV4 m_21 g_21 ep_21 bds_21 7 (dagTraceF m_21 s_21 4 f_21) cur_21) i = true := fun _ h1 h2 => treeBlockF_at nb_21 h1 h2
theorem lb_21 : LowerBin m_21 s_21 g_21 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_21 kn_21 sub_21 gl_21 rc_21 nc_21

def m_22 : Nat := 0xf00f0000f00f0000
def s_22 : List Nat := [0x5005000050050000, 0x3003000030030000, 0xf0000000f0000, 0xf00f0000]
def g_22 : Nat := 0x7000010070000
def ep_22 : Nat := 0x1000000000000000000000000000000000000000000000000000000000020000100200000004000010040000
theorem epk_22 : ep_22 = edgePack m_22 g_22 := by decide +kernel
def bds_22 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_22 : KnownBin bds_22 := by intro b hb; simp [bds_22] at hb
theorem sub_22 : ∀ b ∈ bds_22, m_22 &&& b.1 = b.1 := by intro b hb; simp [bds_22] at hb
theorem gl_22 : ∀ b ∈ bds_22, canon b.1 g_22 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_22] at hb
def cur_22 : Nat → List (Nat × Nat) := unpackCursorV4 0xb146850932244890e8701 0x292874f0d30248243e80c982e508901a105800f 7 127 3 7 9 511 14 16383
def f_22 : Nat → Nat × Nat := unpackForestF 0x54a047c23279e08b844421a298148042c00f 4 9
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV4 m_22 g_22 ep_22 11 bds_22 (dagTraceF m_22 s_22 4 f_22) (cur_22 0) s_22 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_22 : treeBlockF 0 11 (dagCheckNodeV4 m_22 g_22 ep_22 bds_22 11 (dagTraceF m_22 s_22 4 f_22) cur_22) = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 11 → (dagCheckNodeV4 m_22 g_22 ep_22 bds_22 11 (dagTraceF m_22 s_22 4 f_22) cur_22) i = true := fun _ h1 h2 => treeBlockF_at nb_22 h1 h2
theorem lb_22 : LowerBin m_22 s_22 g_22 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_22 kn_22 sub_22 gl_22 rc_22 nc_22

def m_23 : Nat := 0xf00f0000f00f
def s_23 : List Nat := [0x500500005005, 0x300300003003, 0xf0000000f, 0xf00f]
def g_23 : Nat := 0x10070000500f
def ep_23 : Nat := 0x400800000000000000000000000000000000000000000000000000001002000000000000100400005000
theorem epk_23 : ep_23 = edgePack m_23 g_23 := by decide +kernel
def bds_23 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_23 : KnownBin bds_23 := by intro b hb; simp [bds_23] at hb
theorem sub_23 : ∀ b ∈ bds_23, m_23 &&& b.1 = b.1 := by intro b hb; simp [bds_23] at hb
theorem gl_23 : ∀ b ∈ bds_23, canon b.1 g_23 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_23] at hb
def cur_23 : Nat → List (Nat × Nat) := unpackCursorV4 0x72e18b060c0681 0xa92a4cb62a699252900f 7 127 3 7 6 63 10 1023
def f_23 : Nat → Nat × Nat := unpackForestF 0x1b6c86a33194c80f 3 6
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV4 m_23 g_23 ep_23 7 bds_23 (dagTraceF m_23 s_23 4 f_23) (cur_23 0) s_23 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_23 : treeBlockF 0 7 (dagCheckNodeV4 m_23 g_23 ep_23 bds_23 7 (dagTraceF m_23 s_23 4 f_23) cur_23) = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 7 → (dagCheckNodeV4 m_23 g_23 ep_23 bds_23 7 (dagTraceF m_23 s_23 4 f_23) cur_23) i = true := fun _ h1 h2 => treeBlockF_at nb_23 h1 h2
theorem lb_23 : LowerBin m_23 s_23 g_23 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_23 kn_23 sub_23 gl_23 rc_23 nc_23

def m_24 : Nat := 0xc00cc00cc00cc00c
def s_24 : List Nat := [0x4004400440044004, 0xc000c000c000c, 0xc00c0000c00c, 0xc00cc00c]
def g_24 : Nat := 0x400040004400c
def ep_24 : Nat := 0x400800000000000040080000000000000000000000000000000000000000000000000004000400044000
theorem epk_24 : ep_24 = edgePack m_24 g_24 := by decide +kernel
def bds_24 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_24 : KnownBin bds_24 := by intro b hb; simp [bds_24] at hb
theorem sub_24 : ∀ b ∈ bds_24, m_24 &&& b.1 = b.1 := by intro b hb; simp [bds_24] at hb
theorem gl_24 : ∀ b ∈ bds_24, canon b.1 g_24 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_24] at hb
def cur_24 : Nat → List (Nat × Nat) := unpackCursorV4 0x72e18b060c0681 0xae5733d1969244a00f 7 127 3 7 5 31 9 511
def f_24 : Nat → Nat × Nat := unpackForestF 0x3ebc393231300f 3 5
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV4 m_24 g_24 ep_24 7 bds_24 (dagTraceF m_24 s_24 4 f_24) (cur_24 0) s_24 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_24 : treeBlockF 0 7 (dagCheckNodeV4 m_24 g_24 ep_24 bds_24 7 (dagTraceF m_24 s_24 4 f_24) cur_24) = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 7 → (dagCheckNodeV4 m_24 g_24 ep_24 bds_24 7 (dagTraceF m_24 s_24 4 f_24) cur_24) i = true := fun _ h1 h2 => treeBlockF_at nb_24 h1 h2
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_24 kn_24 sub_24 gl_24 rc_24 nc_24

def m_25 : Nat := 0xcc330000cc33
def s_25 : List Nat := [0x441100004411, 0x3300000033, 0xc0300000c03, 0xcc33]
def g_25 : Nat := 0x41300004433
def ep_25 : Nat := 0x402000000000000000000000000000000000000004020000000000000000000000000000041000004400
theorem epk_25 : ep_25 = edgePack m_25 g_25 := by decide +kernel
def bds_25 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_25 : KnownBin bds_25 := by intro b hb; simp [bds_25] at hb
theorem sub_25 : ∀ b ∈ bds_25, m_25 &&& b.1 = b.1 := by intro b hb; simp [bds_25] at hb
theorem gl_25 : ∀ b ∈ bds_25, canon b.1 g_25 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_25] at hb
def cur_25 : Nat → List (Nat × Nat) := unpackCursorV4 0x72e18b060c0681 0xa92a4cb62a699252900f 7 127 3 7 6 63 10 1023
def f_25 : Nat → Nat × Nat := unpackForestF 0x1b6c86a33194c80f 3 6
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV4 m_25 g_25 ep_25 7 bds_25 (dagTraceF m_25 s_25 4 f_25) (cur_25 0) s_25 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25 : treeBlockF 0 7 (dagCheckNodeV4 m_25 g_25 ep_25 bds_25 7 (dagTraceF m_25 s_25 4 f_25) cur_25) = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 7 → (dagCheckNodeV4 m_25 g_25 ep_25 bds_25 7 (dagTraceF m_25 s_25 4 f_25) cur_25) i = true := fun _ h1 h2 => treeBlockF_at nb_25 h1 h2
theorem lb_25 : LowerBin m_25 s_25 g_25 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_25 kn_25 sub_25 gl_25 rc_25 nc_25

def m_26 : Nat := 0x4411441144114411
def s_26 : List Nat := [0x11001100110011, 0x401040104010401, 0x441100004411, 0x44114411]
def g_26 : Nat := 0x11041104114411
def ep_26 : Nat := 0x400400000000400000040000000000000000000000004000400000000000000000000000000000000000000
theorem epk_26 : ep_26 = edgePack m_26 g_26 := by decide +kernel
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
theorem kn_26 : KnownBin bds_26 := by
  intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_14
theorem sub_26 : ∀ b ∈ bds_26, m_26 &&& b.1 = b.1 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_26 : ∀ b ∈ bds_26, canon b.1 g_26 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_26 : Nat → List (Nat × Nat) := fun _ => []
def f_26 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV4 m_26 g_26 ep_26 0 bds_26 (dagTraceF m_26 s_26 4 f_26) (cur_26 0) s_26 4 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_26 g_26 ep_26 bds_26 0 (dagTraceF m_26 s_26 4 f_26) cur_26 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_26 : LowerBin m_26 s_26 g_26 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_26 kn_26 sub_26 gl_26 rc_26 nc_26

def m_27 : Nat := 0xc030c030c030c030
def s_27 : List Nat := [0x4010401040104010, 0x30003000300030, 0xc0300000c030, 0xc030c030]
def g_27 : Nat := 0x10001000104030
def ep_27 : Nat := 0x402000000000000040200000000000000000000000000000000000000000000000000010001000104000
theorem epk_27 : ep_27 = edgePack m_27 g_27 := by decide +kernel
def bds_27 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_27 : KnownBin bds_27 := by intro b hb; simp [bds_27] at hb
theorem sub_27 : ∀ b ∈ bds_27, m_27 &&& b.1 = b.1 := by intro b hb; simp [bds_27] at hb
theorem gl_27 : ∀ b ∈ bds_27, canon b.1 g_27 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_27] at hb
def cur_27 : Nat → List (Nat × Nat) := unpackCursorV4 0x72e18b060c0681 0xae5733d1969244a00f 7 127 3 7 5 31 9 511
def f_27 : Nat → Nat × Nat := unpackForestF 0x3ebc393231300f 3 5
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV4 m_27 g_27 ep_27 7 bds_27 (dagTraceF m_27 s_27 4 f_27) (cur_27 0) s_27 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27 : treeBlockF 0 7 (dagCheckNodeV4 m_27 g_27 ep_27 bds_27 7 (dagTraceF m_27 s_27 4 f_27) cur_27) = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 7 → (dagCheckNodeV4 m_27 g_27 ep_27 bds_27 7 (dagTraceF m_27 s_27 4 f_27) cur_27) i = true := fun _ h1 h2 => treeBlockF_at nb_27 h1 h2
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_27 kn_27 sub_27 gl_27 rc_27 nc_27

def m_28 : Nat := 0xcc330000cc330000
def s_28 : List Nat := [0x4411000044110000, 0x33000000330000, 0xc0300000c030000, 0xcc330000]
def g_28 : Nat := 0x13000004130000
def ep_28 : Nat := 0x400000000000000000000000000000000000000000200000402000000000000000000000010000004100000
theorem epk_28 : ep_28 = edgePack m_28 g_28 := by decide +kernel
def bds_28 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_28 : KnownBin bds_28 := by intro b hb; simp [bds_28] at hb
theorem sub_28 : ∀ b ∈ bds_28, m_28 &&& b.1 = b.1 := by intro b hb; simp [bds_28] at hb
theorem gl_28 : ∀ b ∈ bds_28, canon b.1 g_28 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_28] at hb
def cur_28 : Nat → List (Nat × Nat) := unpackCursorV4 0xb146850932244890e8701 0x292874f0d30248243e80c982e508901a105800f 7 127 3 7 9 511 14 16383
def f_28 : Nat → Nat × Nat := unpackForestF 0x54a047c23279e08b844421a298148042c00f 4 9
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV4 m_28 g_28 ep_28 11 bds_28 (dagTraceF m_28 s_28 4 f_28) (cur_28 0) s_28 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28 : treeBlockF 0 11 (dagCheckNodeV4 m_28 g_28 ep_28 bds_28 11 (dagTraceF m_28 s_28 4 f_28) cur_28) = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 11 → (dagCheckNodeV4 m_28 g_28 ep_28 bds_28 11 (dagTraceF m_28 s_28 4 f_28) cur_28) i = true := fun _ h1 h2 => treeBlockF_at nb_28 h1 h2
theorem lb_28 : LowerBin m_28 s_28 g_28 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_28 kn_28 sub_28 gl_28 rc_28 nc_28

def m_29 : Nat := 0xcc33cc33
def s_29 : List Nat := [0x44114411, 0x330033, 0xc030c03, 0xcc33]
def g_29 : Nat := 0x4134433
def ep_29 : Nat := 0x40200000000000000000000000000402000000000000000000000000000004104400
theorem epk_29 : ep_29 = edgePack m_29 g_29 := by decide +kernel
def bds_29 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_29 : KnownBin bds_29 := by intro b hb; simp [bds_29] at hb
theorem sub_29 : ∀ b ∈ bds_29, m_29 &&& b.1 = b.1 := by intro b hb; simp [bds_29] at hb
theorem gl_29 : ∀ b ∈ bds_29, canon b.1 g_29 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_29] at hb
def cur_29 : Nat → List (Nat × Nat) := unpackCursorV4 0x72e18b060c0681 0xa92a4cb62a699252900f 7 127 3 7 6 63 10 1023
def f_29 : Nat → Nat × Nat := unpackForestF 0x1b6c86a33194c80f 3 6
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV4 m_29 g_29 ep_29 7 bds_29 (dagTraceF m_29 s_29 4 f_29) (cur_29 0) s_29 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29 : treeBlockF 0 7 (dagCheckNodeV4 m_29 g_29 ep_29 bds_29 7 (dagTraceF m_29 s_29 4 f_29) cur_29) = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 7 → (dagCheckNodeV4 m_29 g_29 ep_29 bds_29 7 (dagTraceF m_29 s_29 4 f_29) cur_29) i = true := fun _ h1 h2 => treeBlockF_at nb_29 h1 h2
theorem lb_29 : LowerBin m_29 s_29 g_29 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_29 kn_29 sub_29 gl_29 rc_29 nc_29

def m_30 : Nat := 0xcc33cc3300000000
def s_30 : List Nat := [0x4411441100000000, 0x33003300000000, 0xc030c0300000000, 0xcc3300000000]
def g_30 : Nat := 0x13041300000000
def ep_30 : Nat := 0x400000000000000000000000000000204020000000000000000000000000010041000000000
theorem epk_30 : ep_30 = edgePack m_30 g_30 := by decide +kernel
def bds_30 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_30 : KnownBin bds_30 := by intro b hb; simp [bds_30] at hb
theorem sub_30 : ∀ b ∈ bds_30, m_30 &&& b.1 = b.1 := by intro b hb; simp [bds_30] at hb
theorem gl_30 : ∀ b ∈ bds_30, canon b.1 g_30 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_30] at hb
def cur_30 : Nat → List (Nat × Nat) := unpackCursorV4 0xb146850932244890e8701 0x292874f0d30248243e80c982e508901a105800f 7 127 3 7 9 511 14 16383
def f_30 : Nat → Nat × Nat := unpackForestF 0x54a047c23279e08b844421a298148042c00f 4 9
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV4 m_30 g_30 ep_30 11 bds_30 (dagTraceF m_30 s_30 4 f_30) (cur_30 0) s_30 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30 : treeBlockF 0 11 (dagCheckNodeV4 m_30 g_30 ep_30 bds_30 11 (dagTraceF m_30 s_30 4 f_30) cur_30) = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 11 → (dagCheckNodeV4 m_30 g_30 ep_30 bds_30 11 (dagTraceF m_30 s_30 4 f_30) cur_30) i = true := fun _ h1 h2 => treeBlockF_at nb_30 h1 h2
theorem lb_30 : LowerBin m_30 s_30 g_30 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_30 kn_30 sub_30 gl_30 rc_30 nc_30

def m_31 : Nat := 0x8888222288882222
def s_31 : List Nat := [0x222200002222, 0x808020208080202, 0x88002200880022, 0x88882222]
def g_31 : Nat := 0x200000222
def ep_31 : Nat := 0x22000000000000000000000000200000020000000020000020000000000000000000000000000000000
theorem epk_31 : ep_31 = edgePack m_31 g_31 := by decide +kernel
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
theorem kn_31 : KnownBin bds_31 := by
  intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_8
theorem sub_31 : ∀ b ∈ bds_31, m_31 &&& b.1 = b.1 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_31 : ∀ b ∈ bds_31, canon b.1 g_31 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_31 : Nat → List (Nat × Nat) := fun _ => []
def f_31 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV4 m_31 g_31 ep_31 0 bds_31 (dagTraceF m_31 s_31 4 f_31) (cur_31 0) s_31 4 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_31 g_31 ep_31 bds_31 0 (dagTraceF m_31 s_31 4 f_31) cur_31 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_31 kn_31 sub_31 gl_31 rc_31 nc_31

def m_32 : Nat := 0x5005500550055005
def s_32 : List Nat := [0x1001100110011001, 0x5000500050005, 0x500500005005, 0x50055005]
def g_32 : Nat := 0x5100510055005
def ep_32 : Nat := 0x1000400000001000000040000000000000000000000000000000000000001000100000000000000000000000
theorem epk_32 : ep_32 = edgePack m_32 g_32 := by decide +kernel
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
theorem kn_32 : KnownBin bds_32 := by
  intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_5
theorem sub_32 : ∀ b ∈ bds_32, m_32 &&& b.1 = b.1 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_32 : ∀ b ∈ bds_32, canon b.1 g_32 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_32 : Nat → List (Nat × Nat) := fun _ => []
def f_32 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV4 m_32 g_32 ep_32 0 bds_32 (dagTraceF m_32 s_32 4 f_32) (cur_32 0) s_32 4 = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_32 g_32 ep_32 bds_32 0 (dagTraceF m_32 s_32 4 f_32) cur_32 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_32 : LowerBin m_32 s_32 g_32 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_32 kn_32 sub_32 gl_32 rc_32 nc_32

def m_33 : Nat := 0xc0c03030c0c0303
def s_33 : List Nat := [0x404010104040101, 0x30300000303, 0xc0003000c0003, 0xc0c0303]
def g_33 : Nat := 0x4010304040303
def ep_33 : Nat := 0x400020000000000000000000004000200000000000000000000000000000000000000000004010004040000
theorem epk_33 : ep_33 = edgePack m_33 g_33 := by decide +kernel
def bds_33 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_33 : KnownBin bds_33 := by intro b hb; simp [bds_33] at hb
theorem sub_33 : ∀ b ∈ bds_33, m_33 &&& b.1 = b.1 := by intro b hb; simp [bds_33] at hb
theorem gl_33 : ∀ b ∈ bds_33, canon b.1 g_33 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_33] at hb
def cur_33 : Nat → List (Nat × Nat) := unpackCursorV4 0x72e18b060c0681 0xa92a4cb62a699252900f 7 127 3 7 6 63 10 1023
def f_33 : Nat → Nat × Nat := unpackForestF 0x1b6c86a33194c80f 3 6
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV4 m_33 g_33 ep_33 7 bds_33 (dagTraceF m_33 s_33 4 f_33) (cur_33 0) s_33 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33 : treeBlockF 0 7 (dagCheckNodeV4 m_33 g_33 ep_33 bds_33 7 (dagTraceF m_33 s_33 4 f_33) cur_33) = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 7 → (dagCheckNodeV4 m_33 g_33 ep_33 bds_33 7 (dagTraceF m_33 s_33 4 f_33) cur_33) i = true := fun _ h1 h2 => treeBlockF_at nb_33 h1 h2
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_33 kn_33 sub_33 gl_33 rc_33 nc_33

def m_34 : Nat := 0xcc003300cc0033
def s_34 : List Nat := [0x44001100440011, 0x3300000033, 0xc0003000c0003, 0xcc0033]
def g_34 : Nat := 0x4001300040033
def ep_34 : Nat := 0x2000000000000000000000000000000000000400020004000000000000000000000004001000040000
theorem epk_34 : ep_34 = edgePack m_34 g_34 := by decide +kernel
def bds_34 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_34 : KnownBin bds_34 := by intro b hb; simp [bds_34] at hb
theorem sub_34 : ∀ b ∈ bds_34, m_34 &&& b.1 = b.1 := by intro b hb; simp [bds_34] at hb
theorem gl_34 : ∀ b ∈ bds_34, canon b.1 g_34 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_34] at hb
def cur_34 : Nat → List (Nat × Nat) := unpackCursorV4 0xb146850932244890e8701 0x1491da1b42492ea1b32a54c8784900f 7 127 3 7 6 63 11 2047
def f_34 : Nat → Nat × Nat := unpackForestF 0x2a41e8767d06a1985e2d0a41480f 4 6
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV4 m_34 g_34 ep_34 11 bds_34 (dagTraceF m_34 s_34 4 f_34) (cur_34 0) s_34 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34 : treeBlockF 0 11 (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 11 (dagTraceF m_34 s_34 4 f_34) cur_34) = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 11 → (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 11 (dagTraceF m_34 s_34 4 f_34) cur_34) i = true := fun _ h1 h2 => treeBlockF_at nb_34 h1 h2
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_34 kn_34 sub_34 gl_34 rc_34 nc_34

def m_35 : Nat := 0xcc003300cc003300
def s_35 : List Nat := [0x4400110044001100, 0x330000003300, 0xc0003000c000300, 0xcc003300]
def g_35 : Nat := 0x110004001300
def ep_35 : Nat := 0x400020000000000000000000000000000000000000000000400020000000000000000000000110004001000
theorem epk_35 : ep_35 = edgePack m_35 g_35 := by decide +kernel
def bds_35 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_35 : KnownBin bds_35 := by intro b hb; simp [bds_35] at hb
theorem sub_35 : ∀ b ∈ bds_35, m_35 &&& b.1 = b.1 := by intro b hb; simp [bds_35] at hb
theorem gl_35 : ∀ b ∈ bds_35, canon b.1 g_35 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_35] at hb
def cur_35 : Nat → List (Nat × Nat) := unpackCursorV4 0x72e18b060c0681 0xa96507305d029611208484000f 7 127 3 7 9 511 13 8191
def f_35 : Nat → Nat × Nat := unpackForestF 0x1bab86931184c00f 3 6
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV4 m_35 g_35 ep_35 7 bds_35 (dagTraceF m_35 s_35 4 f_35) (cur_35 0) s_35 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35 : treeBlockF 0 7 (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 7 (dagTraceF m_35 s_35 4 f_35) cur_35) = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 7 → (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 7 (dagTraceF m_35 s_35 4 f_35) cur_35) i = true := fun _ h1 h2 => treeBlockF_at nb_35 h1 h2
theorem lb_35 : LowerBin m_35 s_35 g_35 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_35 kn_35 sub_35 gl_35 rc_35 nc_35

def m_36 : Nat := 0xcccc3333
def s_36 : List Nat := [0x44441111, 0x3333, 0xc0c0303, 0xcc0033]
def g_36 : Nat := 0x4041333
def ep_36 : Nat := 0x20000000000404020000000000000000000000000004041000
theorem epk_36 : ep_36 = edgePack m_36 g_36 := by decide +kernel
def bds_36 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_36 : KnownBin bds_36 := by intro b hb; simp [bds_36] at hb
theorem sub_36 : ∀ b ∈ bds_36, m_36 &&& b.1 = b.1 := by intro b hb; simp [bds_36] at hb
theorem gl_36 : ∀ b ∈ bds_36, canon b.1 g_36 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_36] at hb
def cur_36 : Nat → List (Nat × Nat) := unpackCursorV4 0xb146850932244890e8701 0x292474d0c34209253a84d992a5499019104400f 7 127 3 7 9 511 14 16383
def f_36 : Nat → Nat × Nat := unpackForestF 0x549067433679a0ca864c21921a109042200f 4 9
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV4 m_36 g_36 ep_36 11 bds_36 (dagTraceF m_36 s_36 4 f_36) (cur_36 0) s_36 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36 : treeBlockF 0 11 (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 11 (dagTraceF m_36 s_36 4 f_36) cur_36) = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 11 → (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 11 (dagTraceF m_36 s_36 4 f_36) cur_36) i = true := fun _ h1 h2 => treeBlockF_at nb_36 h1 h2
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_36 kn_36 sub_36 gl_36 rc_36 nc_36

def m_37 : Nat := 0xcccc333300000000
def s_37 : List Nat := [0x4444111100000000, 0x333300000000, 0xc0c030300000000, 0xcc003300000000]
def g_37 : Nat := 0x4111300000000
def ep_37 : Nat := 0x4000200000000000400020000000000000000000000000004111000000000
theorem epk_37 : ep_37 = edgePack m_37 g_37 := by decide +kernel
def bds_37 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_37 : KnownBin bds_37 := by intro b hb; simp [bds_37] at hb
theorem sub_37 : ∀ b ∈ bds_37, m_37 &&& b.1 = b.1 := by intro b hb; simp [bds_37] at hb
theorem gl_37 : ∀ b ∈ bds_37, canon b.1 g_37 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_37] at hb
def cur_37 : Nat → List (Nat × Nat) := unpackCursorV4 0x72e18b060c0681 0xa9654b325d1296912484a4000f 7 127 3 7 9 511 13 8191
def f_37 : Nat → Nat × Nat := unpackForestF 0x32eb2c32932232132000f 3 9
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV4 m_37 g_37 ep_37 7 bds_37 (dagTraceF m_37 s_37 4 f_37) (cur_37 0) s_37 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_37 : treeBlockF 0 7 (dagCheckNodeV4 m_37 g_37 ep_37 bds_37 7 (dagTraceF m_37 s_37 4 f_37) cur_37) = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 7 → (dagCheckNodeV4 m_37 g_37 ep_37 bds_37 7 (dagTraceF m_37 s_37 4 f_37) cur_37) i = true := fun _ h1 h2 => treeBlockF_at nb_37 h1 h2
theorem lb_37 : LowerBin m_37 s_37 g_37 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_37 kn_37 sub_37 gl_37 rc_37 nc_37

def m_38 : Nat := 0xff00ff0000000000
def s_38 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_38 : Nat := 0x100150000000000
def ep_38 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000100150000000000
theorem epk_38 : ep_38 = edgePack m_38 g_38 := by decide +kernel
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_38 : KnownBin bds_38 := by
  intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_38 : ∀ b ∈ bds_38, m_38 &&& b.1 = b.1 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_38 : ∀ b ∈ bds_38, canon b.1 g_38 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV4 m_38 g_38 ep_38 0 bds_38 (dagTraceF m_38 s_38 4 f_38) (cur_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_38 g_38 ep_38 bds_38 0 (dagTraceF m_38 s_38 4 f_38) cur_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_38 kn_38 sub_38 gl_38 rc_38 nc_38

def m_39 : Nat := 0xffff000000000000
def s_39 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_39 : Nat := 0x117000000000000
def ep_39 : Nat := 0x16000000000000010600000000000001120000000000000114000000000000
theorem epk_39 : ep_39 = edgePack m_39 g_39 := by decide +kernel
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13), (m_11, s_11, 4, g_11), (m_7, s_7, 4, g_7), (m_6, s_6, 4, g_6)]
theorem kn_39 : KnownBin bds_39 := by
  intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_13
  · exact lb_11
  · exact lb_7
  · exact lb_6
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

def m_40 : Nat := 0xffff00000000
def s_40 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_40 : Nat := 0x155700000000
def ep_40 : Nat := 0x4200000000000004020000000000001002000000000000155400000000
theorem epk_40 : ep_40 = edgePack m_40 g_40 := by decide +kernel
def bds_40 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_40 : KnownBin bds_40 := by intro b hb; simp [bds_40] at hb
theorem sub_40 : ∀ b ∈ bds_40, m_40 &&& b.1 = b.1 := by intro b hb; simp [bds_40] at hb
theorem gl_40 : ∀ b ∈ bds_40, canon b.1 g_40 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_40] at hb
def cc_40_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0xe24c6d20345319280b83c581a2a0b14048912844921e0b0e04858202c9a124f08268303c141a040402249fa3ff91df28df4467993fc89dda4de8267292f8895c249df246f03f741db00dd3066802f34159809ca046381f100d8605c1026000f 11 2047 5 31 10 1023 17 131071
def cc_40_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0x3d299e140ec26741038251b924d8146a09314998240bc265c102c2795934a80c5205270513024900c4605202410234 8 255 3 7 10 1023 17 131071
def cur_40 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_40_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_40_0 p) (Nat.blt p 32)
def f_40 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV4 m_40 g_40 ep_40 64 bds_40 (dagTraceF m_40 s_40 5 f_40) (cur_40 0) s_40 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_0 : treeBlockF 0 32 (dagCheckNodeV4 m_40 g_40 ep_40 bds_40 64 (dagTraceF m_40 s_40 5 f_40) cur_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_1 : treeBlockF 32 64 (dagCheckNodeV4 m_40 g_40 ep_40 bds_40 64 (dagTraceF m_40 s_40 5 f_40) cur_40) = true := by decide +kernel
theorem nj_40_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_40 g_40 ep_40 bds_40 64 (dagTraceF m_40 s_40 5 f_40) cur_40) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_40_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_40_1 h1 h2)
theorem nc_40 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_40 g_40 ep_40 bds_40 64 (dagTraceF m_40 s_40 5 f_40) cur_40) i = true := nj_40_1
theorem lb_40 : LowerBin m_40 s_40 g_40 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_40 kn_40 sub_40 gl_40 rc_40 nc_40

def m_41 : Nat := 0xff00ff00000000
def s_41 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_41 : Nat := 0x17005700000000
def ep_41 : Nat := 0x40000000000000000000000000000600020000000000120002000000000014005400000000
theorem epk_41 : ep_41 = edgePack m_41 g_41 := by decide +kernel
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
theorem kn_41 : KnownBin bds_41 := by
  intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_11
theorem sub_41 : ∀ b ∈ bds_41, m_41 &&& b.1 = b.1 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_41 : ∀ b ∈ bds_41, canon b.1 g_41 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV4 m_41 g_41 ep_41 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_41 g_41 ep_41 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_41 kn_41 sub_41 gl_41 rc_41 nc_41

def m_42 : Nat := 0xf0f0f0f000000000
def s_42 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_42 : Nat := 0x10105000000000
def ep_42 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000010105000000000
theorem epk_42 : ep_42 = edgePack m_42 g_42 := by decide +kernel
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_42 : KnownBin bds_42 := by
  intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_42 : ∀ b ∈ bds_42, m_42 &&& b.1 = b.1 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_42 : ∀ b ∈ bds_42, canon b.1 g_42 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_42 : Nat → List (Nat × Nat) := fun _ => []
def f_42 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV4 m_42 g_42 ep_42 0 bds_42 (dagTraceF m_42 s_42 4 f_42) (cur_42 0) s_42 4 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_42 g_42 ep_42 bds_42 0 (dagTraceF m_42 s_42 4 f_42) cur_42 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_42 kn_42 sub_42 gl_42 rc_42 nc_42

def m_43 : Nat := 0xf0f0f0f00000000
def s_43 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_43 : Nat := 0x107050700000000
def ep_43 : Nat := 0x400000000000006000200000000000000000000000001020002000000000104050400000000
theorem epk_43 : ep_43 = edgePack m_43 g_43 := by decide +kernel
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
theorem kn_43 : KnownBin bds_43 := by
  intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_13
theorem sub_43 : ∀ b ∈ bds_43, m_43 &&& b.1 = b.1 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_43 : ∀ b ∈ bds_43, canon b.1 g_43 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_43 : Nat → List (Nat × Nat) := fun _ => []
def f_43 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV4 m_43 g_43 ep_43 0 bds_43 (dagTraceF m_43 s_43 4 f_43) (cur_43 0) s_43 4 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_43 g_43 ep_43 bds_43 0 (dagTraceF m_43 s_43 4 f_43) cur_43 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_43 : LowerBin m_43 s_43 g_43 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_43 kn_43 sub_43 gl_43 rc_43 nc_43

def m_44 : Nat := 0xcccccccc00000000
def s_44 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_44 : Nat := 0x4044400000000
def ep_44 : Nat := 0x440000000000004004000000000000404000000000000000000000000000004044400000000
theorem epk_44 : ep_44 = edgePack m_44 g_44 := by decide +kernel
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
theorem kn_44 : KnownBin bds_44 := by
  intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_4
theorem sub_44 : ∀ b ∈ bds_44, m_44 &&& b.1 = b.1 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_44 : ∀ b ∈ bds_44, canon b.1 g_44 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_44 : Nat → List (Nat × Nat) := fun _ => []
def f_44 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV4 m_44 g_44 ep_44 0 bds_44 (dagTraceF m_44 s_44 4 f_44) (cur_44 0) s_44 4 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_44 g_44 ep_44 bds_44 0 (dagTraceF m_44 s_44 4 f_44) cur_44 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_44 : LowerBin m_44 s_44 g_44 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_44 kn_44 sub_44 gl_44 rc_44 nc_44

def m_45 : Nat := 0x3333333300000000
def s_45 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_45 : Nat := 0x113111300000000
def ep_45 : Nat := 0x1000000000000012000200000000010200020000000000000000000000000110111000000000
theorem epk_45 : ep_45 = edgePack m_45 g_45 := by decide +kernel
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
theorem kn_45 : KnownBin bds_45 := by
  intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_6
theorem sub_45 : ∀ b ∈ bds_45, m_45 &&& b.1 = b.1 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_45 : ∀ b ∈ bds_45, canon b.1 g_45 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_45 : Nat → List (Nat × Nat) := fun _ => []
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV4 m_45 g_45 ep_45 0 bds_45 (dagTraceF m_45 s_45 4 f_45) (cur_45 0) s_45 4 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_45 g_45 ep_45 bds_45 0 (dagTraceF m_45 s_45 4 f_45) cur_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin m_45 s_45 g_45 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_45 kn_45 sub_45 gl_45 rc_45 nc_45

def m_46 : Nat := 0xaa00aa00aa00aa
def s_46 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_46 : Nat := 0x200020002002a
def ep_46 : Nat := 0x2800000000000000280000000000000000000200020002000800020002000200200000000000000000
theorem epk_46 : ep_46 = edgePack m_46 g_46 := by decide +kernel
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
theorem kn_46 : KnownBin bds_46 := by
  intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_10
theorem sub_46 : ∀ b ∈ bds_46, m_46 &&& b.1 = b.1 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_46 : ∀ b ∈ bds_46, canon b.1 g_46 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_46 : Nat → List (Nat × Nat) := fun _ => []
def f_46 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV4 m_46 g_46 ep_46 0 bds_46 (dagTraceF m_46 s_46 4 f_46) (cur_46 0) s_46 4 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_46 g_46 ep_46 bds_46 0 (dagTraceF m_46 s_46 4 f_46) cur_46 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_46 : LowerBin m_46 s_46 g_46 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_46 kn_46 sub_46 gl_46 rc_46 nc_46

def m_47 : Nat := 0x5555555500000000
def s_47 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_47 : Nat := 0x115155500000000
def ep_47 : Nat := 0x1440000000000014004000000000010404000000000001101000000000000000000000000000
theorem epk_47 : ep_47 = edgePack m_47 g_47 := by decide +kernel
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2), (m_7, s_7, 4, g_7), (m_1, s_1, 4, g_1), (m_4, s_4, 4, g_4)]
theorem kn_47 : KnownBin bds_47 := by
  intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_2
  · exact lb_7
  · exact lb_1
  · exact lb_4
theorem sub_47 : ∀ b ∈ bds_47, m_47 &&& b.1 = b.1 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_47 : ∀ b ∈ bds_47, canon b.1 g_47 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_47_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8724381de0ee07323981c44b575a02d01642aa4550298940698435b9a80d406623301980c445a429214049844a123109c0064001 0x59003c6015407c9a07d3a36950b460fa10592a048cf1460a9f054b9d07a0c39201a830c4285a8825180a83d002c600c4040120310050280f4e07a6b69342c92a2450b20878f5a46ac94d2ca2874f5826a1c4e0626870f818720c320618830c018547826060d0805952980e400f180310100680c300c0a038c01a6015200b20078c02a8081340fa72cd29468c1f420b25269181c7c0e3d489e904d42a5a892506251e118287c0c3d0a17030a418440c21061003068202c624c0b2012d203e800d400e980310050680d300a90030c030480c300e980a0d0184015200c1207938d4945a460f21058f8a47442360b190e518626c0d2e06250811818741036060c878fc2c7742370b19874fe426e152f7093870fc1876b8370619850bc1856702706118306c102e000f 13 8191 5 31 10 1023 17 131071
def cc_47_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb817017bae0544a80580a014018811001 0x2e9c174d0f27059343c7c16390b19058c42c61514d84a2874f6626a152d8092d21341892a0450620870f5a06a142d4c12858c1f2493a4d0b24c29142c821e3d991a875383a7cf126942683124b08a0c410e1eb00d4702b104c0620078c1f2681520 11 2047 5 31 10 1023 17 131071
def cur_47 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_47_1 (Nat.sub p 32)) (cc_47_0 p) (Nat.blt p 32)
def f_47 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV4 m_47 g_47 ep_47 43 bds_47 (dagTraceF m_47 s_47 6 f_47) (cur_47 0) s_47 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_0 : treeBlockF 0 32 (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 43 (dagTraceF m_47 s_47 6 f_47) cur_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_1 : treeBlockF 32 43 (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 43 (dagTraceF m_47 s_47 6 f_47) cur_47) = true := by decide +kernel
theorem nj_47_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 43 (dagTraceF m_47 s_47 6 f_47) cur_47) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_47_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_47_1 h1 h2)
theorem nc_47 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_47 g_47 ep_47 bds_47 43 (dagTraceF m_47 s_47 6 f_47) cur_47) i = true := nj_47_1
theorem lb_47 : LowerBin m_47 s_47 g_47 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_47 kn_47 sub_47 gl_47 rc_47 nc_47

def m_48 : Nat := 0x3030303030303030
def s_48 : List Nat := [0x1010101010101010, 0x30003000300030, 0x303000003030, 0x30303030]
def g_48 : Nat := 0x10101010101030
def ep_48 : Nat := 0x1000002000001000000000200010000000000020000000000000000000000000000000000010101010101000
theorem epk_48 : ep_48 = edgePack m_48 g_48 := by decide +kernel
def bds_48 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_48 : KnownBin bds_48 := by intro b hb; simp [bds_48] at hb
theorem sub_48 : ∀ b ∈ bds_48, m_48 &&& b.1 = b.1 := by intro b hb; simp [bds_48] at hb
theorem gl_48 : ∀ b ∈ bds_48, canon b.1 g_48 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_48] at hb
def cc_48_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0xe24c6d20345319280b83c581a2a0b14048912844921e0b0e04858202c9a124f08268303c141a040402249fa3ff91df28df4467993fc89dda4de8267292f8895c249df246f03f741db00dd3066802f34159809ca046381f100d8605c1026000f 11 2047 5 31 10 1023 17 131071
def cc_48_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0x3d299e140ec26741038251b924d8146a09314998240bc265c102c2795934a80c5205270513024900c4605202410234 8 255 3 7 10 1023 17 131071
def cur_48 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_48_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_48_0 p) (Nat.blt p 32)
def f_48 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV4 m_48 g_48 ep_48 64 bds_48 (dagTraceF m_48 s_48 5 f_48) (cur_48 0) s_48 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_0 : treeBlockF 0 32 (dagCheckNodeV4 m_48 g_48 ep_48 bds_48 64 (dagTraceF m_48 s_48 5 f_48) cur_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_1 : treeBlockF 32 64 (dagCheckNodeV4 m_48 g_48 ep_48 bds_48 64 (dagTraceF m_48 s_48 5 f_48) cur_48) = true := by decide +kernel
theorem nj_48_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_48 g_48 ep_48 bds_48 64 (dagTraceF m_48 s_48 5 f_48) cur_48) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_48_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_48_1 h1 h2)
theorem nc_48 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_48 g_48 ep_48 bds_48 64 (dagTraceF m_48 s_48 5 f_48) cur_48) i = true := nj_48_1
theorem lb_48 : LowerBin m_48 s_48 g_48 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_48 kn_48 sub_48 gl_48 rc_48 nc_48

def m_49 : Nat := 0x3333000033330000
def s_49 : List Nat := [0x1111000011110000, 0x303000003030000, 0x33000000330000, 0x33330000]
def g_49 : Nat := 0x113000011130000
def ep_49 : Nat := 0x1000000000000000000000000012000000020000010200000002000000000000000000000110000011100000
theorem epk_49 : ep_49 = edgePack m_49 g_49 := by decide +kernel
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
theorem kn_49 : KnownBin bds_49 := by
  intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_6
theorem sub_49 : ∀ b ∈ bds_49, m_49 &&& b.1 = b.1 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_49 : ∀ b ∈ bds_49, canon b.1 g_49 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_49 : Nat → List (Nat × Nat) := fun _ => []
def f_49 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV4 m_49 g_49 ep_49 0 bds_49 (dagTraceF m_49 s_49 4 f_49) (cur_49 0) s_49 4 = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_49 g_49 ep_49 bds_49 0 (dagTraceF m_49 s_49 4 f_49) cur_49 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_49 : LowerBin m_49 s_49 g_49 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_49 kn_49 sub_49 gl_49 rc_49 nc_49

def m_50 : Nat := 0x5555000055550000
def s_50 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_50 : Nat := 0x115000015150000
def ep_50 : Nat := 0x1400000000000000000000000014000000000000010400000404000001100000101000000000000000000000
theorem epk_50 : ep_50 = edgePack m_50 g_50 := by decide +kernel
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
theorem kn_50 : KnownBin bds_50 := by
  intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_7
theorem sub_50 : ∀ b ∈ bds_50, m_50 &&& b.1 = b.1 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_50 : ∀ b ∈ bds_50, canon b.1 g_50 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_50 : Nat → List (Nat × Nat) := fun _ => []
def f_50 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV4 m_50 g_50 ep_50 0 bds_50 (dagTraceF m_50 s_50 4 f_50) (cur_50 0) s_50 4 = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_50 g_50 ep_50 bds_50 0 (dagTraceF m_50 s_50 4 f_50) cur_50 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_50 : LowerBin m_50 s_50 g_50 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_50 kn_50 sub_50 gl_50 rc_50 nc_50

def m_51 : Nat := 0x5500550055005500
def s_51 : List Nat := [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500]
def g_51 : Nat := 0x100150015005500
def ep_51 : Nat := 0x1400400000001400000040000000000000000000010004000400000001001000100000000000000000000000
theorem epk_51 : ep_51 = edgePack m_51 g_51 := by decide +kernel
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2), (m_15, s_15, 4, g_15), (m_5, s_5, 4, g_5), (m_14, s_14, 4, g_14)]
theorem kn_51 : KnownBin bds_51 := by
  intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_2
  · exact lb_15
  · exact lb_5
  · exact lb_14
theorem sub_51 : ∀ b ∈ bds_51, m_51 &&& b.1 = b.1 := by intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_51 : ∀ b ∈ bds_51, canon b.1 g_51 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_51_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_51_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
def cur_51 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_51_1 (Nat.sub p 32)) (cc_51_0 p) (Nat.blt p 32)
def f_51 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV4 m_51 g_51 ep_51 43 bds_51 (dagTraceF m_51 s_51 6 f_51) (cur_51 0) s_51 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_0 : treeBlockF 0 32 (dagCheckNodeV4 m_51 g_51 ep_51 bds_51 43 (dagTraceF m_51 s_51 6 f_51) cur_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_1 : treeBlockF 32 43 (dagCheckNodeV4 m_51 g_51 ep_51 bds_51 43 (dagTraceF m_51 s_51 6 f_51) cur_51) = true := by decide +kernel
theorem nj_51_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_51 g_51 ep_51 bds_51 43 (dagTraceF m_51 s_51 6 f_51) cur_51) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_51_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_51_1 h1 h2)
theorem nc_51 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_51 g_51 ep_51 bds_51 43 (dagTraceF m_51 s_51 6 f_51) cur_51) i = true := nj_51_1
theorem lb_51 : LowerBin m_51 s_51 g_51 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_51 kn_51 sub_51 gl_51 rc_51 nc_51

def m_52 : Nat := 0xf0f00000f0f0
def s_52 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_52 : Nat := 0x105000005070
def ep_52 : Nat := 0x402000000000000000000000004000000020000000000000000000001000000000200000105000005040
theorem epk_52 : ep_52 = edgePack m_52 g_52 := by decide +kernel
def bds_52 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_52 : KnownBin bds_52 := by intro b hb; simp [bds_52] at hb
theorem sub_52 : ∀ b ∈ bds_52, m_52 &&& b.1 = b.1 := by intro b hb; simp [bds_52] at hb
theorem gl_52 : ∀ b ∈ bds_52, canon b.1 g_52 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_52] at hb
def cc_52_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0xe24c6d20345319280b83c581a2a0b14048912844921e0b0e04858202c9a124f08268303c141a040402249fa3ff91df28df4467993fc89dda4de8267292f8895c249df246f03f741db00dd3066802f34159809ca046381f100d8605c1026000f 11 2047 5 31 10 1023 17 131071
def cc_52_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0x3d299e140ec26741038251b924d8146a09314998240bc265c102c2795934a80c5205270513024900c4605202410234 8 255 3 7 10 1023 17 131071
def cur_52 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_52_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_52_0 p) (Nat.blt p 32)
def f_52 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV4 m_52 g_52 ep_52 64 bds_52 (dagTraceF m_52 s_52 5 f_52) (cur_52 0) s_52 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_0 : treeBlockF 0 32 (dagCheckNodeV4 m_52 g_52 ep_52 bds_52 64 (dagTraceF m_52 s_52 5 f_52) cur_52) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_1 : treeBlockF 32 64 (dagCheckNodeV4 m_52 g_52 ep_52 bds_52 64 (dagTraceF m_52 s_52 5 f_52) cur_52) = true := by decide +kernel
theorem nj_52_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_52 g_52 ep_52 bds_52 64 (dagTraceF m_52 s_52 5 f_52) cur_52) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_52_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_52_1 h1 h2)
theorem nc_52 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_52 g_52 ep_52 bds_52 64 (dagTraceF m_52 s_52 5 f_52) cur_52) i = true := nj_52_1
theorem lb_52 : LowerBin m_52 s_52 g_52 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_52 kn_52 sub_52 gl_52 rc_52 nc_52

def m_53 : Nat := 0xf0f00000f0f
def s_53 : List Nat := [0x50500000505, 0x30300000303, 0xf0000000f, 0xf0f]
def g_53 : Nat := 0x5070000070f
def ep_53 : Nat := 0x20800000000000000000000000200000008000000000000000000000002000002000000050400000400
theorem epk_53 : ep_53 = edgePack m_53 g_53 := by decide +kernel
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_53 : KnownBin bds_53 := by
  intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_53 : ∀ b ∈ bds_53, m_53 &&& b.1 = b.1 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_53 : ∀ b ∈ bds_53, canon b.1 g_53 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_53 : Nat → List (Nat × Nat) := fun _ => []
def f_53 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV4 m_53 g_53 ep_53 0 bds_53 (dagTraceF m_53 s_53 4 f_53) (cur_53 0) s_53 4 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_53 g_53 ep_53 bds_53 0 (dagTraceF m_53 s_53 4 f_53) cur_53 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_53 : LowerBin m_53 s_53 g_53 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_53 kn_53 sub_53 gl_53 rc_53 nc_53

def m_54 : Nat := 0x333300003333
def s_54 : List Nat := [0x111100001111, 0x30300000303, 0x3300000033, 0x3333]
def g_54 : Nat := 0x111300001333
def ep_54 : Nat := 0x22000000000000000000000000200000020000000020000020000000000000000000000111000001000
theorem epk_54 : ep_54 = edgePack m_54 g_54 := by decide +kernel
def bds_54 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
theorem kn_54 : KnownBin bds_54 := by
  intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_8
theorem sub_54 : ∀ b ∈ bds_54, m_54 &&& b.1 = b.1 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_54 : ∀ b ∈ bds_54, canon b.1 g_54 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_54 : Nat → List (Nat × Nat) := fun _ => []
def f_54 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV4 m_54 g_54 ep_54 0 bds_54 (dagTraceF m_54 s_54 4 f_54) (cur_54 0) s_54 4 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_54 g_54 ep_54 bds_54 0 (dagTraceF m_54 s_54 4 f_54) cur_54 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_54 : LowerBin m_54 s_54 g_54 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_54 kn_54 sub_54 gl_54 rc_54 nc_54

def m_55 : Nat := 0xaaaa0000aaaa
def s_55 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_55 : Nat := 0x20000022a
def ep_55 : Nat := 0x22800000000000000000000000200000028000000020000020800000002000002200000000000000000
theorem epk_55 : ep_55 = edgePack m_55 g_55 := by decide +kernel
def bds_55 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10), (m_0, s_0, 4, g_0), (m_8, s_8, 4, g_8), (m_9, s_9, 4, g_9)]
theorem kn_55 : KnownBin bds_55 := by
  intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_10
  · exact lb_0
  · exact lb_8
  · exact lb_9
theorem sub_55 : ∀ b ∈ bds_55, m_55 &&& b.1 = b.1 := by intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_55 : ∀ b ∈ bds_55, canon b.1 g_55 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_55_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_55_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_55 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_55_1 (Nat.sub p 32)) (cc_55_0 p) (Nat.blt p 32)
def f_55 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV4 m_55 g_55 ep_55 43 bds_55 (dagTraceF m_55 s_55 6 f_55) (cur_55 0) s_55 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_0 : treeBlockF 0 32 (dagCheckNodeV4 m_55 g_55 ep_55 bds_55 43 (dagTraceF m_55 s_55 6 f_55) cur_55) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_1 : treeBlockF 32 43 (dagCheckNodeV4 m_55 g_55 ep_55 bds_55 43 (dagTraceF m_55 s_55 6 f_55) cur_55) = true := by decide +kernel
theorem nj_55_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_55 g_55 ep_55 bds_55 43 (dagTraceF m_55 s_55 6 f_55) cur_55) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_55_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_55_1 h1 h2)
theorem nc_55 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_55 g_55 ep_55 bds_55 43 (dagTraceF m_55 s_55 6 f_55) cur_55) i = true := nj_55_1
theorem lb_55 : LowerBin m_55 s_55 g_55 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_55 kn_55 sub_55 gl_55 rc_55 nc_55

def m_56 : Nat := 0x3300330033003300
def s_56 : List Nat := [0x1100110011001100, 0x300030003000300, 0x330000003300, 0x33003300]
def g_56 : Nat := 0x100110011001300
def ep_56 : Nat := 0x1000020000001000000002000000000000000000010000000000020000000000000000000100110011001000
theorem epk_56 : ep_56 = edgePack m_56 g_56 := by decide +kernel
def bds_56 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_56 : KnownBin bds_56 := by intro b hb; simp [bds_56] at hb
theorem sub_56 : ∀ b ∈ bds_56, m_56 &&& b.1 = b.1 := by intro b hb; simp [bds_56] at hb
theorem gl_56 : ∀ b ∈ bds_56, canon b.1 g_56 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_56] at hb
def cc_56_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0xe24c6d20345319280b83c581a2a0b14048912844921e0b0e04858202c9a124f08268303c141a040402249fa3ff91df28df4467993fc89dda4de8267292f8895c249df246f03f741db00dd3066802f34159809ca046381f100d8605c1026000f 11 2047 5 31 10 1023 17 131071
def cc_56_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0x3d299e140ec26741038251b924d8146a09314998240bc265c102c2795934a80c5205270513024900c4605202410234 8 255 3 7 10 1023 17 131071
def cur_56 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_56_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_56_0 p) (Nat.blt p 32)
def f_56 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV4 m_56 g_56 ep_56 64 bds_56 (dagTraceF m_56 s_56 5 f_56) (cur_56 0) s_56 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_0 : treeBlockF 0 32 (dagCheckNodeV4 m_56 g_56 ep_56 bds_56 64 (dagTraceF m_56 s_56 5 f_56) cur_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_1 : treeBlockF 32 64 (dagCheckNodeV4 m_56 g_56 ep_56 bds_56 64 (dagTraceF m_56 s_56 5 f_56) cur_56) = true := by decide +kernel
theorem nj_56_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_56 g_56 ep_56 bds_56 64 (dagTraceF m_56 s_56 5 f_56) cur_56) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_56_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_56_1 h1 h2)
theorem nc_56 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_56 g_56 ep_56 bds_56 64 (dagTraceF m_56 s_56 5 f_56) cur_56) i = true := nj_56_1
theorem lb_56 : LowerBin m_56 s_56 g_56 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_56 kn_56 sub_56 gl_56 rc_56 nc_56

def m_57 : Nat := 0xcc00cc00cc00cc00
def s_57 : List Nat := [0x4400440044004400, 0xc000c000c000c00, 0xcc000000cc00, 0xcc00cc00]
def g_57 : Nat := 0x40004004400
def ep_57 : Nat := 0x400400000000400000040000000000000000000000004000400000000000000000000000000040004004400
theorem epk_57 : ep_57 = edgePack m_57 g_57 := by decide +kernel
def bds_57 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
theorem kn_57 : KnownBin bds_57 := by
  intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_14
theorem sub_57 : ∀ b ∈ bds_57, m_57 &&& b.1 = b.1 := by intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_57 : ∀ b ∈ bds_57, canon b.1 g_57 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_57 : Nat → List (Nat × Nat) := fun _ => []
def f_57 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV4 m_57 g_57 ep_57 0 bds_57 (dagTraceF m_57 s_57 4 f_57) (cur_57 0) s_57 4 = true := by decide +kernel
theorem nc_57 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_57 g_57 ep_57 bds_57 0 (dagTraceF m_57 s_57 4 f_57) cur_57 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_57 : LowerBin m_57 s_57 g_57 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_57 kn_57 sub_57 gl_57 rc_57 nc_57

def m_58 : Nat := 0xf000f000f000f000
def s_58 : List Nat := [0x5000500050005000, 0x3000300030003000, 0xf0000000f000, 0xf000f000]
def g_58 : Nat := 0x100010005000
def ep_58 : Nat := 0x1000400000001000000040000000000000000000000000000000000000001000100000000000100010005000
theorem epk_58 : ep_58 = edgePack m_58 g_58 := by decide +kernel
def bds_58 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
theorem kn_58 : KnownBin bds_58 := by
  intro b hb; simp only [bds_58, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_5
theorem sub_58 : ∀ b ∈ bds_58, m_58 &&& b.1 = b.1 := by intro b hb; simp only [bds_58, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_58 : ∀ b ∈ bds_58, canon b.1 g_58 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_58, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_58 : Nat → List (Nat × Nat) := fun _ => []
def f_58 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV4 m_58 g_58 ep_58 0 bds_58 (dagTraceF m_58 s_58 4 f_58) (cur_58 0) s_58 4 = true := by decide +kernel
theorem nc_58 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_58 g_58 ep_58 bds_58 0 (dagTraceF m_58 s_58 4 f_58) cur_58 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_58 : LowerBin m_58 s_58 g_58 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_58 kn_58 sub_58 gl_58 rc_58 nc_58

def m_59 : Nat := 0xf000f000f000f00
def s_59 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_59 : Nat := 0x100050005000700
def ep_59 : Nat := 0x400020000000400000002000000000000000000000000000000000001000000000002000100050005000400
theorem epk_59 : ep_59 = edgePack m_59 g_59 := by decide +kernel
def bds_59 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_59 : KnownBin bds_59 := by intro b hb; simp [bds_59] at hb
theorem sub_59 : ∀ b ∈ bds_59, m_59 &&& b.1 = b.1 := by intro b hb; simp [bds_59] at hb
theorem gl_59 : ∀ b ∈ bds_59, canon b.1 g_59 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_59] at hb
def cc_59_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0xe24c6d20345319280b83c581a2a0b14048912844921e0b0e04858202c9a124f08268303c141a040402249fa3ff91df28df4467993fc89dda4de8267292f8895c249df246f03f741db00dd3066802f34159809ca046381f100d8605c1026000f 11 2047 5 31 10 1023 17 131071
def cc_59_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0x3d299e140ec26741038251b924d8146a09314998240bc265c102c2795934a80c5205270513024900c4605202410234 8 255 3 7 10 1023 17 131071
def cur_59 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_59_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_59_0 p) (Nat.blt p 32)
def f_59 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_59 : dagCheckRootsV4 m_59 g_59 ep_59 64 bds_59 (dagTraceF m_59 s_59 5 f_59) (cur_59 0) s_59 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59_0 : treeBlockF 0 32 (dagCheckNodeV4 m_59 g_59 ep_59 bds_59 64 (dagTraceF m_59 s_59 5 f_59) cur_59) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59_1 : treeBlockF 32 64 (dagCheckNodeV4 m_59 g_59 ep_59 bds_59 64 (dagTraceF m_59 s_59 5 f_59) cur_59) = true := by decide +kernel
theorem nj_59_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_59 g_59 ep_59 bds_59 64 (dagTraceF m_59 s_59 5 f_59) cur_59) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_59_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_59_1 h1 h2)
theorem nc_59 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_59 g_59 ep_59 bds_59 64 (dagTraceF m_59 s_59 5 f_59) cur_59) i = true := nj_59_1
theorem lb_59 : LowerBin m_59 s_59 g_59 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_59 kn_59 sub_59 gl_59 rc_59 nc_59

def m_60 : Nat := 0x33333333
def s_60 : List Nat := [0x11111111, 0x3030303, 0x330033, 0x3333]
def g_60 : Nat := 0x11131333
def ep_60 : Nat := 0x2200000000000020020000000000002020000000000000000000000000011101000
theorem epk_60 : ep_60 = edgePack m_60 g_60 := by decide +kernel
def bds_60 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16)]
theorem kn_60 : KnownBin bds_60 := by
  intro b hb; simp only [bds_60, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_16
theorem sub_60 : ∀ b ∈ bds_60, m_60 &&& b.1 = b.1 := by intro b hb; simp only [bds_60, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_60 : ∀ b ∈ bds_60, canon b.1 g_60 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_60, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_60 : Nat → List (Nat × Nat) := fun _ => []
def f_60 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsV4 m_60 g_60 ep_60 0 bds_60 (dagTraceF m_60 s_60 4 f_60) (cur_60 0) s_60 4 = true := by decide +kernel
theorem nc_60 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_60 g_60 ep_60 bds_60 0 (dagTraceF m_60 s_60 4 f_60) cur_60 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_60 : LowerBin m_60 s_60 g_60 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_60 kn_60 sub_60 gl_60 rc_60 nc_60

def m_61 : Nat := 0xffff0000
def s_61 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_61 : Nat := 0x15170000
def ep_61 : Nat := 0x20000000000000406000000000000101200000000000015140000
theorem epk_61 : ep_61 = edgePack m_61 g_61 := by decide +kernel
def bds_61 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_61 : KnownBin bds_61 := by
  intro b hb; simp only [bds_61, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_61 : ∀ b ∈ bds_61, m_61 &&& b.1 = b.1 := by intro b hb; simp only [bds_61, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_61 : ∀ b ∈ bds_61, canon b.1 g_61 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_61, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_61 : Nat → List (Nat × Nat) := fun _ => []
def f_61 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_61 : dagCheckRootsV4 m_61 g_61 ep_61 0 bds_61 (dagTraceF m_61 s_61 4 f_61) (cur_61 0) s_61 4 = true := by decide +kernel
theorem nc_61 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_61 g_61 ep_61 bds_61 0 (dagTraceF m_61 s_61 4 f_61) cur_61 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_61 : LowerBin m_61 s_61 g_61 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_61 kn_61 sub_61 gl_61 rc_61 nc_61

def m_62 : Nat := 0xffff
def s_62 : List Nat := [0x5555, 0x3333, 0xf0f, 0xff]
def g_62 : Nat := 0x577f
def ep_62 : Nat := 0x28000000000000020800000000000002200000000000005440
theorem epk_62 : ep_62 = edgePack m_62 g_62 := by decide +kernel
def bds_62 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_62 : KnownBin bds_62 := by
  intro b hb; simp only [bds_62, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_62 : ∀ b ∈ bds_62, m_62 &&& b.1 = b.1 := by intro b hb; simp only [bds_62, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_62 : ∀ b ∈ bds_62, canon b.1 g_62 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_62, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_62 : Nat → List (Nat × Nat) := fun _ => []
def f_62 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_62 : dagCheckRootsV4 m_62 g_62 ep_62 0 bds_62 (dagTraceF m_62 s_62 4 f_62) (cur_62 0) s_62 4 = true := by decide +kernel
theorem nc_62 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_62 g_62 ep_62 bds_62 0 (dagTraceF m_62 s_62 4 f_62) cur_62 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_62 : LowerBin m_62 s_62 g_62 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_62 kn_62 sub_62 gl_62 rc_62 nc_62

def m_63 : Nat := 0xff00ff00
def s_63 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_63 : Nat := 0x15005700
def ep_63 : Nat := 0x42000000000000000000000000000400020000000000100002000000000015005400
theorem epk_63 : ep_63 = edgePack m_63 g_63 := by decide +kernel
def bds_63 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_63 : KnownBin bds_63 := by intro b hb; simp [bds_63] at hb
theorem sub_63 : ∀ b ∈ bds_63, m_63 &&& b.1 = b.1 := by intro b hb; simp [bds_63] at hb
theorem gl_63 : ∀ b ∈ bds_63, canon b.1 g_63 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_63] at hb
def cc_63_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0xe24c6d20345319280b83c581a2a0b14048912844921e0b0e04858202c9a124f08268303c141a040402249fa3ff91df28df4467993fc89dda4de8267292f8895c249df246f03f741db00dd3066802f34159809ca046381f100d8605c1026000f 11 2047 5 31 10 1023 17 131071
def cc_63_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0x3d299e140ec26741038251b924d8146a09314998240bc265c102c2795934a80c5205270513024900c4605202410234 8 255 3 7 10 1023 17 131071
def cur_63 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_63_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_63_0 p) (Nat.blt p 32)
def f_63 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_63 : dagCheckRootsV4 m_63 g_63 ep_63 64 bds_63 (dagTraceF m_63 s_63 5 f_63) (cur_63 0) s_63 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_0 : treeBlockF 0 32 (dagCheckNodeV4 m_63 g_63 ep_63 bds_63 64 (dagTraceF m_63 s_63 5 f_63) cur_63) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_1 : treeBlockF 32 64 (dagCheckNodeV4 m_63 g_63 ep_63 bds_63 64 (dagTraceF m_63 s_63 5 f_63) cur_63) = true := by decide +kernel
theorem nj_63_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_63 g_63 ep_63 bds_63 64 (dagTraceF m_63 s_63 5 f_63) cur_63) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_63_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_63_1 h1 h2)
theorem nc_63 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_63 g_63 ep_63 bds_63 64 (dagTraceF m_63 s_63 5 f_63) cur_63) i = true := nj_63_1
theorem lb_63 : LowerBin m_63 s_63 g_63 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_63 kn_63 sub_63 gl_63 rc_63 nc_63

def m_64 : Nat := 0xff00ff
def s_64 : List Nat := [0x550055, 0x330033, 0xf000f, 0xff]
def g_64 : Nat := 0x17007f
def ep_64 : Nat := 0x680000000000000000000000000006000800000000001200200000000000140040
theorem epk_64 : ep_64 = edgePack m_64 g_64 := by decide +kernel
def bds_64 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3), (m_12, s_12, 4, g_12), (m_19, s_19, 4, g_19), (m_18, s_18, 4, g_18)]
theorem kn_64 : KnownBin bds_64 := by
  intro b hb; simp only [bds_64, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_3
  · exact lb_12
  · exact lb_19
  · exact lb_18
theorem sub_64 : ∀ b ∈ bds_64, m_64 &&& b.1 = b.1 := by intro b hb; simp only [bds_64, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_64 : ∀ b ∈ bds_64, canon b.1 g_64 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_64, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_64_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_64_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
def cur_64 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_64_1 (Nat.sub p 32)) (cc_64_0 p) (Nat.blt p 32)
def f_64 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_64 : dagCheckRootsV4 m_64 g_64 ep_64 43 bds_64 (dagTraceF m_64 s_64 6 f_64) (cur_64 0) s_64 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_0 : treeBlockF 0 32 (dagCheckNodeV4 m_64 g_64 ep_64 bds_64 43 (dagTraceF m_64 s_64 6 f_64) cur_64) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_1 : treeBlockF 32 43 (dagCheckNodeV4 m_64 g_64 ep_64 bds_64 43 (dagTraceF m_64 s_64 6 f_64) cur_64) = true := by decide +kernel
theorem nj_64_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_64 g_64 ep_64 bds_64 43 (dagTraceF m_64 s_64 6 f_64) cur_64) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_64_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_64_1 h1 h2)
theorem nc_64 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_64 g_64 ep_64 bds_64 43 (dagTraceF m_64 s_64 6 f_64) cur_64) i = true := nj_64_1
theorem lb_64 : LowerBin m_64 s_64 g_64 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_64 kn_64 sub_64 gl_64 rc_64 nc_64

def m_65 : Nat := 0xf0f0f0f0
def s_65 : List Nat := [0x50505050, 0x30303030, 0xf000f0, 0xf0f0]
def g_65 : Nat := 0x10105070
def ep_65 : Nat := 0x40600000000000000020000000000000000000000000101000200000000010105040
theorem epk_65 : ep_65 = edgePack m_65 g_65 := by decide +kernel
def bds_65 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
theorem kn_65 : KnownBin bds_65 := by
  intro b hb; simp only [bds_65, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_12
theorem sub_65 : ∀ b ∈ bds_65, m_65 &&& b.1 = b.1 := by intro b hb; simp only [bds_65, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_65 : ∀ b ∈ bds_65, canon b.1 g_65 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_65, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_65 : Nat → List (Nat × Nat) := fun _ => []
def f_65 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_65 : dagCheckRootsV4 m_65 g_65 ep_65 0 bds_65 (dagTraceF m_65 s_65 4 f_65) (cur_65 0) s_65 4 = true := by decide +kernel
theorem nc_65 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_65 g_65 ep_65 bds_65 0 (dagTraceF m_65 s_65 4 f_65) cur_65 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_65 : LowerBin m_65 s_65 g_65 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_65 kn_65 sub_65 gl_65 rc_65 nc_65

def m_66 : Nat := 0xf0f0f0f
def s_66 : List Nat := [0x5050505, 0x3030303, 0xf000f, 0xf0f]
def g_66 : Nat := 0x507070f
def ep_66 : Nat := 0x2080000000000020008000000000000000000000000000202000000000005040400
theorem epk_66 : ep_66 = edgePack m_66 g_66 := by decide +kernel
def bds_66 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 4, g_17)]
theorem kn_66 : KnownBin bds_66 := by
  intro b hb; simp only [bds_66, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_17
theorem sub_66 : ∀ b ∈ bds_66, m_66 &&& b.1 = b.1 := by intro b hb; simp only [bds_66, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_66 : ∀ b ∈ bds_66, canon b.1 g_66 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_66, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_66 : Nat → List (Nat × Nat) := fun _ => []
def f_66 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_66 : dagCheckRootsV4 m_66 g_66 ep_66 0 bds_66 (dagTraceF m_66 s_66 4 f_66) (cur_66 0) s_66 4 = true := by decide +kernel
theorem nc_66 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_66 g_66 ep_66 bds_66 0 (dagTraceF m_66 s_66 4 f_66) cur_66 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_66 : LowerBin m_66 s_66 g_66 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_66 kn_66 sub_66 gl_66 rc_66 nc_66

def m_67 : Nat := 0xcccccccc
def s_67 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_67 : Nat := 0x404444c
def ep_67 : Nat := 0x40480000000000000008000000000404000800000000000000000000000004044440
theorem epk_67 : ep_67 = edgePack m_67 g_67 := by decide +kernel
def bds_67 : List (Nat × List Nat × Nat × Nat) := [(m_19, s_19, 4, g_19)]
theorem kn_67 : KnownBin bds_67 := by
  intro b hb; simp only [bds_67, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_19
theorem sub_67 : ∀ b ∈ bds_67, m_67 &&& b.1 = b.1 := by intro b hb; simp only [bds_67, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_67 : ∀ b ∈ bds_67, canon b.1 g_67 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_67, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_67 : Nat → List (Nat × Nat) := fun _ => []
def f_67 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_67 : dagCheckRootsV4 m_67 g_67 ep_67 0 bds_67 (dagTraceF m_67 s_67 4 f_67) (cur_67 0) s_67 4 = true := by decide +kernel
theorem nc_67 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_67 g_67 ep_67 bds_67 0 (dagTraceF m_67 s_67 4 f_67) cur_67 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_67 : LowerBin m_67 s_67 g_67 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_67 kn_67 sub_67 gl_67 rc_67 nc_67

def m_68 : Nat := 0xaaaaaaaa
def s_68 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_68 : Nat := 0x2022a
def ep_68 : Nat := 0x2280000000000020028000000000002020800000000000202200000000000000000
theorem epk_68 : ep_68 = edgePack m_68 g_68 := by decide +kernel
def bds_68 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 4, g_18), (m_0, s_0, 4, g_0), (m_16, s_16, 4, g_16), (m_17, s_17, 4, g_17)]
theorem kn_68 : KnownBin bds_68 := by
  intro b hb; simp only [bds_68, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_18
  · exact lb_0
  · exact lb_16
  · exact lb_17
theorem sub_68 : ∀ b ∈ bds_68, m_68 &&& b.1 = b.1 := by intro b hb; simp only [bds_68, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_68 : ∀ b ∈ bds_68, canon b.1 g_68 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_68, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_68_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_68_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_68 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_68_1 (Nat.sub p 32)) (cc_68_0 p) (Nat.blt p 32)
def f_68 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_68 : dagCheckRootsV4 m_68 g_68 ep_68 43 bds_68 (dagTraceF m_68 s_68 6 f_68) (cur_68 0) s_68 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_0 : treeBlockF 0 32 (dagCheckNodeV4 m_68 g_68 ep_68 bds_68 43 (dagTraceF m_68 s_68 6 f_68) cur_68) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_1 : treeBlockF 32 43 (dagCheckNodeV4 m_68 g_68 ep_68 bds_68 43 (dagTraceF m_68 s_68 6 f_68) cur_68) = true := by decide +kernel
theorem nj_68_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_68 g_68 ep_68 bds_68 43 (dagTraceF m_68 s_68 6 f_68) cur_68) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_68_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_68_1 h1 h2)
theorem nc_68 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_68 g_68 ep_68 bds_68 43 (dagTraceF m_68 s_68 6 f_68) cur_68) i = true := nj_68_1
theorem lb_68 : LowerBin m_68 s_68 g_68 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_68 kn_68 sub_68 gl_68 rc_68 nc_68

def m_69 : Nat := 0xff000000ff000000
def s_69 : List Nat := [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000]
def g_69 : Nat := 0x100000015000000
def ep_69 : Nat := 0x1400000000000000000000000000000000000000010000000400000001000000100000000100000015000000
theorem epk_69 : ep_69 = edgePack m_69 g_69 := by decide +kernel
def bds_69 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
theorem kn_69 : KnownBin bds_69 := by
  intro b hb; simp only [bds_69, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_15
theorem sub_69 : ∀ b ∈ bds_69, m_69 &&& b.1 = b.1 := by intro b hb; simp only [bds_69, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_69 : ∀ b ∈ bds_69, canon b.1 g_69 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_69, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_69 : Nat → List (Nat × Nat) := fun _ => []
def f_69 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_69 : dagCheckRootsV4 m_69 g_69 ep_69 0 bds_69 (dagTraceF m_69 s_69 4 f_69) (cur_69 0) s_69 4 = true := by decide +kernel
theorem nc_69 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_69 g_69 ep_69 bds_69 0 (dagTraceF m_69 s_69 4 f_69) cur_69 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_69 : LowerBin m_69 s_69 g_69 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_69 kn_69 sub_69 gl_69 rc_69 nc_69

def m_70 : Nat := 0xf000f000f000f0
def s_70 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_70 : Nat := 0x10005000100070
def ep_70 : Nat := 0x2000000040000000600000000000000000000000000000000000100000001000200010005000100040
theorem epk_70 : ep_70 = edgePack m_70 g_70 := by decide +kernel
def bds_70 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
theorem kn_70 : KnownBin bds_70 := by
  intro b hb; simp only [bds_70, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_12
theorem sub_70 : ∀ b ∈ bds_70, m_70 &&& b.1 = b.1 := by intro b hb; simp only [bds_70, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_70 : ∀ b ∈ bds_70, canon b.1 g_70 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_70, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_70 : Nat → List (Nat × Nat) := fun _ => []
def f_70 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_70 : dagCheckRootsV4 m_70 g_70 ep_70 0 bds_70 (dagTraceF m_70 s_70 4 f_70) (cur_70 0) s_70 4 = true := by decide +kernel
theorem nc_70 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_70 g_70 ep_70 bds_70 0 (dagTraceF m_70 s_70 4 f_70) cur_70 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_70 : LowerBin m_70 s_70 g_70 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_70 kn_70 sub_70 gl_70 rc_70 nc_70

def m_71 : Nat := 0xf0f00000f0f0000
def s_71 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_71 : Nat := 0x107000005070000
def ep_71 : Nat := 0x400000000000000000000000006000000020000000000000000000001020000000200000104000005040000
theorem epk_71 : ep_71 = edgePack m_71 g_71 := by decide +kernel
def bds_71 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
theorem kn_71 : KnownBin bds_71 := by
  intro b hb; simp only [bds_71, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_13
theorem sub_71 : ∀ b ∈ bds_71, m_71 &&& b.1 = b.1 := by intro b hb; simp only [bds_71, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_71 : ∀ b ∈ bds_71, canon b.1 g_71 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_71, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_71 : Nat → List (Nat × Nat) := fun _ => []
def f_71 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_71 : dagCheckRootsV4 m_71 g_71 ep_71 0 bds_71 (dagTraceF m_71 s_71 4 f_71) (cur_71 0) s_71 4 = true := by decide +kernel
theorem nc_71 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_71 g_71 ep_71 bds_71 0 (dagTraceF m_71 s_71 4 f_71) cur_71 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_71 : LowerBin m_71 s_71 g_71 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_71 kn_71 sub_71 gl_71 rc_71 nc_71

def m_72 : Nat := 0x4444888844448888
def s_72 : List Nat := [0x888800008888, 0x404080804040808, 0x44008800440088, 0x44448888]
def g_72 : Nat := 0x4000004040008
def ep_72 : Nat := 0x400000800000000000000000004000000000008000400000404000800000000000000000000000000000000
theorem epk_72 : ep_72 = edgePack m_72 g_72 := by decide +kernel
def bds_72 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_72 : KnownBin bds_72 := by intro b hb; simp [bds_72] at hb
theorem sub_72 : ∀ b ∈ bds_72, m_72 &&& b.1 = b.1 := by intro b hb; simp [bds_72] at hb
theorem gl_72 : ∀ b ∈ bds_72, canon b.1 g_72 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_72] at hb
def cur_72 : Nat → List (Nat × Nat) := unpackCursorV4 0x1a2d58952244890e8701 0x393c3060e4c08181a30227928fa119313e526480f8419000f 7 127 3 7 10 1023 15 32767
def f_72 : Nat → Nat × Nat := unpackForestF 0xc7c632e9814f8a6443e51824f086400f 3 10
set_option maxHeartbeats 0 in
theorem rc_72 : dagCheckRootsV4 m_72 g_72 ep_72 10 bds_72 (dagTraceF m_72 s_72 4 f_72) (cur_72 0) s_72 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_72 : treeBlockF 0 10 (dagCheckNodeV4 m_72 g_72 ep_72 bds_72 10 (dagTraceF m_72 s_72 4 f_72) cur_72) = true := by decide +kernel
theorem nc_72 : ∀ i, 0 ≤ i → i < 10 → (dagCheckNodeV4 m_72 g_72 ep_72 bds_72 10 (dagTraceF m_72 s_72 4 f_72) cur_72) i = true := fun _ h1 h2 => treeBlockF_at nb_72 h1 h2
theorem lb_72 : LowerBin m_72 s_72 g_72 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_72 kn_72 sub_72 gl_72 rc_72 nc_72

def m_73 : Nat := 0x4444444444444444
def s_73 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_73 : Nat := 0x4044404044444
def ep_73 : Nat := 0x400400000000440000040400004004000000000000404000404000000000000000000000000000000000000
theorem epk_73 : ep_73 = edgePack m_73 g_73 := by decide +kernel
def bds_73 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
theorem kn_73 : KnownBin bds_73 := by
  intro b hb; simp only [bds_73, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_4
theorem sub_73 : ∀ b ∈ bds_73, m_73 &&& b.1 = b.1 := by intro b hb; simp only [bds_73, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_73 : ∀ b ∈ bds_73, canon b.1 g_73 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_73, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_73 : Nat → List (Nat × Nat) := fun _ => []
def f_73 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_73 : dagCheckRootsV4 m_73 g_73 ep_73 0 bds_73 (dagTraceF m_73 s_73 4 f_73) (cur_73 0) s_73 4 = true := by decide +kernel
theorem nc_73 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_73 g_73 ep_73 bds_73 0 (dagTraceF m_73 s_73 4 f_73) cur_73 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_73 : LowerBin m_73 s_73 g_73 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_73 kn_73 sub_73 gl_73 rc_73 nc_73

def m_74 : Nat := 0xc0c0c0c0c0c0c0c
def s_74 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_74 : Nat := 0x404040404040c
def ep_74 : Nat := 0x400000800000400000000080004000000000008000000000000000000000000000000000004040404040400
theorem epk_74 : ep_74 = edgePack m_74 g_74 := by decide +kernel
def bds_74 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_74 : KnownBin bds_74 := by intro b hb; simp [bds_74] at hb
theorem sub_74 : ∀ b ∈ bds_74, m_74 &&& b.1 = b.1 := by intro b hb; simp [bds_74] at hb
theorem gl_74 : ∀ b ∈ bds_74, canon b.1 g_74 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_74] at hb
def cc_74_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0xe24c6d20345319280b83c581a2a0b14048912844921e0b0e04858202c9a124f08268303c141a040402249fa3ff91df28df4467993fc89dda4de8267292f8895c249df246f03f741db00dd3066802f34159809ca046381f100d8605c1026000f 11 2047 5 31 10 1023 17 131071
def cc_74_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0x3d299e140ec26741038251b924d8146a09314998240bc265c102c2795934a80c5205270513024900c4605202410234 8 255 3 7 10 1023 17 131071
def cur_74 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_74_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_74_0 p) (Nat.blt p 32)
def f_74 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_74 : dagCheckRootsV4 m_74 g_74 ep_74 64 bds_74 (dagTraceF m_74 s_74 5 f_74) (cur_74 0) s_74 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_74_0 : treeBlockF 0 32 (dagCheckNodeV4 m_74 g_74 ep_74 bds_74 64 (dagTraceF m_74 s_74 5 f_74) cur_74) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_74_1 : treeBlockF 32 64 (dagCheckNodeV4 m_74 g_74 ep_74 bds_74 64 (dagTraceF m_74 s_74 5 f_74) cur_74) = true := by decide +kernel
theorem nj_74_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_74 g_74 ep_74 bds_74 64 (dagTraceF m_74 s_74 5 f_74) cur_74) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_74_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_74_1 h1 h2)
theorem nc_74 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_74 g_74 ep_74 bds_74 64 (dagTraceF m_74 s_74 5 f_74) cur_74) i = true := nj_74_1
theorem lb_74 : LowerBin m_74 s_74 g_74 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_74 kn_74 sub_74 gl_74 rc_74 nc_74

def m_75 : Nat := 0x50a050a050a050a
def s_75 : List Nat := [0xa000a000a000a, 0x102010201020102, 0x50a0000050a, 0x50a050a]
def g_75 : Nat := 0x10205020502050a
def ep_75 : Nat := 0x400000800000400000000080000000000000000000000000000000001020002000200000000000000000000
theorem epk_75 : ep_75 = edgePack m_75 g_75 := by decide +kernel
def bds_75 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_75 : KnownBin bds_75 := by intro b hb; simp [bds_75] at hb
theorem sub_75 : ∀ b ∈ bds_75, m_75 &&& b.1 = b.1 := by intro b hb; simp [bds_75] at hb
theorem gl_75 : ∀ b ∈ bds_75, canon b.1 g_75 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_75] at hb
def cur_75 : Nat → List (Nat × Nat) := unpackCursorV4 0x16ac58b12a44890e8701 0x31343068c4a08121928204928ea11b393a526c80e841b000f 7 127 3 7 10 1023 15 32767
def f_75 : Nat → Nat × Nat := unpackForestF 0xc7463629d64a0a6c43a494209086c00f 3 10
set_option maxHeartbeats 0 in
theorem rc_75 : dagCheckRootsV4 m_75 g_75 ep_75 10 bds_75 (dagTraceF m_75 s_75 4 f_75) (cur_75 0) s_75 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_75 : treeBlockF 0 10 (dagCheckNodeV4 m_75 g_75 ep_75 bds_75 10 (dagTraceF m_75 s_75 4 f_75) cur_75) = true := by decide +kernel
theorem nc_75 : ∀ i, 0 ≤ i → i < 10 → (dagCheckNodeV4 m_75 g_75 ep_75 bds_75 10 (dagTraceF m_75 s_75 4 f_75) cur_75) i = true := fun _ h1 h2 => treeBlockF_at nb_75 h1 h2
theorem lb_75 : LowerBin m_75 s_75 g_75 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_75 kn_75 sub_75 gl_75 rc_75 nc_75

def m_76 : Nat := 0xaaaaaaaaaaaaaaaa
def s_76 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_76 : Nat := 0x200020002022a
def ep_76 : Nat := 0x22800000000000002280002000200020028000200020002020800020002000202200000000000000000
theorem epk_76 : ep_76 = edgePack m_76 g_76 := by decide +kernel
def bds_76 : List (Nat × List Nat × Nat × Nat) := [(m_55, s_55, 7, g_55)]
theorem kn_76 : KnownBin bds_76 := by
  intro b hb; simp only [bds_76, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_55
theorem sub_76 : ∀ b ∈ bds_76, m_76 &&& b.1 = b.1 := by intro b hb; simp only [bds_76, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_76 : ∀ b ∈ bds_76, canon b.1 g_76 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_76, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_76 : Nat → List (Nat × Nat) := fun _ => []
def f_76 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_76 : dagCheckRootsV4 m_76 g_76 ep_76 0 bds_76 (dagTraceF m_76 s_76 7 f_76) (cur_76 0) s_76 7 = true := by decide +kernel
theorem nc_76 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_76 g_76 ep_76 bds_76 0 (dagTraceF m_76 s_76 7 f_76) cur_76 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_76 : LowerBin m_76 s_76 g_76 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_76 kn_76 sub_76 gl_76 rc_76 nc_76

def m_77 : Nat := 0xff00ff00ff00ff
def s_77 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_77 : Nat := 0x1700570017007f
def ep_77 : Nat := 0x2800000040000000680000000000000000000600020006000800120002001200200014005400140040
theorem epk_77 : ep_77 = edgePack m_77 g_77 := by decide +kernel
def bds_77 : List (Nat × List Nat × Nat × Nat) := [(m_64, s_64, 7, g_64)]
theorem kn_77 : KnownBin bds_77 := by
  intro b hb; simp only [bds_77, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_64
theorem sub_77 : ∀ b ∈ bds_77, m_77 &&& b.1 = b.1 := by intro b hb; simp only [bds_77, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_77 : ∀ b ∈ bds_77, canon b.1 g_77 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_77, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_77 : Nat → List (Nat × Nat) := fun _ => []
def f_77 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_77 : dagCheckRootsV4 m_77 g_77 ep_77 0 bds_77 (dagTraceF m_77 s_77 7 f_77) (cur_77 0) s_77 7 = true := by decide +kernel
theorem nc_77 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_77 g_77 ep_77 bds_77 0 (dagTraceF m_77 s_77 7 f_77) cur_77 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_77 : LowerBin m_77 s_77 g_77 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_77 kn_77 sub_77 gl_77 rc_77 nc_77

def m_78 : Nat := 0xcc33cc33cc33cc33
def s_78 : List Nat := [0x4411441144114411, 0x33003300330033, 0xc030c030c030c03, 0xcc330000cc33, 0xcc33cc33]
def g_78 : Nat := 0x13041304134433
def ep_78 : Nat := 0x400402000000400000040200000000000000000000204020402000000000000000000000010041004104400
theorem epk_78 : ep_78 = edgePack m_78 g_78 := by decide +kernel
def bds_78 : List (Nat × List Nat × Nat × Nat) := [(m_57, s_57, 5, g_57), (m_27, s_27, 5, g_27), (m_28, s_28, 5, g_28), (m_25, s_25, 5, g_25), (m_29, s_29, 5, g_29), (m_30, s_30, 5, g_30), (m_26, s_26, 5, g_26), (m_14, s_14, 4, g_14)]
theorem kn_78 : KnownBin bds_78 := by
  intro b hb; simp only [bds_78, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_57
  · exact lb_27
  · exact lb_28
  · exact lb_25
  · exact lb_29
  · exact lb_30
  · exact lb_26
  · exact lb_14
theorem sub_78 : ∀ b ∈ bds_78, m_78 &&& b.1 = b.1 := by intro b hb; simp only [bds_78, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_78 : ∀ b ∈ bds_78, canon b.1 g_78 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_78, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_78 : Nat → List (Nat × Nat) := unpackCursorV4 0x62a21400c0001 0x1c5e38ba6d68daceb5636a3ad18da2fa5dd4abe937d22b94d5292e5154a0c84db0932116c20fc5ed8b5b15be291b5ad6ac6938d1f394d5292e5154a0c84db0932116c20a34f3697ad1cda1fa4fd48e68fc91bb94f5296e51d4a1993f5276e4dcc99a92b724f213ec25c847b08660fec1dc837306760ae413a81f7036e05d409801f 13 8191 6 63 11 2047 15 32767
def f_78 : Nat → Nat × Nat := unpackForestF 0x1d3f1b81f 1 10
set_option maxHeartbeats 0 in
theorem rc_78 : dagCheckRootsV4 m_78 g_78 ep_78 3 bds_78 (dagTraceF m_78 s_78 7 f_78) (cur_78 0) s_78 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_78 : treeBlockF 0 3 (dagCheckNodeV4 m_78 g_78 ep_78 bds_78 3 (dagTraceF m_78 s_78 7 f_78) cur_78) = true := by decide +kernel
theorem nc_78 : ∀ i, 0 ≤ i → i < 3 → (dagCheckNodeV4 m_78 g_78 ep_78 bds_78 3 (dagTraceF m_78 s_78 7 f_78) cur_78) i = true := fun _ h1 h2 => treeBlockF_at nb_78 h1 h2
theorem lb_78 : LowerBin m_78 s_78 g_78 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_78 kn_78 sub_78 gl_78 rc_78 nc_78

def m_79 : Nat := 0xcccc3333cccc3333
def s_79 : List Nat := [0x4444111144441111, 0x333300003333, 0xc0c03030c0c0303, 0xcc003300cc0033, 0xcccc3333]
def g_79 : Nat := 0x4111304041333
def ep_79 : Nat := 0x400022000000000000000000004000200000020000400020404020000000000000000000004111004041000
theorem epk_79 : ep_79 = edgePack m_79 g_79 := by decide +kernel
def bds_79 : List (Nat × List Nat × Nat × Nat) := [(m_54, s_54, 5, g_54), (m_33, s_33, 5, g_33), (m_37, s_37, 5, g_37), (m_36, s_36, 5, g_36), (m_35, s_35, 5, g_35), (m_34, s_34, 5, g_34), (m_31, s_31, 5, g_31), (m_8, s_8, 4, g_8)]
theorem kn_79 : KnownBin bds_79 := by
  intro b hb; simp only [bds_79, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_54
  · exact lb_33
  · exact lb_37
  · exact lb_36
  · exact lb_35
  · exact lb_34
  · exact lb_31
  · exact lb_8
theorem sub_79 : ∀ b ∈ bds_79, m_79 &&& b.1 = b.1 := by intro b hb; simp only [bds_79, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_79 : ∀ b ∈ bds_79, canon b.1 g_79 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_79, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_79 : Nat → List (Nat × Nat) := unpackCursorV4 0x62a21400c0001 0x1c5e38ba71576291b5636aa6d3b5a6da3d947368d6518f959d2a3e4e7c98b83d5072e0d54189c5ed8a4692b4af795af2ada54a49f593ab26d24c8c96b81d5032e0554089b4f46966d1f5a1da4f9497691e521da3f347668de519f94bd28664ec899d92b9246e13d425b8475086e0fcc1d98375066e0bd415b8275046e07d409801f 13 8191 6 63 11 2047 15 32767
def f_79 : Nat → Nat × Nat := unpackForestF 0x1d2e9981f 1 10
set_option maxHeartbeats 0 in
theorem rc_79 : dagCheckRootsV4 m_79 g_79 ep_79 3 bds_79 (dagTraceF m_79 s_79 7 f_79) (cur_79 0) s_79 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_79 : treeBlockF 0 3 (dagCheckNodeV4 m_79 g_79 ep_79 bds_79 3 (dagTraceF m_79 s_79 7 f_79) cur_79) = true := by decide +kernel
theorem nc_79 : ∀ i, 0 ≤ i → i < 3 → (dagCheckNodeV4 m_79 g_79 ep_79 bds_79 3 (dagTraceF m_79 s_79 7 f_79) cur_79) i = true := fun _ h1 h2 => treeBlockF_at nb_79 h1 h2
theorem lb_79 : LowerBin m_79 s_79 g_79 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_79 kn_79 sub_79 gl_79 rc_79 nc_79

def m_80 : Nat := 0xf00ff00ff00ff00f
def s_80 : List Nat := [0x5005500550055005, 0x3003300330033003, 0xf000f000f000f, 0xf00f0000f00f, 0xf00ff00f]
def g_80 : Nat := 0x710071007500f
def ep_80 : Nat := 0x1000400800001000000040080000000000000000000000000000000000021002100200000004100410045000
theorem epk_80 : ep_80 = edgePack m_80 g_80 := by decide +kernel
def bds_80 : List (Nat × List Nat × Nat × Nat) := [(m_58, s_58, 5, g_58), (m_24, s_24, 5, g_24), (m_22, s_22, 5, g_22), (m_23, s_23, 5, g_23), (m_21, s_21, 5, g_21), (m_20, s_20, 5, g_20), (m_32, s_32, 5, g_32), (m_5, s_5, 4, g_5)]
theorem kn_80 : KnownBin bds_80 := by
  intro b hb; simp only [bds_80, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_58
  · exact lb_24
  · exact lb_22
  · exact lb_23
  · exact lb_21
  · exact lb_20
  · exact lb_32
  · exact lb_5
theorem sub_80 : ∀ b ∈ bds_80, m_80 &&& b.1 = b.1 := by intro b hb; simp only [bds_80, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_80 : ∀ b ∈ bds_80, canon b.1 g_80 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_80, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_80 : Nat → List (Nat × Nat) := unpackCursorV4 0x62a21400c0001 0x1c5e38ba6d68daceb5636a3ad18da2fa5dd4abe937d22b94d5292e5154a0c84db0932116c20fc5ed8b5b15be291b5ad6ac6938d1f394d5292e5154a0c84db0932116c20a34f3697ad1cda1fa4fd48e68fc91bb94f5296e51d4a1993f5276e4dcc99a92b724f213ec25c847b08660fec1dc837306760ae413a81f7036e05d409801f 13 8191 6 63 11 2047 15 32767
def f_80 : Nat → Nat × Nat := unpackForestF 0x1d3f1b81f 1 10
set_option maxHeartbeats 0 in
theorem rc_80 : dagCheckRootsV4 m_80 g_80 ep_80 3 bds_80 (dagTraceF m_80 s_80 7 f_80) (cur_80 0) s_80 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_80 : treeBlockF 0 3 (dagCheckNodeV4 m_80 g_80 ep_80 bds_80 3 (dagTraceF m_80 s_80 7 f_80) cur_80) = true := by decide +kernel
theorem nc_80 : ∀ i, 0 ≤ i → i < 3 → (dagCheckNodeV4 m_80 g_80 ep_80 bds_80 3 (dagTraceF m_80 s_80 7 f_80) cur_80) i = true := fun _ h1 h2 => treeBlockF_at nb_80 h1 h2
theorem lb_80 : LowerBin m_80 s_80 g_80 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_80 kn_80 sub_80 gl_80 rc_80 nc_80

def m_81 : Nat := 0xffffffff00000000
def s_81 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_81 : Nat := 0x117155700000000
def ep_81 : Nat := 0x1440000000000016004200000000010604020000000001121002000000000114155400000000
theorem epk_81 : ep_81 = edgePack m_81 g_81 := by decide +kernel
def bds_81 : List (Nat × List Nat × Nat × Nat) := [(m_39, s_39, 7, g_39), (m_47, s_47, 7, g_47), (m_38, s_38, 5, g_38), (m_42, s_42, 5, g_42), (m_45, s_45, 5, g_45), (m_44, s_44, 5, g_44), (m_43, s_43, 5, g_43), (m_41, s_41, 5, g_41), (m_40, s_40, 6, g_40)]
theorem kn_81 : KnownBin bds_81 := by
  intro b hb; simp only [bds_81, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_39
  · exact lb_47
  · exact lb_38
  · exact lb_42
  · exact lb_45
  · exact lb_44
  · exact lb_43
  · exact lb_41
  · exact lb_40
theorem sub_81 : ∀ b ∈ bds_81, m_81 &&& b.1 = b.1 := by intro b hb; simp only [bds_81, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_81 : ∀ b ∈ bds_81, canon b.1 g_81 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_81, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_81 : Nat → List (Nat × Nat) := unpackCursorV4 0xacf49ff493338c5b7e39713464345773509b4279357428741bb314db06b900590001 0x1c5f1c5b1c571c531b5f1b5e1b5b1b5a1b571b561b531b523b4f3b4e3b4d1a5f1a5e1a5b1a571a531a523a4b4a4a3a494a474a463a433a414a374a364a35195f195b19571953594f494b49475943593f593d593b29395937793559332931392f692b69273923185e1c5f1c5e1c5b1c571c531c521b5f1b5b1b571b533b4f4b4e3b4d3b473b453b433b421a5f1a5e1a5b1a5a1a571a561a531a523a474a463a453a3f3a3e3a3d195f195b19571953494f494b49474943393f393b39373933392f392d392b29293927792539232921185e1c5f1c5e1c5b1c5a1c571c561c531c521b5f1b5b1b571b533b4f3b4e3b4d1a5f1a5b1a571a534a4f4a4e5a4d4a3f4a3e3a3b3a393a334a323a31c230195f195b19571953494f794d494b29494947494549432941493f493b49374933392f692b69273923185e1b4f1b4e1b4b1b471b431b421a4f1a4b1a471a433a3f4a3e3a3d194f194b19471943493f493b49374933392f392b39273923184e38261c5f1c5e1c5b1c571c531c521b5f1b5e1b5b1b571b531b523b4f3b4d3b4b3b4a3b474b463b45c3441a5f1a5e1a5b1a5a1a571a561a531a523a4f5a4e3a4d3a3f3a3e3a3d195f195b19571953594f494b49475943393f393b39373933392f392d392b29293927792539232921185e382688241c5f1c5b1c571c531b5f1b5e1b5b1b5a1b571b561b531b522b4f2b4e2b4d1a5f1a5b1a571a535a4f4a4b4a475a435a3f5a3d5a3b3a395a376a355a333a31195f195e195b195719531952294b494a29494947494629432941493749364935792f292b79272923185e1c5f1c5e1c5b1c571c531c521b5f1b5b1b571b534b4f4b4b4b474b431a5f1a5b1a571a532a4f4a4e2a4d2a472a452a432a422a3f2a3b2a372a33195f195e195b195a1957195619531952294749462945293f393e293b293a2937693629332932292f292e292d185e1c5f1c5e1c5b1c5a1c571c561c531c521b5f1b5b1b571b532b4f2b4e2b4d1a5f1a5b1a571a534a4f6a4d4a4b3a494a474a454a433a414a3f4a3b4a374a33195f195b19571953494f494e594d493f493e293b29392933493229317130792f292b79272923185e1b4f1b4e1b4b1b471b431b421a4f1a4b1a471a434a3f4a3b4a374a33194f194b19471943293f493e293d292f292b29272923184e28161c5f1c5e1c5b1c571c531c521b5f1b5b1b571b535b4f4b4b4b475b431a5f1a5e1a5b1a571a531a522a4f2a4d2a4b2a4a2a474a462a4572442a3f2a3b2a372a33195f195e195b195a1957195619531952294f594e294d293f393e293b293a2937693629332932292f292e292d185e281688141c5f1c5b1c571c531b5f1b5b1b571b533b4f3b4b3b473b431a5f1a5e1a5b1a5a1a571a561a531a523a4f5a4e3a4b3a4a3a474a463a433a422a3f2a3e2a3d195f195e195b195719531952794f294b79472943293b393a29393937393629332931392739266925185e1c5f1c5b1c571c531b5f1b5e1b5b1b571b531b526b4f3b4b6b473b431a5f1a5b1a571a532a4f2a4b2a472a432a3f3a3e2a3d2a372a352a332a32195f195e195b195a1957195619531952294f594e294b294a2947494629432942293769362935292f292e292d185e1c5f1c5b1c571c531b5f1b5e1b5b1b5a1b571b561b531b526b4f5b4e6b4b4b4a6b474b466b435b421a5f1a5b1a571a536a4f3a4b6a473a432a3f2a3e2a3d195f195b19571953794f294b79472943393f393e393d392f392e292b29292923392229212120185e1b4f1b4b1b471b431a4f1a4e1a4b1a471a431a426a3f6a3b6a376a33194f194b19471943293f293b29372933292f692e292d184e28161c5f1c5b1c571c531b5f1b5e1b5b1b571b531b523b4f3b4b3b473b431a5f1a5e1a5b1a571a531a522a4f2a4b2a472a432a3f2a3d2a3b2a3a2a373a362a352234195f195e195b195a1957195619531952294f594e294b294a2947494629432942293f393e293d292f292e292d185e281688141b4f1b4b1b471b431a4f1a4b1a471a43f23fe23bd237b233194f194b19471943a13f913b81376133512f412b31271123184e001f 16 65535 6 63 11 2047 16 65535
def f_81 : Nat → Nat × Nat := unpackForestF 0x18fc63b18df34418cc53f14ec537791053314bc52b149ca34148c01f 4 10
set_option maxHeartbeats 0 in
theorem rc_81 : dagCheckRootsV4 m_81 g_81 ep_81 16 bds_81 (dagTraceF m_81 s_81 8 f_81) (cur_81 0) s_81 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_81 : treeBlockF 0 16 (dagCheckNodeV4 m_81 g_81 ep_81 bds_81 16 (dagTraceF m_81 s_81 8 f_81) cur_81) = true := by decide +kernel
theorem nc_81 : ∀ i, 0 ≤ i → i < 16 → (dagCheckNodeV4 m_81 g_81 ep_81 bds_81 16 (dagTraceF m_81 s_81 8 f_81) cur_81) i = true := fun _ h1 h2 => treeBlockF_at nb_81 h1 h2
theorem lb_81 : LowerBin m_81 s_81 g_81 9 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_81 kn_81 sub_81 gl_81 rc_81 nc_81

def m_82 : Nat := 0xffffffff
def s_82 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_82 : Nat := 0x1517577f
def ep_82 : Nat := 0x42680000000000020028000000000406020800000000101202200000000015145440
theorem epk_82 : ep_82 = edgePack m_82 g_82 := by decide +kernel
def bds_82 : List (Nat × List Nat × Nat × Nat) := [(m_64, s_64, 7, g_64), (m_68, s_68, 7, g_68), (m_61, s_61, 5, g_61), (m_60, s_60, 5, g_60), (m_62, s_62, 5, g_62), (m_67, s_67, 5, g_67), (m_65, s_65, 5, g_65), (m_66, s_66, 5, g_66), (m_63, s_63, 6, g_63)]
theorem kn_82 : KnownBin bds_82 := by
  intro b hb; simp only [bds_82, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_64
  · exact lb_68
  · exact lb_61
  · exact lb_60
  · exact lb_62
  · exact lb_67
  · exact lb_65
  · exact lb_66
  · exact lb_63
theorem sub_82 : ∀ b ∈ bds_82, m_82 &&& b.1 = b.1 := by intro b hb; simp only [bds_82, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_82 : ∀ b ∈ bds_82, canon b.1 g_82 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_82, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_82 : Nat → List (Nat × Nat) := unpackCursorV4 0xacf49ff491b98adb7e337134643455f94f1b4273357428741a39135b06b300590001 0x1c5f1c5b1c5a1c571c561c531b5f1b5e1b5b1b5a1b571b561b531b525b4f5b4e5b4d1a5f1a5b1a571a533a4b3a4a6a493a473a465a435a413a373a363a35195a185f185b18571853584f384b38475843583f483d583b28395837483558332831682f782b782768231c5f1c5b1c571c531b5f1b5b1b5a1b571b561b533b4f3b4e6b4d3b473b453b433b421a5f1a5e1a5b1a5a1a571a561a531a523a473a463a453a3f5a3e3a3d195a185f185b18571853384f384b38473843683f683b68376833382f382d382b282938274825382328211c5f1c5e1c5b1c5a1c571c561c531c521b5f1b5b1b5a1b571b561b533b4f3b4e3b4d1a5f1a5b1a5a1a571a561a533a4f3a4e5a4d3a3f3a3e3a3b3a393a333a326a31c230195a39428940185f185b18571853384f484d384b28493847384538432841383f383b38373833682f782b782768231b4f1b4b1b471b431a4f1a4b1a4a1a471a461a433a3f3a3e5a3d194a3932184f184b18471843383f383b38373833582f582b582758231c5f1c5b1c571c531b5f1b5b1b571b535b4f5b4d3b4b3b4a3b473b466b45c3441a5f1a5e1a5b1a5a1a571a561a531a525a4f5a4e5a4d3a3f3a3e3a3d195a185f185b18571853584f384b38475843683f683b68376833582f482d582b282958274825582328211c5f1c5b1c5a1c571c561c531b5f1b5e1b5b1b5a1b571b561b531b522b4f2b4e2b4d1a5f1a5b1a571a535a4f3a4b3a475a434a3f4a3d4a3b6a394a377a354a334a31195a185f185b18571853284b384a28493847384628432841383738363835482f282b482728231c5f1c5b1c571c531b5f1b5b1b571b533b4f3b4b3b473b431a5a195f195b195a195719561953294f394e294d2947294529432942293f293b29372933185f185e185b185a1857185618531852284738462845283f683e283b283a2837783628332832281f281e281d1c5f1c5e1c5b1c5a1c571c561c531c521b5f1b5b1b5a1b571b561b532b4f2b4e2b4d1a5f1a5b1a571a533a4f7a4d3a4b3a493a473a453a436a413a3f3a3b3a373a33195a39428940185f185b185a185718561853384f384e484d383f383e283b28392833383228317030482f282b482728231b4f1b4b1b471b431a4f1a4b1a471a433a3f3a3b3a373a33194a3932184f184b184a184718461843283f383e283d282f282b282728231c5f1c5b1c571c531b5f1b5b1b571b535b4f3b4b3b475b431a5a195f195b19571953294f294d294b294a2947394629457144293f293b29372933185f185e185b185a1857185618531852284f484e284d283f683e283b283a2837783628332832281f281e281d1c5f1c5b1c571c531b5f1b5b1b5a1b571b561b536b4f6b4b6b476b431a5f1a5e1a5b1a5a1a571a561a531a524a4f5a4e4a4b3a4a4a473a464a434a422a3f2a3e2a3d195a185f185b18571853484f284b48472843283b683a283948374836283328314827482648251c5f1c5b1c571c531b5f1b5b1b571b537b4f6b4b7b476b431a5a195f195b195a195719561953294f294b29472943293f693e293d2937293529332932185f185e185b185a1857185618531852284f584e284b284a2847384628432842283748362835281f281e281d1c5f1c5b1c571c531b5f1b5e1b5b1b5a1b571b561b531b524b4f4b4e4b4b3b4a4b473b464b435b421a5f1a5b1a5a1a571a561a537a4f6a4b7a476a432a3f2a3e2a3d195a49328930185f185b185a185718561853484f284b48472843483f483e483d482f482e282b282928236822282120201b4f1b4b1b471b431a4f1a4b1a471a434a3f4a3b4a374a33194a4922184f184b184a184718461843283f283b28372833282f482e282d1c5f1c5b1c571c531b5f1b5b1b571b536b4f6b4b6b476b431a5a195f195b19571953294f294b29472943293f293d293b293a2937693629352134185f185e185b185a1857185618531852284f584e284b284a2847384628432842283f483e283d281f281e281d1b4f1b4b1b471b431a4f1a4b1a471a43f23fe23bd237b233194a184f184b18471843a03f903b80376033502f402b30271023001f 16 65535 6 63 11 2047 16 65535
def f_82 : Nat → Nat × Nat := unpackForestF 0x18fc63b18df34418cc43f10ec437751043310bc42b109c934108c01f 4 10
set_option maxHeartbeats 0 in
theorem rc_82 : dagCheckRootsV4 m_82 g_82 ep_82 16 bds_82 (dagTraceF m_82 s_82 8 f_82) (cur_82 0) s_82 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_82 : treeBlockF 0 16 (dagCheckNodeV4 m_82 g_82 ep_82 bds_82 16 (dagTraceF m_82 s_82 8 f_82) cur_82) = true := by decide +kernel
theorem nc_82 : ∀ i, 0 ≤ i → i < 16 → (dagCheckNodeV4 m_82 g_82 ep_82 bds_82 16 (dagTraceF m_82 s_82 8 f_82) cur_82) i = true := fun _ h1 h2 => treeBlockF_at nb_82 h1 h2
theorem lb_82 : LowerBin m_82 s_82 g_82 9 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_82 kn_82 sub_82 gl_82 rc_82 nc_82

def m_83 : Nat := 0xffff0000ffff0000
def s_83 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_83 : Nat := 0x117000015170000
def ep_83 : Nat := 0x1400000000000000000000000016000000020000010600000406000001120000101200000114000015140000
theorem epk_83 : ep_83 = edgePack m_83 g_83 := by decide +kernel
def bds_83 : List (Nat × List Nat × Nat × Nat) := [(m_39, s_39, 7, g_39)]
theorem kn_83 : KnownBin bds_83 := by
  intro b hb; simp only [bds_83, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_39
theorem sub_83 : ∀ b ∈ bds_83, m_83 &&& b.1 = b.1 := by intro b hb; simp only [bds_83, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_83 : ∀ b ∈ bds_83, canon b.1 g_83 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_83, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_83 : Nat → List (Nat × Nat) := fun _ => []
def f_83 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_83 : dagCheckRootsV4 m_83 g_83 ep_83 0 bds_83 (dagTraceF m_83 s_83 7 f_83) (cur_83 0) s_83 7 = true := by decide +kernel
theorem nc_83 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_83 g_83 ep_83 bds_83 0 (dagTraceF m_83 s_83 7 f_83) cur_83 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_83 : LowerBin m_83 s_83 g_83 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_83 kn_83 sub_83 gl_83 rc_83 nc_83

def g_84 : Nat := 0x11715571517577f
def ep_84 : Nat := 0x1400422800001440000042680016004200020028010604020406020801121002101202200114155415145440
theorem epk_84 : ep_84 = edgePack fullMask g_84 := by decide +kernel
def bds_84 : List (Nat × List Nat × Nat × Nat) := [(m_51, s_51, 7, g_51), (m_74, s_74, 6, g_74), (m_83, s_83, 8, g_83), (m_81, s_81, 9, g_81), (m_82, s_82, 9, g_82), (m_48, s_48, 6, g_48), (m_52, s_52, 6, g_52), (m_55, s_55, 7, g_55), (m_59, s_59, 6, g_59), (m_77, s_77, 8, g_77), (m_56, s_56, 6, g_56), (m_73, s_73, 5, g_73), (m_49, s_49, 5, g_49), (m_53, s_53, 5, g_53), (m_70, s_70, 5, g_70), (m_50, s_50, 5, g_50), (m_71, s_71, 5, g_71), (m_58, s_58, 5, g_58), (m_79, s_79, 8, g_79), (m_80, s_80, 8, g_80), (m_78, s_78, 8, g_78), (m_72, s_72, 5, g_72), (m_54, s_54, 5, g_54), (m_75, s_75, 5, g_75), (m_46, s_46, 5, g_46)]
theorem kn_84 : KnownBin bds_84 := by
  intro b hb; simp only [bds_84, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_51
  · exact lb_74
  · exact lb_83
  · exact lb_81
  · exact lb_82
  · exact lb_48
  · exact lb_52
  · exact lb_55
  · exact lb_59
  · exact lb_77
  · exact lb_56
  · exact lb_73
  · exact lb_49
  · exact lb_53
  · exact lb_70
  · exact lb_50
  · exact lb_71
  · exact lb_58
  · exact lb_79
  · exact lb_80
  · exact lb_78
  · exact lb_72
  · exact lb_54
  · exact lb_75
  · exact lb_46
theorem sub_84 : ∀ b ∈ bds_84, fullMask &&& b.1 = b.1 := by intro b hb; simp only [bds_84, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_84 : ∀ b ∈ bds_84, canon b.1 g_84 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_84, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_84_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8ee65178ca2691410f97a8f2eb735b7beb49cb6469ab91f95f262984c4e4989313114241ebf93889e61de8b0271394e2249c3ad3863a40b1ab1257c1e6c83059047b205d6407a80005e00001 0x2e2f81716c0b8ae05c5302daf806d780b6b605b5a02dab816d580b6a601b5202caf80a56c0b2ae0295302ca78165340529605947034a280a50c0b27e0593d0149d8064e40b26e069350149980a4c4090be0385b0242b80e14c0909e0384b0242380e10c0907e0483d01c1d80e0e40906e0483501c1980e0c40503e0381b0240b80a04c038be01c5e00e2d807168038ae01c5600e29807148036be01b5b00dab806d4c032be0195b00cab80654c0329e0694d00ca58065240328e0194500ca180a5040327e0693d00c9d8064dc0326a0193300c2f80616c030ae0185300c27812134030960184900c23806114030860384100c1f8060ec0306e018330140f80e06c0902e028130462f81b16c118ae06c531012f07c9583c49c1d246034af80a56c0d2ae02953034a780a52c0d28e029430149c81e494090be0385b0242b80e14c0909e0384b0242380e10c0705203828024128120900503e0381b0240b80a04c0bcfe01e7302ebf81f5f803ae607d7200eb781b5b80dada01c7f02e398071ac158d406c6900e33823198038c606c6100e2b823158118aa01b6f02db3806d7c116ba05b57045aa816d3c0368e02a7f015398069bc054d602a6700d3180697c054ba02a5b0152c80a95c054aa01a530152880a93c0349601a470152180a8f40546e02a35014bf81e5f8052e60297200cb78065b8052d60296a014b3816598032c60196200caf806578052ba0195c014ad80a568052b202958014ab816558052aa0595400ca9806548052a201950014a7816538032960194a00ca380651805286029420149b81a4d80526a0487f01c398061bc070d60486700c3180617c090ba0385b01c2c81215c090aa0185301c2881213c030960184701c2180e0ec0906e0282f0141580a09c050460281f0140e80a06c07032028170240a80a04c0502205e7f00f398075fc0bae601d6f056b701b5b403ace06d6500eb181b588038fe07c7e02e3981b1c8038ce08c660363280717c0d8bc06c5d00db7816d9c0b6be01b5702da781ad340368e09b450153f80a9cc034de02a6b0153380698c054be01a5b00d2b80a94c0549e02a4d00d2580a9240348e02a450152180a9040547a02a370151a80a5fc0f2fc02973014b90065bc032dc0296b014b500a59c0b2cc0196300cb100a57c0b2bc0195b00cad00655c032ac02953014a900a53c0b29c0294d02ca600652c032940294900ca400651c0328c0294500ca200a50c0528402941014a000a4dc0d26c029350243f80e1cc030de0386b0243380618c090be0185b00c2b80e14c0909e0484d00c2580e1240308e0484501c2180e10407076048370141780a0ac0504e028230140f80a07405036038190140b812054050260281103eb781f5b80fac607d6202e3780718c0b8be05c5d00e2d807164058ae02c5500e29807144036de05b6300daf806d74056b602b5900dab806d54056a602b5100da7806d2c0368e01b430352f81a974114ae06a5500d2781691c0b47e01a37014b780a58c052be0195d014ad80655c032aa0194f014a580a51c032860293f00c9d8064dc052660292b014938121bc070c60485f0242e80e16c070b2048570242a80e14c070a20184f01c2581211c030860483f00c1d8060dc070660382b0241380a07c0503602817014098079fc0fcfc07e7303f390175fc03ae601d6f036b701b5b4038fe05c7300e378231b8118da01c5f0462f00716c0d8b201c530562901b1442e8a008b6f045b7022db4136d801b67045b2822d88036be05b5702da7806d1c054fe02a730153780a9b4034d602a6900d3380a994054c602a6100d2f80a96c054ae01a530152780692c0348e02a430151e80a8dc0546a0297f03cbf00a5cc052e40296f044b700a5b4322d80196b00cb500a5a4032d00196700cb300a594032c802963014b100a584052c00195f00caf00a56c052b40295702cab00654c032a40294f02ca700652c032940194700ca300a50c05284029370349b00a4d4090fe03873024378121b4030d60386900c33812194070c60386100c2f80e16c090ae018530242780612c0308e0384301c1d8120dc0505e0282b0141380a08c0503e0281d0140d80e0640502e048150140980a04403ade07d630363780718c038be08c5e0362e822d7c116bc01b57045a9006d3c0d68e02a6f0153180a97c034b601a570152980693c0549602a4a0152381a9180348602a3d0151b80a8d4052de0796e014b180a588052be0895e00cad806568032ae01956014a980a5480329e0194e014a580a5280528e0694600ca18065080526e069360149a8121bc070c60485f00c2d80615c070a60184f01c2581211c030860383b0241b80a0bc05056028270141180a07c0503a0281b01c0c80a05c0902a02813014088175bc03ac601c6f02e3180717c038b601c5700e2981edbc0f6dc07b6303db1006d7c036bc02b5b015ad00ad5c056ac01b5300da9016d3c0b69c01b4b00da5006d1c0368c02b43015a100697c0b4ae05a4f00d2381a8fc0d47a06a370351a80a5bc052c60195f014ad80a55c032a60294f00ca580651c052860193f00c9e80a4dc0326a029330149580a49c090de0386300c2f80e16c090ae018530242780612c0308e038430241f8120f407076038390241b8120d4070660383101c1581209c0503e0281b0140b80a04c0bcfe01e7300ebf8175cc03ade06d6d00eb581b5a803ace0ad66036b285d5900d8fe07c7e00e3981b1c8038de08c6e0363680717c0d8bc06c5d00db7816d9c0b6be01b5700da781ad340d68e09b450153f80a9cc034de02a6b0153380698c054be01a5b00d2b80a94c0349e02a4d0152580a9280549202a480152381a9180548a07a4400d2180a9040547a02a370151a80a5fc0f2fc02973014b90065bc032dc0296b014b500a59c0b2cc0196300cb100a57c0b2bc0195b00cad00655c032ac02953014a900653c0329c0294d00ca600a52c0529402949014a400a51c0d28c029450b0a200650c032840294100ca000a4dc0d26c029350243f80e1cc030de0386b0243380618c090be0185b00c2b80e14c0309e0484d01c2580e1240908e0484500c2180e10407076048370141780a0ac0504e028230140f80a07405036038190140b812054050260281100eb780758c038de07c6e00e31807188038be01c5e00e2e806dbc036c601b5f00dad806d5c036a601b4f00da6806d2c0369201b4700da2806d0c0368201a5f00d2e80695c134aa01a4f00d2680691c0f48a01a3f00d1b80a5bc052c60195f00cad80a564032ae0195300ca880653c0329a0194b00ca380a5140327e0193b00c9b8064cc05256029270243780e18c030be0185b00c2b80614c0309e0184d00c2580e1240308e0484500c218061040307e0183b00c1b8060cc07056048270140f80a06c0502e0281302eb78175b80bac607d6202e3781718c058be02c5e0162e816dbc0b6c605b5f00dae816d6c0b6b205b5700daa816d4c0b6a205b4f02da5816d1c0b68605a5f03d2e81695c0b4aa05a4f04d2681691c0b48a05a3f02d1b80a5bc052c60295f00cae80a55c052aa02953014a780a52c0529202947014a180a5040527e0293b0149b80a4cc05256029270243780e18c090be0485d01c2d80e164090ae0485501c2980e1440909e0384b0242380e10c0907e0383b0241b80e0cc07056048270140f80a06c0502e0281302eb781758c0b8de05c6302e2f81716c0b8ae05c5302db781edb80b6c605b6202daf806d780b6b605b5a02dab816d580b6a601b52015a780ad380569a05a5f02d2b81693c0b49a05a4704d228168fc0b47a05a3703d1a80a5bc052c60295f014ad80a55c052a60294f014a580a5240528e02943014a080a4fc0527a0293b0149b8064d405256029270243780e18c090be0385b0242b80e14c0909e0384b0242380e10c0907e0483d01c1d80e0e40906e0483501c1980e0c407056048270140f80a06c0502e0281300eb780758c038de01c6e00e3181f188038be01c5e00e2d807168038ae01c5600e29807148036de01b6300daf806d6c036ae01b5300da7806d380369a01a5f00d2b80693c0f49a01a4700d228068fc1147a01a3700d1a80a5bc052c60195f00cad80655c032a60194f014a680651c0328a0194300c9f8064ec032720193700c9980a4c405256029270243780e18c030be0185b00c2b80614c0309e0484d00c258061240308e0184500c2180e1040307e0183b00c1b8060cc07056048270140f80a06c0502e0281303eb781f58c0f8de07c630da2f86916c308ae1545304daf826d5c1369e09b470153780a98c054be02a5b0152b80a94c0549e02a4b0152380a90c0547a02a370151a80a5bc0f2dc02963014b100a57c282bc0295b014ad00a55c262ac02953014a900a53c2429c0294b014a500a51c2228c02943014a100a4dc0f26c029350243780e18c090be0385b0242b80e14c0909e0384b0242380e10c07076048370141780a0ac0504e028230140f80a07405036038190140b812054050260281102f3f8079cc0bafe07d7e00eb981f5c803ade06d6e036b68071fc0b8e601c6b0363501b1a4038ce08c6600e3181b184038ae08c560362a81adfc0d6fc06b7303db9006dbc036dc05b6b02db5016d9c0b6cc01b6300db1006d7c036bc06b5d00dae016d6c0b6b406b5902dac016d5c0b6ac06b5502daa006d4c036a406b5100da8016d3c0b69c01b4b00da5006d1c0368c05b4302da10069bc0b4ce01a5f0452e81695c114aa05a4f00d2380a8fc0547c02a3d034bf80a5cc032de0296b02cb380658c032be0695d014ad80a5640b2ae0695500ca980a5440b29e0194b00ca380a50c0525602929014908121fc070e60186f01c3581219c030c60185f0242e80e16c070b2048570242a80614c070a20484f00c2580611c070860483f0241e80e0ec07072048370241a80e0cc070620382b0241380a07c0703604817014098175bc03ac601c6f02e3180717c038b601c5700e29806d7c0b6ae05b4f00da381e9bc0f4dc07a6303d3100697c034bc05a5b02d2d01695c0b4ac01a5300d2901693c0b49c01a4b00d2500691c0348c05a4302d2100a8ec0547408a370151b01a5bc052c60195f014ad81655c032a60594f00ca580651c052860293b0149c81a4dc052620192b00c9481a49c05246019210243780e18c030be0385b0242b80614c0909e0184b00c2380e10c0707604837024178120b407056038290241381209407046038210140f80e06c0902e0281300f3f81f9f80fce607e7202ebf8075cc03ade06d6e036b68071fc0b8e601c6f0463701b1b4038be08c5e00e2d81b164038a606c520362881b1400d6fe06b7e035b981edc80d6de06b6e035b681adb0036d601b6a035b4806da0036ce01b66035b2806d900d6c608b62035b0838d80036be01b5e02dad816d680b6ae05b5600da9806d480b69e05b4e00da5806d280368e01b4602da1816d08114de08a6d00d33822994034be05a5702d2780691c0547e02a3e0151e81a5fc052e60696f034b68065ac052d201967034b280a58c052c20195f014ad81655c032a60594f00ca580651c052860292b0149480a484090fe03873024378121b4030d60386900c33812194070c60386100c2f80e16c090ae018530242780612c0308e038430241f8120f407076038390241b8120d4070660383101c1581209c0503e0381b0240b80a04c0bade05d6e02eb181f5880b8de05c6302e2f81716c0b8ae05c5302daf826d740b6ae05b5502da7816d1c0b4de07a6e02d318169880b4ae05a5602d2a81693c0b49c05a4b00d2501691c0348c05a4302d2100a8ec0547405a370151b01a5bc052c60595f034ae80a56c0b2ae05955014a981653c0529605947014a180a4ec0d26e0292b00c9481649c05246029210243780e18c090be0385b0242b80e14c0909e0384b0242380e10c0707604837024178120b407056038290241381209407046038210140f80e06c0902e0281300eb781f5b803ac601d6200e3780718c038be01c5b00e2b80714c036be01b5d00dab826d540369e01b4700d3781e9b8034c601a6200d2f806978034ba01a4f00d2700692c0349401a4700d2300690c0348401a3b00d1d0068dc0546c0696f014b180657c032ba0195b00cab81a554032a60194f00ca580651c032860293b0349b8064ac052520192700c91806484090de0386300c2f80616c030ae0185300c2780612c0308e0184301c1d8120dc0305e0182d00c1580e0a40304e0482500c118060840503e0381b0240b80a04c03ade01d6300e378071b8038c606c6200e2f80716c038ae01c5300daf806d5c0369e06b4d00da3806d14034de06a6e00d31806988034be01a5e00d2d806968034ae01a5600d298069480348e01a4600d228068ec0347401a370151b01a5bc052c60195f00cad80655c032a60194f034a680652c0328e0194500ca180a4ec0d26e0192b0149480649c03246019210243780e18c030be0185b00c2b80614c0309e0184b00c2380610c070760483700c178060b4030560382900c1381209403046018210140f80e06c0902e0281302eb781758c0b8de07c6e02e318171880b8be05c5b02e2b81714c0b6be05b5702da7816d340b68e09b4502d3781e9b80b4c605a6202d2f8069780b4b605a5a02d2b8169580b4a601a5202d278169380b49a02a3b0151d0168dc0546c0696f014b181657c052b605957014a981653c0b29a0294b02ca381a514052860293b0349b80a4ac03252059270149180a484090de038630242f80e16c090ae038530242780e12c0908e0384301c1d8120dc0905e0482d01c1580e0a40904e0482501c1180e0840503e0381b0240b80a04c0fade07d6303e3781b18c1e8be06c5b06a2b81b14c0d6de07b6e03db181ed880d6be07b5e03dad830d680d6ae07b5603da982cd480d69e07b4e035a5828d280d68e07b46035a1824d08134be09a570352782691c0547e02a3e0151e81a5bc052c60695f014ad81a55c052a60694f014a581a51c052860292b0149480a484090de038630242f80e16c090ae038530242780e12c0908e038430241f8120f407076038390241b8120d4070660383101c1581209c0503e0381b0240b80a04c038be01c5b00e2b806d7c036bc05b4f02da700657c052b60295700ca980a53c0329601947014a18064fc0327a0293b0149c80a4dc0326a029330149880617c070b60485700c2981213c030960184701c218120fc0907a0383b01c1c8120dc0906a0383301c1880a07c0503602817014098075bc0dada01d6b036b500759c11acc06d65046b20071bc118dc06c6d00e2f81b1780d8ba01a6f0153580a99c034c602a5f00d2d80695c054a601a4f0152680a92c0549202a470152280690c0548202a3500cb70165980b2bc0195600ca70065300d28c07144014970061bc070d60486700c3181217c030b60185701c2980613c0909a0384b01c2481211c0908a0184301c2080a0bc05056028270141180e0640902a01b5f00dad806d5c036a601b4f00da6806d2c0369201b4700da2806d0c036820195f00cad80a564032ae0195300ca880653c0329a0194b014a480651c0528a0194300ca08064fc032760193700c9980617c030b60185700c2980613c0309a0184b01c2480611c0908a0184300c208060fc030760183700c1980a07c050360281701409816d7c036ba05b5b02dac816d5c036aa05b5302da8816d3c0b69605b4702da180a57c032ba0295b014ac80a55c052aa02953014a880a53c0529602949014a380a50c052820293f0149d80a4dc052660485f0242e80e16c070b2048570242a80e14c070a20484f01c2581211c070860483f01c1d8120dc070660281f0140d80a05c0502605c5f02e2d81715c0b8a605b5f00daf016d6c0b6b405b5702dab016d4c036a40295f014ad80a55c052a60294f014a580a5240528e02943014a080a4fc0527a0293b0149c80a4dc0326a029330149881217c070b60485701c2981213c070960484701c218120fc0907a0383b01c1c8120dc0906a0383301c1880a07c05036028170140980717c038bc01c5b00e2d00715c038ac01c5300e29006d7c036b601b5700da980657c032b60195700ca980653c0529a0194b00ca480651c0328a01943014a08064fc032760193900c9b8064cc052620185f00c2d80615c030a60184f0242680612c030920184700c2280610c070820183f00c1d8060dc030660281f0140d80a05c0502608c5f0562d82315c0c8a602a5f0152d80a95c054a602a4f0152580a91c0548602a35028af0105580629c021460149701217c070b60485701c2981213c070960484701c2180a0bc05056028270141180e0640902b3045f9622dca515e488a72135f8e9adc68d5e2a6a71434f879a5c20d1de2686eb25f7212db5495d9c4a6ca24f63925b0091d78486b823f5a91dab88dd544669c15f4b0ada3855ce82a66f14f318a597851c942864213f1d89d8d84dc422661c12f0809582049c022460485f01c2d81215c070a60484f01c2581211c070860483f01c1d8120dc070660482f01c1581209c070460481f01c0d81205c070260003f 19 524287 7 127 11 2047 21 2097151
def cc_84_1 : Nat → List (Nat × Nat) := unpackCursorV4 0x928a51839e16b3bfce1790d2e4fa5b627b2ff95fec2ba6ad64a0aab3c52b569d7012f96a49ab44f887ade4ea569b63d33e5c604f0ad27123ed20b783636852348971a0c5d20c9840c9900032 0xeb781d6b03ace0758c0e3781c6b038ce0718c0e2f81c5b038ae0714c2db785b6b0b6ce16d8c0daf81b5b036ae06d4c0da781b4e0569a1e9bc3d3587a670f4c60697c0d2d81a57034a60693c0d2581a4703486168fc2d1d85a370b466065bc0cb581967032c60657c0cad81957032a60651c0ca3019450326e164d80c9aa61340325e064ac0c9381923090de0e1ac243383863030be0616c0c2b818530309e0612c0c23818430907e0e0ec241b838330905e0e0ac2413838230303e0606c0c0b8181303ade075ac0eb381d63038de1f1b80e3581c67038c6071880e2f81c5e038ba06dbc0db581b67036c606d7c0dae81b5b036ae06d540da981b4f0369a06d2c0da481b470368a06d0c0da087a6f114d62e99c3d3181a5f034b60695c0d2981a4f0349a0692c0d2389a4503486068fc0d1d81a37034660a5bc14b582967052c60657c0cad82959032ae0654c0ca88194f0329a0652c14a4819470528a0650c0ca08193f03276064dc0c998292f052560a49c14918486f070d61219c1c318185f030b60615c0c298184f0309a0612c1c24818470908a0610c0c208183f03076060dc0c198482f070561209c1c118281f050360a05c140981d6f0badc075ac0eb381d6303ac4071bc0e3581c67038c60717c0e2f01c5d036de06dac0db381b63036be06d740dad81b59036ae06d540da981b510369e06d340da581b470368a06d0c3d3788a6b154ce1e98c0d2f81a5d034b60695c2d2a81a530349e0692c0d2381a430347e068ec0d1b81a33052de0a5ac14b382963032be065740cad82959032ae0a5540ca9819510329e0652c14a48194703286065040c9f8193b0326e064cc14978292b0524e0a48c24378386b090ce0e18c0c2f8185d030b60e1640c2b84855030a6061440c278184b0308e0610c0c1f8183b0306e060cc24178382b0904e0e08c140f8281b0502e0a04c3eb781d6b82ace0758c0e3786c6b038ce1b18c0e2f81c5b038ae0714c3db788b6b806ce1ed8c0daf88b5b7e6ae06d4c35a781b4b0368e1ad0c153782a6b054ce0a98c0d2f82a5b054ae0694c1527be24e0549a0691c152282a43054840a8fc151d82a37054660a5bc3cb70196b052ce0658c14b10195f7a2bc0656c14ad01957782ac0654c14a9019470f28c0a514149f8193b052740a4dc4c9b019330525e0a4b814968486f070d61219c1c318185f070b61215c0c298484f030960611c1c218483f07076120dc1c198282f050560a09c14118181f0503a0a06c1c0c828170902a0604c140881d6f0badc075ac0eb381d6303ac4071bc0e3581c67038c60717c0e2e81c5b038ae071540e2981b6f036dc06dac0db381b630b6c406d5c0dab01b550369e06d380da581b4a0368e06d180da181b420f4de1e9ac3d3387a63034be0696c0d2b81a530349e0692c0d2381a430347e168f40d1d81a370346a068cc34b78296b0d2ce0a58c0caf8195d032b60655c2caa819530329e0652c0ca3819430327e164f40c9d819390326e064d40c99829310d25e0a4ac349382923090de0e1ac243383863030be0616c0c2b818530309e0612c0c23818430307e120f40c1d818390306e060d40c19838310905e0e0ac2413838230503e0e06c240b8281303ade1f5b80eb581d6703ac6075880e3781c6b038ce0718c0e2f81c5d038b60715c0e2a81c53036de1edb80db581b67036c606d880daf81b5e036ba06d3c0da701b4b0369406d1c0da301b43036841e9bc3d3587a670f4c60697c0d2d81a57034a60693c0d2581a4703486068fc0d1e81a3b0346e268d40d198696f052d61a59c14b18195f032ba0656c0cab86955032a60653c0ca58194703286064fc0c9e8193b05272064dc349a81933032621a4bc14958692705246121bc1c3584867070c60617c0c2d81857030a60613c0c258184703086060fc0c1e8183b07072060dc241a8183303062120bc1c1584827070460a07c1c0d8481705026075bc0eb181c6f038c60717c0e2d81c57038a61edbc3db707b630f6c406d7c0daf01b57036a606d480da781b4e0369606d280da381b460368606d080d2f81a5e034ae069480d2781a470347e068f40d1b81a350d2de0a58c0caf8195b032ae0654c0ca78194b0328e0650c2c9f8593d052760a4e42c9b85935052660a4c4149586927090de0e18c0c2f8185b030ae0614c0c278184b0308e0610c241f8483d070760e0e4241b84835070660e0c41c15848270503e0e06c240b828130bcfe179f82f3987e7203afe075cc0e3f81c7e038e61f1c80e3781c6e038da071b00e3585c6a038d2171a00e3381c66038ca071900e3185c62038c2e11800e2f81c5e038b6071680e2b81c56038a6071480dbf81b73036de06db40db581b69036ce06d940db181b61036be06d6c0dab81b530369e06d380da681a6f034dc069b40d2f81a5e034a40693c452681a470348a068fc0d1b8697f052e6165bc34b68296b052d21659c2cb282963052c20657c0cad81957032a60653c0ca70594d0327e064f80c9d8193903266064c814988292b0d24e121fc1c398486f090da0e1ac1c3484867090ca0e18c1c308185f030b60615c0c298184f0909a0612c0c24818470308a0610c1c208183f03076060dc0c198382b0904e0a07c1c0d84817050261f5bc0eb587d6703ac6071bc3e3707c6b038ce1f18c3e3101c5f0f8bc0716dd22d01c570f8ac0714dca2901b6f0d6d606d9c35b181b5f036b606d5c0da981b4f0569c0ad343d3787a6b0f4ce1e98c0d2f88a5b6e4ae0694c3d2789a4d034960691c3d2287a430d47e068ec0d1b86a330d2de0a5ac34b382963032be0a56c34ab819530d29e1e5383ca68693f0f27c064ec149c829334a2640a4c434978292b0d24e0a48c24378386b090ce0e18c0c2f8385b090ae0614c24278484d030960e1240c2384845070860e104241f8183b0306e0e0cc24178382b0904e0e08c140f8381b0902e0a04c0e2f81c5e038b6071680e2b81c56038a6071480daf81b5b036ae06d4c0da581b49032be0656c0cab8195303296065240c9f8193b0326e0617c0c2d81857030a61213c24268384b070921211c24228384307082060fc0c1d81837030660a07c140d8281705026079f40eb701c6f038d60719c0e3181c59038aa069bc0d3581a67034c60a964152a81a4f0549a0692c0d2501a470348c069140cb78196e032da065b00cb58196a032ce0659814b2a3164032c60658814ac82958052aad45500ca78194e0529a064bc0c970192d030de061ac0c3381863070b2121540c278184b0308e0610c14178282b0504e0a08c140f8281d050360e064140b84815050260a0440ebe81d71038fa071840e2f81c5b038ae0714c153e82a71034be0696c0d2b81a530349e0a9340d2581a4a0348e069180d2281a44052fa1e5f00caf8195e032b6065680cab81956032a6065480ca78194e0529a064bc0c970192d090fa0e1c40c2f8185b030ae0614c0c278184b0308e0610c14178282b0504e0a08c140f8281d050360e064140b84815050260a0442e2f85c5b0b8ae1714c6d2f81a5e0b4b6169682d2b85a561b4a6069482d2785a4e052be0a56c14ab829530529e0a52c14a38292b032521217c1c2d84857070a61213c1c258484707086120bc24168382b070521209c241283823070420a07c140d8281705026175bc2eb585d670bac606db82db305b5e036ac0a9bc153582a67054c60a97c152e82a5b054b40a95c3d2b02a55054720a8d414b78b96e052d60a5a814b38a966052c60a58814af8795e052ba0a5144ca202939052700a4d5909a0292f0525c0a4b424378386b090ce0e18c242f8385b090ae0e14c2422838390906a0a0bc141582827050460a07c140e8281b070320a05c240a82813050220717c0e2d81c57038a60697c0d2f01a5d034ae0a9540d2981a520349e0692c0d2381a43032ae0655814aa8194f0329c0652c0ca38194303284064bc0c970192d030be0616c0c2b818530309e0612c0c23818430505e0a0ac1413828230503e0a06c1c0c82817050260a0442e3785c6d1b8d6071a42e3385c651b8c6071842db185b610b69e16d2c2da385b43052c60658414a78294b0528e0a50c149f8293b0526e121bc24368386b070d21219c243283863070c21213c1c258484707086120fc1c1d84837070660a07c140d8281705026175f40eb881c7d608f8171c42e3805c5f0b8b61715c2e2982a7d0d4f80a9c4153802a5f054b60a95c152982a4f0549a0a92c152502a470f48c0a91414beaf17c052e20a5c014af8b95e052b60a56814ab8a956052a60a54814a78794e0529a0a4d44c9a0292f0525c0a4b4243e83871090be0e16c242b838530909e0e12c2423838430906a0a0bc141582827050460a07c140e8281b070320a05c240a8281305022079fc0f3981d7f0fafc075cc0eb901c7f038e6071bc0e3581c67038c60717c0e2e81c5b038b20715c0e2a81c53038a206da80db381b66036ae06d582daa81b4f0368e0a9fc153981a6f034d60699c0d3181a5f034ba0696c152c81a57054aa0694c0d2881a4f0549a0692c0d2501a470348c06914151d82a37052fe1e5f814b982972032de065b80cb58196a032ce065980cb181962032be065780cae8195c032b60656814ac82958032ae0655814aa8a954032a6065480ca8819500329e0653814a68293b052740a4dc4c9b0192f0325c064b4243f83873030de061ac0c3381863030be061740c2d83859030ae121540c29818510309e0612c0c238184307076120dc14178282b0504e0a08c140f8281d050360e064140b84815050260a0440e2f81c5b038ae0714c0d2f81a5e034b6069680d2b81a56034a6069480d2781a4e032be0656c0cab819530329e0652c0ca5019470328c064ac0c948185f030b60615c0c298184f030960611c0c218482f0905a0e0ac1c14848270904a0e08c1c108281f050360a05c140981d6f03ad60759c0eb181c66036dc06d780dab01a6f034d60699c0d3181a5f054ba0696c0d2d01a57034ac06954151c82a35032de065b80cb58196a032ce065980cb181962032be0657814ae82939052700a4d5609a0192f0325c064b40c378186b030ce0618c0c2f8185b030ae0614c1c1c848350505e0a0ac1413828230503e0a074140d838190502e12054140982811038be0716c0e2b81c530369c0697c0d2f01a5b034b40695c0d2b01a53034a40693c0d270195f032b60655c0ca98194f03296065280ca38194603256064a40c2f8185b030ae0614c0c278184b0308e0610c24178482d070560e0a4241384825070460e084140f8281b0502e0a04c0eb781d6b03ace0758c0e2f01b6e036cc06d580d3781a6b034ce0698c0d2f82a5d034b6069680d2b81a56034aa06950151c82a35032de065b80cb58196a032ce065980cb181962032be0657814ae8293554268064bc0c970192d030de061ac0c3381863030be0616c0c2b8185307072120d414178282b0504e0a08c140f8281d050360e064140b84815050260a0440eb781d630f8de1f1b83e3187c62038be071780e2d81c5a038ae071580e2981c52036de06d8c0daf81b5b036ae06d4c0da581b490368e06d0c0da081a5f034ae1693c2d2682a470548a068fc0d1f01a37034640a5bc14b18195f032b60655c0ca98194f0329a0652c0ca3819450327e064ec0c9d019370326c064cc149582927090de0e18c0c2f8185b030ae0614c24278484d070960e124242384845070860e1040c1f8183b0306e060cc1c15848270503e0a06c140b8281303cfe079cc0ebf81d7e03ae61f5c80eb781d6e03ad6075a80eb381d6603ac6075880e3f81c73038de071ac0e3381c63036de06d9c0daf81b5e0b6ba06d3c0da701b42054fe0a9cc0d3781a6b034ce0698c0d2f82a5d034b6069640d2b81a55034a60a9440d2782a4d03496069280d2381a460348a0a8ec151b8297f0f2fc0a5cc14b90196f032dc065ac0cb501967032cc0658c0cb10195f032bc0a57540ae0194f0329c0a534149d8293a0526e224d80c978192e0325a121fc1c398186f030d60619c0c318185f090ba0616c0c2c81857030aa0614c1c288184f030960611c0c218383b0906e0a0bc141582827050460a07c140e8281b070320a05c240a82813050220717c0e2d81c57038a61ad7c35ad86b570d6a606d3c0da581b47036860697c0d2d81a57034a60693c0d2581a4703486068fc0d1d81a37034661e57c3cad879570f2a60653c0ca581947032861a4fc349d869370d266064bc0c9581927032461217c1c2d84857070a60613c0c258184703086120fc1c1d8483707066060bc0c1581827030461207c1c0d8481707026075bc0eb581d6703ac6071bc0e3581c67038c60717c0e2d81c57038a606dbc0db585b6a036ce06d980db181b5f036bc06d6c0dab81b53036a406d3c0da701b4d0f4de1e9ac3d3387a63034be0696c0d2b81a530349e0692c0d2381a430347e068ec0d1c81a3703466168c414b78296b052ce0a58c0caf8195b032ae0654c0ca78194e0529a985300c9f8193e0527a0a4bc14958292705246121bc1c3584867070c60617c0c2d81857030a60613c0c258184703086060fc241e8183b0306e060d40c198482f070561209c1c118281f050360a05c140981d6f03ad6075a80eb385d6603ac6071bc2e3701c6b038ce0718c0e3101c5f038bc071740db781b6b036ce06d8c0daf81b5b036b206d5c0da981b510369e06d340da581b490368e06d140da181b410f4de2e9ac5d3387a63034be0696c0d2b81a530349e069340d2581a470b48a0690c0d1f81a3b0346e068cc14b78296b052ce0a58c0caf8195b052b20655c0ca9819510329e065340ca5829490328e0a5140ca1819410327e064ec0c9b819330525e0a4ac149382923090de0e1ac243383863030be0616c0c2b818530309e061340c25838490308e121140c21818410307e060ec0c1b818330905e0e0ac2413838230503e0a06c140b828130b8bc06d7c0dad81b57036a606d240caf8195b032ae0654c14a48193f03276064dc242f8385b090ae0e14c0c1f8183b0306e060cc140f8281b0502e0a04c2eb785d6e0bad61759c2eb187d620b8de071ad1a3505c670b8cc0718c162f82c5e058ba06dbc2db581b670b6c606d7c0dae85b5b0b6b206d5c0daa85b530b6a206d3c0da585b490368e06d0c2da087a6f154d62a99c3d3185a5f134ba1696c2d2b85a550b4a60693c2d2585a4703486168fc0d1d81a370b4660a5bc14b582967052c60657c0cae8195b032b20a55c14aa82953052a20653c14a5829490528e0650c14a08293f03276064dc14998292f052560a49c14918486f070d61219c1c318485f090ba0e16c1c2c84857090aa0e14c1c288184f070961211c0c218483f03076060dc1c198482f070561209c1c118281f050360a05c140985d6f68ad61759c3eb187c6f0b8d6cd19c2e3185c5f0b8b61715c2e2987b6f626d6b8d9c3db1ad35f0b6b616d5d59a985b4f526969cd1c2da182a6f054d60a99c153182a5f054b60a95c152982a4f0549a0a92c152502a474a48c0a914151f82a3b0546e0a8cc14b78796e052d60a59c14b182962052be9057814ad8295a052ae8855814a9829520529e1e53814a68293f052760a4e8149b89936052660a4bc14970292d090de0e1ac243383863090be0e16c242b838530909e0e12c2423838430907e0e0ec241b838330505e0a0ac1413828230503e0a074140d838190502e12054140982811036be06d6c0dab81b530369e06d340da581b490368e06d140da181b41032be065740cad819570d2aa0654c0ca78194d032960a5240ca38694503286065040c9f8193b0326e064cc0c2f8185b030ae0614c0c278184d030960e1240c238484503086061040c1f8183b0306e060cc140f8381b0902e0a04c2daf81b5d0b6b616d642dab81b550b6a616d442da785b4b0b68e16d0c2caf8695d052b60a5642cab85955052a6065442ca78694d052961651c2ca2829430b27e0a4ec2c9b82933090be121741c2d83859090ae121541c29838510909e0e12c2423838430907e0e0ec241b838330503e0e06c240b82813 19 524287 7 127 11 2047 19 524287
def cc_84_2 : Nat → List (Nat × Nat) := unpackCursorV4 0x911c31aaf22a95c34c183e56ffd01f456bd32b76288e68b9be1e3554e63ddab89e565d6aad3d500b492fa51f4d20a693b3c26999cb9739367923f5a404f471dd8acee0f8c2172fc1e6000079 0x2eb787d6e0fad61759c3eb187d620b8de1f1ac2e3387c63058be0b178162e87b6f0b6d61ed9c2db185b5fc46ba16d6c3dac85b570f6aa16d4f09a885b4f0b69616d1c2da187a6f0f4d61e99c3d3187a5f134ba1696c2d2b87a550f4a62a93c2d2585a4715486168fc551ddf2370b4661a5bc14b586967052c61a57c3caf0795d0d29e1e53814a582949052873850814a08593f052761a4dc14998692f052561a49c14918486f070d61219c1c318485f090ba0e16c1c2c84857090aa0e14c1c288484f070961211c1c218483f07076120dc1c198482f070561209c1c118281f070361205c140981d7d03ac2071f40e3881c5f038b60715c0e2982a7d054e20697c0d2e81a5b034b40695c0d2b02a550b4a80693c0d2581a4703486065f43cbe0195f032bc065740ca78194e03296065280ca38194603286065080c978292e0325a121f41c388185f030b60615c0c298184f030960611c0c218282f050560a09c14118181f0303a0606c1c0c818170902a0604c0c0881c5f038b60715c0e2981b5f036bc06d3c0da701b4b0369406d1c0da301b43036840657c0cad819570329e0652c0ca381943052760a4e40c2f8185b030ae0614c0c278184b0308e0610c241f8483d070760e0e4241b84835070660e0c4140f8281b0502e0a04c0ebe81d6f03ad60759c0eb181c6e038cc071780d3781a6d034d6069a80d3381a66054ca0697c0d2d81a57034a60a92415228196f032dc065b40caf8195e032ba165700cad8195a032ae065580caacc154032a6065480ca4819480328b705100c978292e0325a061bc0c3581867030c60617c0c2d81857030a60e12424228282f050560a09c14118181f0303a0606c1c0c818170902a0604c0c0881c5f038b60715c0e2981a5f034bc2e93c2d2701a4b034940691c0d230ba430b4840657c14ad829570529e0652c0ca382943052560a4a40c2f8385b090ae0614c24278184b0308e0e10c24178482d070560e0a4241384825070460e084140f8281b0502e0a04c0eb781d6b03ace0758c0db705b660b6bc06d580d3782a6d054d60a9a8153387a66054ca0a97c0d2d81a57054a60a8e4151a8196f0f2dc0a5b40caf9195e032b60a5680cab88956032a60a54814a28994403272064e0149ada1340525e0a4b814968186f070d61219c0c318485f030b60615c1c298484507072120d414178282b0504e0a08c0c0f8281d050360e064140b84815030260a0440e2f85c5b038ae1714c152f85a5e054ba0a95c152a82a53054a40a93c0d2581a47054860a55c2cab029550329e165380ca581947032860a50814978292e0525a1217c1c2d84857070a61213c0c2581847070860a0bc141582827050460607c140d838190502e0604c140881c63038c206dbc0db68bb6b0b6d206d9c0db28bb630b6c206d3c0da581b47036860a58c14b08194f052960a51c149f8193b0326e0a4cc24378486d070d60e1a4243384865070c60e1840c278384b0908e0610c241f8183b0306e0e0cc140f8281b0502e0a04c2ebed857c03ae2075c00e3e85c71038be0716c0e2b81c53054fa1e9f0153882a70034be0a974152d82a5a054ae1e958152a82a4f034960691c15218297dae2f8065c40cb80195f0f2bc0a5740ca78e94e032960a5280ca388946032860a508149a899340525e0a4b814968487d070e20617c1c2d84857030a61213c0c258184707086120d414178282b0504e0a08c0c0f8281d050360e064140b84815030260a0440e2f81c5b038ae0714c0daf01a5f034bc0693c0d2701a4b034940691c0d2301a43034840657c0cad8195a032ae065580ca78194b0328e0650c149582929030be0616c0c2b818530309e0612c0c23818430905e120b41c15838290904e120941c11838210503e0a06c140b8281303ade075ac0eb381d63038dc06d980daf01b56034de069b40d3581a6a034ce06998153285a64034be0696c0d2b81a53054720a8d40cb78196e032da0657c0caf0195b032b40655c0cab01953032a4064d6a89a0192f0525c064b40c378186b030ce0618c0c2f8185b030ae0614c1c1c848350505e0a0ac1413828230303e060740c0d838190302e120540c09818110fade1f5b83eb187d62038de0718c0e2d81c59038ae0714c0e2881b6f036c606d7c0dae81b5b036b206d5c0daa81b53036a206d3c0da581b47036860697c0d2e81a57034aa0693c0d2701a4703484068fc0d1b8296f052c60a57c14ae8295b052ae0a5540ca78194b032940651c0ca3019430327e064ec0c9b81933052560a49c243783863090be121741c2d83859090ae121541c29838510309e0612c0c23818430307e060ec0c1b81833070561209c140f8281b0502e0a04c2f3f85e7e0bce61f9c80ebf81d73038fe071cc0e3781c6d038d6071a40e3381c65038c6071840e2f81c5b038ae0714c0db781b6e036da06d7c0daf01b520369e06d1c153f82a73054de0a9b4153582a69054ce0a994153182a61034be069740d2d81a5a034ae06958152a81a4f034960691c0d2182a3b0546e065fc3cbf01973032e4065bc2cb70196da62d80657c0caf0195d0329e065380ca58194a0328e065180ca18194203276064e80c9b899360325e0a4b80c968487f070e6121bc24368386b070d21219c243283863070c20617c0c2d81857030a60613c0c2581847030860e0ec241b8282f050560a09c14118181f0303a0606c1c0c818170902a0604c0c0881e7f03ce6075fc0eb981d6f03ad60759c0eb185c7f0f8fc171cc2e3901c6f038dc071ac0e3501c67038cc0718c0e3101b6f036ce06d680dab81b560368e06d180da282a7f054e6069bc0d3681a6b034d40699c0d3302a65034be0696c0d2b81a530549e0a934152582a490548e0a914152182a41054760a8dc0cbf8797e032e6065c80cb78196e032da0657c0caf0195b032b40655c0cab01953032a40653c2ca70194d0b2980652c0ca501949032900651c2ca301945112880650c0ca10194103280064ec0c9d019371326c064bc14970192d090fe0e1cc0c378186b030ce0618c0c2f8185b030ae0614c24278484d070960e124242384845070860e1041c1d848370505e0a0ac1413828230303e060740c0d838190302e120540c0981811038be0716c0e2b81c53034be069780d2781a4e03496069280d2381a4603486069080caf8195b032b40655c0cab0194f032960651c0ca18292b052520617c0c2d81857030a60613c0c258184703086120bc24168382b070521209c241283823070420a07c140d8281705026075bc0eb581d6703ac6071580db701b66036bc069bc0d3681a6b034d40699c0d3302a65034be0696c0d2b81a53054720a8d40cb78196e032da0657c0caf0195b032b40655c0cab01953032a4064e40c9c01935a0268064bc14970192d030de061ac0c3381863030be0616c0c2b8185307072120d414178282b0504e0a08c0c0f8181d030360e0640c0b8481503026060442eb785d6b0bace1758c0e3781c6b038d40719c2e3301c63038be0b1780e2e81b6f036d606d9c0db181b5f036b606d5c0da981b4f0369606d240da381b43036821e9bc3d3587a670f4c61697c2d2d85a570b4a60693c0d2585a490348e0690c0d2081a3f03476068dc0d198196f032d60659c0cb18195f0b2bc0657494ae0194f0329c065340c9f8193b0326e064cc0c978192b0324e0648c24378386b090ce0e18c242f8385b090ae0e14c0c278184d030960611c2422818430307e060ec0c1b818330905e0e0ac2413838230303e0606c0c0b8181303ade075ac0eb381d63038de071ac2e3501c67038cc0718c0e2f81c5e038b60715c0e2981c52036de06db80db581b67036c616d880daf81b5e036b606d680dab81b56036a606d480da781b4e0369a1e9bc8d358ea670f4c60697c0d2d81a57034a60693c0d2581a4703486068fc2d1e81a3b0346e068d40d198296f052d60a59c14b18195f032b60655c0ca98194f03296065240ca38194305282064fc149e8193b03272064dc0c9a81933052620a4bc14958292705246121bc1c3584867070c60617c0c2d81857030a60613c0c258184703086060fc241e8183b03072060dc0c1a8183307062120bc1c1584827070460a07c140d82817050260717c0e2d81c57038a606d780da70195f032b60655c0ca78194b0328e0650c149c8185f030b60615c0c298184f030960611c0c218281f050360a05c140981d6f03ad60759c0eb181c6f038dc071ac0e3381c630f8c40717c0e2f01c5b038b40715c0e2b01c53038a406dbc0db5cc36a036ce06d980db181b5f036bc06d6c0dab81b53036a406d3c0da701b4d0f4de229ac453387a63034be0696c0d2b81a530349e229340d2581a470348a0690c0d1f81a3b0346e068cc14b78296b052ce0a58c0caf8195b032ae0654c0ca78294d03296065240ca381945032860a5040c9f8193b03272064dc0c99829310525e0a4ac149382923090de0e1ac243383863030be0616c0c2b818530309e121340c25818490308e061140c21838410307e060ec0c1b818330905e0e0ac2413838230503e0a06c140b828130fade075aeeab381d63038df6d1ac0e3387c63038be0716c0e2b81c530f6df64daeb1b387b63036bf50d6e91ab81b53a269e06d2c0da3cf343054de0a9ac153382a63034be0a974152d82a5a054af38958152a82a4f034960691c152182a3f054760a8dc15198296f0f2dc065ac14b381963052c40657c3caf0295d0329f345380ca58294a0328f2c5180ca1829420527e064ec149d029371326c064cc14978292e0525a121bc1c3584867070c60617c1c2d84857030a61213c0c258184707086120fc1c1d84837070660a0bc141582827050460607c140e8281b070320a05c240a8181305022075bc0eb581d6703ac6071bc2e3701c6b038ce0718c0e3101c5f038bc071740db781b6b036ce06d8c0daf81b5b036b206d5c0da981b510369e06d340da581b490368e06d140da181b410f4de1e9ac3d3387a63034be0696c0d2b81a530349e069340d2581a470b48a0690c0d1f81a3b0346e068cc34b78296b0d2ce0a58c0caf8195d032b60655c2caa819530329e065340ca5829490328e165140ca1819410327e064ec0c9b819330d25e0a4ac349382923090de0e1ac243383863030be0616c0c2b818530309e061340c25838490308e121140c21818410307e060ec0c1b818330905e0e0ac2413838230503e0e06c240b828130bade175b82eb585d670bac61f5882e3781c6b0b8ce0718c2e2f85c5e0b8ba06dbc2db581b670b6c606d7c0dae82b5b056b206d5c0daa85b53056a206d3c0da585b490368e06d0c2da087a6f0f4d61e99c3d3185a5f134ba1696c2d2b85a550b4a60693c2d2585a4703486168fc0d1d81a370b4661a5bc14b586967052c61657c34ae8295b052b20655c0caa81953032a20653c34a68294b0b28e165140ca18593f03276064dc14998692f052561a49c14918486f070d61219c1c318485f090ba0e16c1c2c84857090aa0e14c1c288184f070961211c0c218483f03076060dc1c198482f070561209c1c118281f070361205c140981e7f03ce6075fc3ebf01d7303ae4071fc0e3981c6f038d60719c0e3181c5f038ba0716c0e2c81c57038aa0714c0e2885b7f0f6fc16dcc2db901b6f036dc06dac0db501b67036cc06d8c0db101b5f036bc06d740dae01b5b036b416d642dac01b57036ac16d5455aa01b53036a406d440da801b4f0369c0ad340d3501a67034cc0695c0d2b05a550349e0691c2d1f85a3d0b46e268d434bf82973032de065ac0cb381963032be065740cad82959032ae1a5540ca98195103296065280ca4819470328c0650c14a0819370326c064d4149586927090fe0e1cc0c378186b030ce0618c0c2f8185d030b60e1640c2b84855030a6061440c278184b0308e0610c241f8483d070760e0e4241b84835070660e0c41c15848270503e0e06c240b82813038be071780e2d81c5a038ae071580e2981c52036be06d6c0dab81b530369606d240caf8195b032ae0654c0ca38194503276064e80c9b81936032660617c0c2d81857030a61213c24268384b070921211c24228384307082060fc0c1d81837030660a07c1c0d8481705026075bc0eb581d6703ac6071bc0e3701c6b038d40719c0e3301c63038c40717c0e2f02c5d036cc069b80d2f01a560b49c169302d2346244032de065ac0cb381963032b6065680cac81957032ac0654c14a8819470328c06514149486925030de061ac0c3381863030be0616c0c2b818530909e121341c25838490908e121141c21838410705212094140f8381b0902e0a04c0eb781d6b03ace0758c0e3781c6e038d6071a80e3381c66038c6071880e2f81c5e058ba06d780d3701a66034ac1691941220196f032d60659c0cb18195b032b4065640cab81956032a60a5440ca3819460328a0a4a434928186f030d60619c0c318185f030b60615c0c298484f0909a0e12c1c24848470908a0e10c1c20838290904a0a07c1c0d8481705026079fc0f3981d7f03afc075cc3eb901d6f03adc075ac0eb501d6703acc0758c0eb101c7f038e6071bc0e3581c67038c616dfc3dbf05b730b6e406dbc0db701b6b036d406d9c0db301b63036c406d7c0daf05b5d546b806d3c0da702b4d034de0699c0d2f81a5e0b4ba0693c0d2701a420b480168fc2d1e85a371146a1a5fc14b98196f032d60659c0cb18195f0d2ba0656c0cac81957032aa0654c14a88194b03294065240ca381946032860a5040c9b819360326a0a4ac34938487f070e6061bc0c3581867030c60617c242e8185b030b20615c0c2a81853070a20613c0c258184703086120fc241e8383b07072120dc241a83833070620e0ac24138281f070361205c140985d6f0fad61759c3eb187c6f0b8d61f19c2e3185c5f0b8b61715c2e2987b6f0f6dc16dac3db385b630f6c416d7e49af05b5b0f6b416d5e41ab05b530f6a40ad3c15a702b4d0f4de1e9ac3d3387a638e4be1696c2d2bc52530b49f1092e192385a430b47e1e8f43d1d87a371346a168cc34b78296b0d2ce0a58c34af8295b0b2ae0a54c14a5be14a052921a51c3ca302943052821a4dc3c9b079350d25e0a4ac349382923090de0e1ac243383863090be0e16c242b838530909e0e12c2423838430907e120f41c1d838390906e120d41c19838310905e0e0ac2413838230503e0e06c240b8281303afa075840e3e81c7c038e21b1c00e2f81c5b038ae0714c153e82a71034be0696c0d2b81a530349e06938152681a470348a0690c0d210197d0d2f8065c40cb80195f032bc0656c0cad01957032ac0654c0ca9019470328c065140c978292e0325a121f41c388185f030b60615c0c298184f030960611c0c218282f050560a09c14118181f0303a0606c1c0c818170902a0604c0c0885d7d03ae2071f40e3e05c710d8e00717c0e2d81c57038a60a9f4153881a5f054b60a95c0d2982a4f0f49c0a9340d2382a45054860a90814be8697c032e2065c00caf8b95e032b60a5680cab8a956032a60a5480ca3879460528a0a4bc14970292d090fa0e1c40c2f8385b090ae0614c24278184b0308e0e10c241a8282f050560a09c14118181f0503a0a06c1c0c828170902a0604c140885e7f0bcfc179cc3f3901d7f03ae6071fc0e3981c6f038da071ac0e3481c67038ca0718c0e3081c5f038b60715c0e2981b6f036dc06db40daf81b5e036a406d3c0da382a7f054e60a9bc153682a6b054d20a99c153282a63054c20697c0d2d81a57034a60693c0d2702a4d0348e069140d2181a42054760a8dc0cbf8797e032e6065c80cb78596e032da1a5b00cb58196a032d2065a00cb385966032ca165900cb181962032c2065800caf8195e032b6065680cab81956032a6065480ca3819460328a064ec0c9d019371126c064bc14970192d090fe0e1cc24378486d070d60e1a4243384865070c60e1840c2f8185b030ae0614c0c278184b0308e0610c1c1d848370505e0a0ac1413828230303e060740c0d838190302e120540c0981811 19 524287 7 127 11 2047 19 524287
def cc_84_3 : Nat → List (Nat × Nat) := unpackCursorV4 0x97523298a64855c5ce888e5707949faa93dfab76da4e3749b46533567603ceb90ed56b727ce14be76926ad1996a13bf3fc5679eb4e3e01a14d2c9f24c59c7ef38cd61131d2191a41e6780079 0x1c5d01c5501b5e01b5a01b5601b5201b4e01b4a01b4601b420193d0483d038390483503831038190281101d6d01d6501c6e01c6d01c5e02a7d01a4d02a4902a4501a410297d0196e0196a01966019620195e0195a01956019520194e0194d0194c0194a029490294801946029457e1440194201941019400184d03849048450184103829028210281d03819048150281101c5f01c5e10c5b05c5a10c5705c5601c5301c5201b5f01b5b01b5701b5302b4b02b490195f0295b029570195301947019450193b01937029330185f0385b04857018530484f0484d0384b03849048470484503843038410483f0183b01837038330281f0281b028170281301d6f09d6e01d6b0cd6a01d6709d6601d637d56201c6f01c6b01c6701c6306b5e06b4e02a7d01a6f02a6b02a6701a6302a5f07a5e02a5d07a5c01a5b02a5901a5702a5502a5302a5202a5102a5002a4f01a4b01a4702a430297d0196f0196e0296b0296a029670596601963019620295f0995e0295d7c15c0195b0195a029590195801957019560295501954029530295202951029500294f0594e0294d7714c0194b0194a01947019460294501944029430294202935099340186f0386b04867018630485f0485d0185b03859018570485503853038510484f0184b01847038430282f0282b038290282702823028210281f0281d0281b038190281704815028130281101c5f09c5e01c5d01b5f01b5d01b5b01b5701b5501b5301b4f01b4b01b4701b4301a5e01a4e0295b02959029570295302951019470193f0193b01937019330485f0485d0385b0485704855038530184f0184b01847018430183f0183b01837018330281f0281b028170281301d6f07d6e01d6301d6201c6f07c6e01c6301c6201c5f01c5e01c5d01b6f01b6301b5f01b5d01b5b01b5701b5501b5301b4f01b4d01b4b01b4901b4701b4501b4301b4101a5f01a5d01a577a25501a4f01a4d01a4709a4501a3f01a370296f029630195f0195b029590195701953019510194f0194d0194b01947029450193f0193b01937019330292b029270486f038630185f0185d0185b0185704855018530184f0184d0184b03849018470484501843018410183f0183b01837018330382b048270281f0281b028170281305d6f05d6e05d6307d6205c6f05c6e05c6307c6202c5f02c5e02c5d05b6f05b6305b5f01b5d05b5b05b5905b5701b5505b5305b5105b4f05b4d05b4b05b4705b4505b4305a5f09a5d05a5705a5505a4f0aa4d05a4705a4505a3f05a370296f029630295f0195d0295702955029530294f0294b029490294702943029410293f0293b02937029330292b029270486f038630485f0485d0385b03859048570485503853038510484f0484d0384b0484704845038430483f0383b04837038330382b048270281f0281b028170281301c5f01c5b05c5a01c5705c5601c5301b5f05b5b05b5701b5305b4f09b4e05b4d05a4e05a3e0195f0295b02957019530194b02949019470294302941019370185f0385b04857018530484f0484d0184b0184704845038430483f0383b04837038330281f0281b028170281305d6f05d6305c6f07c6e05c6305c6205c5f05c5b05c5a05c5705c5605c5305b6f07b6e05b6305b6205b5f01b5e05b5b05b5a05b5705b5605b5301b5202b4f02b4e02b4d05a5f05a5705a4f05a4d05a477724505a3f05a3d05a3709a350296f029630295f0295b02957029530294f0294b029490294702943029410293f0293d0293b02937019350292b029270486f038630485f0385b04857038530484f0484d0384b0484704845038430483f0483d0383b03839048370483503833038310382b048270281f0281b028170281301d6f01d6301c6f01c6e01c6307c6201c5f01c5e01c5b01c5a01c5701c5601c5301c5201b6f01b6e01b6307b6201b5f01b5b01b5a01b5701b5601b5301b4f01b4e01b4d01a5f01a5701a4f08a4d01a4701a4501a3f08a3d01a3701a350296f029630195f0195b01957019530194f0294d0194701945019430193f0193b019390193701933029310292b029270486f038630185f0185b01857018530184f0484d0184b01849018470184501843038410183f0483d0183b0183701835018330382b048270281f0281b028170281307d6f07d6307c6f07c638d45f8c45b8a457844538335f813577f34f7b34702a6f02a6d02a6502a5f02a5b02a5702a5302a4f02a4b02a4702a4302a3b02a370296f0796e0296d0295f7915e0295b0295a029577815602953029520294f7614e0294b0294a029477514602943029420293b0293a02937099360486f038630485f0385b04857038530484f0384b04847038430383b048370282f0282b038290282702823028210281f0281d0281b038190281704815028130281101d6f01d6b01d6701d6301c6f01c6b01c6701c6301c5f01c5e01c5b01c5701c5301c5201b6f01b6e01b6b01b6701b6305b6201b5f01b5e01b5b01b5a01b5701b5601b5301b5201b4f01b4e01b4d07a6f07a6b07a6707a6301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f05a3d01a3b01a3701a3501a330696f0296b06967029630195f0195b01957019530194f0594d0194b0194701945019430193f0593d0193b01939019370193501933029310692f0292b06927029230486f0386b04867038630185f0185b01857018530184f0184b01847018430183f0483d0183b01839018370183501833038310482f0382b04827038230281f0381b048170281301d6f01d6e01d6b01d6701d6306d6201c6f01c6b01c6701c6301c5f01c5d01c5b01c5901c5701c5501c5301c5101b6f01b6b01b6701b6301b5f01b5e01b5d01b4f01b4e01b4b01b4701b4301b4207a6f07a6b07a6707a6301a5f06a5d01a5b01a5701a5501a5301a4f01a4b01a4701a4301a3f01a3b01a3701a330696f0296b06967029630195f0695d0195b01959019570195501953029510194f0194b01947019430193f0693d0193b0193701935019330692f0292b06927029230486f0386b04867038630185f0485d0185b01859018570185501853038510184f0184b01847018430183f0183b01837018330482f0382b04827038230281f0381b048170281301d6f01d6e01d6d01c6f01c6b01c6701c6301c5f01c5d01c5b01c5901c5701c5501c5301c5101b6e01a6601a565325401a4e01a460196b0196a02969019670196601963019610195701956059550194f0194b019470194302929069250186f0186b01867018630185f0185d0185b03859018570485501853018510184f0184b018470184303829048250281f0381b048170281305e7f05e7e05e7307e7201d7f01d7301c7f07c7e01c7301c7201c6f05c6e01c6d5546c01c5f01c5e01c5d01b7f01b7301b6f01b6d01b6b01b6901b6701b6501b6301b6101b5f01b5b01b5701b5301b4f01b4d01b4b01b4901b4701b4501b4301b4101a6f01a6e01a6d01a5f01a5e01a5201a5001a4f01a4d01a4709a4501a3f01a370697f029730596f0696d0296b02969059670596502963029610195b0195a02959019570195601953019510194701946059450193f0193b01937019330292b069270487f038730486f0486d0386b03869048670486503863038610185f0185b01857018530184f0184d0184b03849018470484501843018410183f0183b01837018330382b048270281f0381b048170281307d6f01d6b07d6701d6307c6f07c6e01c6b07c6701c6307c6201c5f02c5e02c5d01b6f06b6b01b6706b6301b5f01b5b01b5701b5301b4f07b4d01b4b7334901b477234501b4307b4107a6f07a6b07a6707a6301a5f7125b7025701a5301a4f07a4d07a4b07a4709a4501a4306a3f01a3b01a3706a330696f0296b06967029630295b1295a02959069570795601953029510694707946079450693f0193b01937029330692f0292b06927029230486f0386b04867038630185f0385b04857018530184f0484d0384b03849048470484501843038410483f0183b01837038330482f0382b04827038230281f0381b048170281301e7d01d6e01c6f01c6b01c6701c6301c5901c5501a6f01a6e01a6d01a6702a6501a6301a6202a5902a5501a4f01a4b01a4701a4301967019660296502955079540194f0194e0194b0194a019470194601943019420192f0192e0192d0186f0186b018670186303859048550184f0184b01847018430282f0282b02827028230281f0281d0281b038190281704815028130281101c5f01c5b01c5701c5301a5f01a5d01a5702a5501a5301a4f01a4b01a4701a430195701956029550194f0194b0194a0194701946019430192f0192e0192d0185f0185b01857018530184f0184b01847018430282f0282b02827028230281f0281b0381902817028130281101c6f01c6d01b6f01b6d01b6b01b6901b6701b6501b6301b6101b4f01b4b01b4701b4301963019610194f0194e0194701943019420193f0193b01937019330486f0486d0386b03869048670486503863038610184f0184b01847018430183f0183b01837018330281f0281b028170281301d7d05d7c01d716d57001c7d01c6101c5f01c5b01c5701c5302a7d02a7101a5f01a5e01a5d01a5702a5501a5301a5201a4f01a4b01a4701a430297d6c17c02971029700195701956029550194f0194e0194b0194a019470194601943019420192f0192e0192d0487d038710185f0185b01857018530184f0184b01847018430282f0282b02827028230281f0281d0281b038190281704815028130281101c5f01c5b01c5701c5301a5f01a5d01a5702a5501a5301a4f01a4b01a4701a430195701956029550194f0194e0194b0194701943019420192f0192e0192d0185f0185b01857018530184f0184b01847018430282f0282b02827028230281f0281b0381902817028130281105c6f05c6d0fb6f01b6d05b6b05b690fb6701b6505b6305b6105b4f05b4b05b4705b4302963019610294f0794e0294702943029420293f0293b02937029330486f0486d0386b03869048670486503863038610484f0384b04847038430483f0383b04837038330281f0281b028170281305d7d05d7c01d716a57001c7d05c7105c5f05c5b05c5705c5302a7d02a7102a5f07a5e02a5d02a5702a5502a5302a5202a4f02a4b02a4702a430297d6917c02971029700295707956029550294f0e94e0294b0294a029470894602943029420292f0292e0292d0487d038710485f0385b04857038530484f0384b0484703843048350282f0282b02827028230281f0281d0281b038190281704815028130281101d6f01d6307c6f07c6e07c6307c6201c5f01c5e01c5b01c5a01c5701c5601c5301c5201b6f01b6301b5f01b5b01b5701b5301b4b01b4901b4701b4301b4101a5f01a5705a4f05a4d02a4702a4501a3f01a370296f029630195f0195b01957019530194f0194d0194b01949019470194501943019410193f0193b01937019330292b029270486f038630185f0185b01857018530484f0484d0384b03849048470484503843038410183f0183b01837018330382b048270281f0281b028170281301e7f01e7301d7f01d7e01d7307d7201d6f01d6e01d6b01d6a01d6701d6601d6301d6201c7f01c7301c6f01c6b01c6701c6301b6f01b6701b5f01b5e05b5d01b4f01b4e01b4202a7f02a7301a6f01a6e01a6d01a6702a6501a6301a6201a5f02a5d01a5b01a5901a5701a5501a5302a5101a4f01a4b01a4701a4302a3b02a370297f0797e02973029720196701966029650195f0195e0295d6715c0195b0195a019590195801957019560195501954019530195202951029500194f0194e0194b0194a019470194601943019420293b0293a02937099360192f0192e0192d0487f038730186f0186b01867018630185f0485d0185b01859018570185501853038510184f0184b01847018430383b048370282f0282b02827028230281f0281d0281b038190281704815028130281105d6f01d6b05d6701d6301c6f05c6b01c6705c6301c5f01c5b05c5a01c5705c5601c5305b6f07b6e05b6b05b6705b6305b6201b5f01b5e05b5b05b5a05b5705b5601b5301b5202b4f02b4e02b4d07a6f0aa6b0ea6707a6301a5f05a5b05a5701a5305a4f01a4b01a4705a4305a3f05a3d05a3b05a3709a3505a330296f0296b02967029630195f0295b02957019530294f0194b029490194702943029410293f0293d0293b02939019370193501933019310292f0292b02927029230486f0386b04867038630185f0385b04857018530484f0184b01847038430483f0483d0383b03839048370483503833038310482f0382b04827038230281f0281b028170281301d6f01d6b01d6701d6301c6f01c6e01c6b01c6701c6305c6201c5f01c5e01c5b01c5a01c5701c5601c5301c5201b6f01b6b01b6701b6301b5f01b5b01b5a01b5701b5601b5301b4f01b4e01b4d07a6f08a6b08a6707a6301a5f01a5b01a5701a5301a4f05a4d01a4b01a4701a4501a4301a3f01a3b01a3701a330296f0296b02967029630195f0195b01957019530194f0294d0194b01949019470194501943029410193f0193b019390193701933029310292f0292b02927029230486f0386b04867038630185f0185b01857018530184f0484d0184b01849018470184501843038410183f0183b01837018330482f0382b04827038230281f0281b028170281305d6f6e56b05d6707d6307c6f05c6b6b46705c6305c5f05c5b05c5705c5307b6f0ab6b6836707b630ab5f05b5b05b570ab5305b4f0ab4b6634705b4302a6f02a6b02a6702a6302a5f12a5e02a5d02a5702a5502a5302a5202a4f02a4b02a4702a4302a3f02a3b02a3702a330296f0796e0296b0296702963029620295707956029550294f6514e0294b0294a029476414602943029420293f0293b0293a0293709936029330292f0292e0292d0486f0386b04867038630485f0385b04857038530484f0384b04847038430483f0383b04837038330282f0282b02827028230281f0281d0281b038190281704815028130281101d6f01d6b01d6701d6301c6f05c6e01c6b01c6701c6301c6201c5f01c5e01c5b01c5a01c5701c5601c5301c5201b6f01b6e01b6b01b6701b6305b6201b5f01b5b01b5a01b5701b5601b5301b4701b4601b4507a6f07a6b07a6707a6301a5f01a5b01a5701a5301a4f01a4d01a4b01a4705a4501a4301a3f01a3b01a3701a330696f0296b06967029630195f0195b01957019530194f0194d0194b02949019470594501943019410193f0593d0193b0193701935019330692f0292b06927029230486f0386b04867038630185f0185b01857018530184f0184d0184b03849018470484501843018410183f0183b01837018330482f0382b04827038230281f0381b048170281305d6f01d6b05d6701d6301c6f07c6e05c6b01c6705c6305c6201c5f01c5b05c5a01c5705c5601c5305b6f07b6e05b6b05b6705b6305b6201b5f01b5e02b5b02b5a05b5702b5601b5301b5205b4f05b4e05b4d07a6f07a6b07a6707a6301a5f05a5b05a5701a5305a4f01a4b01a4705a4305a3f05a3d05a3b05a3709a3505a330696f0296b06967029630195f0295b05957019530594f0594d0194b0194706945029430193f0193d0193b01939059370693502933029310692f0292b06927029230486f0386b04867038630185f0385b04857018530484f0184b01847038430483f0483d0383b03839048370483503833038310482f0382b04827038230281f0381b048170281301d6f01d6301c6f01c6301c5f01c5b01c5701c5307b6f07b6e07b6307b6201b5f01b5e01b5b01b5a01b5701b5601b5301b5201b4f01b4e01b4701b4301b4201a5f01a5701a4f01a4e01a4701a4205a3f05a3d05a3705a350696f029630195f0195b01957019530194f0194b01947019430193f0193d0193b01939019370193501933019310292b069270486f038630185f0185b01857018530184f0184b01847018430483f0483d0383b03839048370483503833038310382b048270281f0381b048170281305e7f05e7e05e7307e7201d7f01d7301d6f02d6e01d6d01c7f01c7e01c7307c7201c6f01c6e01c6d01c6c01c6b05c6a01c6905c6801c6701c6601c6501c6401c6305c6201c616046001c5f01c5e01c5b01c5a01c5701c5601c5301c5201b7f01b7301b6f01b6d01b6b01b6901b6701b6501b6301b6101b5f01b5b01b5701b5305a6f09a6d05a6705a6501a5f01a5701a4f01a4e05a4d01a3f01a3e01a320697f029730196f0196e0196d0195f0195e0195b029590195301952019510194f0694d0194b01949019470194501943029410193f0193b01937019330292b069270487f038730486f0486d0386b03869048670486503863038610185f0185b01857018530184f0484d0184b01849018470184501843038410183f0183b01837018330382b048270281f0381b0481702813 19 524287 7 127 11 2047 20 1048575
def cc_84_4 : Nat → List (Nat × Nat) := unpackCursorV4 0x83c297da627904a7533d7163d6d6406b422672426522061e345ea345b6345823454141510314d0404ae2242f7f3b07f3634d2d88b287512582f2570125403200541847c122620f72b08f680622d00062 0x2e7d01d6d01d6901d6501d6101c6d01c6901c6501c6101c5d01c5506b6e01b6d06b6c01b6a01b6901b6806b6601b650fb6401b6201b6101b6001b5e01b5d01b4e029710193d0293906935019310486d0386904865038610183d038390483501831038190381102e7d06d6f05d6d01d6b01d6906d6705d6501d6301d6101c6f06c6e01c6d01c6c06c6b06c6a09c699f46801c6706c6601c6501c6406c6306c6206c6106c6001c5f09c5e01c5b16c5a01c5709c5601c539e45201b6f01b6d06b6b05b6901b6701b6506b6305b6101b5f01b5b01b5701b5306a4e06a3e029710195f0295b06957019530694f0694e0694d0694c0194b029490194706945029430994202941029400693f0193b01937029330486f0486d0386b03869048670486503863038610185f0385b04857018530484f0484d0184b03849018470484503843038410483f0183b01837038330281f0381b0381904817028130381102d6f02d6e02d6d07c6f07c6306c5f07c5d07c5ba945907c57a845506c5307c5107b6f06b6306b5f07b5d06b5ba735906b57a635506b5307b51a534f06b4ba334706b4306a5f07a5d07a5709a55a224fa024706a3f9d2370296902963029610694f0294b06947029430693f0293b06937029330292b069270486f038630485f0485d0385b03859048570485503853038510484f0384b04847038430483f0383b04837038330382b048270281f0381b0381904817028130381101d6f06d6e06d6d01c6b0bc6a06c6901c670bc6601c6306c6101c570bc560cc5502a7d01a6f02a6b02a6701a6301a5f02a5d02a5b02a5902a5702a5501a5302a5102a4f01a4b01a4702a430196e059660195e0195c05956059540594e019460292e0186f0386b04867018630185f0485d0385b03859048570485501853038510484f0184b01847038430282f0282b0282702823038190481501d6f0bd6e06d6d01d6706d6501d6306d6201c670cc6606c6501c5f06c5e06c5d02a7d01a6f02a6b02a6701a6302a5f01a5b01a5702a5302a4f02a4d01a4b02a4901a4702a4502a4302a410196e059660595e019560594e0594c01946019440292e0186f0386b04867018630485f0185b01857038530484f0484d0184b03849018470484503843038410282f0282b0282702823038190481507e7107e7001d6f06d6e06d6d01c6f0bc6e0bc6d01c5f0bc5e01c5b06c5901c530bc5206c519845002a7d02a6f02a6d01a6b02a6901a6702a6502a6302a6101a5f02a5b02a5701a5302a4f01a4b01a4702a430796e0796c01966019640195e059560594e019460292e0486f0486d0186b03869018670486503863038610185f0385b04857018530484f0184b01847038430282f0282b0282702823038190481507d6101c5f0cc5e06c5d02a6d02a5f01a5b01a5702a5301a4f02a4b02a4a02a4706a4601a430795e019560194e069460292e0485f0185b01857038530184f0384b04847018430282f0282b0282702823038190481501d6f06d6d01d6b06d6a01d670bd6606d659856401c6f0bc6e06c6d01c5f06c5e06c5d02a7d01a6f02a6b02a6701a6302a5f01a5b01a5702a5301a4f02a4d02a4b02a4a02a4902a4802a4706a4602a4507a4401a4302a410196e059660595e019560194e0194c06946079440292e0186f0386b04867018630485f0185b01857038530184f0484d0384b03849048470484501843038410282f0282b028270282303819048159b45f9a45b994579745302a6d02a5f02a5b02a5702a5302a4f02a4b02a4702a430795e079560794e079460292e0485f0385b04857038530484f0384b04847038430282f0282b0282702823038190481505b5f01b5d05b5b05b5905b5701b5505b5305b5105b4f05b4b05b4905b4705b4305b410595f0595d0295b01959059570695502953029510594f0694d0294b0594705945029430593f0293b05937029330485f0485d0385b03859048570485503853038510484f0384b04847038430483f0383b04837038330281f0381b048170281301b5f01b5b01b5901b5701b5301b5101b4f01b4d01b4b01b4901b4701b4501b4301b410195f0195d0195b0195706955019530194f0194d0194b02949019470694501943019410193f0193b01937019330185f0185b01857018530184f0184d0184b03849018470484501843018410183f0183b01837018330281f0381b048170281301c5f01c5d01c5b01c5901c5701c5501c5301c5101b4f01b4e01b4b01b4701b4301b420195f0195d0195b02959019570695501953019510194f0194b01947019430193f0693d0193b0193701935019330185f0185d0185b03859018570485501853018510184f0184b01847018430183f0183b01837018330281f0381b048170281305c5f05c5e05c5b05c5705c5305c5205b5f01b5e05b5b05b5a05b5705b5605b5301b520595f0295b05957029530594f0594d0294b0594706945029430593f0593d0293b01939059370693502933029310485f0385b04857038530484f0384b04847038430483f0483d0383b03839048370483503833038310281f0381b048170281305d7d01d7105c7d05c7c01c7101c7001c5f06c5e06c5d01b7d01b7c05b7105b7001b5b06b5a06b5901b570bb5601b5306b5101b470bb4606b450697d029610195f0295b05957019530194f0694d0294b02949059470694501943029410593f0193b01937029330487d0487c03871038700185f0385b04857018530184f0484d0384b03849048470484501843038410483f0183b01837038330281f0381b048170281305c5b05c5a01b5f0bb5e01b5b06b5901b5306b5206b5106b5001b4f01b4d029610195f0295b05957019530694f0694d0194b01949069470694502943019410593f0193b01937029330185f0385b04857018530484f0484d0384b03849048470484503843038410483f0183b01837038330281f0381b048170281301d7d01d7c0dd719057005c7d01c7101c5f06c5e06c5d01b7d05b7101b5f0bb5e06b5d01b4f0bb4e01b4b06b4901b4306b4206b4106b400697d029610695f0695d0195b02959019570695502953029510194f0294b05947019430593f0193b01937029330487d0487c03871038700485f0485d0185b03859018570485503853038510184f0384b04847018430483f0183b01837038330281f0381b04817028139546d944619336d923619134f06b4b8f34706b430796d029510694f0294b06947029430693f0293b06937029330486d0486c03861038600484f0384b04847038430483f0383b04837038330281f0381b048170281305e7f01e7305d7f07d7e01d7307d7201d6f06d6e06d6d01c7f05c7301c6b0cc6a06c6901c670cc6601c6306c6101c570cc560cc5501b6f05b6701b5f09b5d05b5709b5505b4f01b4702a7f02a7d02a7501a6f02a6b02a6701a6301a5f02a5d02a5b02a5902a5702a5501a5302a5102a4f01a4b01a4702a4302a3b02a370297f0697e0297d0196f0196e0296d0196c0296b0296a0296705966029650596401963019620195f0195e0295d0195c0295b0295a029590295802957059560295505954019530195202951019500294f0594e0194b0194a019470194602943029420293b0293a02937099360487f038730186f0386b04867018630185f0485d0385b03859048570485501853038510484f0184b01847038430383b048370282f0282b038290282702823028210281f0281d0281b038190281704815028130281105e7f01e7301d7f05d7301d6f0cd6e06d6d01d6706d6501d6306d6201c7f07c7e05c7306c7201c670cc6606c6501c5f06c5e06c5d01b6f05b6705b5f01b5705b4f06b4d01b4709b4502a7f02a7d02a7501a6f02a6b02a6701a6302a5f01a5b01a5702a5302a4f02a4d01a4b02a4901a4702a4502a4302a4102a3b02a370297f0697e0297d0196f0196e0296b0296a029670596601963019620295f0595e0295d0595c0195b0195a0195701956029550195402953029520294f0594e0294d0594c0194b0194a029490194801947019460294501944029430294202941029400293b0293a02937099360487f038730186f0386b04867018630485f0185b01857038530484f0484d0184b03849018470484503843038410383b048370282f0282b038290282702823028210281f0281d0281b038190281704815028130281107d6f06d6e06d6306d6205c6f01c6305c5f05c5d01c5b01c5902c5702c5501c5301c5101b6f05b6301b5f01b5d02b5b02b5901b5701b5502b5302b5101b4f01b4b01b4701b430ca5f09a5d0ca5709a5501a4f05a4705a3f01a370296f029630295f0195d0295b01957019550194f0294b02947019430293f0193b01937029330292b029270486f038630485f0485d0385b03859048570485503853038510184f0384b04847018430483f0183b01837038330382b048270281f0281b028170281301e7f07e7e0ce7907e7307e7207e7107e7005d7f01d7301d6f06d6e06d6d01c7f05c7301c6f0cc6e10c6d01c5f0cc5e01c5b06c5901c530cc5206c518945008b6f09b6d01b6709b6501b5f05b5705b4f01b4702a7f02a7d02a7502a6f07a6e02a6d07a6c01a6b02a6901a6702a6502a6302a6202a6102a6001a5f02a5b02a5701a5302a4f01a4b01a4702a4302a3b02a370297f0697e0297d0296f0c96e0296d8b16c0196b0196a029690196801967019660296501964029630296202961029600195f0195e0295d0195c0295b0295a0295705956029550595401953019520294f0594e0294d0594c0194b0194a0194701946029450194402943029420293b0293a02937099360487f038730486f0486d0186b03869018670486503863038610185f0385b04857018530484f0184b01847038430383b048370282f0282b038290282702823028210281f0281d0281b038190281704815028130281101d6f0cd6907d6307d6106c6f01c6301c5f0cc5e06c5d08b5f01b5701b4f06b4702a6f02a6d02a6502a5f06a5e01a5b01a5702a5302a5201a4f02a4b02a4701a4302a3b02a370296f0696e0296d0295f0c95e0195b0195a019570195602953029520194f0194e0294d0194c0294b0294a0294706946029458814401943019420293b0293a02937099360486f038630485f0185b01857038530184f0384b04847018430383b048370282f0282b038290282702823028210281f0281d0281b038190281704815028130281101c5f0cc5907c5307c5106b5f06b530cb4f0cb4e01b4b01b4702b4302b4208a4f01a4715a3f872370295f029530294f0694e0194b0194702943029420193f02937029330292b029270485f038530484f0184b01847038430483f0383b04837038330382b048270281f0281b038190281702813028110694c8756409a3c0694c05d6f01d6301c6f05c6301c5f06c5d01c5b06c5a01c570cc5606c558845401c5306b6f06b6e06b6306b6201b5f01b5e02b5b02b5a02b5702b5601b5301b5205b4f05b4e01b4b01b4a01b4701b4602b4302b4201a5f05a5705a4f01a4715a3f09a3d8623709a350296f029630195f0295b02957019530294f0194b01947029430193f0193d0293701935029330292b029270486f038630185f0385b04857018530484f0184b01847038430483f0483d0383b03839048370483503833038310382b048270281f0281b0381902817028130281105e7f01e7301d7f05d7301d6f06d6d01d6b06d6a01d670cd6606d658956406c7f07c7e01c7306c7201c6f10c6e06c6d01c5f06c5e06c5d01b6f05b6705b5f01b5701b4f06b4d06b4709b4502a7f02a7d02a7501a6f02a6b02a6701a6302a5f01a5b01a5702a5301a4f02a4d02a4b02a4902a4702a4501a4302a4102a3b02a370297f0697e0297d0196f0196e0296b0296a029670596601963019620295f0595e0195b0195a019570195602953029520194f0194e0294d0194c0294b0294a029490294802947069460294585144019430194202941019400293b0293a02937099360487f038730186f0386b04867018630485f0185b01857038530184f0484d0384b03849048470484501843038410383b048370282f0282b038290282702823028210281f0281d0281b038190281704815028130281101c6f01c6b01c6701c6301c5f09c5d01c5b06c5901c5710c5501c5306c5109b6609b5602a7d01a6f02a6b02a6701a6301a5f02a5d02a5b02a5902a5702a5501a5302a5102a4f01a4b01a4702a430297d0196f0196e0296d0196c0296b0296a0296705966029650a96401963019620195f0195e0295d0195c0295b0295a02959029580295709956029550a954019530195202951019500294f0594e0194b0194a019470194602943029420186f0386b04867018630185f0485d0385b03859048570485501853038510484f0184b01847038430282f0282b038290282702823028210281f0281d0281b038190281704815028130281102c5b01c590cb5f01b5d05b5b05b590cb5701b5505b5305b5105b4f05b4b05b4705b4302957029550294b02947029430293f0293b02937029330485f0485d0385b03859048570485503853038510484f0384b04847038430483f0383b04837038330281f0281b028170281305c6f10c6d05c6b06c6905c6709c6505c6306c6105c5f05c5b05c5705c5309b6e09b5e02a7d02a6f07a6e02a6d07a6c02a6b02a6902a6702a6502a6302a6202a6102a6002a5f02a5b02a5702a5302a4f02a4b02a4702a430297d0296f0996e0296d8216c0296b0296a029690296802967059660296505964029630296202961029600295f0195e0295d7a15c0295b0295a0295705956029550595402953019520294f0594e0294b0194a0294701946029430294202935099340486f0486d0386b03869048670486503863038610485f0385b04857038530484f0384b04847038430282f0282b038290282702823028210281f0281d0281b038190281704815028130281101d6e01d6d01c6901c6101c5502a7d01a5d02a5902a5501a510297d0196e0196d0196c0196a019660296505964019620195e0195d0195c0195a02959029580195602955059540195201951019500194e0194a01946019420185d03859048550185103829028210281d03819048150281105d6f05d6b05d6705d6305c6f8046e05c6b06c6a05c670cc6605c6306c6206b5606b4602a7d02a6f02a6b02a6702a6302a5f02a5b02a5702a5302a4f02a4d02a4b02a4902a4702a4502a4302a410297d0296f0196e0296b0296a029670596602963019620295f0595e0295d0595c0295b0195a0295701956029550895402953029520294f0594e0294d0594c0294b0294a029490294802947069460294508944029430294202941029400486f0386b04867038630485f0385b04857038530484f0484d0384b03849048470484503843038410282f0282b038290282702823028210281f0281d0281b0381902817048150281302811 20 1048575 8 255 11 2047 20 1048575
def cc_84_5 : Nat → List (Nat × Nat) := unpackCursorV4 0x83832806327e6207866073a4c6ee4c6a6486743264232622205f72b597605494e523264d54e4894c441484142d3e2323b032390203444c2f84c2ac4c2604c1e57b1964f116800b85e08d2b02b620002b 0x1c5f01c5e01c5b01c5701c5301c5201b5f01b5e01b5b01b5a01b5701b5601b5301b520195f0195b01957019530194f0194b01947019430193f0593d0193b01939019370193501933029310185f0185b01857018530184f0184b01847018430183f0483d0183b01839018370183501833038310481f0381b048170381301c5f01c5e01c5b01c5a01c5701c5601c5301c5201b5f01b5e01b5b01b5701b5301b520195f0195b01957019530194f0694d0194b01949019470194501943029410193f0193b01937019330185f0185b01857018530184f0484d0184b01849018470184501843038410183f0183b01837018330481f0381b048170381301c5f01c5b01c5701c53bf35609a5ebe24ebd2460195f0a95b0a957019534514f0194b019472b14302929079250185f0385b04857018530484f0184b018470384303829048250481f0381b048170381301e7d01d7d01c6f01c6b01c6701c6301c5f01c5d01c5b01c5a01c5905c5801c5701c5601c5508c5401c5301c5101b6f01b6e01b6b01b6a01b6701b6601b6301b6201b5f01b5e01b5d01b5c01b5b01b5a05b5905b5801b5701b5605b5508b5401b5301b5201b5101b5001a4601a360196f0196b01967019630195f0195d0195b02959019570695501953019510194f0194b01947019430593f0593d0593b02939059370793505933029310186f0186b01867018630185f0185d0185b03859018570485501853018510184f0184b01847018430483f0483d0383b03839048370483503833038310481f0381b048170381301d6f01d6301c6f05c6e01c6301c6201c5f01c5e01c5d01b6f01b6301b5f01b5b01b5901b5701b5301b5101b4f01b4d01b4b01b4701b4501a5f01a5d01a5705a5501a4f01a4d01a4705a4501a3f01a370696f801630195f0195b01957019530194f0194d0194b02949019470594501943019410193f0193b01937019330892b069270486f038630185f0185b01857018530184f0184d0184b03849018470484501843018410183f0183b01837018330382b048270481f0381b048170381305d6f05d6e05d6307d6205c6f01c6305c5f05c5e05c5d01b6f05b6301b5f01b5d01b5701b5505b5301b4f01b4b05b4901b4701b4305b4105a5f08a5d01a5701a5501a4f08a4d05a4705a4505a3f01a370696f0c9630595f0695d0595b02959059570595505953029510194f0594b05947019430593f0193b01937059330892b069270486f038630485f0485d0385b03859048570485503853038510184f0384b04847018430483f0183b01837038330382b048270481f0381b048170381305d6fbb56308c6f05c6305c5f05c5b05c5705c5308b6f07b6e05b6307b6205b5fba35e05b5b09b5a05b57b935605b5309b5209a5f05a5713a4a08a4709a4608a3709a3609a350696f7f1630695f0595b05957511530594f0694b06947059430593f0793d0693b02939069370793505933029310992b069270486f038630485f0385b04857038530484f0384b04847038430483f0483d0383b03839048370483503833038310382b048270481f0381b048170381301b5f01b5d01b5b01b5701b5501b5301b4f01b4d01b4b01b4901b4701b4501b4301b410195f0195b01957019530194f0194d0194b02949019470694501943019410193f0193b01937019330185f0185b01857018530184f0184d0184b03849018470484501843018410183f0183b01837018330481f0381b048170381301b5f01b5d01b5b01b5901b5701b5501b5301b5101b4f01b4d01b4b01b4701b4501b430195f0195d0195b02959019570595501953019510194f0194b01947019430193f0193b01937019330185f0185d0185b03859018570485501853018510184f0184b01847018430183f0183b01837018330481f0381b048170381301c5f01c5b01c5701c5313b4eb725eb625609a460195f0a95b0a957019534414f0194b019472914302929079250185f0385b04857018530484f0184b018470384303829048250481f0381b048170381301c5f01c5b01c5701b5f01b5e01b4f01b4e0195f0195b01957019530194f0194b01947019430793f0693d0793b02939079370693507933029310185f0185b01857018530184f0184b01847018430483f0483d0383b03839048370483503833038310481f0381b048170381301e7d01d7101c6f01c6e01c6d01c6c01c6b05c6a01c69b446801c6701c6601c6501c6401c6305c6201c6105c6001c5f01c5e01c5b01c5a01c5905c5801c5701c5601c5301c5201c51b145001b6f01b6d01b6b01b6901b6701b6501b6301b6101b5f01b5b01b5701b5301a4e01a3e0596f0596d0596b02969059670696505963029610195f0195b01957019530194f0794d0194b01949019470194501943029410193f0193b01937019330486f0486d0386b03869048670486503863038610185f0185b01857018530184f0484d0184b01849018470184501843038410183f0183b01837018330481f0381b048170381301d6f05d6e01d6301d6201c6f01c6301c5f01c5d01c5b01c5701c5501c5301b6f01b6e01b6305b6201b5701b5601b5501b4f01b4e01b4701b4301b4201a5f01a5d01a5705a5501a4f01a4701a3f05a3d01a3701a351696f0c9630195f0195b01957019530194f0194b01947019430193f0593d0193b01939019370193501933029310992b099270486f038630185f0185b01857018530184f0184b01847018430183f0483d0183b01839018370183501833038310382b048270481f0381b048170381301d6d01c5f01c5d01c5701c5501c5301b5705b5601b5501b4f0595f0595b05957059530194f0194b01947019430193f0193b01937019330485f0385b04857038530184f0184b01847018430183f0183b01837018330481f0381b048170381301d6fb156e01d6301d6201c6f01c6301c5f01c5d01c5b01c5701c5501c5301b6f07b6e01b6301b6201b5f01b5e01b5d01b4f01b4e01b4701b4301b4201a5f01a5d01a5709a5501a4f01a4701a3f01a3d01a3709a359e16f7d1630195f0195b01957019530194f0194b01947019430193f0193d0193b02939019370693501933019310992b099270486f038630185f0185b01857018530184f0184b01847018430183f0183d0183b03839018370483501833018310382b048270481f0381b048170381301d6f01d6e01d6b01d6a01d6701d6601d6301d6201c7d01c6f01c6b01c6701c6301b7d01b6f01b6e01b6b01b6a01b6701b6601b6301b6201a5e01a4e0196f0196b01967019630195f0695d0195b01959019570195501953029510194f0194b01947019430593f0593d0593b02939059370693505933029310186f0186b01867018630185f0485d0185b01859018570185501853038510184f0184b01847018430483f0483d0383b03839048370483503833038310481f0381b0481703813b356f01d6301c6f07c6e09c6307c6201c5f09c5e01c5bb245a01c5709c5601c53b045201b6faf36301b5f01b5b01b5701b5301a5f09a5708a4f09a4e09a4d08a3f09a3ead2329d16f7b1630195f6615b5f157019530994f0794d0194b02949019470794509943029414313f0193b01937271330992b099270486f038630185f0385b04857018530484f0484d0184b03849018470484503843038410483f0183b01837038330382b048270481f0381b048170381301c5f01c5b01c5701c5301b5f01b5b01b5a01b5701b5601b5301a4e13a4c01a3e0195f0195b01957019530194f0194b01947019430193f0593d0193b0193701935019330185f0185b01857018530184f0184b01847018430183f0183b018390183701833038310481f0381b048170381301b5f01b5b01b5901b5701b5301b5101b4f01b4d01b4b01b4901b4701b4501b4301b410195f0195b01957019530194f0194d0194b02949019470594501943019410193f0193b01937019330185f0185b01857018530184f0184d0184b03849018470484501843018410183f0183b01837018330481f0381b048170381301b5f01b5d05b5b05b5901b5701b5505b5305b5101b4f01b4b05b4901b4701b4305b410595f0695d0595b02959059570595505953029510194f0594b05947019430593f0193b01937059330485f0485d0385b03859048570485503853038510184f0384b04847018430483f0183b01837038330481f0381b048170381305c5f05c5b05c5705c53ad346ac25eab25609a4e0695f0595b059574f1530594f0694b069470594302929079250485f0385b04857038530484f0384b048470384303829048250481f0381b048170381301d6f07d6e01d6301d6201c6f02c6e01c6301c6201c5f01c5e01c5d01b6f01b6301b5f01b5b01b5701b5301b4f01b4d01b4b01b4901b4701b4501b4301b4101a5f01a5701a4f01a4d01a4709a4501a3f01a370696f029630195f0195d0195b0195706955019530194b029490194701943019410193f0193b01937019330292b069270486f038630185f0185b01857018530184f0184d0184b03849018470484501843018410183f0183b01837018330382b048270281f0381b048170281302d6b02d6905d6302d6105c6f05c6e05c6d05c5f05c5e05c5307c5205b6f01b6d05b6b05b6905b6701b6505b6305b6105b5f05b5305b4f05b4b05b4705b4305a6f09a6d05a6705a6505a4f05a4705a3f05a370596f0296b0296902963019610695f029530594f0694d0294b0594705945029430593f0293b05937029330292b069270486f0486d0386b03869048670486503863038610485f038530484f0384b04847038430483f0383b04837038330382b048270281f0381b048170281305d6f05d6305c6f07c6e05c6305c6205c5f05c5b05c5705c5305b6f02b6e02b6302b6205b5f01b5e05b5b05b5a05b5705b5605b5301b5205b4f05b4e05b4d05a5f05a5705a4f05a4705a3f05a3d05a3709a350696f029630595f0295b05957029530594f0594d0294b0594706945029430293b019390593702933029310292b069270486f038630485f0385b04857038530484f0384b04847038430483f0483d0383b03839048370483503833038310382b048270281f0381b048170281301d6b01d6901d6302d6101c6f01c6d01c6b01c6901c6701c6501c6301c6101c5f01c5301b6f01b6e01b6d01b5f01b5e01b5306b5201b4f01b4b01b4701b4301a6f06a6d01a6701a6501a4f01a4701a3f01a370196f0196b0196901963029610695f029530194f0194b01947019430193f0693d0193b0193701935019330292b069270186f0486d0186b01869018670186501863038610485f038530184f0184b01847018430183f0183b01837018330382b048270281f0381b048170281302e7f02e7e02e7d05d7f01d7305d6f05d6d01d6b01d6905d6705d6501d6301d6105c7f07c7e01c7307c7205c6f06c6e05c6d05c6c01c6b06c6a01c6901c6805c6706c6605c6505c6401c6306c6201c6101c6001c5f06c5e06c5d01b7f05b7301b6f01b6d05b6b05b6901b6701b6505b6305b6101b5b06b5a06b5901b570db5601b5306b5101b470db4606b4506a6f06a6d06a6709a6501a5f05a5701a4f09a4d05a4709a4505a3f01a370297902973029710195f0295b05957019530194f0694d0294b02949059470694501943029410593f0193b01937029330292b069270487f038730486f0486d0386b03869048670486503863038610185f0385b04857018530184f0484d0384b03849048470484501843038410483f0183b01837038330382b048270281f0381b0381904817028130381105d6f01d6307c6f02c6e02c6302c6201c5f01c5e05c5b05c5a05c5705c5601c5301c5201b6f05b6301b5f01b5b01b5701b5301b4f01b4d05b4b05b4901b4701b4505b4305b4101a5f05a570da4f09a4d0da4709a4505a3f01a370696f0296902963029610195f0295b05957019530194b019490694702943019410593f0193b01937029330292b069270486f038630185f0385b04857018530484f0484d0384b03849048470484503843038410483f0183b01837038330382b048270281f0381b048170281302e7f02e7e02e7d01d7f07d7e07d7307d7201d6f06d6e01d6d01d6c06d6b06d6a0dd69a456801d6706d6601d6501d6406d6306d6206d6106d6005c7f01c7305c6f05c6d01c6b01c6905c6705c6501c6301c6101c5f06c5e06c5d01b7f05b7301b6f01b6d05b6b05b6901b6701b6505b6305b6101b5f0db5e06b5d01b4f0db4e01b4b06b4901b4306b4206b4106b4006a6f06a6d06a6709a6508a5f09a5d01a5709a5501a4f05a4705a3f01a370297902973029710695f0695e0695d0695c0195b029590195706955029530d95202951029500194f0294b05947019430593f0193b01937029330292b069270487f038730486f0486d0386b03869048670486503863038610485f0485d0185b03859018570485503853038510184f0384b04847018430483f0183b01837038330382b048270281f0381b0381904817028130381102e7d06d6f05d6d01d6b01d6907d6705d6501d6301d6106c6f06c6e07c6d06c6c01c6b07c6a01c6901c6807c6707c6609c650ac6401c6306c6201c6101c6001b6f01b6d06b6b05b6901b6701b6506b6305b6101b5f01b5b01b5701b5301b4f09b4d01b4b06b4901b470db4501b4306b4109a5609a46029710195f0295b06957019530194f0694d0294b02949069470694501943029410693f0193b01937029330486f0486d0386b03869048670486503863038610185f0385b04857018530184f0484d0384b03849048470484501843038410483f0183b01837038330281f0381b0381904817028130381106c5f01c5e05b5f05b5b05b5705b530fb4f01b4d05b4b05b490fb4701b4505b4305b410695f0295b059570294b029490593f0293b06937029330485f0385b04857038530484f0484d0384b03849048470484503843038410483f0383b04837038330281f0381b048170281302e7d05d6f06d6e05d6d05d6c07d6b07d6a09d69a156805d6707d6605d6505d6406d6306d6207d6106d6005c6f05c6d07c6b01c6905c6705c6506c6301c6106b6f01b6d05b6b05b6906b6701b6505b6305b6105b5f0db5d05b5b06b5905b5709b5505b5306b5105b4f05b4b05b4705b4309a5e09a4e029710695f0795e0695d0695c0295b029590595706955029530995202951029500694f0294b05947029430593f0293b06937029330486f0486d0386b03869048670486503863038610485f0485d0385b03859048570485503853038510484f0384b04847038430483f0383b04837038330281f0381b0381904817028130381101c5f01c5b01c5701c5301b5f01b5e0db5b05b5a0db5705b5601b5301b5206b4f05b4e0195f0295b06957019530694f0194b019470193b019390185f0385b04857018530484f0184b01847038430483f0483d0383b03839048370483503833038310281f0381b0481702813 20 1048575 8 255 11 2047 20 1048575
def cc_84_6 : Nat → List (Nat × Nat) := unpackCursorV4 0xcf7033b05c8ac7033fc080af599b8e92ce2baab1e9a21a08c26240920d22e34850d1fa347a489b96064d316d4c52521303245cc9072038530cbab26f8074ce186983ace05b20002d 0x5d7d05d7c01d7101d7001c7d05c7101c5f0ac5e08c5d01c5708c5501c530ac5201b7d01b7c05b7105b7001b5708b5608b5501b4f0bb4e0ab4d0697d029710195f0595b05957019530594f0194b01947059430593f0793d0193b02939019370793505933029310487d038710185f0385b04857018530484f0184b01847038430483f0483d0183b0383901837048350383303831048250481f0381b0481703813da46002a5807a540695c0793405c5b05c5a01b5f08b5e01b5b08b5901b530ab5208b51d935001b4f01b4d0195f0595b05957019530794f0694d1794b029490794706945dd143029410593f0193b01937059330185f0385b04857018530484f0484d0384b03849048470484503843038410483f0183b0183703833048250481f0381b048170381301d7d01d7c08d71dc57005c7d01c7101c5f08c5e0ac5d01b7d05b7101b5f08b5e08b5d01b4f08b4e01b4b08b4901b430ab4208b41d83400697d029710795f0795d0195b02959019570795508953029510194f0594b05947019430593f0193b01937059330487d038710485f0485d0185b03859018570485503853038510184f0384b04847018430483f0183b0183703833048250481f0381b048170381306a54079340bb5d0bb4f0bb4d09a360694f1794b06947da1430193f0693b06937019330484f0384b04847038430183f0383b0483701833048250481f0381b048170381301c6d01c6c08c61d94600bb6d01b610bb5d01b4f08b4e0bb4d09a360696d029610694f0194b01947089430193f0693b06937019330486d038610484f0184b01847038430183f0383b0483701833048250481f0381b048170381301c5301c5105b5305b5101b4f01b4b01b470695f0695d0b95b0295906957069550b953029510194f0594b05947019430593f0193b01937059330485f0485d0385b03859048570485503853038510184f0384b04847018430483f0183b01837038330481f0381b048170381305d7d05d7c01d7101d7001c7d01c7c05c7105c7001c5f08c5d01c5b0ac5a01c570ac5608c55d84540bb7dd737c01b7101b700bb6d07b6c01b5f08b5e08b5d01b4f0ab4e0ab4d09a3609a340697d029710195f0595b05957019530594f0194b01947059430193f0793d0693b02939069370793501933029310487d038710185f0385b04857018530484f0184b01847038430183f0483d0383b0383904837048350183303831048250481f0381b0481703813e346de2461e136de0361df34fde34bdb347d63430796d029610794f6814b07947561430793f4013b079372e1330486d038610484f0384b04847038430483f0383b0483703833048250481f0381b048170381301c5f08c5d01c5b0ac5a01c5708c5608c5508c5401b5f01b5e05b4f05b4e0195f0595b05957019530594f0194b01947059430693f0693d0793b02939069370693507933029310185f0385b04857018530484f0184b01847038430483f0483d0383b03839048370483503833038310481f0381b048170381301d6f08d6d01d6b0ad6a01d6708d6608d6508d6401c6f08c6e08c6d01c5f08c5e0ac5d01a6e05a6605a5e01a5601a4e01a4c11a46d42440196f0596b05967019630595f0195b01957059530194f0794d0694b029490694707945019430294102929069250186f0386b04867018630485f0185b01857038530184f0484d0384b0384904847048450184303841038290382804825048240481f0381b048170381301b5f01b5d01b5b01b5701b5501b5301b4f01b4d01b4b01b4901b4701b4501b4301b410195f0195d0195b0195707955019530194f0194d0194b02949019470694501943019410193f0193b01937019330185f0185b01857018530184f0184d0184b03849018470484501843018410183f0183b01837018330481f0381b048170381305b5f01b5d05b5b05b5905b5701b5505b5305b5105b4f05b4d05b4b05b4705b4505b430595f0695d0595b02959059570595505953029510594f0794d0594b0594705945059430593f0593b05937059330485f0485d0385b03859048570485503853038510484f0384b04847038430483f0383b04837038330481f0381b048170381305c5f05c5b05c5a05c5705c5605c5305b5f01b5e05b5b05b5a05b5705b5605b5301b520595f0595b05957059530594f0594d0594b0594706945059430593f0593d0593b02939059370693505933029310485f0385b04857038530484f0384b04847038430483f0483d0383b03839048370483503833038310481f0381b048170381301c5f01c5e01c5b01c5a01c5701c5601c5301c5201b5f01b5b01b5a01b5701b5601b530195f0195b01957019530194f0694d0194b01949019470194501943029410193f0793d0193b0193701935019330185f0185b01857018530184f0484d0184b01849018470184501843038410183f0183b01837018330481f0381b048170381308c5f0ac5b08c57d3453d225ed1256d024ecf2460795f0795b07957079530794f0794b079470794302929079250485f0385b04857038530484f0384b0484703843038290382804825048240481f0381b048170381301c7d01c6f01c6b01c6701c6301c5f01c5d01c5b01c5901c5701c5501c5301c5101b7d01b6f01b6e01b6d01b6c01b6b01b6a01b6701b6605b650ab6401b6301b6201b5f01b5e01b5d01b5c01b5b01b5a05b5905b5801b5701b5605b550ab5401b5301b5201b5101b5001a6601a560196f0196b01967019630195f0195d0195b02959019570695501953019510194f0194b01947019430593f0593d0593b02939059370793505933029310186f0186b01867018630185f0185d0185b03859018570485501853018510184f0184b01847018430483f0483d0383b03839048370483503833038310481f0381b048170381301d6f01d6301c6f01c6301c5f01c5e01c5b01c5701c5301c5201b6f01b6e01b6305b6201b5f01b5b01b5a01b5701b5601b4f01b4e01b4d01a5f01a5701a4f05a4d01a4701a4501a3f05a3d01a3701a350696f069630195f0195b01957019530194f0194b01947019430193f0593d0193b01939019370193501933029310692b069270486f038630185f0185b01857018530184f0184b01847018430183f0483d0183b01839018370183501833038310382b048270481f0381b048170381301d6f01d6e01d6307d6201c6f01c6301c5f01c5d01c5701c5501c5301b6f01b6301b5f01b5e01b5d01b4f01b4e01b4b01b4701b4301b4201a5f08a5d01a5701a5501a4f01a4701a3f08a3d01a3701a350d96f109630195f0695d0195b01959019570195501953029510194f0194b01947019430193f0193b01937019330892b089270486f038630185f0485d0185b01859018570185501853038510184f0184b01847018430183f0183b01837018330382b048270481f0381b04817038130ad6f01d6309c6f07c6e01c6307c6201b6fcd36301b5f01b5b01b5701b5301b4f09b4d01b4bcc34901b47cb34501b4309b4114a5a09a5709a5609a4709a4609a4509a3f01a37a216f831630195f0a95b0a957019530194f0794d0994b02949099470794501943029414713f0193b019372d1330992b099270486f038630185f0385b04857018530184f0484d0384b03849048470484501843038410483f0183b01837038330382b048270481f0381b048170381301c5f01c5b05c5a01c5705c5601c5301b5f01b5e05b5b05b5a05b5705b5601b5301b520195f0595b05957019530594f0194b01947059430593f0593d0593b02939059370693505933029310185f0385b04857018530484f0184b01847038430483f0483d0383b03839048370483503833038310481f0381b048170381301c5f01c5e01c5b01c5a01c5701c5601c5301c5201b5f01b5b01b5a01b5701b5601b530195f0195b01957019530194f0594d0194b01949019470194501943029410193f0193b01937019330185f0185b01857018530184f0484d0184b01849018470184501843038410183f0183b01837018330481f0381b048170381305c5f05c5b05c5705c5314b5e09a56c924ec82467115f0595b05957541530594f0894b089470594302929079250485f0385b04857038530484f0384b048470384303829048250481f0381b048170381301d7d01c7d01b6f01b6d01b6b01b6901b6701b6501b6301b6101b5f01b5b01b5701b5301b4f01b4d01b4b01b4901b4701b4501b4301b4101a6e01a5e0596f0796d0596b02969059670596505963029610195f0195b01957019530194f0194d0194b02949019470794501943019410193f0193b01937019330486f0486d0386b03869048670486503863038610185f0185b01857018530184f0184d0184b03849018470484501843018410183f0183b01837018330481f0381b048170381301c5f01c5e01b5f01b5b01b5701b4b01b490195f0195b01957019530794f0694d0794b02949079470694507943029410193f0193b01937019330185f0185b01857018530484f0484d0384b03849048470484503843038410183f0183b01837018330481f0381b048170381301e7d01d6f01d6e01d6d01d6c01d6b01d6a05d69c556801d6701d6605d6505d6401d6301d6201d6101d6001c6f01c6d01c6b01c6901c6701c6501c6301c6101b7101b5f01b5e01b5d01b5c01b5b01b5901b5701b5501b5305b5201b51c235001b4f01b4b01b4701b4301a5e01a4e0196f0196d0196b02969019670796501963019610595f0695d0595b02959059570595505953029510194f0194b01947019430193f0193b01937019330186f0186d0186b03869018670486501863018610485f0485d0385b03859048570485503853038510184f0184b01847018430183f0183b01837018330481f0381b048170381301d6f01d6301c6f05c6e01c6301c6201c5f01c5e01c5701c5301c5201b6f01b6e01b6305b6201b5f01b5b01b5a01b5701b5601b5301b4701b4601b4501a5f01a5701a4f01a4d01a4705a4501a3f05a3d01a3701a350d96f109630195f0195b01957019530194f0194d0194b02949019470594501943019410193f0193b01937019330892b089270486f038630185f0185b01857018530184f0184d0184b03849018470484501843018410183f0183b01837018330382b048270481f0381b048170381301d6d01c5f01c5d01c5701c5501c5301b5701b5605b5501b4f0195f0195b01957019530194f0194b01947019430593f0593b05937059330185f0185b01857018530184f0184b01847018430483f0383b04837038330481f0381b048170381305d6f01d6301c6fc246e05c6305c6201c5f01c5b05c5a01c5705c5601c5305b6f07b6e05b6305b6201b5f01b5e05b5701b5301b5205b4f05b4e05b4d01a5f05a5705a4f05a4d01a4709a4501a3f01a3d05a3709a350696f069630195f0595b05957019530594f0194b01947059430593f0593d0593b02939059370693505933029310692b069270486f038630185f0385b04857018530484f0184b01847038430483f0483d0383b03839048370483503833038310382b048270481f0381b048170381305d6f07d6e09d6307d6205c6fc6463c436f05b6305b5fc335d05b5b09b5905b5709b5505b53c135105b4f05b4b05b4705b4309a5f09a5e09a5d09a4f09a4ebf24205a3f09a37a016f811630995f0795d0595b02959059570795509953029517014f0594b05947521430593f3f13b37137059330992b099270486f038630485f0485d0385b03859048570485503853038510484f0384b04847038430483f0383b04837038330382b048270481f0381b048170381301b5f01b5b01b5701b5301b4f01b4d01b4b01b4701b4501b4305a5e14a5c01a4e0595f0595b05957059530194f0194d0194b0194705945019430193f0193b01937019330485f0385b04857038530184f0184b038490184701843018410183f0183b01837018330481f0381b0481703813 18 262143 7 127 11 2047 20 1048575
def cc_84_7 : Nat → List (Nat × Nat) := unpackCursorV4 0xf88efbdc9e0dd77124d450320e1bdf4ac761aa6ee80d2983023bca805d5d0626c6f5933d5cd0162a150b0132a0474acfcc1392c0ccb02d2c09cb0230847136158d83b36080d80040 0x717e068b601c5781229bf4d7c036b6fb35700da9806d3e0269d0034d7692f82296db04ae08a530452780692c0348e08a4300d1f8228ede646e01a33034afa6056c0d2ae89153034a780652c0328eff14300c9f81a4ec0d26e019330349785c4ac0d24e089230242f80e16c090ae038530242780612c0308e0384300c1f80e0ec0906e018330241780e0ac0904e038230240f80e06c0902e0381300eb78075b803ada01c6f00e3480718c038c201c5f00e2e80716c038b201c5300e28806da4036c601b6100da7806d380369a07a6d05d3281e97c0f4ba07a5704d2a80693c0348e01a3f00d1b81a5bc0d2c60695f034ae81a56c052b206957034aa81a54c052a20194f00ca580651c032860193f00c9d8064dc032660692b034938121bc070c60485f0242e80e16c070b2048570242a80e14c070a20184f00c2580611c030860183f00c1d8060dc030660382b0241381207c070360481701c098079fc03cfc01e7d00ebf8075e403ae601d7100eb78075b403ad601d6900eb1807584038fe01c7900e398071c4038de01c6d00e358071a4038c601c6100e2f807174038b601c5a00e2b807158038aafd45400dbc806de0036e601b7200db8806dc0036be01b5e00dae806d3c0369c01b4d03d3e82e9d40f4de07a6d03d33826994034be01a5700d2780691c0347e01a3d00d1b8628d40d2fe06973034b781a5b40d2d602969034b381a5940d2c60296100caf80656c032ae0195300ca780652c0328e0194300c9f8064f4032760693900c9b81a4d403266019310349581a49c090fe03873024378121b4070d60386902433812194070c60386100c2f80616c030ae0185300c2780612c0308e0184300c1f8060f4030760383900c1b8120d4030660183101c1581209c0903e0381b0240b80e04c038da01c6100e28806db4036a201b4f00da7006d340d2da0296100ca780652c0328e0194300c9f8064f403276019370349a8064cc090da0386100c2780612c0308e0184300c1f8060f403076018370241a8060cc0903e0381b0240b80e04c03afa01d7100eb08071f4038e201c6100e2f807174038b601c5a00e2b807158038aafb45400dbe81edf0036c201b6000daf806d78036ba01b4f00da7006d340d2fa0297100caf80656c032ae0195300ca780652c0328e0194300c9f8064f4032760693900c9b81a4d403266019310243e80e1c4030be0185b00c2b80614c0309e0184b00c2380610c0307e0183d00c1d80e0e40306e0483500c198060c40903e0381b0240b80e04c03ade01d6b00eb380758c038de05c6e00e3580719c038c601c6200e2f807178038ba01b6f00db5806d9c036c601b5b00dad006d64036ae01b5600da9806d440368e01b4600da28229bc114d608a670453180697c034b601a5700d2980693c0349a01a4b00d238169140348601a3f00d1d8068dc034660696f05cb581a59c212c60195f00cad80655c032a60194f00ca680652c052920194702ca280650c032820193f00c9d8064dc032660692f0449581a49c112460486f01c3581219c070c60185f00c2d80615c030a60184f00c2680612c07092018470242280610c030820183f00c1d8060dc030660482f01c1581209c070460481f01c0d81205c0702601d6f00eb580759c03ac601c6f00e3580719c038c601c5700e2b007155ec8a801b6f00db5806d9c036c601b5700dab006d540369e01b4e00da68229bc114d608a670453180697c034b601a5700d2980693c0349601a4700d218068fc0347601a3700d1981a5bc0d2d606967034b180657c032b60195700ca980653c032960194700ca18064fc032760193700c9981a4bc0d25606927034918121bc070d60486701c3180617c030b60185700c2980613c030960184700c218060fc030760183700c198120bc070560482701c1181207c070360481701c098075bc03ad601d6700eb18071bc038d601c6700e3180717c038bc01c5d00e2b807154038a601c5200db7806db8036d601b6700db1816d88036ae01b5600daa806d3c0369c01b4d055378229ac154ce08a6300d2f80696c034ae01a5300d2780692c0348e01a4300d1f8168f40347601a3700d1a8068cc0d2de0696b034b381a58c032be0195b00cab80654c0329e0194b00ca380650c0327e0593d00c9d8064e40326e0193500c9980a4c40d25e0692b0349381a48c090de0386b0243380e18c030be0185b00c2b80614c0309e0184b00c2380610c0307e0483d00c1d8060e40306e0183500c1980e0c40905e0382b0241380e08c0903e0381b0240b80e04c038be01c5b00e2b80714c036be01b5b00dab806d4c0369e01b4e00da682297c114b608a570452980693c0349601a4700d218068fc0347601a3700d1981a57c0d2b606957034a980653c032960194700ca18064fc032760193700c9981a4bc0d256069270349181217c070b60485701c2980613c030960184700c218060fc030760183700c198120bc070560482701c1181207c070360481701c098075bc03ad601d6700eb18071bc038d601c6700e3180715c038ac01c557b22a006dbc036d601b6700db1806d7c036bc01b5d00da3806d180368a0aa6f0553582a99c154c601a5f00d2d80695c034a601a4f00d2580691c0348601a3f00d1d8068dc034660696f034b581a59c0d2c60195f00cad80655c032a60194f00ca580651c032860193f00c9d8064dc032660692f0349581a49c0d2460486f01c3581219c070c60185f00c2d80615c030a60184f00c2580611c030860183f00c1d8060dc030660482f01c1581209c070460481f01c0d81205c0702601d6f00eb68075ac03ad401d6700eb300759411ac801c6f00e370071b4038be01c5e00e2e806db8036bc01b4e00da60069b8034cc01a5e00d2b006918134880196f00cb580659c032c60195f00cad80655c032a60194f00ca680652c0d29201947034a280650c0328202929034928061bc030d60186700c3180617c030b60185700c2980613c0309a0184b01c2480611c0908a0184300c2080e0a40904a0481f01c0d81205c0702601d6f00eb18271bc0f8dc09c6303e3100717c038bc01c5700e2b00714c038a401b6f00db1806d7c036bc01b5d04535026998034be01a5e00d2b8069480349e01a4e00d268068fc0347c01a3200d1801a5bc0d2c60195f00cad80655c032a60694f034a681a52c0529206947034a281a50c052820193f00c9d8064dc032660692b034938121bc070c60185f00c2d80615c030a60484f0242680e12c07092048470242280e10c070820183f00c1d8060dc030660382b0241381207c070360481701c098079fc03ce601d7f00eb98075bc03ada01d6b00eb500759c03acc01d6579ab20271fc0f8fc09c7303e390071bc038dc01c6700e3300718c038c401c5f00e2f00715c038ac01c5300e29006dfc316fc01b7300db9006dbc036dc01b6d00daf806d78036ba0ba7a04d3b0069bc034dc01a6700d3100697c034bc01a5700d2900693c0349c01a4d00d1f8068f80347a01a3c00d190068c00d2fe0697300cb78065ac032ce0196300caf80656c032ae01953034a781a5340d29602949034a381a5140d2860294100c9f8064f4032760693900c9b81a4d403266019310349581a49c090fe0387300c378061ac030ce0186300c2f80616c030ae0185302427812134070960384902423812114070860384100c1f8060f4030760383900c1b8120d4030660183101c1581209c0903e0381b0240b80e04c0bade01d6b02eb380758c038de05c6b00e3381718c038bef845d00e2dbd5168038af064568222abf9151f86de07b6e00db5be8d9c036c607b6200dafbe4d79f06ba01b4f7b9a73d4d35d84dee926b6b133b4c98c034be05a5b02d2b80694c0b49e01a4b00d2381690c0347e09a3d7a11dbc88dc1346a01a33034b7a5c5ac0d2ce8416300caf81656c0b2ae0195302ca780652c0328e0594300c9f81e4f40d276029390349b81e4d40326602931034978544ac0d24e061230243780e1ac090ce0386300c2f80e16c090ae018530242780612c0308e0384300c1f8120f407076038390241b8120d403066038310241780e0ac0904e038230240f80e06c0902e0381302eb68075840b8da05c6c00e30807180038be0ec5e0462e806db40b6c201b5b055ad022d64036ae08b5600da9822d440368e08b46045a281a5b4052c20195f02cad81655c032a60194f03ca681652c052920594703ca280650c052820593f00c9d8064dc0b2660486d01c3080617c070b60485700c2980613c0909a0384b01c2481211c0908a0184301c208120fc030760183701c1981207c070360481701c098175b403ac201c6d02e3080717c158bc08c5d00e2b823154038a60ac5200db6806db00b6c205b6000dab822d58116aa01b4f075a702ad340d2da0296100caf81656c0b2ae0195302ca780652c0328e0594302c9f81e4f4032760293900c9b81e4d40b266029310243680e184030be0385b0242b80614c0909e0184b00c2380e10c0907e0483d00c1d80e0e40306e0483501c1980e0c40903e0381b0240b80e04c03ada01d6c03eb081f5800b8da01c6100e2f823178158ba01b6d02db0806d7c116bc08b5d00da7822d380369608b4900da182ad0811682ed3400452f0269700d2da0296103caf81e574032b60295900cab81e5540f2a60295100ca781652c0b28e0194302c9f8064ec0326e059330243680e184090be0485d00c2d80e164030ae0485501c2980e1440309e0384b0242380610c0907e0183b00c1b80e0cc0903e0381b0240b80e04c038ba07c5103db681ed74036a201b4f045a703ad341149c0695d014a881a53c032960194703ca18064fc0d2760693700c99812174070a20484f00c2580611c070860183f01c1d8120dc030660481f01c0d81205c0702605d6d00eb08071b40b8c201c5f0462e80716c158b401c570562b023155da8a807b7d03dbe01edb40f6d801b6100db0006d7c116bc08b5d00da782ad381569a0696d014b080657c0b2b60595700ca981653c032960194702ca18064fc0f27a0693b0149c81a4dc0f26a01933014988121b4070c20185f01c2d81215c030a60484f00c2580611c070860183f0241e80e0ec07072048370241a8060cc070620481f01c0d81205c0702607c5d03e2881ed740f6a2f034f779a5bb8d1dd86860795d014a881e53c0f2960794703ca181e4fc0f2760793703c99812174070a20484f01c2581211c070860483f01c1d8120dc070660481f01c0d81205c0702601c5f00e2d80715c036be01b5e02da7816d38032be0595b02cab80654c0b29e0194b00ca381650c0d27e0693d05c9d80a4e40d26e0693505c9980a4c4030be0385b0242b80614c0909e0184b00c2380e10c0907e0483d01c1d80e0e40906e0483501c1980e0c40903e0381b0240b80e04c03ade08d6d00eb582b5a803ace08d66046b2823590038de08c6e0463680717c118bc0ac5d05da3026d10034dc05a6602d2f0069580349c01a4c05d233a8910032de0596b02cb380658c0b2be0195b00cab81654c0329e0794d034a580a5240d28e0794500ca180a504052520692500c3780e1ac090ce018630242f80616c030ae0385300c2781213407096038490242381211403086038410241a80e0a40904a0481f01c0d81205c0702601b5f00dad806d5c036a601b4f00da6806d2c0369201b4700da2806d0c036820195f00cad80655c032a60194f00ca680652c0529201947034a280650c032820193f00c9d8064dc032660185f00c2d80615c030a60184f00c2680612c07092018470242280610c030820183f00c1d8060dc030660481f01c0d81205c0702605b5f00dae816d6c0b6b205b5700daa816d4c0b6a205b4f02da5816d1c0b6860595f034ae81656c052b20595702caa81654c052a20594f02ca581651c0b2860593f02c9d8164dc0b2660485f0242e80e16c070b2048570242a80e14c070a20484f01c2581211c070860483f01c1d8120dc070660481f01c0d81205c0702605c5f02e2d81715c0b8a605b5f00daf016d6c0b6b405b5702dab016d4c036a40595f02cad81655c0b2a60594f02ca581651c0b2860593f02c9e8164ec05272059370349a8164cc052620485f01c2d81215c070a60484f01c2581211c070860483f0241e80e0ec07072048370241a80e0cc070620481f01c0d81205c0702601c5f00e2f00716c038b401c5700e2b00714c038a401b5f00dad806d5c036a60195f00cad80655c032a60194f034a680652c032920194700ca280650c052820193f00c9d8064dc032660185f00c2d80615c030a60184f0242680612c030920184700c2280610c070820183f00c1d8060dc030660481f01c0d81205c0702608c5f0562d82315dd28a6e825e7392b398939ca48c0795f054ad81e55cb22a60794f044a581e51c622860292903c9281217c070b60485701c2981213c070960484701c218120d407052048250240f80e06c0902e0381302daf806d740b6b605b5902dab806d540b6a605b5102da7816d2c0b69205b4702da1816d040b2be0595d02cad80a5640b2ae0695502ca980a5440b29e0594b02ca481651c0b2865814102c9f8164ec0b26e059330242f812174070b6038590242b812154070a6038510242780e12c070920484701c2180e1040907e0383b0241b80e0cc0903e0381b0240b80e04c036be01b5b00dac806d5c036a601b5100da7806d340369601b4900da3806d140368601b4100caf80656cd42b20195700ca98065440329e0194d00ca580a5240328e0694500ca18065040327e0193b00c9b8064cc030be0185b01c2c80615c030a60185100c27806134030960384900c23812114030860184100c1f8060ec0306e018330240f80e06c0902e0381300e2f807174038b601c5900e2b807154038a601c5100da7806d380369601b4700da1806d08032be0195d00cad80a564032ae0695500ca98065440329e0194b00ca380650c0327e0193b00c9c8064dc032663013100c2f806174030b60385900c2b812154030a60185100c2780612c0308e0184300c1f8060ec030720183700c1980e0c40903e0381b0240b80e04c0b8be05c5e02e2d81715c0b8a605c5202daf806d780b6b605b5a02dab816d580b6a601b5202caf81656c0b2ae0595302ca781652c0d2920594702ca18165040b27e0593d02c9d80a4e40b26e0693502c9980a4c4090be0385b0242b80e14c0909e0384b01c2481211c07086038410241f8120f407076038390241b8120d407066038310240f80e06c0902e0381302ebe8075c40b8fa05c7c00e388071c0038be0bc5e0462e806df4036f805b7102db8006d6c156b408b5900dab822d58036a608b5100da3822d181168a0697d014b880657c0b2b60595700ca980653c0f29a0594b014a481651c0f28a01943014a08164fc032760193702c998121f4070e20185f01c2d81215c030a60184f0242680e12c07092048470242280610c070820483f00c1d8060dc07066048250240f80e06c0902e03813 18 262143 7 127 11 2047 21 2097151
def cc_84_8 : Nat → List (Nat × Nat) := unpackCursorV4 0x9863296620930368fa368da208b62488f2783d527eb527a348742616f05269e5263c625da6257961538414c3754715241f52386992ed9928b6224d3e1eb621ad3e14b6212a210dd4d0a23b0673b00067 0xdaf806d740b6b605b5900dab806d540b6a605b5100da7806d2c0b69201b4700da1816d040b2be0695d02cad80a5640b2ae0595502ca980a5440329e0594b02ca380650c0b27e0193b00c9b8164cc090be0485d01c2d80e164090ae0485501c2980e1440309e0384b0242380610c0907e0183b00c1b80e0cc0903e0381b0240b80e04e408da05c5f02e2d81715c0b8a71f35e8f1ab01ed380d2be0595b02cab96c54c0b29e0694b034a381650c05272079350242f80e16c090ae038530242780e12c0908e0384301c1c8120d40903e0381b0240b80e04c036be01b5d00dad806d64036ae01b5500da9806d440369e01b4d00da5806d1c0368a01b4300caf816574032b60195900cab806554032a60295100ca780652c0b2920194700ca18065040327e0193b00c9b8064cc030be0485d00c2d806164030ae0185500c2980e1440309e0184b01c2480611c030860184100c1f8060ec0306e018330240f80e06c0902e0381300daf806d74036b601b5700daa806d4c0369e01b4d00da5806d240368e01b4500da1806d04032be0195b368ac80655c032a60195100ca7806534032960294900ca381a514032860194100c9f8064ec0326e0193300c2f80616c070b20185700c298061440309e0184d00c2580e1240308e0484500c218061040307e0183b00c1b8060cc0903e0381b0240b80e04e388db1b46103db6c60d440369e01b4b00da3806d0c0f2da0296100ca79ac52c0f28e0194303c9f8064ec0326e331330243680e1840309e0384b0242380610c0907e0183b00c1b80e0cc0903e0381b0240b80e04c038be01c5b00e2b80714c0369e01b4b00da3806d0c0d2be0695b034ab81a54c0329e0194b00ca380650c0327e0193b00c9b8064cc090be0385b0242b80e14c0309e0184b00c2380610c0307e0183b00c1b8060cc0903e0381b0240b80e04c038da01c5f00e2d80715c038a605b6d8c9b6006d7c036b601b5700da980657c032b60195700ca980653c032960194700ca18164fc0b2760593702c9980617c030b60185700c2980613c030960184700c218120fc070760483701c1981207c070360481701c098075bc0badc01d6300eb10071bc0b8dc01c6300e3100717c038bc01c5d00db7806d8c036be01b5b00dac806d5c036a601b5100da7806d340369601b4700da280697c034ba01a5702d2a80693c0349a01a4702d228068fc0346e0696f03cb180657c032ba0195b00cab816554032a60194f00ca680652c052920194702ca280650c032820193f00c9d8064dc032660792b034938121bc070c60185f00c2e80616c030ae0485500c2980613c0309a0184b01c2480611c0908a0184300c208060fc030760183700c1980e0ac0904e0481f01c0d81205c0702601d6f00eb701758c0fac405c6f02e3700718c0f8c405c5f02e2f017174036de05b6300daf806d74036ae01b5502da9806d3c0369605b4900da3806d0c0b68205a5f04d2e81695c0b4aa01a4f0552681691c0b48a05a3f00d1b81a5bc0f2c60595f034ae81656c052b20595702caa81654c052a20194f034a681652c0b28e0594500ca18164fc032760193702c9981e4ac0d24e0486f01c3181217c090ba0385b01c2c81215c090aa0385301c2880613c0909a0384b02423812114030860483f00c1d8060dc070660382b0241381207c070360481701c098175bc0fac607c6f03e36c611940b8be05c5b02e2b81714c0f6de07b6e03db6816d7e2e6bc05b5b03dad016d5e2c6ac05b5303da933497c0b4ae05a4f579238168fc0f47a07a3704d1a81a5bc0f2c60695f02cad81655c0f2a60594f034a581a51c0b2860593f03c9e81a4ec052720693703c9a8164cc052620792b034938121bc070c60485f01c2d81215c070a60484f01c2581211c070860483f0241e80e0ec07072048370241a80e0cc070620382b0241381207c070360481701c098175bc03ad605d6700eb18171bc0f8dc01c6b02e3380718c0f8c401c5f8822f3e1174036de05b6b00db3816d8c036b71335a891ac806d5e186ac01b537c1a8806d1e1868d11345781378229adbe4ce08a6300d2f81696c0b4ae01a5300d278269340b49605a4704d2280690c0b47e01a3b00d1b8168cd4a2de9b16b488b3a3458c032be0595b02cab80654c0329e0794d02ca580a5240b28e0794500ca180a5040b27e0193b00c9b8164cc1125e1b12b0789382248c090de0386b0243380e18c030be0385b0242b80614c0309e0484d01c2580e1240908e0484500c2180e1040907e0183b00c1b80e0cc0905e0382b0241380e08c0903e0381b0240b80e04c03ade01d6b00eb380758c038de01c6b00e3380718c038be01c5e00e2e806dbc036d601b6700db1806d5c036ac01b5500da3806d180368b07344055378229ac154ce08a6300d2f80696c034ae01a5300d2780692c0348e01a4300d1f8068ec0346e01a33034b782e5ac0d2ce0c96300caf80656c032ae0195300ca780652c0328e0194300c9f8064ec0326e019330349782a4ac0d24e089230243780e1ac090ce0386300c2f80616c030ae0185300c2780612c0308e0184300c1f8060ec0306e018330241780e0ac0904e038230240f80e06c0902e0381300eb78075ac03ace01d6300e378071ac038ce01c6300e2b807158038aa01b6f00db5806d9c036c601b5700dab006d560a6a801b4f00da7006d34114de08a6b0453382298c034be01a5b00d2b80694c0349e01a4b00d2380690c0347e01a3b00d1b8068cc0d2de0696b034b381a58c032be0195b00cab80654c0329e0194b00ca380650c0327e0193b00c9b8064cc0d25e0692b0349381a48c090de0386b0243380e18c030be0185b00c2b80614c0309e0184b00c2380610c0307e0183b00c1b8060cc0905e0382b0241380e08c0903e0381b0240b80e04c03ade01d6e00eb580759c03ac607d6200e378071ac038ce01c6300e2f807178038ba01b6f00db5806d9c036c601b5f00daf006d740369e01b4e00da5806d240368601b4200da0bd8d00114de08a6b0453382298c034be08a5d00d2d80695c034aa01a5300d2780692c0348e01a4300d1f8068ec0346e01a33034b78325ac0d2ce0c96300caf81a574032b60195900cab806554032a60295100ca780652c0328e0194300c9f8064ec0326e01933034978224ac0d24e089230243780e1ac090ce0386300c2f812174030b60185900c2b806154030a60385100c2780612c0308e0184300c1f8060ec0306e018330241780e0ac0904e038230240f80e06c0902e0381300eb78075ac03ace01d6300e378071ac038ce01c6300e2f807174038b601c5a00e2b807158038aaf645400db781edb8036d601b6700db1806d88036be01b5e00dae806d3c0369c01b4d075378229ac174ce08a6300d2f80696c034ae01a5300d2780692c0348e01a4300d1f8068f40347601a3704d1a8068cc0d2de0696b034b381a58c032be0195b00cab80654c0329e0194b00ca380650c0327e0193d00c9d80a4e40326e0693500c998064c40d25e0692b0349381a48c090de0386b0243380e18c030be0185b00c2b80614c0309e0184b00c2380610c0307e0183d00c1d80e0e40306e0483500c198060c40905e0382b0241380e08c0903e0381b0240b80e04c0bade01d6b02eb380758c038de05c6b00e3381718c038bf1345e8922e80715e168aa01c537aa29006dbc0f6dc05b6b00db3816d8c0f6c401b57889ab42cd540369f1034e7a9a6bbc9bc154d6de2670553180697c0b4b605a5700d2981693c0349601a4702d218168fc1347a01a3b00d1b8268d40b4660696f4d0b581a59d182c60195f02cad81655c032a60594f00ca580651c0b2860593f03c9e8064ec052720193703c9a8164cc052620692f0d09581a49c152460486f01c3581219c070c60185f01c2d81215c030a60484f00c2580611c070860483f0241e8060ec07072018370241a80e0cc070620482f01c1581209c070460481f01c0d81205c0702601e7d00f3e0075f403ade01d6e00eb68071b80f8d801c5e00e2b006df4036de01b6e00db6806d7c036bc01b5b00dac806d4c036a401b51819a8006d240368a0c97100cb781e5b4032d60196900cb3806594032c60f96100caf80656c032ae01953014a481a5140327e0193b00c9b8064cc030de0486d00c358061a4030ce0186500c3180e184030be0185b00c2b80614c070920484500c1f8060ec0306e018330240f80e06c0902e0381300f3f8079f803cfa01e7c00f3a8079d003afe01d7d00eba8075cc03ade01d6e00eb68071fc038fc01c7d00e2d807168038ae01c5600e29807148036fe01b7d00dba806dcc036de01b6e00db6806d7c036bc01b5b00dac806d4c036a401b51811a8006d3c0369a01b4700da2806d0c0368201a6f0453680699c034ca01a5f00d2b81e93c0f49a07a47045228068fc0346e0797f03cbc81e5cc0f2e20196f03cb68065ac032d20196700cb280658c0f2c20195f00cad80655c032a60794f034a681e52c0529207947034a281e50c052820193f00c9d8064dc032660792b03c938121fc070e60186f024368061ac030d20186700c3280618c070c20185f00c2d80615c030a60484f0242680e12c07092048470242280e10c070820183f00c1d8060dc030660382b0241381207c070360481701c098075bc03ad601d6700eb18071bc038d601c6700e3180717c038bc01c5d00db7806dac036ce01b6300daf806d78036ba01b4f00da7006d35ec69808a6f0453582299c114c601a5f00d2d80695c034a601a4f00d2580691c0348601a3f00d1d8068dc034660d96f05cb582e59c192c60195f00cad80655c032a60194f00ca580651c032860193f00c9d8064dc032660892f0449582249c112460486f01c3581219c070c60185f00c2d80615c030a60184f00c2580611c030860183f00c1d8060dc030660482f01c1581209c070460481f01c0d81205c0702601d6f00eb580759c03ac601c6f00e3580719c038c601c5f00e2f007174036de01b6b00db3806d8c036be01b5e00dae806d3c0369c01b4d7b1a60229bc114d608a670453180697c034b601a5700d2980693c0349601a4700d218068fc0347601a3700d1981a5bc0d2d606967034b180657c032b60195700ca980653c032960194700ca18064fc032760193700c9981a4bc0d25606927034918121bc070d60486701c3180617c030b60185700c2980613c030960184700c218060fc030760183700c198120bc070560482701c1181207c070360481701c098079fc03cfc01e7b03f3d0079dc03cec01e7303f3901b5fc0fafc06d7b036bb81b5cc0dae401d6f00eb700b5b405ad801c7f00e3d8071dc038e601c6f00e370071b4038be01c5d00e2d807164038ae01c5500e29807144036fe01b7b00dbb806dcc036de01b6e00db6806d7c036ba01b5b00dac806d5c036aa01b5300da8806d3c0369c01b4b00da4806d0c0368401b41035a001e9fc0f4f607a7703d398069bc114da01a6b00d3480699c034ca01a630453081a97c0d4ba06a5b0352b8229540d4a601a4f00d2580691c0348601a3f00d1d8068dc034660697f034bf00a5ec0d2ee0297303cb90065ac032d40196900cb400659c032cc0196500cb200658c052c20195700cab0065540329e0194b00ca500651c0328c0194300c9f8064ec032740193700c9b0064cc0d25e0292b0349380a48c090fe0387b0243b80e1cc030de0486d00c358061a4030ce0186500c3180e184090be0485d01c2d80e164090ae0485501c2980e1440309e0184b00c2380610c0307e0183b00c1b8060cc0905e0382b0241380e08c0503e0381b0240b80a04c03cfe01e7e00f3d83f9e803cee01e7600f3981f9c803afe01d7b00ebb8075cc03ade01d6e00eb68071fc038f601c7700e398071bc038dc01c6d00e2f807178038b601c5900e29807148038a2ff45003dbf822dec116ee07b7300db7822db4036d601b6900db3806d94036c608b6100daf806d6c036ae01b5300da7806d2c0368e01b430153f8369f8054f602a770153980a9c8034de02a6d00d358069a8034d201a6800d33806998034ca01a6400d2f80696c034b401a5700d2b00694c0349e01a4b00d2500691c0348c01a430151f80a8ec0546e02a33014bf81e5f8052f602977014b980a5c8032de0196e014b681a5b0032be0195e00cad806568032ae0195600ca98065480329e0194e00ca58065280328e0194600ca18065080527e0293b0149d00a4dc1126c0293300c978064b80325a0487f01c3d8121dc070e60186f024368061ac030d20186700c3280618c070c20185f00c2d80615c030a60184f00c2580611c030860483f01c1d8120dc070660282f0141580a09c050460281f0140e80a06c07032028170240a80a04c0502201d6f03eb74395ac03acf0d56303eb10171bc038d605c6700e3180717e168bcf745d00db7816dac036ce05b6300dafc30d79f26ba01b4f861a7006d2e1669201b43831a1410d05fc680ee26f04535b6c99c114c608a5f04d2e80696c034ae09a550452980693c0b49605a4700d218168fc0347601a3702d19a8c5bd322d68f167450b1c2857c0f2ba0195b014ac80655c0f2ab09153014a880653c0b2960594700ca18164fc032760193702c998224bc302560d127044918121bc070d60486701c3181217c090ba0185b01c2c80615c090aa0385301c2880613c070960484700c218120fc030760183701c198120bc070560482701c1181207c070360481701c0980717c038b601c5700e29806d7c036b601b5700da9806d3c0369601b4a00da3806d18036860aa5f0452d82a95c114a601a4f00d2580691c0348601a3f00d1d8068dc034660695f05cad81a55c192a60194f00ca580651c032860193f00c9d8064dc032660692f0549581a49c112460485f01c2d81215c070a60184f00c2580611c030860183f00c1d8060dc030660482f01c1581209c070460481f01c0d81205c0702601d6f00eb580759c03ac601c6f02e370071ac038d401c6702e3300718c038c401c5f00e2f007174036de01b6b00db3806d8c036be01b5e00daec1cd700369e01b4e00da682a9bc114d60aa670453180697c034b601a5700d2980693c0349a01a4b02d2480691c0b48a01a4300d208068fc0347601a3700d1981a5bc172d606967064b180657c032b60195700ca980653c0329a0194b02ca480651c0b28a0194300ca08064fc032760193700c9981a4bc1525606927044918121bc070d60486701c3180617c030b60185700c2980613c0309a0184b01c2480611c0908a0184300c208060fc030760183700c198120bc070560482701c1181207c070360481701c0980717c038b601c5700e29806d7c036b601b5700da9806d3c0369601b4a00da3806d180368608a5f0452d82295c114a601a4f00d2580691c0348601a3f00d1d8068dc034660695f034ad81a55c0d2a60194f00ca580651c032860193f00c9d8064dc032660692f0349581a49c0d2460485f01c2d81215c070a60184f00c2580611c030860183f00c1d8060dc030660482f01c1581209c070460481f01c0d81205c0702601d6f00eb580759c03ac601c6f00e370071ac0b8d401c6700e3300718c0b8c401c5f00e2f007174036de01b6b00db3806d8c036be01b5e00daec14d700369e01b4e00da68229bc114d608a670453180697c034b601a5700d2980693c0b49a01a4b00d2480691c0348a01a4302d208068fc0347601a3700d1981a5bc0d2d606967034b180657c032b60195700ca980653c0b29a0194b00ca480651c0328a0194302ca08064fc032760193700c9981a4bc0d25606927034918121bc070d60486701c3180617c030b60185700c2980613c0909a0184b00c2480611c0308a0184301c208060fc030760183700c198120bc070560482701c1181207c070360481701c098075b4038bc01b6d00daf806d78036ba01b4900da2832584032be0195b00cab80654c052920694500c9f8064ec0326e0193300c2f80616c030ae0185301c248121140307e0183b00c1b8060cc0903e0381b0240b80e04c03ade01d6d00eb28071bc038dc01c6d00db7806db4036ca01b6300daf806d78036ba01b4f00da6806d1c0368a01b4300da080697c034ae07a4f03d2681e91c1148a01a3f00d1b81a5bc0f2d20796303cb080657c032b60195900cab80654c0f2a20694f034a681e52c0529206947034a281e50c052820193f00c9d8064dc032660792b034938121bc070c60185f00c2d806164030ae0185301c2881213c0909a0384b01c2481211c0908a0384301c208060fc030760183700c1980e0ac0904e0481f01c0d81205c0702601c5f00e2d80715c038a601b5f00dad806d5c036a601b4f00da7006d34114be08a5b0452b82294c0349e01a4b00d2380690c0347e01a3b00d1b8068cc0d2be0c95b034ab83254c0329e0194b00ca380650c0327e0193b00c9b8064cc0d25e0892b0349382248c090be0385b0242b80e14c0309e0184b00c2380610c0307e0183b00c1b8060cc0905e0382b0241380e08c0903e0381b0240b80e04c038be01c5b00e2b80714c036be01b5b00dab806d4c0368e01b4600da283a97c114b60ba570452980693c0349601a4700d218068fc0347601a3700d1981a57c0d2b606957034a980653c032960194700ca18064fc032760193700c9981a4bc0d256069270349181217c070b60485701c2980613c030960184700c218060fc030760183700c198120bc070560482701c1181207c070360481701c098075bc03adc01d6b00eb380758c0fac401c6f00e3580719c038c601c5f00e2f0071740f6de08b6b045b381ed8c036be01b5b00dab806d4c0369e01b4b00da3806d0c054de06a6e0153580a99c054c602a6200d2f80a974034b601a5a00d2b806958034aa01a5400d2780692c0349401a4700d2300690c0547e02a3b0151b80a8cc052de0796e014b580a59c052c60296200caf806578052ba0194f00ca700652c032940194700ca300650c032840293f0149d80a4e80526e08936014998064bc0325c0192d0243780e1ac090ce0386300c2f80616c030ae0185300c2780612c0308e018430241f80e0ec0906e038330141780a0ac0504e028230140f80a07405036038190140b8120540502602811 20 1048575 8 255 11 2047 21 2097151
def cc_84_9 : Nat → List (Nat × Nat) := unpackCursorV4 0x87731f7cc74f21c02769cc98e325f8816336520d938204989112a73a748c0d22732076cc143302cc80649c0032 0x175bc03ac601c6f03e3701718c0b8c401c5f00e2d817168038ae05c5600e29816dbc0f6dc01b6300db1006d7c036bc05b5700da9806d480b69e05b4e02da680697c0b4ae05a4f00d238168fc0b47a05a3704d1a81a5bc0d2c60195f02cad81655c032a60594f00ca580651c0b2860593f02c9e8164ec05272059370349a8164cc052620692b034938121bc070c60185f01c2d81215c030a60484f00c2580611c070860483f0241e80e0ec07072048370241a80e0cc070620382b0241381207c070360481701c098075bc03adc01d6302eb10071bc038c601c5f00e2d807164038a601c5100db7806db8036c605b6200daf806d78036ba01b4f00da5806d280368e01b4600da180697c0b4ba01a5700d2a80693c0348e01a3f00d1b81e5bc0f2c60195f02cae80656c032b20195700caa80654c052a20194f00ca580651c032860193f00c9d8064dc032660792b03c938121bc070c60185f0242e80616c030b20185700c2a80614c070a20184f00c2580611c030860183f00c1d8060dc030660382b0241381207c070360481701c0981f5bc0fadc07d6d97a3481f18c0f8c207b6f02db1816d7c0f6ba05b5b991ac816d5e626aa05b5303da8816d3c0b69605b4702da181697c0f4ba07a5704d2a82a93c0b48e05a3f5991b81e5bc0f2c60595f03cae81e56c052b20795703caa81654c052a20794f02ca581651c0f2860593f03c9d81e4dc0b2660792b03c938121bc070c60485f0242e80e16c070b2048570242a80e14c070a20484f01c2581211c070860483f01c1d8120dc070660382b0241381207c070360481701c0981719a508c801c5e00db7806dac036ce01b6300daf806d6c036ae01b5302cb78165ac0b2ce0596300caf80656c032ae0195300c9f8064ec0326e019330243780e1ac090ce0386300c2f80616c030ae0185300c1f8060ec0306e018330240f80e06c0902e0381300e2f807178038b601c5700e29807148036be01b5e00dad806d68036ae01b5600da9806d48032be0195b00cab80654c0329e0194b00ca380650c0327e0593d00c9d8064e40326e0193500c9980a4c4030be0185b00c2b80614c0309e0184b00c2380610c0307e0483d00c1d8060e40306e0183500c1980e0c40903e0381b0240b80e04c038be01c5e00e2d807168038ae01c5600e29807148036be01b5e00dad806d5c036a601b5200caf80656c032ae0195300ca781a534032960194900ca3806514032860294100c9f8064ec0326e0193300c2f80616c030ae0185300c27812134030960184900c23806114030860384100c1f8060ec0306e018330240f80e06c0902e0381397ab681f178036be01b5b00dab806d4e5c6932d34500caf9b856c0f2ae01953014a481e5140f27e0193b00c9b8d04cc030be0385b0242b80614c07092048450241f8060ec0306e038330240f80e06c0902e0381300e378071b4038d601c6900e33807194038c601c6100da7806d2c0369401b4700da3006d0c032de0196d00cb580a5a4032ce0596500cb18065840329e0194b00ca380650c0327e0193b00c9c8064dc032660593100c378061b4030d60386900c33812194030c60186100c2780612c0308e0184300c1f8060ec030720183700c1980e0c40903e0381b0240b80e04c038be01c5b02e2d00715c0b8ac01c5300daf806d780b6b605b5a02dab816d58036a601b5200caf81656c0b2ae0195302ca780652c0d2920194702ca18165040b27e0593d02c9d80a4e40b26e0693502c9980a4c4030be0385b0242b80614c0909e0184b01c2480611c07086038410241f8120f407076038390241b8120d407066038310240f80e06c0902e0381303e36c9d146566db2a36102da7816d2c0b68e05b4303cb680a5840f29e0594b02ca397450c0b27e4113b03c9b8164cc090da038610242780e12c0908e038430241f80e0ec0906e038330240f80e06c0902e0381300daf806d6c036ae01b5300da7806d2c0368e01b4303caf81e56c0f2ae0795300ca780652c0328e0194300c9f8064ec0326e019330242f80e16c090ae0385300c2780612c0308e0184300c1f8060ec0306e018330240f80e06c0902e0381300eb68071b6508d801b5f00dad806d5c036a601b4f00da5806d1c036860195f00cad80655c032a60194f00ca580651c032860193f00c9d8064dc032660185f00c2d80615c030a60184f00c2580611c030860183f00c1d8060dc030660481f01c0d81205c0702601d6f00eb18071bc038dc01c6302e3100717c038bc01c5b00e2b80714c038a401b6f00db7006d8c0b6c401b5f00dad806d68036ae01b5600da7806d380369a01a5f00d2b80693c0b49a01a4700d228068fc0b47a01a3700d1a81a5bc0d2c60195f00cad80655c032a60194f02ca680652c0328e0194500ca18064fc0b27a0193b00c9c8064dc0326a019330149881a4ac0d24e0486f01c3180617c030b60185700c2980613c0909a0184b00c23806114030860183f0241e8060ec030720183700c1a8060cc070620382b0241381207c070360481701c098075bc03ac601c6f00e3700718c0f8c401c5b00e2d00715c038ac01c5300db7806db8036c607b6200daf806d78036b601b5700da9806d480369e01b4e00da680697c034ae01a4f0452680691c0348a01a3f0451e8068dc0346a0796f03cb180657c032b60195700ca980653c0d29a0194b00ca480651c0328a01943014a08064fc0f27a0193b00c9b8064d4032660792b03c938121bc070c60185f00c2d80615c030a60184f0242680612c030920184700c2280610c070820183f0241e8060ec0306e0183500c1980e0ac0904e0481f01c0d81205c0702607d6f03eb6c9d5940f8de07c6e03e36806dbc0f6c601b5f00dad806d5c036a601b4f03da6806d2e4c69201b47929a2806d0c0f68201a5f6312b80693c0f49a07a4704d22aec8fc0346e0796f03cb180657c0f2b60795700ca980653c0f29a0794b014a481e51c0f28a01943014a081e4fc032760193703c9981e4ac0f24e0486f01c3180617c070b60485700c2980613c0909a0384b01c2481211c0908a0184301c208120fc030760183701c1980e0ac0904e0481f01c0d81205c0702601d6f03eb700758c03ac401c6f03e3700718c038c401c5f00e2f007174036de01b6300daf806d74036b601b5700daa806d4c0369601b4900da3806d0c0368201a5f00d2b80693c0349a01a4704d228068fc0346e0796f03cb180657c032b60195700ca980653c0329a0194b014a480651c0d28a0194300ca08064fc032760193700c9981e4ac0f24e0486f01c3180617c030b60185700c2980613c0309a0184b01c2480611c0908a0184300c208060fc030760183700c1980e0ac0904e0481f01c0d81205c0702601d6b02eb480758c03ac201c6f00e370071b4038be05c5e00e29807148036de01b6b00db4806d8c036c201b5f00da9806d3c0369a01b4b00da3806d140368601a6f00d3680699c0b4ca01a4f00d238068fc0346e0196f00cb68065ac052d20196702cb280658c032c20795f03ca980653c032960194700ca18064fc032760193700c9981e4ac0f24e0186f00c368061ac070d2018670243280618c030c20485f01c2980613c030960184700c218060fc030760183700c1980e0ac0904e0481f01c0d81205c0702607d6f03eb701f5b40f8de01c6300e2f81f174038b72345900e2bc89154038a607c51901b481ed8c0f6c201b4f00da5806d1c0368601a5f03d2e81e95c134aa01a4f621238228fc0346e0796f03cb180657c0f2ba0795b014ac81e55c0f2aa01953014a880653c0f2960794700ca181e4fc032760193703c9981e4ac0f24e0486f01c3180617c090ba0385b01c2c81215c090aa0185301c2880613c070960484700c218120fc030760183701c1980e0ac0904e0481f01c0d81205c0702601d6f00eb580759c03ac601c5f00e2d80715c038a601b668c9b2006d38032de0196b00cb380658c032be0195b00cab80654c0329e0194b00ca380650c030de0186b00c3380618c030be0185b00c2b80614c0309e0184b00c2380610c0903e0381b0240b80e04c036be01b5b00dac806d5c036a601b5100da7806d340369601b4900da3806d140368601b4100caf80656c032ae0195300ca7806534032960294900ca3816514032860194100c9f8064ec0326e0193300c2f80616c030ae0185300c27806134030960384900c23812114030860184100c1f8060ec0306e018330240f80e06c0902e03813 18 262143 7 127 11 2047 21 2097151
def cur_84 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_84_9 (Nat.sub p 288)) (cc_84_8 (Nat.sub p 256)) (Nat.blt p 288)) (cc_84_7 (Nat.sub p 224)) (Nat.blt p 256)) (Bool.rec (cc_84_6 (Nat.sub p 192)) (cc_84_5 (Nat.sub p 160)) (Nat.blt p 192)) (Nat.blt p 224)) (Bool.rec (Bool.rec (Bool.rec (cc_84_4 (Nat.sub p 128)) (cc_84_3 (Nat.sub p 96)) (Nat.blt p 128)) (cc_84_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (cc_84_1 (Nat.sub p 32)) (cc_84_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 160)
def f_84 : Nat → Nat × Nat := unpackForestF 0x98b5998b5500c5f96d6d96b4996b4500c5b9536d9536100c579446c92d6592b4992b4500c53914599145500b5f8f46d8f35e8f35600b5b8dc6d8dc6100b578cb6c8b4658b35e8b35600b5300b4f8845e8845d883568834e00b4b84d6b84d6384b4e84b498495f8495300b4783b5c7945682b5c794557fc5b7fc537fb4e7fb4d7f943794547ec547936f7dc54793677935e7935d7934e7b4547934d7923b79d647923700b437634f7634b7634776c547634300a5f7524472c5372a5e72a5672a4e72a4600a5b6b46d6b4616b36d6b3616b34f6b34b6e9436e5706b3476d1436cc606bc546bb7c6b34300a576a24467c5367a5e67a5667a4e67a4600a5365b6365b4965b4500a4f6424e6424600a4b60c6362d6860b6f60b5d6146e60b5100a475eb565ea4e5ea4600a435cd635cb5e5cb5600a3f5b25e5b25600a3b5a46857d6f57c5a58d6e57c5257b6300a3755b4655a5e55a5600a334ec594ec554eb594eb554eb4f525684eb474ea4f50d684ea474f4684f4524ea370095f4bc5f4bc5b4bc574c5644bc530095b47c6d47c6147b6d47b6147b4f4857047b47009573ac5f3ac5b4596c3ac5742d644345443d6443237429443ac533ab5f4116c3ab574046e3ab4f3f1443e5623e15c3ab473d2553a95e3a9563ba453a94e3a9460095338349383453825b382570094f3256b365703617c3246734d703497c323673395c323473214e321460094b2fb5d2fb51304602fa370094725d672e14425c6b2d13425b6b2bd7c2b97c25b672a93425b5b2996c25b5725b4f2813425b4325a562594e2636a259460094321b5e21b5621a5f2324421a5321a4b21a470093f1e5671e3671e3571e24e1e15e1e1560093b1bc5a1bc521c4601ba57009371a9541156b11467191341136b17c7c1797c113671135f1613411353151341134b1415c113471314c112461115e11c6a11156009330ea5e0ea560ea4e0ea460092f08c5f08c5b0c96c08c570b5640b14408c530895e089560894e089460092b04c5f0736004c5704b5a04b5204b4a04b420092703944014530115e011560114e01146009230003f 9 11
set_option maxHeartbeats 0 in
theorem rc_84 : dagCheckRootsV4 fullMask g_84 ep_84 307 bds_84 (dagTraceF fullMask rootStock 11 f_84) (cur_84 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_84_0 : treeBlockF 0 32 (dagCheckNodeV4 fullMask g_84 ep_84 bds_84 307 (dagTraceF fullMask rootStock 11 f_84) cur_84) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_84_1 : treeBlockF 32 64 (dagCheckNodeV4 fullMask g_84 ep_84 bds_84 307 (dagTraceF fullMask rootStock 11 f_84) cur_84) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_84_2 : treeBlockF 64 96 (dagCheckNodeV4 fullMask g_84 ep_84 bds_84 307 (dagTraceF fullMask rootStock 11 f_84) cur_84) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_84_3 : treeBlockF 96 128 (dagCheckNodeV4 fullMask g_84 ep_84 bds_84 307 (dagTraceF fullMask rootStock 11 f_84) cur_84) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_84_4 : treeBlockF 128 160 (dagCheckNodeV4 fullMask g_84 ep_84 bds_84 307 (dagTraceF fullMask rootStock 11 f_84) cur_84) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_84_5 : treeBlockF 160 192 (dagCheckNodeV4 fullMask g_84 ep_84 bds_84 307 (dagTraceF fullMask rootStock 11 f_84) cur_84) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_84_6 : treeBlockF 192 224 (dagCheckNodeV4 fullMask g_84 ep_84 bds_84 307 (dagTraceF fullMask rootStock 11 f_84) cur_84) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_84_7 : treeBlockF 224 256 (dagCheckNodeV4 fullMask g_84 ep_84 bds_84 307 (dagTraceF fullMask rootStock 11 f_84) cur_84) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_84_8 : treeBlockF 256 288 (dagCheckNodeV4 fullMask g_84 ep_84 bds_84 307 (dagTraceF fullMask rootStock 11 f_84) cur_84) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_84_9 : treeBlockF 288 307 (dagCheckNodeV4 fullMask g_84 ep_84 bds_84 307 (dagTraceF fullMask rootStock 11 f_84) cur_84) = true := by decide +kernel
theorem nj_84_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 fullMask g_84 ep_84 bds_84 307 (dagTraceF fullMask rootStock 11 f_84) cur_84) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_84_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_84_1 h1 h2)
theorem nj_84_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeV4 fullMask g_84 ep_84 bds_84 307 (dagTraceF fullMask rootStock 11 f_84) cur_84) i = true := block_join nj_84_1 (fun _ h1 h2 => treeBlockF_at nb_84_2 h1 h2)
theorem nj_84_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeV4 fullMask g_84 ep_84 bds_84 307 (dagTraceF fullMask rootStock 11 f_84) cur_84) i = true := block_join nj_84_2 (fun _ h1 h2 => treeBlockF_at nb_84_3 h1 h2)
theorem nj_84_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeV4 fullMask g_84 ep_84 bds_84 307 (dagTraceF fullMask rootStock 11 f_84) cur_84) i = true := block_join nj_84_3 (fun _ h1 h2 => treeBlockF_at nb_84_4 h1 h2)
theorem nj_84_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeV4 fullMask g_84 ep_84 bds_84 307 (dagTraceF fullMask rootStock 11 f_84) cur_84) i = true := block_join nj_84_4 (fun _ h1 h2 => treeBlockF_at nb_84_5 h1 h2)
theorem nj_84_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeV4 fullMask g_84 ep_84 bds_84 307 (dagTraceF fullMask rootStock 11 f_84) cur_84) i = true := block_join nj_84_5 (fun _ h1 h2 => treeBlockF_at nb_84_6 h1 h2)
theorem nj_84_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeV4 fullMask g_84 ep_84 bds_84 307 (dagTraceF fullMask rootStock 11 f_84) cur_84) i = true := block_join nj_84_6 (fun _ h1 h2 => treeBlockF_at nb_84_7 h1 h2)
theorem nj_84_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeV4 fullMask g_84 ep_84 bds_84 307 (dagTraceF fullMask rootStock 11 f_84) cur_84) i = true := block_join nj_84_7 (fun _ h1 h2 => treeBlockF_at nb_84_8 h1 h2)
theorem nj_84_9 : ∀ i, 0 ≤ i → i < 307 → (dagCheckNodeV4 fullMask g_84 ep_84 bds_84 307 (dagTraceF fullMask rootStock 11 f_84) cur_84) i = true := block_join nj_84_8 (fun _ h1 h2 => treeBlockF_at nb_84_9 h1 h2)
theorem nc_84 : ∀ i, 0 ≤ i → i < 307 → (dagCheckNodeV4 fullMask g_84 ep_84 bds_84 307 (dagTraceF fullMask rootStock 11 f_84) cur_84) i = true := nj_84_9
theorem lb_84 : LowerBin fullMask rootStock g_84 12 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_84 kn_84 sub_84 gl_84 rc_84 nc_84

def wg : List Gate := [⟨GateOp.and, [0, 3]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.or, [0, 10]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.or, [6, 8]⟩, ⟨GateOp.and, [9, 11]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [14, 15]⟩, ⟨GateOp.and, [16, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276677288 * 2 ^ 32 + 3941116032) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276677288 * 2 ^ 32 + 3941116032)) (13 - 1) := by
  rw [show canon fullMask (4276677288 * 2 ^ 32 + 3941116032) = g_84 by decide]
  exact lb_84

end PEqualNP.Outside.L_meta_48472

theorem PEqualNP.Outside.L_meta_48472 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677288 * 2 ^ 32 + 3941116032) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677288 * 2 ^ 32 + 3941116032) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_48472.table2_from_lowerBin (4276677288 * 2 ^ 32 + 3941116032) 13 PEqualNP.Outside.L_meta_48472.root_lb PEqualNP.Outside.L_meta_48472.wg 18 rfl PEqualNP.Outside.L_meta_48472.wfits PEqualNP.Outside.L_meta_48472.weval
