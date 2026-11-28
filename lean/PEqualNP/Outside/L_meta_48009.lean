import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48009

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

def m_0 : Nat := 0x3300000033000000
def s_0 : List Nat := [0x1100000011000000, 0x300000003000000, 0x33000000]
def g_0 : Nat := 0x100000013000000
def ep_0 : Nat := 0x1200000000000000000000000000000000000000010000000200000000000000000000000100000010000000
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

def m_3 : Nat := 0xf0f0
def s_3 : List Nat := [0x5050, 0x3030, 0xf0]
def g_3 : Nat := 0x1070
def ep_3 : Nat := 0x60000000000000000000000000000010200000000000001040
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

def m_5 : Nat := 0x3333000000000000
def s_5 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_5 : Nat := 0x113000000000000
def ep_5 : Nat := 0x12000000000000010200000000000000000000000000000110000000000000
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

def m_6 : Nat := 0x5555000000000000
def s_6 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_6 : Nat := 0x115000000000000
def ep_6 : Nat := 0x14000000000000010400000000000001100000000000000000000000000000
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

def m_7 : Nat := 0x222200002222
def s_7 : List Nat := [0x20200000202, 0x2200000022, 0x2222]
def g_7 : Nat := 0x200000222
def ep_7 : Nat := 0x22000000000000000000000000200000020000000020000020000000000000000000000000000000000
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

def m_8 : Nat := 0xaa000000aa
def s_8 : List Nat := [0x2200000022, 0xa0000000a, 0xaa]
def g_8 : Nat := 0x20000002a
def ep_8 : Nat := 0x2800000000000000000000000000000000000000020000000800000002000000200000000000000000
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

def m_9 : Nat := 0xff000000000000
def s_9 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_9 : Nat := 0x17000000000000
def ep_9 : Nat := 0x600000000000000120000000000000014000000000000
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

def m_10 : Nat := 0xf000f0
def s_10 : List Nat := [0x500050, 0x300030, 0xf0]
def g_10 : Nat := 0x100070
def ep_10 : Nat := 0x600000000000000000000000000000000000000000001000200000000000100040
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

def m_11 : Nat := 0xf0f000000000000
def s_11 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_11 : Nat := 0x107000000000000
def ep_11 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
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

def m_12 : Nat := 0x44444444
def s_12 : List Nat := [0x4040404, 0x440044, 0x4444]
def g_12 : Nat := 0x40444
def ep_12 : Nat := 0x4400000000000040040000000000004040000000000000000000000000000000000
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

def m_13 : Nat := 0xa0a00000a0a0000
def s_13 : List Nat := [0x202000002020000, 0xa0000000a0000, 0xa0a0000]
def g_13 : Nat := 0x20000020a0000
def ep_13 : Nat := 0x208000000000000000000000002000000080000000000000000000000020000020000000000000000000000
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

def m_14 : Nat := 0xcc330000cc33
def s_14 : List Nat := [0x441100004411, 0x3300000033, 0xc0300000c03, 0xcc33]
def g_14 : Nat := 0x41300000c33
def ep_14 : Nat := 0x820000000000000000000000000000000000000040200000c0000000000000000000000041000000000
theorem epk_14 : ep_14 = edgePack m_14 g_14 := by decide +kernel
def bds_14 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_14 : KnownBin bds_14 := by intro b hb; simp [bds_14] at hb
theorem sub_14 : ∀ b ∈ bds_14, m_14 &&& b.1 = b.1 := by intro b hb; simp [bds_14] at hb
theorem gl_14 : ∀ b ∈ bds_14, canon b.1 g_14 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_14] at hb
def cur_14 : Nat → List (Nat × Nat) := unpackCursorV4 0x72e18b060c0681 0xad2b4cf63a6d9352d00f 7 127 3 7 6 63 10 1023
def f_14 : Nat → Nat × Nat := unpackForestF 0x1f6e87a3b1d4e80f 3 6
set_option maxHeartbeats 0 in
theorem rc_14 : dagCheckRootsV4 m_14 g_14 ep_14 7 bds_14 (dagTraceF m_14 s_14 4 f_14) (cur_14 0) s_14 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_14 : treeBlockF 0 7 (dagCheckNodeV4 m_14 g_14 ep_14 bds_14 7 (dagTraceF m_14 s_14 4 f_14) cur_14) = true := by decide +kernel
theorem nc_14 : ∀ i, 0 ≤ i → i < 7 → (dagCheckNodeV4 m_14 g_14 ep_14 bds_14 7 (dagTraceF m_14 s_14 4 f_14) cur_14) i = true := fun _ h1 h2 => treeBlockF_at nb_14 h1 h2
theorem lb_14 : LowerBin m_14 s_14 g_14 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_14 kn_14 sub_14 gl_14 rc_14 nc_14

def m_15 : Nat := 0x3c003c003c003c00
def s_15 : List Nat := [0x1400140014001400, 0xc000c000c000c00, 0x3c0000003c00, 0x3c003c00]
def g_15 : Nat := 0x140010001c00
def ep_15 : Nat := 0x100008000000140000000c000000000000000000000000000000000000000000000000000000140010001000
theorem epk_15 : ep_15 = edgePack m_15 g_15 := by decide +kernel
def bds_15 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_15 : KnownBin bds_15 := by intro b hb; simp [bds_15] at hb
theorem sub_15 : ∀ b ∈ bds_15, m_15 &&& b.1 = b.1 := by intro b hb; simp [bds_15] at hb
theorem gl_15 : ∀ b ∈ bds_15, canon b.1 g_15 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_15] at hb
def cur_15 : Nat → List (Nat × Nat) := unpackCursorV4 0xcc61 0x4a5420f 4 15 2 3 6 63 9 511
def f_15 : Nat → Nat × Nat := unpackForestF 0x1a708f 1 6
set_option maxHeartbeats 0 in
theorem rc_15 : dagCheckRootsV4 m_15 g_15 ep_15 3 bds_15 (dagTraceF m_15 s_15 4 f_15) (cur_15 0) s_15 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_15 : treeBlockF 0 3 (dagCheckNodeV4 m_15 g_15 ep_15 bds_15 3 (dagTraceF m_15 s_15 4 f_15) cur_15) = true := by decide +kernel
theorem nc_15 : ∀ i, 0 ≤ i → i < 3 → (dagCheckNodeV4 m_15 g_15 ep_15 bds_15 3 (dagTraceF m_15 s_15 4 f_15) cur_15) i = true := fun _ h1 h2 => treeBlockF_at nb_15 h1 h2
theorem lb_15 : LowerBin m_15 s_15 g_15 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_15 kn_15 sub_15 gl_15 rc_15 nc_15

def m_16 : Nat := 0x3c3c00003c3c0000
def s_16 : List Nat := [0x1414000014140000, 0xc0c00000c0c0000, 0x3c0000003c0000, 0x3c3c0000]
def g_16 : Nat := 0x140000101c0000
def ep_16 : Nat := 0x10080000000000000000000000140000000c0000000000000000000000000000000000000014000010100000
theorem epk_16 : ep_16 = edgePack m_16 g_16 := by decide +kernel
def bds_16 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_16 : KnownBin bds_16 := by intro b hb; simp [bds_16] at hb
theorem sub_16 : ∀ b ∈ bds_16, m_16 &&& b.1 = b.1 := by intro b hb; simp [bds_16] at hb
theorem gl_16 : ∀ b ∈ bds_16, canon b.1 g_16 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_16] at hb
def cur_16 : Nat → List (Nat × Nat) := unpackCursorV4 0xcc61 0x4a5420f 4 15 2 3 6 63 9 511
def f_16 : Nat → Nat × Nat := unpackForestF 0x1a708f 1 6
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsV4 m_16 g_16 ep_16 3 bds_16 (dagTraceF m_16 s_16 4 f_16) (cur_16 0) s_16 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16 : treeBlockF 0 3 (dagCheckNodeV4 m_16 g_16 ep_16 bds_16 3 (dagTraceF m_16 s_16 4 f_16) cur_16) = true := by decide +kernel
theorem nc_16 : ∀ i, 0 ≤ i → i < 3 → (dagCheckNodeV4 m_16 g_16 ep_16 bds_16 3 (dagTraceF m_16 s_16 4 f_16) cur_16) i = true := fun _ h1 h2 => treeBlockF_at nb_16 h1 h2
theorem lb_16 : LowerBin m_16 s_16 g_16 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_16 kn_16 sub_16 gl_16 rc_16 nc_16

def m_17 : Nat := 0x3c3c3c3c
def s_17 : List Nat := [0x14141414, 0xc0c0c0c, 0x3c003c, 0x3c3c]
def g_17 : Nat := 0x101c1c3c
def ep_17 : Nat := 0xc2000000000000c0020000000000000000000000000000000000000000010101000
theorem epk_17 : ep_17 = edgePack m_17 g_17 := by decide +kernel
def bds_17 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_17 : KnownBin bds_17 := by intro b hb; simp [bds_17] at hb
theorem sub_17 : ∀ b ∈ bds_17, m_17 &&& b.1 = b.1 := by intro b hb; simp [bds_17] at hb
theorem gl_17 : ∀ b ∈ bds_17, canon b.1 g_17 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_17] at hb
def cc_17_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xd41a8350624c41883105c3b81686d0581b0148e90520a41482524a09412062144088108610420802d941d001 0xf83c3c0d0e82c38090d34432930c244284b0a2342a910993c244c0804c1e110702c1a09040100c0d018240c050181410490384c0a110203c040d24a3f868f60a3b808dde235748cdc93f704edb937644cd712f5a4ad41274648d103f420ed0037360ccb82f2c0ac88271808c581f1406c48170204c000f 11 2047 5 31 10 1023 18 262143
def cc_17_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc8ba8e888180808080808080646060604b484140393823202020200400000000 0x1f924f8127a8fbb47b892db092b40b5504bda4cd89e6a4d340319814c5a260932f489582cac9a58912a07948309ca64c51250312014 8 255 3 7 10 1023 17 131071
def cc_17_2 : Nat → List (Nat × Nat) := unpackCursorV4 0x989190896560525050421610090100 0x1f9347c4d1ea449a4e26134960e250347e49228247c49228247a8da1235904ea39368c0ea203684911ea3c 8 255 3 7 10 1023 18 262143
def cur_17 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_17_2 (Nat.sub p 64)) (cc_17_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_17_0 p) (Nat.blt p 32)
def f_17 : Nat → Nat × Nat := unpackForestF 0x252712934941c4a0d00c7f113a889b440ea28491036031ec29100c7606377c923e091ec7c06357726018cc0a7e053b029bb34f19a68cc18660a014cd7e88be4c5f22014bc0a56a644569a290f14860052748a624511203090140291810fc08760437381e1c0d0e0587024021998d10c49862440217810ac94885234249e124c0084e344c1a220d0b068480423020f8106c082e09240426060501088083c060a020d00826000f 7 10
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsV4 m_17 g_17 ep_17 78 bds_17 (dagTraceF m_17 s_17 5 f_17) (cur_17 0) s_17 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17_0 : treeBlockF 0 32 (dagCheckNodeV4 m_17 g_17 ep_17 bds_17 78 (dagTraceF m_17 s_17 5 f_17) cur_17) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17_1 : treeBlockF 32 64 (dagCheckNodeV4 m_17 g_17 ep_17 bds_17 78 (dagTraceF m_17 s_17 5 f_17) cur_17) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17_2 : treeBlockF 64 78 (dagCheckNodeV4 m_17 g_17 ep_17 bds_17 78 (dagTraceF m_17 s_17 5 f_17) cur_17) = true := by decide +kernel
theorem nj_17_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_17 g_17 ep_17 bds_17 78 (dagTraceF m_17 s_17 5 f_17) cur_17) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_17_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_17_1 h1 h2)
theorem nj_17_2 : ∀ i, 0 ≤ i → i < 78 → (dagCheckNodeV4 m_17 g_17 ep_17 bds_17 78 (dagTraceF m_17 s_17 5 f_17) cur_17) i = true := block_join nj_17_1 (fun _ h1 h2 => treeBlockF_at nb_17_2 h1 h2)
theorem nc_17 : ∀ i, 0 ≤ i → i < 78 → (dagCheckNodeV4 m_17 g_17 ep_17 bds_17 78 (dagTraceF m_17 s_17 5 f_17) cur_17) i = true := nj_17_2
theorem lb_17 : LowerBin m_17 s_17 g_17 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_17 kn_17 sub_17 gl_17 rc_17 nc_17

def m_18 : Nat := 0xaa00aa00aa00aa0
def s_18 : List Nat := [0x220022002200220, 0xa000a000a000a0, 0xaa000000aa0, 0xaa00aa0]
def g_18 : Nat := 0x2000a20
def ep_18 : Nat := 0x2000a2000000000000008200000000000000000000000000000000000000000020000200000000000000000
theorem epk_18 : ep_18 = edgePack m_18 g_18 := by decide +kernel
def bds_18 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_18 : KnownBin bds_18 := by intro b hb; simp [bds_18] at hb
theorem sub_18 : ∀ b ∈ bds_18, m_18 &&& b.1 = b.1 := by intro b hb; simp [bds_18] at hb
theorem gl_18 : ∀ b ∈ bds_18, canon b.1 g_18 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_18] at hb
def cur_18 : Nat → List (Nat × Nat) := unpackCursorV4 0x1a2d58952244890e8701 0x1d383481d302480d3024a243980c58295085019104400f 7 127 3 7 9 511 14 16383
def f_18 : Nat → Nat × Nat := unpackForestF 0x239231f3022922121953052821100f 3 9
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsV4 m_18 g_18 ep_18 10 bds_18 (dagTraceF m_18 s_18 4 f_18) (cur_18 0) s_18 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_18 : treeBlockF 0 10 (dagCheckNodeV4 m_18 g_18 ep_18 bds_18 10 (dagTraceF m_18 s_18 4 f_18) cur_18) = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 10 → (dagCheckNodeV4 m_18 g_18 ep_18 bds_18 10 (dagTraceF m_18 s_18 4 f_18) cur_18) i = true := fun _ h1 h2 => treeBlockF_at nb_18 h1 h2
theorem lb_18 : LowerBin m_18 s_18 g_18 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_18 kn_18 sub_18 gl_18 rc_18 nc_18

def m_19 : Nat := 0xff0000ff
def s_19 : List Nat := [0x55000055, 0x33000033, 0xf00000f, 0xff]
def g_19 : Nat := 0x1300007f
def ep_19 : Nat := 0x200000800000000130000200000000010000040
theorem epk_19 : ep_19 = edgePack m_19 g_19 := by decide +kernel
def bds_19 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_19 : KnownBin bds_19 := by intro b hb; simp [bds_19] at hb
theorem sub_19 : ∀ b ∈ bds_19, m_19 &&& b.1 = b.1 := by intro b hb; simp [bds_19] at hb
theorem gl_19 : ∀ b ∈ bds_19, canon b.1 g_19 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_19] at hb
def cur_19 : Nat → List (Nat × Nat) := unpackCursorV4 0x72e18b060c0681 0xa9a54d327b13a69b24d4a6800f 7 127 3 7 9 511 13 8191
def f_19 : Nat → Nat × Nat := unpackForestF 0x33db3433a33633533400f 3 9
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsV4 m_19 g_19 ep_19 7 bds_19 (dagTraceF m_19 s_19 4 f_19) (cur_19 0) s_19 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19 : treeBlockF 0 7 (dagCheckNodeV4 m_19 g_19 ep_19 bds_19 7 (dagTraceF m_19 s_19 4 f_19) cur_19) = true := by decide +kernel
theorem nc_19 : ∀ i, 0 ≤ i → i < 7 → (dagCheckNodeV4 m_19 g_19 ep_19 bds_19 7 (dagTraceF m_19 s_19 4 f_19) cur_19) i = true := fun _ h1 h2 => treeBlockF_at nb_19 h1 h2
theorem lb_19 : LowerBin m_19 s_19 g_19 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_19 kn_19 sub_19 gl_19 rc_19 nc_19

def m_20 : Nat := 0xff00ff0000000000
def s_20 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_20 : Nat := 0x100150000000000
def ep_20 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000100150000000000
theorem epk_20 : ep_20 = edgePack m_20 g_20 := by decide +kernel
def bds_20 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_20 : KnownBin bds_20 := by
  intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_20 : ∀ b ∈ bds_20, m_20 &&& b.1 = b.1 := by intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_20 : ∀ b ∈ bds_20, canon b.1 g_20 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_20 : Nat → List (Nat × Nat) := fun _ => []
def f_20 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV4 m_20 g_20 ep_20 0 bds_20 (dagTraceF m_20 s_20 4 f_20) (cur_20 0) s_20 4 = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_20 g_20 ep_20 bds_20 0 (dagTraceF m_20 s_20 4 f_20) cur_20 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_20 : LowerBin m_20 s_20 g_20 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_20 kn_20 sub_20 gl_20 rc_20 nc_20

def m_21 : Nat := 0xffff000000000000
def s_21 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_21 : Nat := 0x117000000000000
def ep_21 : Nat := 0x16000000000000010600000000000001120000000000000114000000000000
theorem epk_21 : ep_21 = edgePack m_21 g_21 := by decide +kernel
def bds_21 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11), (m_9, s_9, 4, g_9), (m_6, s_6, 4, g_6), (m_5, s_5, 4, g_5)]
theorem kn_21 : KnownBin bds_21 := by
  intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_11
  · exact lb_9
  · exact lb_6
  · exact lb_5
theorem sub_21 : ∀ b ∈ bds_21, m_21 &&& b.1 = b.1 := by intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_21 : ∀ b ∈ bds_21, canon b.1 g_21 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_21_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_21_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_21 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_21_1 (Nat.sub p 32)) (cc_21_0 p) (Nat.blt p 32)
def f_21 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV4 m_21 g_21 ep_21 43 bds_21 (dagTraceF m_21 s_21 6 f_21) (cur_21 0) s_21 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21_0 : treeBlockF 0 32 (dagCheckNodeV4 m_21 g_21 ep_21 bds_21 43 (dagTraceF m_21 s_21 6 f_21) cur_21) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21_1 : treeBlockF 32 43 (dagCheckNodeV4 m_21 g_21 ep_21 bds_21 43 (dagTraceF m_21 s_21 6 f_21) cur_21) = true := by decide +kernel
theorem nj_21_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_21 g_21 ep_21 bds_21 43 (dagTraceF m_21 s_21 6 f_21) cur_21) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_21_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_21_1 h1 h2)
theorem nc_21 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_21 g_21 ep_21 bds_21 43 (dagTraceF m_21 s_21 6 f_21) cur_21) i = true := nj_21_1
theorem lb_21 : LowerBin m_21 s_21 g_21 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_21 kn_21 sub_21 gl_21 rc_21 nc_21

def m_22 : Nat := 0xffff00000000
def s_22 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_22 : Nat := 0x155700000000
def ep_22 : Nat := 0x4200000000000004020000000000001002000000000000155400000000
theorem epk_22 : ep_22 = edgePack m_22 g_22 := by decide +kernel
def bds_22 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_22 : KnownBin bds_22 := by intro b hb; simp [bds_22] at hb
theorem sub_22 : ∀ b ∈ bds_22, m_22 &&& b.1 = b.1 := by intro b hb; simp [bds_22] at hb
theorem gl_22 : ∀ b ∈ bds_22, canon b.1 g_22 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_22] at hb
def cc_22_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0xe24c6d20345319280b83c581a2a0b14048912844921e0b0e04858202c9a124f08268303c141a040402249fa3ff91df28df4467993fc89dda4de8267292f8895c249df246f03f741db00dd3066802f34159809ca046381f100d8605c1026000f 11 2047 5 31 10 1023 17 131071
def cc_22_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0x3d299e140ec26741038251b924d8146a09314998240bc265c102c2795934a80c5205270513024900c4605202410234 8 255 3 7 10 1023 17 131071
def cur_22 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_22_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_22_0 p) (Nat.blt p 32)
def f_22 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV4 m_22 g_22 ep_22 64 bds_22 (dagTraceF m_22 s_22 5 f_22) (cur_22 0) s_22 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_22_0 : treeBlockF 0 32 (dagCheckNodeV4 m_22 g_22 ep_22 bds_22 64 (dagTraceF m_22 s_22 5 f_22) cur_22) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_22_1 : treeBlockF 32 64 (dagCheckNodeV4 m_22 g_22 ep_22 bds_22 64 (dagTraceF m_22 s_22 5 f_22) cur_22) = true := by decide +kernel
theorem nj_22_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_22 g_22 ep_22 bds_22 64 (dagTraceF m_22 s_22 5 f_22) cur_22) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_22_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_22_1 h1 h2)
theorem nc_22 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_22 g_22 ep_22 bds_22 64 (dagTraceF m_22 s_22 5 f_22) cur_22) i = true := nj_22_1
theorem lb_22 : LowerBin m_22 s_22 g_22 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_22 kn_22 sub_22 gl_22 rc_22 nc_22

def m_23 : Nat := 0xff00ff00000000
def s_23 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_23 : Nat := 0x17005700000000
def ep_23 : Nat := 0x40000000000000000000000000000600020000000000120002000000000014005400000000
theorem epk_23 : ep_23 = edgePack m_23 g_23 := by decide +kernel
def bds_23 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_23 : KnownBin bds_23 := by
  intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_23 : ∀ b ∈ bds_23, m_23 &&& b.1 = b.1 := by intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_23 : ∀ b ∈ bds_23, canon b.1 g_23 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_23 : Nat → List (Nat × Nat) := fun _ => []
def f_23 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV4 m_23 g_23 ep_23 0 bds_23 (dagTraceF m_23 s_23 4 f_23) (cur_23 0) s_23 4 = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_23 g_23 ep_23 bds_23 0 (dagTraceF m_23 s_23 4 f_23) cur_23 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_23 : LowerBin m_23 s_23 g_23 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_23 kn_23 sub_23 gl_23 rc_23 nc_23

def m_24 : Nat := 0xf0f0f0f000000000
def s_24 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_24 : Nat := 0x10105000000000
def ep_24 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000010105000000000
theorem epk_24 : ep_24 = edgePack m_24 g_24 := by decide +kernel
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_24 : KnownBin bds_24 := by
  intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_24 : ∀ b ∈ bds_24, m_24 &&& b.1 = b.1 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_24 : ∀ b ∈ bds_24, canon b.1 g_24 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_24 : Nat → List (Nat × Nat) := fun _ => []
def f_24 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV4 m_24 g_24 ep_24 0 bds_24 (dagTraceF m_24 s_24 4 f_24) (cur_24 0) s_24 4 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_24 g_24 ep_24 bds_24 0 (dagTraceF m_24 s_24 4 f_24) cur_24 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_24 kn_24 sub_24 gl_24 rc_24 nc_24

def m_25 : Nat := 0xf0f0f0f00000000
def s_25 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_25 : Nat := 0x107050700000000
def ep_25 : Nat := 0x400000000000006000200000000000000000000000001020002000000000104050400000000
theorem epk_25 : ep_25 = edgePack m_25 g_25 := by decide +kernel
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
theorem kn_25 : KnownBin bds_25 := by
  intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_11
theorem sub_25 : ∀ b ∈ bds_25, m_25 &&& b.1 = b.1 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_25 : ∀ b ∈ bds_25, canon b.1 g_25 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_25 : Nat → List (Nat × Nat) := fun _ => []
def f_25 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV4 m_25 g_25 ep_25 0 bds_25 (dagTraceF m_25 s_25 4 f_25) (cur_25 0) s_25 4 = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_25 g_25 ep_25 bds_25 0 (dagTraceF m_25 s_25 4 f_25) cur_25 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_25 : LowerBin m_25 s_25 g_25 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_25 kn_25 sub_25 gl_25 rc_25 nc_25

def m_26 : Nat := 0xcccccccc00000000
def s_26 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_26 : Nat := 0x4044400000000
def ep_26 : Nat := 0x440000000000004004000000000000404000000000000000000000000000004044400000000
theorem epk_26 : ep_26 = edgePack m_26 g_26 := by decide +kernel
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
theorem kn_26 : KnownBin bds_26 := by
  intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_4
theorem sub_26 : ∀ b ∈ bds_26, m_26 &&& b.1 = b.1 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_26 : ∀ b ∈ bds_26, canon b.1 g_26 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_26 : Nat → List (Nat × Nat) := fun _ => []
def f_26 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV4 m_26 g_26 ep_26 0 bds_26 (dagTraceF m_26 s_26 4 f_26) (cur_26 0) s_26 4 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_26 g_26 ep_26 bds_26 0 (dagTraceF m_26 s_26 4 f_26) cur_26 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_26 : LowerBin m_26 s_26 g_26 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_26 kn_26 sub_26 gl_26 rc_26 nc_26

def m_27 : Nat := 0x3333333300000000
def s_27 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_27 : Nat := 0x113111300000000
def ep_27 : Nat := 0x1000000000000012000200000000010200020000000000000000000000000110111000000000
theorem epk_27 : ep_27 = edgePack m_27 g_27 := by decide +kernel
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
theorem kn_27 : KnownBin bds_27 := by
  intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_5
theorem sub_27 : ∀ b ∈ bds_27, m_27 &&& b.1 = b.1 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_27 : ∀ b ∈ bds_27, canon b.1 g_27 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_27 : Nat → List (Nat × Nat) := fun _ => []
def f_27 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV4 m_27 g_27 ep_27 0 bds_27 (dagTraceF m_27 s_27 4 f_27) (cur_27 0) s_27 4 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_27 g_27 ep_27 bds_27 0 (dagTraceF m_27 s_27 4 f_27) cur_27 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_27 kn_27 sub_27 gl_27 rc_27 nc_27

def m_28 : Nat := 0x5050505050505050
def s_28 : List Nat := [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050]
def g_28 : Nat := 0x10105010101050
def ep_28 : Nat := 0x1000000000001040000000400010004000000040000000000000000000101000101010000000000000000000
theorem epk_28 : ep_28 = edgePack m_28 g_28 := by decide +kernel
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_28 : KnownBin bds_28 := by
  intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_28 : ∀ b ∈ bds_28, m_28 &&& b.1 = b.1 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_28 : ∀ b ∈ bds_28, canon b.1 g_28 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_28 : Nat → List (Nat × Nat) := fun _ => []
def f_28 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV4 m_28 g_28 ep_28 0 bds_28 (dagTraceF m_28 s_28 4 f_28) (cur_28 0) s_28 4 = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_28 g_28 ep_28 bds_28 0 (dagTraceF m_28 s_28 4 f_28) cur_28 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_28 : LowerBin m_28 s_28 g_28 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_28 kn_28 sub_28 gl_28 rc_28 nc_28

def m_29 : Nat := 0x5555555500000000
def s_29 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_29 : Nat := 0x115155500000000
def ep_29 : Nat := 0x1440000000000014004000000000010404000000000001101000000000000000000000000000
theorem epk_29 : ep_29 = edgePack m_29 g_29 := by decide +kernel
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2), (m_6, s_6, 4, g_6), (m_1, s_1, 4, g_1), (m_4, s_4, 4, g_4)]
theorem kn_29 : KnownBin bds_29 := by
  intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_2
  · exact lb_6
  · exact lb_1
  · exact lb_4
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

def m_30 : Nat := 0x3030303030303030
def s_30 : List Nat := [0x1010101010101010, 0x30003000300030, 0x303000003030, 0x30303030]
def g_30 : Nat := 0x10101010101030
def ep_30 : Nat := 0x1000002000001000000000200010000000000020000000000000000000000000000000000010101010101000
theorem epk_30 : ep_30 = edgePack m_30 g_30 := by decide +kernel
def bds_30 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_30 : KnownBin bds_30 := by intro b hb; simp [bds_30] at hb
theorem sub_30 : ∀ b ∈ bds_30, m_30 &&& b.1 = b.1 := by intro b hb; simp [bds_30] at hb
theorem gl_30 : ∀ b ∈ bds_30, canon b.1 g_30 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_30] at hb
def cc_30_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0xe24c6d20345319280b83c581a2a0b14048912844921e0b0e04858202c9a124f08268303c141a040402249fa3ff91df28df4467993fc89dda4de8267292f8895c249df246f03f741db00dd3066802f34159809ca046381f100d8605c1026000f 11 2047 5 31 10 1023 17 131071
def cc_30_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0x3d299e140ec26741038251b924d8146a09314998240bc265c102c2795934a80c5205270513024900c4605202410234 8 255 3 7 10 1023 17 131071
def cur_30 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_30_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_30_0 p) (Nat.blt p 32)
def f_30 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV4 m_30 g_30 ep_30 64 bds_30 (dagTraceF m_30 s_30 5 f_30) (cur_30 0) s_30 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_0 : treeBlockF 0 32 (dagCheckNodeV4 m_30 g_30 ep_30 bds_30 64 (dagTraceF m_30 s_30 5 f_30) cur_30) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_1 : treeBlockF 32 64 (dagCheckNodeV4 m_30 g_30 ep_30 bds_30 64 (dagTraceF m_30 s_30 5 f_30) cur_30) = true := by decide +kernel
theorem nj_30_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_30 g_30 ep_30 bds_30 64 (dagTraceF m_30 s_30 5 f_30) cur_30) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_30_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_30_1 h1 h2)
theorem nc_30 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_30 g_30 ep_30 bds_30 64 (dagTraceF m_30 s_30 5 f_30) cur_30) i = true := nj_30_1
theorem lb_30 : LowerBin m_30 s_30 g_30 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_30 kn_30 sub_30 gl_30 rc_30 nc_30

def m_31 : Nat := 0xcccc0000cccc
def s_31 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_31 : Nat := 0x44400000c4c
def ep_31 : Nat := 0x808000000000000000000000040000000400000040000000c0800000000000000000000044400000040
theorem epk_31 : ep_31 = edgePack m_31 g_31 := by decide +kernel
def bds_31 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_31 : KnownBin bds_31 := by intro b hb; simp [bds_31] at hb
theorem sub_31 : ∀ b ∈ bds_31, m_31 &&& b.1 = b.1 := by intro b hb; simp [bds_31] at hb
theorem gl_31 : ∀ b ∈ bds_31, canon b.1 g_31 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_31] at hb
def cur_31 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0xf 2 3 1 1 4 15 5 31
def f_31 : Nat → Nat × Nat := unpackForestF 0xf 1 4
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV4 m_31 g_31 ep_31 1 bds_31 (dagTraceF m_31 s_31 3 f_31) (cur_31 0) s_31 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31 : treeBlockF 0 1 (dagCheckNodeV4 m_31 g_31 ep_31 bds_31 1 (dagTraceF m_31 s_31 3 f_31) cur_31) = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_31 g_31 ep_31 bds_31 1 (dagTraceF m_31 s_31 3 f_31) cur_31) i = true := fun _ h1 h2 => treeBlockF_at nb_31 h1 h2
theorem lb_31 : LowerBin m_31 s_31 g_31 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_31 kn_31 sub_31 gl_31 rc_31 nc_31

def m_32 : Nat := 0x3333000033330000
def s_32 : List Nat := [0x1111000011110000, 0x303000003030000, 0x33000000330000, 0x33330000]
def g_32 : Nat := 0x113000013130000
def ep_32 : Nat := 0x1200000000000000000000000012000000000000010200000202000000000000000000000110000010100000
theorem epk_32 : ep_32 = edgePack m_32 g_32 := by decide +kernel
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_32 : KnownBin bds_32 := by
  intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_32 : ∀ b ∈ bds_32, m_32 &&& b.1 = b.1 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_32 : ∀ b ∈ bds_32, canon b.1 g_32 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_32 : Nat → List (Nat × Nat) := fun _ => []
def f_32 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV4 m_32 g_32 ep_32 0 bds_32 (dagTraceF m_32 s_32 4 f_32) (cur_32 0) s_32 4 = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_32 g_32 ep_32 bds_32 0 (dagTraceF m_32 s_32 4 f_32) cur_32 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_32 : LowerBin m_32 s_32 g_32 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_32 kn_32 sub_32 gl_32 rc_32 nc_32

def m_33 : Nat := 0xaaaa0000aaaa0000
def s_33 : List Nat := [0x2222000022220000, 0xa0a00000a0a0000, 0xaa000000aa0000, 0xaaaa0000]
def g_33 : Nat := 0x20000020a0000
def ep_33 : Nat := 0x20800000000000000000000000200000008000000020000020a000000020000020000000000000000000000
theorem epk_33 : ep_33 = edgePack m_33 g_33 := by decide +kernel
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
theorem kn_33 : KnownBin bds_33 := by
  intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_13
theorem sub_33 : ∀ b ∈ bds_33, m_33 &&& b.1 = b.1 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_33 : ∀ b ∈ bds_33, canon b.1 g_33 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_33 : Nat → List (Nat × Nat) := fun _ => []
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV4 m_33 g_33 ep_33 0 bds_33 (dagTraceF m_33 s_33 4 f_33) (cur_33 0) s_33 4 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_33 g_33 ep_33 bds_33 0 (dagTraceF m_33 s_33 4 f_33) cur_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_33 kn_33 sub_33 gl_33 rc_33 nc_33

def m_34 : Nat := 0x5555000055550000
def s_34 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_34 : Nat := 0x115000011150000
def ep_34 : Nat := 0x1000000000000000000000000014000000040000010400000004000001100000111000000000000000000000
theorem epk_34 : ep_34 = edgePack m_34 g_34 := by decide +kernel
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
theorem kn_34 : KnownBin bds_34 := by
  intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_6
theorem sub_34 : ∀ b ∈ bds_34, m_34 &&& b.1 = b.1 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_34 : ∀ b ∈ bds_34, canon b.1 g_34 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_34 : Nat → List (Nat × Nat) := fun _ => []
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV4 m_34 g_34 ep_34 0 bds_34 (dagTraceF m_34 s_34 4 f_34) (cur_34 0) s_34 4 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_34 g_34 ep_34 bds_34 0 (dagTraceF m_34 s_34 4 f_34) cur_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_34 kn_34 sub_34 gl_34 rc_34 nc_34

def m_35 : Nat := 0xff000000ff00
def s_35 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_35 : Nat := 0x150000001f00
def ep_35 : Nat := 0xa00000000000000000000000000000000000000040000000e0000001000000010000000150000001000
theorem epk_35 : ep_35 = edgePack m_35 g_35 := by decide +kernel
def bds_35 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_35 : KnownBin bds_35 := by intro b hb; simp [bds_35] at hb
theorem sub_35 : ∀ b ∈ bds_35, m_35 &&& b.1 = b.1 := by intro b hb; simp [bds_35] at hb
theorem gl_35 : ∀ b ∈ bds_35, canon b.1 g_35 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_35] at hb
def cur_35 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0xf 2 3 1 1 4 15 5 31
def f_35 : Nat → Nat × Nat := unpackForestF 0xf 1 4
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV4 m_35 g_35 ep_35 1 bds_35 (dagTraceF m_35 s_35 3 f_35) (cur_35 0) s_35 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35 : treeBlockF 0 1 (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 1 (dagTraceF m_35 s_35 3 f_35) cur_35) = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_35 g_35 ep_35 bds_35 1 (dagTraceF m_35 s_35 3 f_35) cur_35) i = true := fun _ h1 h2 => treeBlockF_at nb_35 h1 h2
theorem lb_35 : LowerBin m_35 s_35 g_35 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_35 kn_35 sub_35 gl_35 rc_35 nc_35

def m_36 : Nat := 0xff000000ff
def s_36 : List Nat := [0x5500000055, 0x3300000033, 0xf0000000f, 0xff]
def g_36 : Nat := 0x570000007f
def ep_36 : Nat := 0x2800000000000000000000000000000000000000020000000800000002000000200000005400000040
theorem epk_36 : ep_36 = edgePack m_36 g_36 := by decide +kernel
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
theorem kn_36 : KnownBin bds_36 := by
  intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_8
theorem sub_36 : ∀ b ∈ bds_36, m_36 &&& b.1 = b.1 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_36 : ∀ b ∈ bds_36, canon b.1 g_36 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_36 : Nat → List (Nat × Nat) := fun _ => []
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV4 m_36 g_36 ep_36 0 bds_36 (dagTraceF m_36 s_36 4 f_36) (cur_36 0) s_36 4 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_36 g_36 ep_36 bds_36 0 (dagTraceF m_36 s_36 4 f_36) cur_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_36 kn_36 sub_36 gl_36 rc_36 nc_36

def m_37 : Nat := 0xf0f00000f0f0
def s_37 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_37 : Nat := 0x105000001070
def ep_37 : Nat := 0x2000000000000000000000004000000060000000000000000000001000000010200000105000001040
theorem epk_37 : ep_37 = edgePack m_37 g_37 := by decide +kernel
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_37 : KnownBin bds_37 := by
  intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_37 : ∀ b ∈ bds_37, m_37 &&& b.1 = b.1 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_37 : ∀ b ∈ bds_37, canon b.1 g_37 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_37 : Nat → List (Nat × Nat) := fun _ => []
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV4 m_37 g_37 ep_37 0 bds_37 (dagTraceF m_37 s_37 4 f_37) (cur_37 0) s_37 4 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_37 g_37 ep_37 bds_37 0 (dagTraceF m_37 s_37 4 f_37) cur_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_37 kn_37 sub_37 gl_37 rc_37 nc_37

def m_38 : Nat := 0x333300003333
def s_38 : List Nat := [0x111100001111, 0x30300000303, 0x3300000033, 0x3333]
def g_38 : Nat := 0x111300001333
def ep_38 : Nat := 0x22000000000000000000000000200000020000000020000020000000000000000000000111000001000
theorem epk_38 : ep_38 = edgePack m_38 g_38 := by decide +kernel
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
theorem kn_38 : KnownBin bds_38 := by
  intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_7
theorem sub_38 : ∀ b ∈ bds_38, m_38 &&& b.1 = b.1 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_38 : ∀ b ∈ bds_38, canon b.1 g_38 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV4 m_38 g_38 ep_38 0 bds_38 (dagTraceF m_38 s_38 4 f_38) (cur_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_38 g_38 ep_38 bds_38 0 (dagTraceF m_38 s_38 4 f_38) cur_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_38 kn_38 sub_38 gl_38 rc_38 nc_38

def m_39 : Nat := 0xaaaa0000aaaa
def s_39 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_39 : Nat := 0x200000a2a
def ep_39 : Nat := 0xa28000000000000000000000002000000200000000200000a0800000002000000200000000000000000
theorem epk_39 : ep_39 = edgePack m_39 g_39 := by decide +kernel
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
theorem kn_39 : KnownBin bds_39 := by
  intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_7
theorem sub_39 : ∀ b ∈ bds_39, m_39 &&& b.1 = b.1 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_39 : ∀ b ∈ bds_39, canon b.1 g_39 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_39 : Nat → List (Nat × Nat) := fun _ => []
def f_39 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV4 m_39 g_39 ep_39 0 bds_39 (dagTraceF m_39 s_39 4 f_39) (cur_39 0) s_39 4 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_39 g_39 ep_39 bds_39 0 (dagTraceF m_39 s_39 4 f_39) cur_39 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_39 : LowerBin m_39 s_39 g_39 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_39 kn_39 sub_39 gl_39 rc_39 nc_39

def m_40 : Nat := 0x3300330033003300
def s_40 : List Nat := [0x1100110011001100, 0x300030003000300, 0x330000003300, 0x33003300]
def g_40 : Nat := 0x100110013001300
def ep_40 : Nat := 0x1200020000001000000000000000000000000000010000000200020000000000000000000100110010001000
theorem epk_40 : ep_40 = edgePack m_40 g_40 := by decide +kernel
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_40 : KnownBin bds_40 := by
  intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_40 : ∀ b ∈ bds_40, m_40 &&& b.1 = b.1 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_40 : ∀ b ∈ bds_40, canon b.1 g_40 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_40 : Nat → List (Nat × Nat) := fun _ => []
def f_40 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV4 m_40 g_40 ep_40 0 bds_40 (dagTraceF m_40 s_40 4 f_40) (cur_40 0) s_40 4 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_40 g_40 ep_40 bds_40 0 (dagTraceF m_40 s_40 4 f_40) cur_40 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_40 : LowerBin m_40 s_40 g_40 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_40 kn_40 sub_40 gl_40 rc_40 nc_40

def m_41 : Nat := 0xcc00cc00cc00cc
def s_41 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_41 : Nat := 0x40044000c004c
def ep_41 : Nat := 0x800080000004000000040000000000000000000040000000c000800000000000000000004004400000040
theorem epk_41 : ep_41 = edgePack m_41 g_41 := by decide +kernel
def bds_41 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_41 : KnownBin bds_41 := by intro b hb; simp [bds_41] at hb
theorem sub_41 : ∀ b ∈ bds_41, m_41 &&& b.1 = b.1 := by intro b hb; simp [bds_41] at hb
theorem gl_41 : ∀ b ∈ bds_41, canon b.1 g_41 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_41] at hb
def cur_41 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0xf 2 3 1 1 4 15 5 31
def f_41 : Nat → Nat × Nat := unpackForestF 0xf 1 4
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV4 m_41 g_41 ep_41 1 bds_41 (dagTraceF m_41 s_41 3 f_41) (cur_41 0) s_41 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41 : treeBlockF 0 1 (dagCheckNodeV4 m_41 g_41 ep_41 bds_41 1 (dagTraceF m_41 s_41 3 f_41) cur_41) = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_41 g_41 ep_41 bds_41 1 (dagTraceF m_41 s_41 3 f_41) cur_41) i = true := fun _ h1 h2 => treeBlockF_at nb_41 h1 h2
theorem lb_41 : LowerBin m_41 s_41 g_41 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_41 kn_41 sub_41 gl_41 rc_41 nc_41

def m_42 : Nat := 0xffff0000
def s_42 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_42 : Nat := 0x131f0000
def ep_42 : Nat := 0xc000000000000020e000000000000131000000000000010100000
theorem epk_42 : ep_42 = edgePack m_42 g_42 := by decide +kernel
def bds_42 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_42 : KnownBin bds_42 := by intro b hb; simp [bds_42] at hb
theorem sub_42 : ∀ b ∈ bds_42, m_42 &&& b.1 = b.1 := by intro b hb; simp [bds_42] at hb
theorem gl_42 : ∀ b ∈ bds_42, canon b.1 g_42 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_42] at hb
def cur_42 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0xf 2 3 1 1 4 15 5 31
def f_42 : Nat → Nat × Nat := unpackForestF 0xf 1 4
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV4 m_42 g_42 ep_42 1 bds_42 (dagTraceF m_42 s_42 3 f_42) (cur_42 0) s_42 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42 : treeBlockF 0 1 (dagCheckNodeV4 m_42 g_42 ep_42 bds_42 1 (dagTraceF m_42 s_42 3 f_42) cur_42) = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_42 g_42 ep_42 bds_42 1 (dagTraceF m_42 s_42 3 f_42) cur_42) i = true := fun _ h1 h2 => treeBlockF_at nb_42 h1 h2
theorem lb_42 : LowerBin m_42 s_42 g_42 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_42 kn_42 sub_42 gl_42 rc_42 nc_42

def m_43 : Nat := 0xffff
def s_43 : List Nat := [0x5555, 0x3333, 0xf0f, 0xff]
def g_43 : Nat := 0x1f7f
def ep_43 : Nat := 0x600000000000000e0800000000000010200000000000001040
theorem epk_43 : ep_43 = edgePack m_43 g_43 := by decide +kernel
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_43 : KnownBin bds_43 := by
  intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_43 : ∀ b ∈ bds_43, m_43 &&& b.1 = b.1 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_43 : ∀ b ∈ bds_43, canon b.1 g_43 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_43 : Nat → List (Nat × Nat) := fun _ => []
def f_43 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV4 m_43 g_43 ep_43 0 bds_43 (dagTraceF m_43 s_43 4 f_43) (cur_43 0) s_43 4 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_43 g_43 ep_43 bds_43 0 (dagTraceF m_43 s_43 4 f_43) cur_43 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_43 : LowerBin m_43 s_43 g_43 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_43 kn_43 sub_43 gl_43 rc_43 nc_43

def m_44 : Nat := 0xff00ff00
def s_44 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_44 : Nat := 0x13001f00
def ep_44 : Nat := 0xc0000000000000000000000000002000e0000000000130010000000000010001000
theorem epk_44 : ep_44 = edgePack m_44 g_44 := by decide +kernel
def bds_44 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_44 : KnownBin bds_44 := by intro b hb; simp [bds_44] at hb
theorem sub_44 : ∀ b ∈ bds_44, m_44 &&& b.1 = b.1 := by intro b hb; simp [bds_44] at hb
theorem gl_44 : ∀ b ∈ bds_44, canon b.1 g_44 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_44] at hb
def cur_44 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0xf 2 3 1 1 4 15 5 31
def f_44 : Nat → Nat × Nat := unpackForestF 0xf 1 4
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV4 m_44 g_44 ep_44 1 bds_44 (dagTraceF m_44 s_44 3 f_44) (cur_44 0) s_44 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44 : treeBlockF 0 1 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1 (dagTraceF m_44 s_44 3 f_44) cur_44) = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 1 (dagTraceF m_44 s_44 3 f_44) cur_44) i = true := fun _ h1 h2 => treeBlockF_at nb_44 h1 h2
theorem lb_44 : LowerBin m_44 s_44 g_44 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_44 kn_44 sub_44 gl_44 rc_44 nc_44

def m_45 : Nat := 0xff00ff
def s_45 : List Nat := [0x550055, 0x330033, 0xf000f, 0xff]
def g_45 : Nat := 0x1f007f
def ep_45 : Nat := 0x60000000000000000000000000000e000800000000001000200000000000100040
theorem epk_45 : ep_45 = edgePack m_45 g_45 := by decide +kernel
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
theorem kn_45 : KnownBin bds_45 := by
  intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_10
theorem sub_45 : ∀ b ∈ bds_45, m_45 &&& b.1 = b.1 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_45 : ∀ b ∈ bds_45, canon b.1 g_45 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_45 : Nat → List (Nat × Nat) := fun _ => []
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV4 m_45 g_45 ep_45 0 bds_45 (dagTraceF m_45 s_45 4 f_45) (cur_45 0) s_45 4 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_45 g_45 ep_45 bds_45 0 (dagTraceF m_45 s_45 4 f_45) cur_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin m_45 s_45 g_45 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_45 kn_45 sub_45 gl_45 rc_45 nc_45

def m_46 : Nat := 0xf0f0f0f0
def s_46 : List Nat := [0x50505050, 0x30303030, 0xf000f0, 0xf0f0]
def g_46 : Nat := 0x10101070
def ep_46 : Nat := 0x600000000000000060000000000000000000000000101010200000000010101040
theorem epk_46 : ep_46 = edgePack m_46 g_46 := by decide +kernel
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_46 : KnownBin bds_46 := by
  intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_46 : ∀ b ∈ bds_46, m_46 &&& b.1 = b.1 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_46 : ∀ b ∈ bds_46, canon b.1 g_46 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_46 : Nat → List (Nat × Nat) := fun _ => []
def f_46 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV4 m_46 g_46 ep_46 0 bds_46 (dagTraceF m_46 s_46 4 f_46) (cur_46 0) s_46 4 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_46 g_46 ep_46 bds_46 0 (dagTraceF m_46 s_46 4 f_46) cur_46 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_46 : LowerBin m_46 s_46 g_46 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_46 kn_46 sub_46 gl_46 rc_46 nc_46

def m_47 : Nat := 0xcccccccc
def s_47 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_47 : Nat := 0xc0c4c
def ep_47 : Nat := 0xc4000000000000c004000000000000c0c0800000000000000000000000000000040
theorem epk_47 : ep_47 = edgePack m_47 g_47 := by decide +kernel
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
theorem kn_47 : KnownBin bds_47 := by
  intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_12
theorem sub_47 : ∀ b ∈ bds_47, m_47 &&& b.1 = b.1 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_47 : ∀ b ∈ bds_47, canon b.1 g_47 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_47 : Nat → List (Nat × Nat) := fun _ => []
def f_47 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV4 m_47 g_47 ep_47 0 bds_47 (dagTraceF m_47 s_47 4 f_47) (cur_47 0) s_47 4 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_47 g_47 ep_47 bds_47 0 (dagTraceF m_47 s_47 4 f_47) cur_47 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_47 : LowerBin m_47 s_47 g_47 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_47 kn_47 sub_47 gl_47 rc_47 nc_47

def m_48 : Nat := 0xaaaaaaaa
def s_48 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_48 : Nat := 0x20a0a2a
def ep_48 : Nat := 0x820000000000008002000000000020a0a0800000000020000200000000000000000
theorem epk_48 : ep_48 = edgePack m_48 g_48 := by decide +kernel
def bds_48 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_48 : KnownBin bds_48 := by intro b hb; simp [bds_48] at hb
theorem sub_48 : ∀ b ∈ bds_48, m_48 &&& b.1 = b.1 := by intro b hb; simp [bds_48] at hb
theorem gl_48 : ∀ b ∈ bds_48, canon b.1 g_48 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_48] at hb
def cc_48_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xb41682b1560ac148a80d009c3382704e09c1382704648c1182304607c8f81f03a2740e81b1341680c841c001 0xf138749a360b1a048b8305ca226d212680893c40981c130d088602c2c12125308288304c1422040402249fa3ff91df28df4467893fb89dda4deb267512fa495c849df246e03f641db00dd6066a82f50159e09ca046381f100d8605c1026000f 11 2047 5 31 10 1023 17 131071
def cc_48_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb0b0b0b0b0949090909074707062606052494841404040404040242020202004 0x3d299e140ec26741038251b924d8146a09330719034c00c5e052c2616244a1a44ed02607928308ca64451210310014 8 255 3 7 10 1023 17 131071
def cur_48 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_48_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_48_0 p) (Nat.blt p 32)
def f_48 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c838c834053fbc18bc14053b0537b2440533052f052b97489740943c94300527814c814480188014052375387534043f682c6824043b04375d440433042f042b43484340413c413004272c4c2c442c2c2c240423214c2144041f144c1444041b041709240413000f 6 10
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

def m_49 : Nat := 0x55555555
def s_49 : List Nat := [0x11111111, 0x5050505, 0x550055, 0x5555]
def g_49 : Nat := 0x11151555
def ep_49 : Nat := 0x4400000000000040040000000000004040000000000111010000000000000000000
theorem epk_49 : ep_49 = edgePack m_49 g_49 := by decide +kernel
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
theorem kn_49 : KnownBin bds_49 := by
  intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_12
theorem sub_49 : ∀ b ∈ bds_49, m_49 &&& b.1 = b.1 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_49 : ∀ b ∈ bds_49, canon b.1 g_49 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_49 : Nat → List (Nat × Nat) := fun _ => []
def f_49 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV4 m_49 g_49 ep_49 0 bds_49 (dagTraceF m_49 s_49 4 f_49) (cur_49 0) s_49 4 = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_49 g_49 ep_49 bds_49 0 (dagTraceF m_49 s_49 4 f_49) cur_49 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_49 : LowerBin m_49 s_49 g_49 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_49 kn_49 sub_49 gl_49 rc_49 nc_49

def m_50 : Nat := 0xff000000ff000000
def s_50 : List Nat := [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000]
def g_50 : Nat := 0x100000013000000
def ep_50 : Nat := 0x1200000000000000000000000000000000000000010000000200000001000000130000000100000010000000
theorem epk_50 : ep_50 = edgePack m_50 g_50 := by decide +kernel
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_50 : KnownBin bds_50 := by
  intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_50 : ∀ b ∈ bds_50, m_50 &&& b.1 = b.1 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_50 : ∀ b ∈ bds_50, canon b.1 g_50 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_50 : Nat → List (Nat × Nat) := fun _ => []
def f_50 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV4 m_50 g_50 ep_50 0 bds_50 (dagTraceF m_50 s_50 4 f_50) (cur_50 0) s_50 4 = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_50 g_50 ep_50 bds_50 0 (dagTraceF m_50 s_50 4 f_50) cur_50 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_50 : LowerBin m_50 s_50 g_50 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_50 kn_50 sub_50 gl_50 rc_50 nc_50

def m_51 : Nat := 0xff000000ff0000
def s_51 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_51 : Nat := 0x170000001f0000
def ep_51 : Nat := 0x800000000000000000000000000000000000000060000000e000000120000001000000014000000100000
theorem epk_51 : ep_51 = edgePack m_51 g_51 := by decide +kernel
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_51 : KnownBin bds_51 := by
  intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_51 : ∀ b ∈ bds_51, m_51 &&& b.1 = b.1 := by intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_51 : ∀ b ∈ bds_51, canon b.1 g_51 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_51 : Nat → List (Nat × Nat) := fun _ => []
def f_51 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV4 m_51 g_51 ep_51 0 bds_51 (dagTraceF m_51 s_51 4 f_51) (cur_51 0) s_51 4 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_51 g_51 ep_51 bds_51 0 (dagTraceF m_51 s_51 4 f_51) cur_51 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_51 : LowerBin m_51 s_51 g_51 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_51 kn_51 sub_51 gl_51 rc_51 nc_51

def m_52 : Nat := 0xf000f000f000f0
def s_52 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_52 : Nat := 0x10005000100070
def ep_52 : Nat := 0x2000000040000000600000000000000000000000000000000000100000001000200010005000100040
theorem epk_52 : ep_52 = edgePack m_52 g_52 := by decide +kernel
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
theorem kn_52 : KnownBin bds_52 := by
  intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_10
theorem sub_52 : ∀ b ∈ bds_52, m_52 &&& b.1 = b.1 := by intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_52 : ∀ b ∈ bds_52, canon b.1 g_52 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_52 : Nat → List (Nat × Nat) := fun _ => []
def f_52 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV4 m_52 g_52 ep_52 0 bds_52 (dagTraceF m_52 s_52 4 f_52) (cur_52 0) s_52 4 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_52 g_52 ep_52 bds_52 0 (dagTraceF m_52 s_52 4 f_52) cur_52 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_52 : LowerBin m_52 s_52 g_52 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_52 kn_52 sub_52 gl_52 rc_52 nc_52

def m_53 : Nat := 0xf0f00000f0f0000
def s_53 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_53 : Nat := 0x1070000030f0000
def ep_53 : Nat := 0x2080000000000000000000000060000000c0000000000000000000001020000030000000104000000000000
theorem epk_53 : ep_53 = edgePack m_53 g_53 := by decide +kernel
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
theorem kn_53 : KnownBin bds_53 := by
  intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_11
theorem sub_53 : ∀ b ∈ bds_53, m_53 &&& b.1 = b.1 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_53 : ∀ b ∈ bds_53, canon b.1 g_53 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_53 : Nat → List (Nat × Nat) := fun _ => []
def f_53 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV4 m_53 g_53 ep_53 0 bds_53 (dagTraceF m_53 s_53 4 f_53) (cur_53 0) s_53 4 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_53 g_53 ep_53 bds_53 0 (dagTraceF m_53 s_53 4 f_53) cur_53 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_53 : LowerBin m_53 s_53 g_53 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_53 kn_53 sub_53 gl_53 rc_53 nc_53

def m_54 : Nat := 0x5050a0a05050a0a0
def s_54 : List Nat := [0xa0a00000a0a0, 0x1010202010102020, 0x5000a0005000a0, 0x5050a0a0]
def g_54 : Nat := 0x10000010100020
def ep_54 : Nat := 0x1000002000000000000000000010000000000020000000000000000000100000101000200000000000000000
theorem epk_54 : ep_54 = edgePack m_54 g_54 := by decide +kernel
def bds_54 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_54 : KnownBin bds_54 := by intro b hb; simp [bds_54] at hb
theorem sub_54 : ∀ b ∈ bds_54, m_54 &&& b.1 = b.1 := by intro b hb; simp [bds_54] at hb
theorem gl_54 : ∀ b ∈ bds_54, canon b.1 g_54 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_54] at hb
def cur_54 : Nat → List (Nat × Nat) := unpackCursorV4 0x1a2d58952244890e8701 0x393c3060e4c08181a30227928fa119313e526480f8419000f 7 127 3 7 10 1023 15 32767
def f_54 : Nat → Nat × Nat := unpackForestF 0xc7c632e9814f8a6443e51824f086400f 3 10
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV4 m_54 g_54 ep_54 10 bds_54 (dagTraceF m_54 s_54 4 f_54) (cur_54 0) s_54 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54 : treeBlockF 0 10 (dagCheckNodeV4 m_54 g_54 ep_54 bds_54 10 (dagTraceF m_54 s_54 4 f_54) cur_54) = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 10 → (dagCheckNodeV4 m_54 g_54 ep_54 bds_54 10 (dagTraceF m_54 s_54 4 f_54) cur_54) i = true := fun _ h1 h2 => treeBlockF_at nb_54 h1 h2
theorem lb_54 : LowerBin m_54 s_54 g_54 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_54 kn_54 sub_54 gl_54 rc_54 nc_54

def m_55 : Nat := 0x1111111122222222
def s_55 : List Nat := [0x22222222, 0x101010102020202, 0x11001100220022, 0x111100002222]
def g_55 : Nat := 0x111111102020222
def ep_55 : Nat := 0x1000000000200010000000000020010000000202020000000000000000000000000000000000
theorem epk_55 : ep_55 = edgePack m_55 g_55 := by decide +kernel
def bds_55 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_55 : KnownBin bds_55 := by intro b hb; simp [bds_55] at hb
theorem sub_55 : ∀ b ∈ bds_55, m_55 &&& b.1 = b.1 := by intro b hb; simp [bds_55] at hb
theorem gl_55 : ∀ b ∈ bds_55, canon b.1 g_55 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_55] at hb
def cur_55 : Nat → List (Nat × Nat) := unpackCursorV4 0x1a2d58b12a44874e0701 0x31244050c490c142234326928ea11b393a526c40e841b000f 7 127 3 7 10 1023 15 32767
def f_55 : Nat → Nat × Nat := unpackForestF 0xc7463629d6490a6ce3469a10e886c00f 3 10
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV4 m_55 g_55 ep_55 10 bds_55 (dagTraceF m_55 s_55 4 f_55) (cur_55 0) s_55 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55 : treeBlockF 0 10 (dagCheckNodeV4 m_55 g_55 ep_55 bds_55 10 (dagTraceF m_55 s_55 4 f_55) cur_55) = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 10 → (dagCheckNodeV4 m_55 g_55 ep_55 bds_55 10 (dagTraceF m_55 s_55 4 f_55) cur_55) i = true := fun _ h1 h2 => treeBlockF_at nb_55 h1 h2
theorem lb_55 : LowerBin m_55 s_55 g_55 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_55 kn_55 sub_55 gl_55 rc_55 nc_55

def m_56 : Nat := 0x2222222222222222
def s_56 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_56 : Nat := 0x2000202020222
def ep_56 : Nat := 0x200022000000000000000200002000200000020000200020202020000000000000000000000000000000000
theorem epk_56 : ep_56 = edgePack m_56 g_56 := by decide +kernel
def bds_56 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
theorem kn_56 : KnownBin bds_56 := by
  intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_7
theorem sub_56 : ∀ b ∈ bds_56, m_56 &&& b.1 = b.1 := by intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_56 : ∀ b ∈ bds_56, canon b.1 g_56 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_56 : Nat → List (Nat × Nat) := fun _ => []
def f_56 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV4 m_56 g_56 ep_56 0 bds_56 (dagTraceF m_56 s_56 4 f_56) (cur_56 0) s_56 4 = true := by decide +kernel
theorem nc_56 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_56 g_56 ep_56 bds_56 0 (dagTraceF m_56 s_56 4 f_56) cur_56 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_56 : LowerBin m_56 s_56 g_56 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_56 kn_56 sub_56 gl_56 rc_56 nc_56

def m_57 : Nat := 0xa0a0a0a0a0a0a0a
def s_57 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_57 : Nat := 0x20002020a0a0a
def ep_57 : Nat := 0x2080a0800000000000008000002000200080000000000000000000000020002020000000000000000000000
theorem epk_57 : ep_57 = edgePack m_57 g_57 := by decide +kernel
def bds_57 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
theorem kn_57 : KnownBin bds_57 := by
  intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_13
theorem sub_57 : ∀ b ∈ bds_57, m_57 &&& b.1 = b.1 := by intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_57 : ∀ b ∈ bds_57, canon b.1 g_57 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_57 : Nat → List (Nat × Nat) := fun _ => []
def f_57 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV4 m_57 g_57 ep_57 0 bds_57 (dagTraceF m_57 s_57 4 f_57) (cur_57 0) s_57 4 = true := by decide +kernel
theorem nc_57 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_57 g_57 ep_57 bds_57 0 (dagTraceF m_57 s_57 4 f_57) cur_57 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_57 : LowerBin m_57 s_57 g_57 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_57 kn_57 sub_57 gl_57 rc_57 nc_57

def m_58 : Nat := 0x5a5a00005a5a
def s_58 : List Nat := [0xa0a00000a0a, 0x121200001212, 0x5a0000005a, 0x5a5a]
def g_58 : Nat := 0x105200001a5a
def ep_58 : Nat := 0xa0800000000000000000000004200000040000000000000000000001002000010000000000000000000
theorem epk_58 : ep_58 = edgePack m_58 g_58 := by decide +kernel
def bds_58 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_58 : KnownBin bds_58 := by intro b hb; simp [bds_58] at hb
theorem sub_58 : ∀ b ∈ bds_58, m_58 &&& b.1 = b.1 := by intro b hb; simp [bds_58] at hb
theorem gl_58 : ∀ b ∈ bds_58, canon b.1 g_58 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_58] at hb
def cc_58_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xec1d07a0686d0198720e40c4388300d65ac148a905209c5382704e0944f99f03e07c0f81f03e07c0d901d001 0xf134408e8fa36344b8712d3a0b4e02534070803c1e0b0582c1c4f0b84c2c110a82c28090782c180507834160506034160b0903d220d4802e1c0b4681d14054284c08110183c040d24a3f8c8ee1a37848ce093f804edf9376e4cda12f5e4ad61275648d503f520ed4037460cd102f360b8c82b3009c982312088401f0e06c30170204c000f 11 2047 5 31 10 1023 18 262143
def cc_58_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc2c0b9b8b8b8b18d88816b686868684c48483330303030303030301409080100 0x3d259c814f49a724d3e489e13cec9a740638028f02cd9266a911d079994cc8a2620630029703cb418380b270793034941648090e0610814 8 255 3 7 10 1023 17 131071
def cc_58_2 : Nat → List (Nat × Nat) := unpackCursorV4 0x183060c112039468100b1020401 0x9a9c4c4d2587128344216484a23a48803c8a2644100f858f930 7 127 3 7 9 511 17 131071
def cur_58 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_58_2 (Nat.sub p 64)) (cc_58_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_58_0 p) (Nat.blt p 32)
def f_58 : Nat → Nat × Nat := unpackForestF 0x252712934941c4a0d00c7f1d288e92018ee20991040031b818cc0a7e053b029bb8911ea68e13c709a38061ca68e0140299b5931ac88052f60a6305118030c0140295ad0f1686005270291810fc08760437481e240d1205890240219810bd0828723a391b1e4d0e05a702502171a07008560427282614110a058502402118a0f4506a282e1e1a0a0b4503a2c3416160a0540844041f020d8105c10980844041e020d00826000f 7 10
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV4 m_58 g_58 ep_58 78 bds_58 (dagTraceF m_58 s_58 5 f_58) (cur_58 0) s_58 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_0 : treeBlockF 0 32 (dagCheckNodeV4 m_58 g_58 ep_58 bds_58 78 (dagTraceF m_58 s_58 5 f_58) cur_58) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_1 : treeBlockF 32 64 (dagCheckNodeV4 m_58 g_58 ep_58 bds_58 78 (dagTraceF m_58 s_58 5 f_58) cur_58) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_2 : treeBlockF 64 78 (dagCheckNodeV4 m_58 g_58 ep_58 bds_58 78 (dagTraceF m_58 s_58 5 f_58) cur_58) = true := by decide +kernel
theorem nj_58_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_58 g_58 ep_58 bds_58 78 (dagTraceF m_58 s_58 5 f_58) cur_58) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_58_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_58_1 h1 h2)
theorem nj_58_2 : ∀ i, 0 ≤ i → i < 78 → (dagCheckNodeV4 m_58 g_58 ep_58 bds_58 78 (dagTraceF m_58 s_58 5 f_58) cur_58) i = true := block_join nj_58_1 (fun _ h1 h2 => treeBlockF_at nb_58_2 h1 h2)
theorem nc_58 : ∀ i, 0 ≤ i → i < 78 → (dagCheckNodeV4 m_58 g_58 ep_58 bds_58 78 (dagTraceF m_58 s_58 5 f_58) cur_58) i = true := nj_58_2
theorem lb_58 : LowerBin m_58 s_58 g_58 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_58 kn_58 sub_58 gl_58 rc_58 nc_58

def m_59 : Nat := 0x5a005a005a005a00
def s_59 : List Nat := [0xa000a000a000a00, 0x1200120012001200, 0x5a0000005a00, 0x5a005a00]
def g_59 : Nat := 0x100012001a00
def ep_59 : Nat := 0x12000a0000001000000008000000000000000000000000000000000000001000120010000000000000000000
theorem epk_59 : ep_59 = edgePack m_59 g_59 := by decide +kernel
def bds_59 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_59 : KnownBin bds_59 := by intro b hb; simp [bds_59] at hb
theorem sub_59 : ∀ b ∈ bds_59, m_59 &&& b.1 = b.1 := by intro b hb; simp [bds_59] at hb
theorem gl_59 : ∀ b ∈ bds_59, canon b.1 g_59 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_59] at hb
def cur_59 : Nat → List (Nat × Nat) := unpackCursorV4 0xcc61 0x92952100f 4 15 2 3 9 511 12 4095
def f_59 : Nat → Nat × Nat := unpackForestF 0x329c840f 1 9
set_option maxHeartbeats 0 in
theorem rc_59 : dagCheckRootsV4 m_59 g_59 ep_59 3 bds_59 (dagTraceF m_59 s_59 4 f_59) (cur_59 0) s_59 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59 : treeBlockF 0 3 (dagCheckNodeV4 m_59 g_59 ep_59 bds_59 3 (dagTraceF m_59 s_59 4 f_59) cur_59) = true := by decide +kernel
theorem nc_59 : ∀ i, 0 ≤ i → i < 3 → (dagCheckNodeV4 m_59 g_59 ep_59 bds_59 3 (dagTraceF m_59 s_59 4 f_59) cur_59) i = true := fun _ h1 h2 => treeBlockF_at nb_59 h1 h2
theorem lb_59 : LowerBin m_59 s_59 g_59 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_59 kn_59 sub_59 gl_59 rc_59 nc_59

def m_60 : Nat := 0x50a050a050a050a0
def s_60 : List Nat := [0xa000a000a000a0, 0x1020102010201020, 0x50a0000050a0, 0x50a050a0]
def g_60 : Nat := 0x100010001020
def ep_60 : Nat := 0x1000002000001000000000200000000000000000000000000000000000001000100010200000000000000000
theorem epk_60 : ep_60 = edgePack m_60 g_60 := by decide +kernel
def bds_60 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_60 : KnownBin bds_60 := by intro b hb; simp [bds_60] at hb
theorem sub_60 : ∀ b ∈ bds_60, m_60 &&& b.1 = b.1 := by intro b hb; simp [bds_60] at hb
theorem gl_60 : ∀ b ∈ bds_60, canon b.1 g_60 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_60] at hb
def cur_60 : Nat → List (Nat × Nat) := unpackCursorV4 0x16ac58b12a44890e8701 0x31303060c8f08181a3c226128fa119393e526480f8419000f 7 127 3 7 10 1023 15 32767
def f_60 : Nat → Nat × Nat := unpackForestF 0xc7c63229f68f0a6443e51e24c086400f 3 10
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsV4 m_60 g_60 ep_60 10 bds_60 (dagTraceF m_60 s_60 4 f_60) (cur_60 0) s_60 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60 : treeBlockF 0 10 (dagCheckNodeV4 m_60 g_60 ep_60 bds_60 10 (dagTraceF m_60 s_60 4 f_60) cur_60) = true := by decide +kernel
theorem nc_60 : ∀ i, 0 ≤ i → i < 10 → (dagCheckNodeV4 m_60 g_60 ep_60 bds_60 10 (dagTraceF m_60 s_60 4 f_60) cur_60) i = true := fun _ h1 h2 => treeBlockF_at nb_60 h1 h2
theorem lb_60 : LowerBin m_60 s_60 g_60 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_60 kn_60 sub_60 gl_60 rc_60 nc_60

def m_61 : Nat := 0xaaaaaaaaaaaaaaaa
def s_61 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_61 : Nat := 0x20002020a0a2a
def ep_61 : Nat := 0x2080a280000000000000820000200020008002000020002020a0a0800020002020000200000000000000000
theorem epk_61 : ep_61 = edgePack m_61 g_61 := by decide +kernel
def bds_61 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8), (m_48, s_48, 6, g_48), (m_13, s_13, 4, g_13), (m_56, s_56, 5, g_56), (m_33, s_33, 5, g_33), (m_18, s_18, 5, g_18), (m_7, s_7, 4, g_7)]
theorem kn_61 : KnownBin bds_61 := by
  intro b hb; simp only [bds_61, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_8
  · exact lb_48
  · exact lb_13
  · exact lb_56
  · exact lb_33
  · exact lb_18
  · exact lb_7
theorem sub_61 : ∀ b ∈ bds_61, m_61 &&& b.1 = b.1 := by intro b hb; simp only [bds_61, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_61 : ∀ b ∈ bds_61, canon b.1 g_61 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_61, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_61 : Nat → List (Nat × Nat) := unpackCursorV4 0xb807fd7e07e05d158258037103a001 0x2c5d3c5a2c562c552b5e2b5d2b4e3b4d3a59625182395a3129592951293a29392938693629311859185118491841183d183918351831181918113c5964513b5a3342524e2a4a2a465a423a3d185918511831182d18291825182118113a542a3433522b4a225e3a5a3a565a522a3d292a2928184918411831182d18291825182118112b4f3b4b2b4773433a4b42432a3b1233294b2943293b2933184f184b18471843183f183b18371833182f1823181f181918131811001f 12 4095 5 31 11 2047 16 65535
def f_61 : Nat → Nat × Nat := unpackForestF 0x42391686b1455270a4326a44978519801f 4 11
set_option maxHeartbeats 0 in
theorem rc_61 : dagCheckRootsV4 m_61 g_61 ep_61 9 bds_61 (dagTraceF m_61 s_61 7 f_61) (cur_61 0) s_61 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61 : treeBlockF 0 9 (dagCheckNodeV4 m_61 g_61 ep_61 bds_61 9 (dagTraceF m_61 s_61 7 f_61) cur_61) = true := by decide +kernel
theorem nc_61 : ∀ i, 0 ≤ i → i < 9 → (dagCheckNodeV4 m_61 g_61 ep_61 bds_61 9 (dagTraceF m_61 s_61 7 f_61) cur_61) i = true := fun _ h1 h2 => treeBlockF_at nb_61 h1 h2
theorem lb_61 : LowerBin m_61 s_61 g_61 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_61 kn_61 sub_61 gl_61 rc_61 nc_61

def m_62 : Nat := 0x5555555555555555
def s_62 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_62 : Nat := 0x115155511151555
def ep_62 : Nat := 0x1000000000001440000004400014004000040040010404000004040001101000111010000000000000000000
theorem epk_62 : ep_62 = edgePack m_62 g_62 := by decide +kernel
def bds_62 : List (Nat × List Nat × Nat × Nat) := [(m_29, s_29, 7, g_29)]
theorem kn_62 : KnownBin bds_62 := by
  intro b hb; simp only [bds_62, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_29
theorem sub_62 : ∀ b ∈ bds_62, m_62 &&& b.1 = b.1 := by intro b hb; simp only [bds_62, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_62 : ∀ b ∈ bds_62, canon b.1 g_62 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_62, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_62 : Nat → List (Nat × Nat) := fun _ => []
def f_62 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_62 : dagCheckRootsV4 m_62 g_62 ep_62 0 bds_62 (dagTraceF m_62 s_62 7 f_62) (cur_62 0) s_62 7 = true := by decide +kernel
theorem nc_62 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_62 g_62 ep_62 bds_62 0 (dagTraceF m_62 s_62 7 f_62) cur_62 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_62 : LowerBin m_62 s_62 g_62 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_62 kn_62 sub_62 gl_62 rc_62 nc_62

def m_63 : Nat := 0xff00ff00ff00ff00
def s_63 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_63 : Nat := 0x100150013001f00
def ep_63 : Nat := 0x12000a000000140000000c0000000000000000000100040002000e0001001000130010000100150010001000
theorem epk_63 : ep_63 = edgePack m_63 g_63 := by decide +kernel
def bds_63 : List (Nat × List Nat × Nat × Nat) := [(m_50, s_50, 5, g_50), (m_0, s_0, 4, g_0), (m_20, s_20, 5, g_20), (m_44, s_44, 4, g_44), (m_2, s_2, 4, g_2), (m_35, s_35, 4, g_35), (m_15, s_15, 5, g_15), (m_59, s_59, 5, g_59)]
theorem kn_63 : KnownBin bds_63 := by
  intro b hb; simp only [bds_63, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_50
  · exact lb_0
  · exact lb_20
  · exact lb_44
  · exact lb_2
  · exact lb_35
  · exact lb_15
  · exact lb_59
theorem sub_63 : ∀ b ∈ bds_63, m_63 &&& b.1 = b.1 := by intro b hb; simp only [bds_63, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_63 : ∀ b ∈ bds_63, canon b.1 g_63 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_63, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_63_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x828505020a03fc672b4e309c6033d46684cd019a0320558aeb1015c1a7514e808c451411ecf3d807908c6b18c025b04a046ca0d411a8021500300001 0x1a44700904b4970d047a4d1291429290e4844c59791447b5d12d684b5612d544a5e1e975d24e069281a461a9084a3e128f4592d1649428390a0c4382d120a828290a0a078260e095b0240a08428480e111935e12d684b5660d481b4e1ad341a4a069241a461a9041a36068d4194d06514193d064d4383d0a0e438350a0c44a44504901b4e50d086a3d068d419210717964521ad341b4a06d181b45549784a5a129586a52069386a4d068f81a3d064b4192a1a49819254c490382d0a0a438250a084495c0e170285006d341b4906d141b41169351249409145a41125584946064d8592e0e13428490e11428410a064e25e129684a56169481a4e069281a4606908595e06538593616498382d0a0a438250a08458150a0a0382416d784b5a12d58c35206d381b4a06d181b4206518593e164b8383d0a0e438350a0c4594c061304b5e0ed684b560ed481b4e0ad343a3d288e492350e8c4193d064d4285a0e158184a0612418460a1041836060d4382e0a0884a5e0e9684a560e948724e069281a460e9082a3e0a8f4392d16494385e0a148384e0a108283a0a0e438360a0c438260a094281a0e05859240ed784b5a0ed584b520ed381b4a06d1853420a8f82a3d164f439350a16838560e0f8283d0e0b828290a08828210a4903a5e129683a56129481a4e069281a46069083a3e0c8e83a36088c81946164f8292e0a16838560e0f828320a0641b4f12d2c1b4784d0df24f1292c4a476890d723f068ec1a37488ccf14f1251c193f064dcd12f2c49c484f0a12c48470a10c803f060ec18370a0cc602f0a0ac40270a08c281b0405c001f 15 32767 6 63 11 2047 18 262143
def cc_63_1 : Nat → List (Nat × Nat) := unpackCursorV4 0x700ccabf160816 0x6d404b40164f0383c0a0c01c5d131681c56071541b5e06d741b4e12d344a59789441a4958905823d8c8e622351a8c4194d06514193d064d4485d1215418490a104383d0a0e438350a0c45934131787c5d06d36034906d158341129684a59129587a51129184a451653459451217448550e13428490e11428410a0a42821 11 2047 5 31 11 2047 18 262143
def cur_63 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_63_1 (Nat.sub p 32)) (cc_63_0 p) (Nat.blt p 32)
def f_63 : Nat → Nat × Nat := unpackForestF 0x891cc48d4168703490527b7145b49ce3416c120290d86bcc352051fa714934bca3424c92028cd0492824504a79c978125e63520493928e4946a083f1d27020bc56840827091d048c8102e001f 6 11
set_option maxHeartbeats 0 in
theorem rc_63 : dagCheckRootsV4 m_63 g_63 ep_63 36 bds_63 (dagTraceF m_63 s_63 7 f_63) (cur_63 0) s_63 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_0 : treeBlockF 0 32 (dagCheckNodeV4 m_63 g_63 ep_63 bds_63 36 (dagTraceF m_63 s_63 7 f_63) cur_63) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_1 : treeBlockF 32 36 (dagCheckNodeV4 m_63 g_63 ep_63 bds_63 36 (dagTraceF m_63 s_63 7 f_63) cur_63) = true := by decide +kernel
theorem nj_63_1 : ∀ i, 0 ≤ i → i < 36 → (dagCheckNodeV4 m_63 g_63 ep_63 bds_63 36 (dagTraceF m_63 s_63 7 f_63) cur_63) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_63_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_63_1 h1 h2)
theorem nc_63 : ∀ i, 0 ≤ i → i < 36 → (dagCheckNodeV4 m_63 g_63 ep_63 bds_63 36 (dagTraceF m_63 s_63 7 f_63) cur_63) i = true := nj_63_1
theorem lb_63 : LowerBin m_63 s_63 g_63 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_63 kn_63 sub_63 gl_63 rc_63 nc_63

def m_64 : Nat := 0xf0f0f0f0f0f0f0f0
def s_64 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_64 : Nat := 0x10105010101070
def ep_64 : Nat := 0x1000002000001040000000600010004000000060000000000000000000101000101010200010105010101040
theorem epk_64 : ep_64 = edgePack m_64 g_64 := by decide +kernel
def bds_64 : List (Nat × List Nat × Nat × Nat) := [(m_30, s_30, 6, g_30), (m_52, s_52, 5, g_52), (m_46, s_46, 5, g_46), (m_37, s_37, 5, g_37), (m_24, s_24, 5, g_24), (m_54, s_54, 5, g_54), (m_28, s_28, 5, g_28), (m_10, s_10, 4, g_10), (m_1, s_1, 4, g_1)]
theorem kn_64 : KnownBin bds_64 := by
  intro b hb; simp only [bds_64, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_30
  · exact lb_52
  · exact lb_46
  · exact lb_37
  · exact lb_24
  · exact lb_54
  · exact lb_28
  · exact lb_10
  · exact lb_1
theorem sub_64 : ∀ b ∈ bds_64, m_64 &&& b.1 = b.1 := by intro b hb; simp only [bds_64, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_64 : ∀ b ∈ bds_64, canon b.1 g_64 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_64, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_64 : Nat → List (Nat × Nat) := unpackCursorV4 0xd00a18a007186a3643640339038001 0x1ebadd687ab0f551cbc397471f363d1a7284c4e96c1293a4ab48461ca431285b10a9214a428784c5094a1224213cbab968f2b1e553c7c68c8eaf1d5d627c34e869b2d323a5cb4b4e14a421283ab06920ca418582c5054a0a24113c6874d0a1a0e341a4850907af23523cbc6948f1e8e3a1c6c38d471a115e6ab4d5596a90d3e3a7a34b8696943d186a50b4a12941d483250552088e4f6c96391dd219d4f6a96751d4a19d2f1a56349c491944f4896511d221942f1856309d211941f3836505d209801f 12 4095 5 31 10 1023 15 32767
def f_64 : Nat → Nat × Nat := unpackForestF 0x2129190d93e150cb52294895e148c01f 4 10
set_option maxHeartbeats 0 in
theorem rc_64 : dagCheckRootsV4 m_64 g_64 ep_64 9 bds_64 (dagTraceF m_64 s_64 7 f_64) (cur_64 0) s_64 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64 : treeBlockF 0 9 (dagCheckNodeV4 m_64 g_64 ep_64 bds_64 9 (dagTraceF m_64 s_64 7 f_64) cur_64) = true := by decide +kernel
theorem nc_64 : ∀ i, 0 ≤ i → i < 9 → (dagCheckNodeV4 m_64 g_64 ep_64 bds_64 9 (dagTraceF m_64 s_64 7 f_64) cur_64) i = true := fun _ h1 h2 => treeBlockF_at nb_64 h1 h2
theorem lb_64 : LowerBin m_64 s_64 g_64 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_64 kn_64 sub_64 gl_64 rc_64 nc_64

def m_65 : Nat := 0x3333333333333333
def s_65 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_65 : Nat := 0x113111313131333
def ep_65 : Nat := 0x1200022000001000000000200012000200000020010200020202020000000000000000000110111010101000
theorem epk_65 : ep_65 = edgePack m_65 g_65 := by decide +kernel
def bds_65 : List (Nat × List Nat × Nat × Nat) := [(m_30, s_30, 6, g_30), (m_27, s_27, 5, g_27), (m_40, s_40, 5, g_40), (m_32, s_32, 5, g_32), (m_38, s_38, 5, g_38), (m_56, s_56, 5, g_56), (m_55, s_55, 5, g_55), (m_0, s_0, 4, g_0), (m_7, s_7, 4, g_7)]
theorem kn_65 : KnownBin bds_65 := by
  intro b hb; simp only [bds_65, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_30
  · exact lb_27
  · exact lb_40
  · exact lb_32
  · exact lb_38
  · exact lb_56
  · exact lb_55
  · exact lb_0
  · exact lb_7
theorem sub_65 : ∀ b ∈ bds_65, m_65 &&& b.1 = b.1 := by intro b hb; simp only [bds_65, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_65 : ∀ b ∈ bds_65, canon b.1 g_65 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_65, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_65 : Nat → List (Nat × Nat) := unpackCursorV4 0xd00a18a007187006a3643339038001 0x2c5e2c5d5a5e2a5d5a4e2a492a422a41895e495d495c39594955795239513950292d4925805d185968551851282d30251c5e1c5d625d2a596a552a51695e495d495c39594955695239513950585e185d584e184918421841182a2026181a48161a50395018502a50295038505b5e435a6b565b522a5a32561a3e1a3d493d39394935393139292921185a2056283e183d282e1829182218211820381e18125a4f2a4b72472a43494f394b49473943292f392b49272923584f184b50471843282f182b10271823381f181b48171813001f 12 4095 5 31 11 2047 16 65535
def f_65 : Nat → Nat × Nat := unpackForestF 0x205d191da5d111cb5a2958856109c01f 4 10
set_option maxHeartbeats 0 in
theorem rc_65 : dagCheckRootsV4 m_65 g_65 ep_65 9 bds_65 (dagTraceF m_65 s_65 7 f_65) (cur_65 0) s_65 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65 : treeBlockF 0 9 (dagCheckNodeV4 m_65 g_65 ep_65 bds_65 9 (dagTraceF m_65 s_65 7 f_65) cur_65) = true := by decide +kernel
theorem nc_65 : ∀ i, 0 ≤ i → i < 9 → (dagCheckNodeV4 m_65 g_65 ep_65 bds_65 9 (dagTraceF m_65 s_65 7 f_65) cur_65) i = true := fun _ h1 h2 => treeBlockF_at nb_65 h1 h2
theorem lb_65 : LowerBin m_65 s_65 g_65 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_65 kn_65 sub_65 gl_65 rc_65 nc_65

def m_66 : Nat := 0xcccccccccccccccc
def s_66 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_66 : Nat := 0x40444000c0c4c
def ep_66 : Nat := 0x808080000044000000c4000040040000c004000040400000c0c0800000000000000000004044400000040
theorem epk_66 : ep_66 = edgePack m_66 g_66 := by decide +kernel
def bds_66 : List (Nat × List Nat × Nat × Nat) := [(m_26, s_26, 5, g_26), (m_12, s_12, 4, g_12), (m_41, s_41, 4, g_41), (m_31, s_31, 4, g_31)]
theorem kn_66 : KnownBin bds_66 := by
  intro b hb; simp only [bds_66, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_26
  · exact lb_12
  · exact lb_41
  · exact lb_31
theorem sub_66 : ∀ b ∈ bds_66, m_66 &&& b.1 = b.1 := by intro b hb; simp only [bds_66, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_66 : ∀ b ∈ bds_66, canon b.1 g_66 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_66, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cur_66 : Nat → List (Nat × Nat) := unpackCursorV4 0x421840f89e0bc0704d841d001 0x30931287490c1464f153458d0f4f3d2cf473d0ce4f392ce47390d63fe8ed637a8ccd4f352cd47350dd3f84edd3744cdd2f54ad527248cc4630f801f 11 2047 5 31 10 1023 14 16383
def f_66 : Nat → Nat × Nat := unpackForestF 0x31de4a0c6653b69e14cca4601f 3 10
set_option maxHeartbeats 0 in
theorem rc_66 : dagCheckRootsV4 m_66 g_66 ep_66 8 bds_66 (dagTraceF m_66 s_66 6 f_66) (cur_66 0) s_66 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66 : treeBlockF 0 8 (dagCheckNodeV4 m_66 g_66 ep_66 bds_66 8 (dagTraceF m_66 s_66 6 f_66) cur_66) = true := by decide +kernel
theorem nc_66 : ∀ i, 0 ≤ i → i < 8 → (dagCheckNodeV4 m_66 g_66 ep_66 bds_66 8 (dagTraceF m_66 s_66 6 f_66) cur_66) i = true := fun _ h1 h2 => treeBlockF_at nb_66 h1 h2
theorem lb_66 : LowerBin m_66 s_66 g_66 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_66 kn_66 sub_66 gl_66 rc_66 nc_66

def m_67 : Nat := 0xff00ff00ff00ff
def s_67 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_67 : Nat := 0x170057001f007f
def ep_67 : Nat := 0x800280000004000000060000000000000000000060002000e000800120002001000200014005400100040
theorem epk_67 : ep_67 = edgePack m_67 g_67 := by decide +kernel
def bds_67 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8), (m_10, s_10, 4, g_10), (m_45, s_45, 5, g_45), (m_23, s_23, 5, g_23), (m_51, s_51, 5, g_51), (m_41, s_41, 4, g_41), (m_9, s_9, 4, g_9)]
theorem kn_67 : KnownBin bds_67 := by
  intro b hb; simp only [bds_67, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_8
  · exact lb_10
  · exact lb_45
  · exact lb_23
  · exact lb_51
  · exact lb_41
  · exact lb_9
theorem sub_67 : ∀ b ∈ bds_67, m_67 &&& b.1 = b.1 := by intro b hb; simp only [bds_67, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_67 : ∀ b ∈ bds_67, canon b.1 g_67 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_67, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_67 : Nat → List (Nat × Nat) := unpackCursorV4 0x6d0b35b981cc05e42f01742aa85502a432388f1460e3011618b0448a202d5e6a03501a0495e3d69e80f407622d70ec0078001 0xc1e0e0c0b8aa5b552d26c0914b47a1a39e91a868c54254183d1c1c860d4706249502e2f16d2764ba1a59892a86946e48b523d791ae854892a0812a0c2e8e16430aa38510e28388d038bd835d2dacc4d54b6a373450d24868e9a46c192a0c2e8616430aa18510c228611092a05c5aaa2b16d6a86ac1b4e0da68692834925a460d20968d8346a49392498864a8324c505a0c2b06134308a183d0c1c860d43062183c1c181254030b838507122389103088184c922d4515a06b4f3560da706d3434b4d2562d2706934b47c1a390d19068c4929249410c950649860b418560c2706134309818490c22b0108308238400c1e860d522b8495051a5a0d1c34961a470d1f868ec346e1a3324a59251c927e493b249b924cc3096684a0c2386118307e183b0c1b860cc305e182b0c138608c303e181b0c0b8604c327e193b0c9b864cc325a183f0c1d860dc3066181f0c0d8605c3026404c1c20148fc347632370d199a4a8308a383f1c1d8e0dc7066182f1c158e09c30461b4e0d278692c348e1a430ca78652c328e19430c9a864bc325619270c91861083035c34bc9a38692ec48f323f0d1dac8dc3466493b2499924ace25461260c918e12c409418470823060fc707618371c19860bc305618270c118607c7026001f 13 8191 5 31 11 2047 17 131071
def f_67 : Nat → Nat × Nat := unpackForestF 0xea350b4bd25dd1520b47bb5dbb450a47a456a3560a3f645a6456635a63567244625660420a37434b495c4347092a09261a3f204c1a37084a0846001f 5 11
set_option maxHeartbeats 0 in
theorem rc_67 : dagCheckRootsV4 m_67 g_67 ep_67 30 bds_67 (dagTraceF m_67 s_67 7 f_67) (cur_67 0) s_67 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67 : treeBlockF 0 30 (dagCheckNodeV4 m_67 g_67 ep_67 bds_67 30 (dagTraceF m_67 s_67 7 f_67) cur_67) = true := by decide +kernel
theorem nc_67 : ∀ i, 0 ≤ i → i < 30 → (dagCheckNodeV4 m_67 g_67 ep_67 bds_67 30 (dagTraceF m_67 s_67 7 f_67) cur_67) i = true := fun _ h1 h2 => treeBlockF_at nb_67 h1 h2
theorem lb_67 : LowerBin m_67 s_67 g_67 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_67 kn_67 sub_67 gl_67 rc_67 nc_67

def m_68 : Nat := 0xffffffff00000000
def s_68 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_68 : Nat := 0x117155700000000
def ep_68 : Nat := 0x1440000000000016004200000000010604020000000001121002000000000114155400000000
theorem epk_68 : ep_68 = edgePack m_68 g_68 := by decide +kernel
def bds_68 : List (Nat × List Nat × Nat × Nat) := [(m_21, s_21, 7, g_21), (m_29, s_29, 7, g_29), (m_20, s_20, 5, g_20), (m_24, s_24, 5, g_24), (m_27, s_27, 5, g_27), (m_26, s_26, 5, g_26), (m_25, s_25, 5, g_25), (m_23, s_23, 5, g_23), (m_22, s_22, 6, g_22)]
theorem kn_68 : KnownBin bds_68 := by
  intro b hb; simp only [bds_68, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_21
  · exact lb_29
  · exact lb_20
  · exact lb_24
  · exact lb_27
  · exact lb_26
  · exact lb_25
  · exact lb_23
  · exact lb_22
theorem sub_68 : ∀ b ∈ bds_68, m_68 &&& b.1 = b.1 := by intro b hb; simp only [bds_68, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_68 : ∀ b ∈ bds_68, canon b.1 g_68 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_68, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_68 : Nat → List (Nat × Nat) := unpackCursorV4 0xacf49ff493338c5b7e39713464345773509b4279357428741bb314db06b900590001 0x1c5f1c5b1c571c531b5f1b5e1b5b1b5a1b571b561b531b523b4f3b4e3b4d1a5f1a5e1a5b1a571a531a523a4b4a4a3a494a474a463a433a414a374a364a35195f195b19571953594f494b49475943593f593d593b29395937793559332931392f692b69273923185e1c5f1c5e1c5b1c571c531c521b5f1b5b1b571b533b4f4b4e3b4d3b473b453b433b421a5f1a5e1a5b1a5a1a571a561a531a523a474a463a453a3f3a3e3a3d195f195b19571953494f494b49474943393f393b39373933392f392d392b29293927792539232921185e1c5f1c5e1c5b1c5a1c571c561c531c521b5f1b5b1b571b533b4f3b4e3b4d1a5f1a5b1a571a534a4f4a4e5a4d4a3f4a3e3a3b3a393a334a323a31c230195f195b19571953494f794d494b29494947494549432941493f493b49374933392f692b69273923185e1b4f1b4e1b4b1b471b431b421a4f1a4b1a471a433a3f4a3e3a3d194f194b19471943493f493b49374933392f392b39273923184e38261c5f1c5e1c5b1c571c531c521b5f1b5e1b5b1b571b531b523b4f3b4d3b4b3b4a3b474b463b45c3441a5f1a5e1a5b1a5a1a571a561a531a523a4f5a4e3a4d3a3f3a3e3a3d195f195b19571953594f494b49475943393f393b39373933392f392d392b29293927792539232921185e382688241c5f1c5b1c571c531b5f1b5e1b5b1b5a1b571b561b531b522b4f2b4e2b4d1a5f1a5b1a571a535a4f4a4b4a475a435a3f5a3d5a3b3a395a376a355a333a31195f195e195b195719531952294b494a29494947494629432941493749364935792f292b79272923185e1c5f1c5e1c5b1c571c531c521b5f1b5b1b571b534b4f4b4b4b474b431a5f1a5b1a571a532a4f4a4e2a4d2a472a452a432a422a3f2a3b2a372a33195f195e195b195a1957195619531952294749462945293f393e293b293a2937693629332932292f292e292d185e1c5f1c5e1c5b1c5a1c571c561c531c521b5f1b5b1b571b532b4f2b4e2b4d1a5f1a5b1a571a534a4f6a4d4a4b3a494a474a454a433a414a3f4a3b4a374a33195f195b19571953494f494e594d493f493e293b29392933493229317130792f292b79272923185e1b4f1b4e1b4b1b471b431b421a4f1a4b1a471a434a3f4a3b4a374a33194f194b19471943293f493e293d292f292b29272923184e28161c5f1c5e1c5b1c571c531c521b5f1b5b1b571b535b4f4b4b4b475b431a5f1a5e1a5b1a571a531a522a4f2a4d2a4b2a4a2a474a462a4572442a3f2a3b2a372a33195f195e195b195a1957195619531952294f594e294d293f393e293b293a2937693629332932292f292e292d185e281688141c5f1c5b1c571c531b5f1b5b1b571b533b4f3b4b3b473b431a5f1a5e1a5b1a5a1a571a561a531a523a4f5a4e3a4b3a4a3a474a463a433a422a3f2a3e2a3d195f195e195b195719531952794f294b79472943293b393a29393937393629332931392739266925185e1c5f1c5b1c571c531b5f1b5e1b5b1b571b531b526b4f3b4b6b473b431a5f1a5b1a571a532a4f2a4b2a472a432a3f3a3e2a3d2a372a352a332a32195f195e195b195a1957195619531952294f594e294b294a2947494629432942293769362935292f292e292d185e1c5f1c5b1c571c531b5f1b5e1b5b1b5a1b571b561b531b526b4f5b4e6b4b4b4a6b474b466b435b421a5f1a5b1a571a536a4f3a4b6a473a432a3f2a3e2a3d195f195b19571953794f294b79472943393f393e393d392f392e292b29292923392229212120185e1b4f1b4b1b471b431a4f1a4e1a4b1a471a431a426a3f6a3b6a376a33194f194b19471943293f293b29372933292f692e292d184e28161c5f1c5b1c571c531b5f1b5e1b5b1b571b531b523b4f3b4b3b473b431a5f1a5e1a5b1a571a531a522a4f2a4b2a472a432a3f2a3d2a3b2a3a2a373a362a352234195f195e195b195a1957195619531952294f594e294b294a2947494629432942293f393e293d292f292e292d185e281688141b4f1b4b1b471b431a4f1a4b1a471a43f23fe23bd237b233194f194b19471943a13f913b81376133512f412b31271123184e001f 16 65535 6 63 11 2047 16 65535
def f_68 : Nat → Nat × Nat := unpackForestF 0x18fc63b18df34418cc53f14ec537791053314bc52b149ca34148c01f 4 10
set_option maxHeartbeats 0 in
theorem rc_68 : dagCheckRootsV4 m_68 g_68 ep_68 16 bds_68 (dagTraceF m_68 s_68 8 f_68) (cur_68 0) s_68 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68 : treeBlockF 0 16 (dagCheckNodeV4 m_68 g_68 ep_68 bds_68 16 (dagTraceF m_68 s_68 8 f_68) cur_68) = true := by decide +kernel
theorem nc_68 : ∀ i, 0 ≤ i → i < 16 → (dagCheckNodeV4 m_68 g_68 ep_68 bds_68 16 (dagTraceF m_68 s_68 8 f_68) cur_68) i = true := fun _ h1 h2 => treeBlockF_at nb_68 h1 h2
theorem lb_68 : LowerBin m_68 s_68 g_68 9 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_68 kn_68 sub_68 gl_68 rc_68 nc_68

def m_69 : Nat := 0xffffffff
def s_69 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_69 : Nat := 0x131f1f7f
def ep_69 : Nat := 0xc6000000000000c006000000000020e0e0800000000131010200000000010101040
theorem epk_69 : ep_69 = edgePack m_69 g_69 := by decide +kernel
def bds_69 : List (Nat × List Nat × Nat × Nat) := [(m_45, s_45, 5, g_45), (m_46, s_46, 5, g_46), (m_3, s_3, 4, g_3), (m_43, s_43, 5, g_43), (m_10, s_10, 4, g_10), (m_48, s_48, 6, g_48), (m_47, s_47, 5, g_47), (m_42, s_42, 4, g_42), (m_49, s_49, 5, g_49), (m_12, s_12, 4, g_12), (m_44, s_44, 4, g_44), (m_17, s_17, 6, g_17), (m_19, s_19, 5, g_19)]
theorem kn_69 : KnownBin bds_69 := by
  intro b hb; simp only [bds_69, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_45
  · exact lb_46
  · exact lb_3
  · exact lb_43
  · exact lb_10
  · exact lb_48
  · exact lb_47
  · exact lb_42
  · exact lb_49
  · exact lb_12
  · exact lb_44
  · exact lb_17
  · exact lb_19
theorem sub_69 : ∀ b ∈ bds_69, m_69 &&& b.1 = b.1 := by intro b hb; simp only [bds_69, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_69 : ∀ b ∈ bds_69, canon b.1 g_69 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_69, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_69_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8f808d05880a878187808682860185818580848284018185818081807f84719c641b62835d8a5c035b815b80521350044f814e824e804d82392915c700aa0001 0x7d1600b8a00c9480f09c01e0c040ad005d600152c02a920052a8079480e89201a1700f0900784002dae022d703446805c5002da80591600b8a005a340462c051140034900ba440891a006d00224a80a94003c20017178118b41b4590462c0231580b8a41945102e28060d682e6ac07b4e03da6854974264aa0ba4d00d2482e914034821223d0811a80a524052820a9390549880a1340508a0783903c1880ad74056aa0aa4a025230068f8034640794a014a30064f8032640292d0149280a4900b0bc0785a0442b0161480d09c0784a05c2301a1080506c078350141700a0b40503c0481d014920060f0050580d3640152000a8c00329804930014920061300f07002830014160169400b498028140140a0169380b4840ba3a05d1b012538142840613a0249b0064b8052440284e048210100e80506c0182e0241100a0740502a02814035200124d005068028140140a018950050280425401498016d78116b408b5602da901ad38176940bb46035a100a974054b40b2560152a820950054940724603d1f00a8f40a2940494600c9f00a4e40526402931014980064b809252019220149080c1280508c0183e00c1e8060d4090640182e01414806088050420281d0140a80a0500b8be4f45b26a2b81714c0b6be4c35d015ad928d5c886aa02b53211a780ad2c7c68e02b430552d81694c154963b24a1c92302a90c0547c04a3b0151980a8c8052be0795b014ab81654c0529e0794b1a0a500a51c6028c079430149f8124f80527602937014998124c80525e0292d014928a84900b0be0585e03c2d822168500ae0885602c298161484a09e0684e03c258841283808e0f04603c2181a1080507e0183e03c1d8380e81806e02036014198060c80505e0282e01416816d3ec86975e34702da181693eba49b5b24bac123d4c9140b4874f23fa611dd188de804660594f9e0a5ce851c0b2873613f9509dc9c4de402671812f8a095be849dce2460584f6f825b7411c0b086d903f6301daf80dd64066aa02f518159fc09cd80466301f2c80d94405c020260001f 16 65535 7 127 11 2047 21 2097151
def cc_69_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb77da8ac8731a980434a1810a1840c201b30d616a0b501434a004f0a78134486a24f91847c83e01d10aa054026211100c0002000 0x209b20aa50094880a5703ca80294405248fc1703c2c0b8540f0a01a13080220183c0e0680a4901412029240c0680a091e9aebc3550347c068c9b0a5331460927c124c814968a92a1524c0a49414920885a110ac1a13854268a8450d0842a0e8281b0282d0d0541a0981412828241569a12974252a81a410947a128d414a6b513a6426c124b824910885a110ace8134341f068320905412098201a02824706badcd55b125352460547c0a8c814a3029450327c064c83c96879250f0b42215834270784d0f08a1a1083c1d030360505c0a0b4340d06816050281a080162c82c510569c1ed34152e82a550349206904151e82a35052940a519989d321360525c0a488442d088560509cc4134341f06832050540a098140f0281d5e270b41703c2802a4d0548a064b80c912703d3c06a0a0a814130c81d1902a16d3d71a5ac3470b6860a93c152682a4b0548e0a914152182a3f054760a8dc1519ab13a032441613c3c25a90470b086980fc3c1d9d0370f0660a0bc14158282a0504e0a09814118c81d0b080a44902c36078580b0a09c520649c0aa58054901e56014a2261240f0b01a14110220183c17068231602e282435d466aa161783c2d088560b0a4881183c228183e0f0742e0d80c190a82e0f05a1e0783c0e9f124 13 8191 5 31 11 2047 19 524287
def cc_69_2 : Nat → List (Nat × Nat) := unpackCursorV4 0x9a893502506c4967e2cd699aa0b4056800cf059c0b20659aa8d99180a00c3f827624aef9581239e43108210fc21f803b102d285020418011c0200001 0x296c0f2c17c1b0443204b5d096aa068f80d190493a0926c0a4b41492888560d09c120dae8130a81e0b8bc23168462b05c520b6bc16d48252e84a550949a06924252281a410947a128d41426878490508a1e1043c1c87831090541209815ae82b55154940a8c83ca5029460527c0a4c814968585e0f0b4221582c290684e0f0948811834210183e050740a0d80c190282d0b8bf8116ef22b85c53096be12d7415ad84b57096aa0ad4c25a782b4b0968e0ad0ee12502a32052be1e56c14ab859530529e1e52c14a3879430527e0a4ec249d029370926c0a4cc14968585e110ac1a13ad8230183e0906d68079781008a680b4c16092035202e0100f0201e040453456260aa2c00a1b2a0302c010056ba0ad54151d0595e112b4225582ca90193e052740a4d80c990284d0508a0a0e8141b02821560400a074140c82815050221717eba2dd34570b8a60ad7c15ae82b5b056ae0ad5415a982b4f056960ad1c15a188a5a0b4a548928352102a3a034640a4e8142f8285b050ae0a14c14278284b0508e0a10c141f8283b050740a0dc141b028330505a0a045500808b58154901e52014a22e124110d016180342e180540d0981e1228022068405a028b0492703607868110c81e1802c2e088540d0985c1102dab02b550b4b412959e92504a460347c068c82cad02956702940a5180c9f019320525a0a49414920585e0b0b4161582c290684e480945411834210183e050740a0d80c190282e0505a071502dae0aa60052d81e58014924b06c0f0d0221903c300585c110b0221502c280183c160680a490442a0a0340504822150481a05a4c034801a13230220183c0b06816d7815ae82b4a8268c1297a49293c24a0948c068f80d190295e902a4dc52814a30193e032640a4b41492829248e0bc22168442b450520d09c8c1289823068420307c0a0f40c1e0283a0506c340d4401a018320505c0a0b445ac05b50094a82a92014aa07948052880a490342e120540d0981e122182206840094680a4d014924004c170881a0f0881a40254 15 32767 6 63 11 2047 19 524287
def cc_69_3 : Nat → List (Nat × Nat) := unpackCursorV4 0xf482ef8aee82e88cd3aabeaabe80bd03aa26aa00a902922e920092007d2a7d007c026e1c42d7428042803e883e803c052e1c2d81249202c40280028000050000 0x6d700da20586c110c81a173c02a0684c03091f81100c207202cde048071400da80296c0f2c1f01b00c3408864030c016170442a0684cee089c40b3701208b4f1169622d1c45a181a4f0349a0692c0d2381a4503486068fc0d1d81a37034661253c24a58494709286124fc249d8493709266064bc0c9581927032460a13c142582847050860a0fc141d8283705066060bc0c1581827030460a07c140d828170502616d3c35a586b470b6860693c0d2681a4b0348e069140d2181a3f03476068dc0d198494f092961251c24a18493f09276124dc24998192f032560649c0c918284f050960a11c14218283f050760a0dc14198182f030560609c0c118281f050360a05c140981b50050b81e1402e2f08c5a118ac171482daf7835aee6ac16d480da701b4d034ba069540d2681a490348a069040d1e81a390346a068c424a4849410927a124e4249a849310509a0a1241422828410507a0a0e4141a828310305406098140f04812050b81e1402da7f534be868e16d0c0d2781a4d034960691c0d2281a430347e068ec0d1b81a330929e1252c24a3849430927e124ec249b849330325e064ac0c93819230509e0a12c1423828430507e0a0ec141b828330305e060ac0c15018270304c0608c140f8281e050360a05c1409848120b69fc8d2f89a385b430349e069340d2581a470348a0690c0d1f81a3b0346e068cc24a78494b0928e1250c249f8493b0926e124cc0c978192b0324e0648c14278284b0508e0a10c141f8283b0506e0a0cc0c178182b0304e0608c140f8281b0502e0a04c142e078500b69fbcd2f71a385b430349e069340d2581a470348a0690c0d1f81a3b0346e068cc14278284b0508e0a10c141f8283b0506e0a0cc0c178182b030540609c0c13018230b8bff516fda2b85c53036be06d740dad81b57036aa06d4c0da781b4b0368e06d0c252f84a5b094ae1294c252784a4b0948e1290c0d1f81a3b0346e068cc14af8295b052ae0a54c14a78294b0528e0a50c0c9f8193d03276064e80c9b819360526a0a4bc14970292b0524e0a48c24910185f0b0bc061742c2e0185b030b40615c442b01855f40a80614c0c290184f0d09c06137c8260184b030940611fb02301845e60880610c0c210183f0307c060f40c178482e0305bc00b00c15818270304bb40900c11818220303e0a0780c0e8596c112c81a53014a46b14405281a812014220aa60d02d80a5a044b2029600b8bc23168462b05c520b6bc16d4815a702b4d054ba0a954152681a490548a06904151e82a350f2922a504549c8a931052540a4981424828410507a0a0d4140c82811050880ad7415aa82a3a0546c0a56844ab0694e052840a4e8149b0792e0525a0a11814228183e030640a05b280a85c5fd28b79d15c2e2982b5f056ba0ad6c15ab82b55056a60ad3c15a582b47056862a96c2d298aa4b154860a8ec151d02a36054660a57c2caf0295b052b40a55c44ab02953052a40a53c34a70294b052940a51f30a302943052840a4fc0c9f0293b052740a4dc149b02933032640a4bed0970292d050be0a16c142b828530509e0a12f2025028470508c0a10c141f8283e050760a0dc141982832050520a08c1410e22480b0d822190342661044 16 65535 7 127 11 2047 19 524287
def cc_69_4 : Nat → List (Nat × Nat) := unpackCursorV4 0x91068518850084818107810080817c887c807c017b817709770077006a1a680454285400530253005300518351804f0537303681368036803209320028930051 0x2b6c08b6802b649f3609113c8b13005c5e05c5202b5d02b5502b4d02b4505a5e08a5a08a5605a5202a4602a4501a3e02a3a02a3601a320a9290a9210284d028450182d0282901825028210a9300aa409c14c0294802944089409b018028140a9300aa409914c02948029440a94004828980180281406a300a9300aa409614c0294802944069400193c95134940180281405b4f9234b9134705b4302a4f02a4d01a4b02a4702a4501a4302a3f01a3b02a3701a330284f0284b02847028430283f0283b02837028330182f0282b028270182308c5805c50029400a93002b5d02b5504a5e0aa5a04a5605a5204a4e0aa4a04a460aa4201a3e02a3a02a3601a320595e0895a08956059520694e0a94a8f146069420293a029360292e0292d8504a028460183e018320282d02829048280282502824028210181d0281601815018148d038028348404804838028348845805c500a930028448303805b4f8c34b8b34705b4302a4f02a4d01a4b02a4702a4501a4302a3f01a3b02a3701a330594f0a94b8a147059438913f0a93b871370a9330192f0292b02927019230284f0284b02847028430283f0283b8203a0283702836028330182f0182e0282b0282701823018220181f0281b0481a0281702816028130481402a4d02a458413d8313502836028350182e018220481608b5a02b5602b4e06b4202a5d02a5502a3e02a3d0293e0293902932851318213002846028450283e8103d0182e0182205c5fa045b9e45705c5302b5f02b5e02b5b08b5a02b5702b5602b5305b5202b4f02b4e02b4b9d34a02b4702b4602b4306b4202a5f02a5d01a5b02a5702a5501a5302a4f01a4b02a4701a4302a3f02a3e02a3d0495f9a15b04957059530494f9714b04947931430293f0293e9013c0293b029390293702933029328e131861300192f0292b02927019230285f0285b02857028530284f0284b8004a0284702846028430183f0183e0183d0182f0182e0282b028290182301822028210281f0281b0481a028170281602813 16 65535 7 127 11 2047 20 1048575
def cc_69_5 : Nat → List (Nat × Nat) := unpackCursorV4 0x7ceabbe51da0aed0074c3ba405b33ed9806c80b64019834bf1a4d64a68052e0c96814b00a4820fa546f1c23e790e2083083e861d440de18582e05cd02c00140400140000 0x2c5f02c5e02c5b08c5a02c59c545802c5702c5602c5305c5202c5105c5005b5f06b5b09b5705b5302b4f02b4eb334d02a5f02a5d02a5b02a5702a5502a5302a4f02a4d02a4b01a4902a4702a4502a4301a4102a3f02a3d02a3b02a3702a3502a330595f0995b09957059530294f0294b029490294702943c41410693fc213bbf137069330292f0292b02927029230285f0285b0985a0285702856028530284f0284e0284d0283f0283e0283b028390283306832028310282f0282b0282a0282702826028230281f0281e0281b02817028133001205b5602b550294d0694a02946029450585e0585a05856058520284e0284d0183e0283a0283601832b702e068220281e0681d0a83c0a82c0482804824068200294c07940bb04c068400183cb9034b602c06a3005b5e08b5a08b5605b5202b4e01b4a01b4602b4202a5d02a5a09a5602a5509a5406a4e02a4206a3e02a3d0a9390a9310292db91250284d0684a02846028450183d028390183502831028290282107830b735d09b5509a5a09a5606a4e06a420aa3ab62360595e0895a08956059520294e029420193e0a93ab5136019320692e0692d0684a068460782907821078190781102b5d02b550795a029560294e0294d02945069420293a029360292e079220585e0785a088560585202846028450183e0283a02836018320a82e078220281e0681d05c5f06c5b06c5705c5305b5fbd35d02b5b09b5709b5502b5306b4f02b4b06b4702b4305a5f09a5b09a5705a5306a4f06a4b06a4706a4302a3fbc23bba23702a330295f0795b02957059530294f0294d0694b0694a0294706946029450293f0293b02937029330292f0792b02927079230585f0585e0685b0685a068570885605853058520284f0284e0284d0283f0183e0683b0683a06837b803602833018320682fb402e0682b0682706823068220681fb301e0681d01b5c05a6c08a6406a4c01a48b124401a4001c5008a54af26c01a6808a6401a6005a5c08a540286cae06008b4f08b4b08b4708b4301a4f01a4d01a4b01a4701a4501a4301a3f01a3b01a3701a330494f0494b04947049430493f0493b04937049330192f0192b01927019230284f0284b02847028430283f0283b02837028330182f0182b01827018230281f0281b028170281305c5e08c5a08c5605c5201b4e01b4d01a5d01a5501a4d01a4901a4501a4101a3901a3104949049410493d049350284d0284902845028410283d028350182a018260281e0481205c5fb045bad45705c5301b5f01b5d01b5b01b5701b5501b5301b4f01b4b01b4701b4301a5f05a5e01a5d05a5c01a5b01a5a01a5708a5601a55ac25401a5301a5201a4f06a4e01a4b01a4a01a47ab24601a4301a4201a3f01a3e01a3d0495f0495b04957049530494f0494b04947049430193f0193b01937019330192f0192b049290192701923019210285f0285b02857028530284f0284b02847028430183b0183a02839018370183601833018310182701826028250281f0281e0281b028170281304812079480294408868058600284c0784802844068400286c07868028640786007928029240282c0782802824078200493807928029240a8300282c07828028240782007928029240282c07828028240682002b5d02b550795a029560294e0294d029450694202936029350292e0792202846028450183e0283d07835018320681d0181a01816028150181405c5fa945ba845705c5302b5f02b5d01b5b02b5702b5501b5302b4f01b4b02b4701b4304a5fa725b04a5705a5304a4fa624b04a47a524301a3f02a3b02a3701a330295f0295b02957029530294f0294ba414a0294702946029430193f0193e0293d029370293501933019320292f0292b0492a0292702926029230285f0285e0285b0885a028570285602853058520284f0284e0284b0b84a028470284602843068420283702836028350282f0282e0282b02827028230e0220181f0181e0181d8d13008b6805b6002b4ca234802b4406b409213c8c130a104802844 17 131071 7 127 11 2047 20 1048575
def cc_69_6 : Nat → List (Nat × Nat) := unpackCursorV4 0x924d3fd2ddc44d82c650e28b3d2b34869e40c51fa18f51076883b401ce18e00e641830c298600c3006101304098200a93052051567856a8152c0a010304018000c00000c 0x2b5d02b5505a5a05a5609a4a09a4602a3e02a320595a059560694e0994a09946069420193e0293a02936019320292e0292d0984a028460282d028250281d0281502c5f02c5e05c5d02b5f09b5d02b5b02b5902b5702b5502b5306b5105b4f05b4b05b4705b4302a5f02a5d02a5b01a5902a5702a5502a5301a5102a4f02a4d02a4b02a4702a4502a4302a3f02a3b02a3702a330295f0295b029590295702953de1510594f0594b05947059430993f0993b09937099330292f0292b02927029230285f0285e0285d0284f0284e0284b028490284305842028410283f0283b0983a0283702836028330282f0282b02827028230281f0281b028170281302b5d02b5505a5e09a5a09a5605a5206a4e06a4a06a4606a4202a3e02a3a02a3602a320595e0895a08956059520694e069420193e0293a02936019320292e0292d0684a028460282d0282902825028210281d0281505b4f06b4b06b4705b4302a4f02a4d02a4b02a4702a4502a4302a3f02a3b02a3702a330594f0994b09947059430693f0693b06937069330292f0292b02927029230284f0284b02847028430283f0283b0683a0283702836028330282f0282b02827028230281f0281b028170281305a4f06a4b06a4705a430294f0294d0294b0294702945029430292f0292d0292b0292702925029230284f0284b02847028430282f0282b02827028230281f0281b028170281305c5f06c5b06c5705c5302b5f05b5e02b5b02b5a02b5708b5602b5302b5202b4f06b4e02b4d02a5f02a5d02a5b02a5702a5502a5302a4f02a4d02a4b02a4702a4502a4302a3f02a3d02a3b01a3902a3702a3502a3301a310595f0995b09957059530694f0694b06947069430293f0293b0293adc139db1380293702936da13402933029310292f0292b02927029230285f0285b02857028530284b0684a02849028470284602843028410283702836028350282f0282b02827028230281f0281b028170281305b5602b550595a029560294e0294d02945069420293a029360292e381220585e0585a058560585202846028450183e0283a0283601832cd02e240220281e0681d09c5e09c5205b5e02b5d02b4a09b460895a029560294e0294d02945069420293a029360292e371220985e0885a088560985202846028450183e0283a0283601832cc02e230220281e0681d09b640295c079500185c028580285401850028440183c0b8343613007928029240a83c0282c0782009d6805d600295c07950351200285c07850cb02c0293c0292c079200a83c0a82c0482804824078200294c079400292cd204c07840ca02c069480294407938028540184c078380283005b5e08b5a08b5605b5201b4e02b4a02b4601b4202a5d02a5502a4a0ba4607a3e02a3d0a9390a9310284d028450183d0283901835028310282902821079300292c06920078380783005c5007830cd35dcc35505a5e05a520aa4acb2460aa3aca2360595e0895a08956059520294a029460193e0a93ac9136019320792e0792d078290782106819068110293c06930079200a83c0782005c5f06c5b09c5705c5305b5fd835d02b5b09b57d735502b5306b4f02b4bd634702b4305a5f09a5b09a5705a5306a4fd524bd424706a4302a3fd323bd123702a330295f0795b0995a0295709956059530294f0694e0294d029470294506943069420293f0293ba413a0293780136029330292f6412e0792b0292707923341220585f0585e0785b0885a098570885605853058520284702846028450283f0183e0783b0b83ad0037cf0360283301832ce02fc802e0782bc702707823210220681f0681e0681d05b4f08b4b08b4706b4302a4f02a4b02a4702a4302a3f02a3d02a3b02a3702a3502a330694f0994b09947069430893f0893b08937089330292f0292b02927029230284f0284b02847028430283f0283b02837028330282f0282b02827028230281f0281b028170281302b5d02b550aa4ac124602a3e02a320595e0895a08956059520794a221460193e0293a02936019320292e0292d0282d028250281d0281505c5009d6805d600aa50029580795033020c30180281409d6805d6009c6805c6002c5c22450c1140069300285cc00500683032010 17 131071 7 127 11 2047 20 1048575
def cc_69_7 : Nat → List (Nat × Nat) := unpackCursorV4 0x8500428020f0af91d731339409c014df026cc5b24857142b8805bc129a894d00a60149d2a4e0127008321418020a04e04a4a4c23c291e008a0a35201a408d2004d38004d 0x7f22c01714005290fd13803c18016d3e086970334702da181293c0949a01a4b025238129140348604a3f00d1d8128dc034670213a00c9101613c0f0970104702c21bfc0fc0f076fc03703c198060bc090560482700c1180a0740b8bf1145b87a2b81714c116b405b52871a501ad08094be04a5d00d2d81295c094aa01a530252780692c0948e01a430251ec30528032440285f7202d80a15c0b0a60284f6882580a11d740860283d8481e4180c5f60600182f0141580a09c030460281d00dae006d100b2d808964034ae3cc5500d298019487c8a2006501da030ea01400e28006d40154c0f716c00cb4022590032c00595c044aa01a531e4288ec0187480a022d3c1169608b47045a180693c0349a01a4700d2280690c0347e01a3b00d1b8068cc09296049430249d8124cc03256019230142780a12c0508e028430141f80a0ec0506e0283300c178060ac0304e018230140f80a04c0b69e06b4b035a3816d0c0349e01a4d00d2580691c0348a01a4300d1f8068ec0346e0494b024a18124ec092660192b00c9180a13c05096028470142180a0fc0507602837014198060bc030560182700c1180a07c0502601b50054a8017178118b408c5602e29016d79e66b4f235602da9006d380369a01a5d00d2a8069340348a01a3d00d1c8068d40346204949024a08124e4092620192a00c9300a13405092028450142080a0f405072028350141880a064050220a95002da7bc0d2dde68e05b4300d278069340349601a4700d2280690c0347e01a3700d1981252c092860493b024998064ac032540192600c9180a13c05096028470142180a0fc0507602837014198060bc030560182700c1180a07c050320281301408816d3dda696ec34702da180693c0349a01a4b00d238069140348601a3f00d1d8068dc034660494b024a18124ec092660192b00c9180a13c05096028470142180a0fc0507602837014198060bc03056018270140f80a04c152a005b4f751a5ba4d1c0b68601a4f00d2680692c0348e01a4500d218068fc0347601a3700d1981252c092860493b024998064ac032540192600c9180a13c05096028470142180a0fc0507602837014198060ac0304e018230140f80a064050260281102e2fbe116dec8ae05c5300daf806d74036b601b5700daa806d4c0369e01b4b00da3806d0c094b604a530252581290c0347601a3a00d1b00657c0b2bc0195d02cae00656c032b401957044ab006555ea2a80195300ca900653c0d29c0194d7a0a600652c0329401947788a3006515dc2880194300ca10064bc0925c0192d0142f80a16c050ae028530142780a12c0508e0284300c1f8060ec0306e018330141780a0a4050460282100c0f806074030360181a0140cbac0600302e018160140aba005003026018110541e02a0b0090500482403c1000a5300f280e504c03c203880b0118b205c5100daf00ad74036b802b5a015ab00ad54036a406b4e04da5026d180d68402a5d0152d016958054aa08a5403d1f00a8f4152720a9310142e80a154130940284600c1e80a0e40306a028310141480a0840f06008c5902e28816d74116aa05a5a02d2b026938134840aa3a7111b00a568052ac0694e04ca50265180d2840193e0549d3844d8032640792e03c968261281308c0782903c108160640b02205c5f02e2d8231640b8ae05c5302e28816d7c0b6ba02b5b02dab822d54056a609b4f015a5826d1c0568605a5f02d2d81695c0b4a609a4f04d2582691c1348602a3f7311db908dc054660295f02caf00a574052ae0295502ca98165480529e0794b04ca500a51c1328c079430149f80a4ec0526e029330149781e4ac0524e079230142b80a158050aa0884f0342701e12c110940884704c2301e10c0d0840283f00c1f01e0ec11074088377181b00a0cc030640882f7001701e0ac1104e078230441101607c0b03c0581d 17 131071 7 127 11 2047 21 2097151
def cc_69_8 : Nat → List (Nat × Nat) := unpackCursorV4 0x9784978097019485879a7d946b25678765845b153a423a0039813607360034042b122b00250c25002500181a16831503059f0580050105000108010001000002 0x169b0114c806a4c8f9220229523a4d808a6402d2e022952382c008b4f045a5822d1c1168601a4f00d2680692c0348e01a4500d218068fc0347601a3700d1980a13c05096028470142180a0fc0507602837014198060bc030560182700c11817178118b408c5602e29006974034aa01a4d00d248069140348201a3900d188064a80509a028490142280a1040507a028350140881717e3c8b71b45702e29806d7c036ba01b5b00dab806d54036a601b4f00da5806d1c0368605a5e02d2e02295a344a806a4e8c9230068f8032740285f0142d80a15c050a60284f0142580a11c050860183f00c1d8060dc03066028290141280a044154900896802cb00125301529004944034a00125b0112d004964054b0012d74096aa08a5a0252b0129380949a04a45035210064f80927a0a93500c9901a4b4032540192602492806490090520a8210140e80a0540b8bf1745b8b22b81714c096be04b5d00dad812d5c096aa01b53025a7806d2c0968e01b430252d81294c094971524a0252301290c0347c01a3300d1901257c092bc0495b044ad01255c092ac0495302ca901253c0929c0494b05ca501251c0928c04943034a10064bc0325c0192d0142fb9816c050ae0585301427b4c12c0508ebc04300c1f80a0ec0506e018330141780a0b40504a048230140f80a07409036048190140b80a054090260e01182818022da00b6c113348035a04485221607904030045b4440d82140790303002e2f017148096ba04b55025a6812d140b4bc08a5a0452b0169480347c04a3a0251b0068c80505a078290141281e084116b406b420252e8129540947b0d13d00c9700648a10063020300140e80a0540b69f0b34b851a3816d0c0549e02a4b0152380a90c0547e02a3b0151b80a8cc0529e0294d00ca580a51c0528a019430149f8064ec0526e01933014978064ac0524e019230149600a4900504808c5802e2801e0c0056ba02b55841250068c8052bc0795a014ab0165480529c0794a014a301e5080327c0293a0149b0064c80525a0292c02c2f01e168110ac058520342701e12a0e08c0684200c1f00a0e80506c0183201416c144e00949a04a4500c9700648a0007afd0350140e80a0560029002938 16 65535 7 127 11 2047 21 2097151
def cc_69_9 : Nat → List (Nat × Nat) := unpackCursorV4 0xad0053072568520958791c066de836e61c699331c617238b60659c2aa6514e0aa700538029c01363098853b621a668c1244c2921890d66c58262c00160007c68007c0000 0x462c8171440b6ba08b5504d250269180b2b40595604ca701e5080f2749b1360549701e488050bc028520342701e1281308c0684200c1f01e0ea7c06c0183202c170160880f03c0781d02e2f81716c118b205c5702e298171440b6be05b5d025ad816d5c116aa04b5304da7812d2c1368e04b4302d2f01694c0b4a409a4b04d250269181348604a3b0251982253c0d29c0894b044a502251c1328c08943034a10124fc0327c0893b0449d0224de7e26c0493300c990164bc0b25c0592d02c2f81616c0b0ae0585304c2782612c1308e098430241fa9c0ed3406e048330541782a08c1103e0281d0440dcf40641102e0281504409822044096ba04b5504d250165680b2ac0794a04ca30124f8092640285e02c2d016158050a40684e03c250261180d0840183e0241d0120d80306405c5d04dae81ad440b69e05b4b02da3816d0c094ba01a51025278129340949604a470252281290c0947e04a3b0251b8128cc0b2840993a0142ecec1440b09e0584b02c2381610c1307e0983b04c1b8260cc0905e0482b0241381208c096ba04b55035250165780f2b40995602ca901a5380d29406946034a10124f80927404936024990161780f0b40885602c2901a1380509402846034210060f8090740483600c19016d3c0d69606b4702da181293c0949a04a4b025238129140948604a3f0251d8128dc094660693a02c2781e12c1308e058430341f81a0ec0d06e06833024178120ac0904e0482302da781ad2c0d68e05b430152780a92c0548e02a430151f80a8ec0546e02a33014a780a5340529602947014a280a50c0527e0293d0149d80a4dc0526a029330149780a4ac0524e0292302e2f81b16c0d8ae05c5302daf022d580d69c04a5f0252e81296c094ae04a550252981293c0949a04a4b025238129140948601a390251a81a5280b0be0985b04c2b81614c0d09e0684b0342381a10e72073380380141acdc0d00905e0482b0241381208c0b6ac04b5502d2d0129580949c06a420251d0128d80b2bc0595a02cab0165480327c0493a0249b0064c80925c0692d024148f40840503b2f0190140a890044138bc09c5202daf012d740969409b460452d0129580949c06a420251d0128d8132bc0895a044ab0265480327c0493a0249b0064c80925c0692d024148f00840503b2e0190140a88c044136c80aa50024ac006540032780b9340352402a8e0032980a93802498016d78116b408b5602da9006d380368404a5d0252a8129281748c0aa3e0251e8124e409262049290249080a0f40f0720283503c1882a4c015258079200341800a0925e6bb2e35502caf0165480f294c314603c9d2604d81525c0792202c2f01e168110ac058520142700a1080307c0783a9681b0060c80d05c0682203c0f01e0740d4600792c0541800a0701502005c5f0362d82715c0b8a605b5f9a9ae812d6c136af34355025a981ad3c0969733347025a182696c134b409a5602d2981a9380d48606a420251dc548ea1846c04a3302caf816578132b60895a04cab8225580b2a6059520249f8064f8152760b93a9909bcc44d809266019320349781a4b80d25a0585f04c2d82615c0b0a60684f6a825b0811c0d0860483f5301da5c0dc090660a82f2e01482a08c760420a81f0140ecc006e580332b0170140a82a04c4202205b4f045a5822d1c0d68604a4f0252581291c0948604a3f0251e8128ec0946e04a350251981a13c1309609847034218220fc1107608837044198120bc090560482702411812d74096aa0794a600a30124f8092640585e03c2d0221580b0a40284e03c25088118050840183e0241d0120d80306408c5a94a2c0171480b8a005b5f035ad826d5c0b6a72434d0252f812974094b604a570252a81294c0949a01a410251f8128f40947604a370251a8128cc132b4069320249501617c130b60985702c2980a136500820683f6a01dafc0dc0d0660482f0241581209c090463901102dab012d540d49404a4602caf0165680b2ac0595200c9f0124e80926c019320249701a4b40503b230190140a81a0440b6bc08b5a045ab016d480369401b460252e812968134ac04a5504d2a01a9380948406a3e0251e81a5280928c04939024988124a4092420283d03c1c80a0d40f0620482d4a812812d74096aa09a5a035210128e80b2bc0895a044ab0165480327c0493a0249b0064c80d25a0a8210140e81e0640502a07811919ae826d540d49406a4603cad0265580d29c0694203c9d2504d81525c0792202c2f01e168110ac058520142500a1180307c0783a9101b0060c81505c078220340f01a0740b8be06c5b0362b81714c0b6bf2635d025ad826d5c136aa04b53035a7812d2c0d68e04b4304d2d81694c0d49606a4a035230128ec094660595f02caf01a56c0d2b406957044ab01654c0b2a40493f00c9f01a4ec0d274069379289b0124cc032640692f9209701a4b40b0be0985b04c2b81614c0d09e0684b0342381a10c0907ea503b4981b8120cc1505e0a8230340f80a0740d037210190340b80a0540d02606811 17 131071 7 127 11 2047 21 2097151
def cc_69_10 : Nat → List (Nat × Nat) := unpackCursorV4 0x9ff266c2795ea632ca8927214217a35de88076c6ddb0073079b7a96aa699d9a6387d67cd552993faa45f410a1b3e090e0af34e68c41f27140862c1c4a8631c138a8382c03754001b 0x2e2f81b1780b8ba05b5f02daf016d740b69e05b4e02da581ad240b68605b4202da082297ec64ba08a5b00d2c82295c114aa08a5300d2881693c0b49a05a4b02d238229140b48606a3f04d1d8268dc0d4660895f044ad822564112ae08953b08a881653c0b2960594702ca181a4fc132760993703499c6c4be2c2570f1277b09182217c050ba0885b0442c82215c050aa08853af82881613c0b0960584702c2181a0fc130760983703419ab40bd500569e0273d81199c07cbc0365301726809816d3c0b69605b4702da181691c0b48d5c245a911f8068ee9646e01a33024a781652c0928e059430249fcd44ec0926f2613300c978124ac0924e019230142781612c0508e058430141fb600ec0506ebd03300c1780a0ac0504e018230140f81206c0502e4c013045a7822d2c1168e08b4300d278169380349a01a3f00d1d8068e80346e09a3600d1981253c0929604947024a18124fc0927604937024998064bc032560192700c9180a13c05096028470142180a0fc0507602837014198060bc030560182700c1180a07c05036028170140981717c0b8b605c5702e29806d7c0b6bc01b5d00dab806d54036a601b5200da7806d2c0369401b4704da3006d0c034ae05a5600d2ad709500349e06a4e00d258069280348e09a4600d218069080347e01a3e00d1e81257c092b604957024a981253c0929604947024a18064fc032760193700c998064bc032560492900c9380648c032420285f0142d80a15c050a60284f0142580a11c050860183f00c1d8060dc030660182f00c168060ac05052018270141280608c030420281f0140d80a05c0502608c5902e28812d74096aa05a5a0252b0129381348404a3a0251b006568032ac0495500caa01a5381329409946034a10124e80926c0492e044968120a4150420281d03c0c80a0540f02208c5902e2880ad74056aa0295d02cad00a558052aa0294e03ca100a4e80526c0292e03c9100a178050ba0185a00c2b00a154030a8028520342701e1281308c0684200c1f00a0e80506c018320541701e0880503c0781d00e2f807178038ba08b5f04dae822d6c0d6b208b57045aa822d4c0d6a205b4f02da6816d2c1169205b47045a2816d0c0b68205a5f02d2f0169740b49e05a4e02d268169300349601a4900d218169080348209a3f00d1d8268e81346e09a3600d1981257c112b608959024ab82254eb42a20494f024a681652c1129204947024a281650c0b2820493f04c9d8124dc132660192f0249581249c032460285f0142e82216c110b2028570142a82214eb20a20284f0142681612c11092028470142281610c0b0820283f04c1d80a0dc130660182f0141580a09c030460281f0240d80a05c9402608c5904e28816d78096ba04b4a04da3022968094ac04a4e04d210128e80946c0694e04ca50265180d2840493a0249b0064c80925c0892d024149240840503b570190140a914044118b209c5102daf00ad740569409b46014ae822568052ac02955014a7026508052740293601497120488050bc0285d034270261281308c0684200c1f00a0e80506c01832aa8171140880503c0881d04da7822d2c1168e09b4302d278169380b49a09a3f00d1dd388ea9446f4923600d1981253c1129604947ab0a18124fe682760493704c998064bc092560492700c9180a13c1109602847aa02180a0fdae0760283704c198060bc050560282700c1180a07c0903602817220098171680b8ac05b5e02dad016d580b6a401b4e00da6816958034aa01a4a00d2481a9180348206a3600d1a8125340928a049390249880a1340508a0283d0141c80a0d40506204b5d025aa826968094ac04a4e035210128e80946c0595e044ad0225580b2a40194e024a6806530032840493a0249b0124b80d25a048290541080a0740f0320281503c0880ad74056aa0795a014ab00a5380529a02945034a100a4e80526c0292e03c910161780f0b40885602c290061380509a0184c0142500a1180508a0184200c1f00a0e80506c018320541701e0880503c0681d02e2f81b16c0d8ae05c5302daf816d780d6b606b5a035ab822d580b6a605b5200da7806d380369a05a5fa912e80696c134ae09a5500d2980692c0d49401a490352381a9180348601a410351b81a8d81746a0495f04cad81255c0b2a60494f024a681a52c0928e04945034a18124fc0d277511390249b81a4cc0d2620192f0249581249c032460285f04c2d80a15c0b0a60284f0142681a12c0508e028450342180a0fc0507a0683ba801c80a0dc0506a06833034188060bc050560282700c1180a07c090360281721009826d3c0d69608b47035a180693c1349c01a4d00d1b8268d80346a0494f024a581251c092860493f0249d8124dc092660192f00c9580649c032460284f0142580a11c050860283f0141d80a0dc050660182f00c1580609c030460281f0140d80a05c0502608b4f035a5822d1c0b68601a4f00d2680692c0348e01a4500d218068fc0347601a3700d1981253c0929604947024a18124fc0927604937024998064bc032560192700c9180a13c05096028470142180a0fc0507602837014198060bc030560182700c1180a07c05036028170140981717c0d8b609c5702e29806d7c036ba01b5b00dad006d5c136ac01b55a71aa006d4c0369e06b4e00da6806d1c0368a01b4300da100697c0b4bc01a5d02d2e00696c034b401a570452b0069569a4a801a5300d2900691c1748c01a4500d1f8068f80347a0495f024ad81255c092a60494f024a581251c092860193f00c9d8064dc032660192f00c958124a40324e0192300c9080a17c050b6028570142980a13c0509602847014218060fc030760183700c198060bc0305a0182b0141480609c0504a0182300c1080a07c0503602817014098171780b8b405c5602e29016d680b6ac01b4e00da6816958034aa09a54035270069340d47c01a3900d190068c409292049410249e8124d40509a028490142280a1040507a0283502e2f01b168118ac05c5204daf026d480369c01b4d02d2f0069740d49c01a4d0351f0068e80347201a3800d190068c409292049410249e8124d40325a04929024928064840509a028490142280a1040507a0283500c1680a0a40504a0182102da7816d380d69608b4704da1816d081349e09a4e0352582291c0d48609a4200d1f8068f80347a0494f044a581251c132860493f05c9d8124dc172660492f024968264ac0924e049250349180a13c110960284704c2180a0fc170760283705c1980a0bc0505a0982b0141380a0940d0460281f0240d80a05c8202604b5d025aa8129780b4a40aa4a025230128e80946c0595e044ad0225580b2a40194a00ca3012514032880493a0249b0124b81525a048290541080a0740f0320281503c0880ad74056aa0295e02ca900a5340f29402946014a280a4e80526c0292e03c910161780f0b40885602c2900a1380509a0184a00c2300a114030880284200c1f00a0e80506c018320541701e0880503c0781d02e2f817178138b608c5a04e2b8231580b8a605c5202daf81ad6c136ae05b5300da7806d380369a05a5fa592e80696c134b409a5704d2b528956924a801a530352781a9380d49a06a3f0351f0068ec0347201a33035190068c4092be0995b024ab81654c0929e0b94b05ca481251c17287481410249f8124f666276049370249a81a4cc0325e0492b0249380648c050be0985b0142b81614c0509e0284d05c2582e1240508e0284505c21d1c1040507e0283d6b01d80a0dc0506a0683300c1780a0ac0504e018230140f81206c0502e3e01302da781ad2c0d68e06b4300d278069340349601a4700d2280690c0347e01a3b00d1d0068dc0d46c01a33024a781252c0928e049430249f8124ec0926e0493300c978064ac0324e019230142780a12c0508e028430141f80a0ec0506e0283300c178060ac0304e018230140f80a06c0502e0281302da781ad2c0d68e05b4300d278069340349601a4700d2280690c0347e01a3b00d1b8068cc0929e0494b024a381250c0927e0493b0249b8124cc0325e0192b00c9380648c0509e0284b0142380a10c0507e0283b0141b80a0cc0305e0182b00c1380608c0503e0281b0140b80a04c0b69e06b4b035a3816d0c0349e01a4d00d2580691c0348a01a4300d1f8068f40347601a3700d1a8068cc0509e0284b0142380a10c0507e0283b0141b80a0cc0305e0182b00c1380608c0b69e06b4b035a3816d0c0349e01a4d00d2580691c0348a01a4300d1f8068ec0346e01a33024a781252c0928e049430249f8124ec0926e0493300c978064ac0324e019230142780a12c0508e028430141f80a0ec0506e0283300c178060ac0304e018230140f80a06c0502e0281302da781ad2c0d68e05b4300d278069340349601a4700d2280690c0347e01a3d00d1d8068dc0346a01a33014a780a52c0528e029430149f80a4ec0526e0293300c978064ac0324e019230242781212c0908e048430241f8120ec0906e0483300c178060ac0304e018230140f80a06c0502e0281302e2f81b16c0d8ae05c5300daf806d74036b601b5700daa806d4c0369e01b4d00da5806d280368e06b4600da280697c0b4bc01a5d02d2e00696c034b401a570452b0069568a4a801a5300d2900693c0d49c01a4d00d1f8068f80347a0495f024ad81255c092a60494f024a581251c092860193f00c9d8064dc032660192f00c958064a8092534412800c9380649a862480192300c9080a17c050b6028570142980a13c0509602847014218060fc030760183700c198060bc0305a0182b00c1500a0a6840500182700c1300a096820480182300c1080a07c0503602817014098231640b8a201b5e025ae806d70036a406b4e04da5026d180d68404a5d0252d016958094aa08a540451f0128f413294049460249c8124c409252049210141e81e0e40506a07831 18 262143 7 127 11 2047 21 2097151
def cc_69_11 : Nat → List (Nat × Nat) := unpackCursorV4 0x1ac835805f18be0148695e69d9c38063c68701001c 0xb8ba06c5500daf016d74036b805b5a02dab022d54036a405b4e00da5006d180b68405a5d02d2d016958114aa08a540352701a9080d47c06a3d044ac816544152720a9310442c8161440507a078390141a81e0c40b6ba08b5502d2d0169580d49c06a420551d4488d80b2b40595602ca70165080327c0a93ab409b0064c80d25c0692d3101482a0840503a078190140a81e0440b6ba08b5502cad0165580d29c0694203c9d2844d8d425c079220142f0161680b0ac0285202c2700a1280508c0584200c1f01e0eacc06c018320541701e0880d03c0681d02e2f8171780b8ba05c570362a81714c0b8a405b5702dab01ad540b69e05b4e02da681697c0b4ba05a5b02d2b8229540b4a606a4f0352581a91c0d48606a3f0351e81a8ec0347206a37b491a81a8cc034620595f02cad8225640b2ae0595302ca881a53c0d29606947034a181a4fc0d277671390349b81a4cc0d2631e12f8b895c4449df02460585f02c2d8221640b0ae0585302c2881a13c0d096068470342181a0fc0507a0683bb281c81a0dc0506a0683303418ac00bd52056a00273e8119a407cc0036570172780981b1780b8ba01c5902e2a817148038a201c5002dae806d640b6aa01b51035a4816d04114ac08a5502d268169280b48c08a45045220268e81346c0a959054a880a1740f0b20285503c288224c005078078300362c8171440b6ba08b5502d2d0169581349409a468e11f02a8c80b2b40595602ca50165180327c0a93ab109b0064c81125c0892d054169540940503a078190140a81e04415260078300362c8171440b6ba08b5502cad0165580f294099465709f01e4c80f254541260142f0161680b0ac02852014270161280b08c0284200c1f01e0eac006c018320541701e0880f03c0781d 15 32767 7 127 11 2047 21 2097151
def cur_69 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_69_11 (Nat.sub p 352)) (cc_69_10 (Nat.sub p 320)) (Nat.blt p 352)) (cc_69_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (Bool.rec (cc_69_8 (Nat.sub p 256)) (cc_69_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_69_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (cc_69_5 (Nat.sub p 160)) (cc_69_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_69_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_69_2 (Nat.sub p 64)) (cc_69_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_69_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def f_69 : Nat → Nat × Nat := unpackForestF 0xb2a35b4136b2939b3036b283900b4bafa5db1136af951b0036af85100b4700a4dae25400a4bac951ac85100a47ab819aa143aa82eaa04300a45a825da8139a803900a3fa6b54a6a5400a3ba3a5da3a55a3a54a3941a384100a37a0a54a0928a0924a0828a082400a339e9369f0369e8190094b9d851009479b8399b8389b8340093f95b5d95b5595b4795937959369581b96b5d96b559683695819958170093b94458940410093790b5d909369092e9135d9103690819009338fa448cc5b8e26c8e1608cc578ca548ca460092f8ac5b8ac578aa4a0092b89348891487dc5b883607dc577db4a8693d7d94a8534b853477d83c83a4a838467d831829387e34b7e3477e13a7e047801487e03f7ec587e9387e0377d830009277c9447445b7b96c74457741547414c7935a793567414677b4b77b47741447634b763477401874b4b74b4774014009237023b7284c702377003670a36709367002e0084b6f151008476d1396d1386d1340083f63b5d63b5563b4763a4b63a4763a3b6904c63a3763837638366382f64b5d64b5564a4664a36649366382e638270083b5fc585f941618185f93b60140600505f9370083759b5d59a3b5d84c59a375c925598365ab5d5aa365a9365982e5981e0083358a4455c5b5726c5706055c5755a5455a460082f5245b524575225b5224b522435214a0082b50b48508484045b4fb60404574034a4d94c4d8184015b4c14c4c0184014b4a14c4a1344a0184014348b4b48b474013c47946401314683843b4b43b47439474393f444584393740130409314193d41935409304083d4004a008273f04436c5b3e06c36c57368543684c3bb5a3bb56368463a34b3a3473684438b4b38b473682c3734b37347368240082335144350483245b3416c3245732146328153204a0081f30a48308442d45b2f86c2d4572e8262d24a2d0462d01e0081b2c2482945b2a2602a1602a060294572924a00817280440145b2706c014570135d2586c0135722a52229522285e230442285201355218440134f1fb64202541f85c013471e35d1e3550124a1d04d012461ab5d1ab551aa4a1aa460114a1893a189361884d011461793815b4b1685c15b471593a01124149240105713948131240104f1135d11355110460104a0ed680f4580f1380e92401047084590d234084510835a083560b4580825d0a450082550823d08a5408235010460103a06b640103701a56049420484201a5401a46032540194a022540184a01036008130001f 9 11
set_option maxHeartbeats 0 in
theorem rc_69 : dagCheckRootsV4 m_69 g_69 ep_69 362 bds_69 (dagTraceF m_69 s_69 8 f_69) (cur_69 0) s_69 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_0 : treeBlockF 0 32 (dagCheckNodeV4 m_69 g_69 ep_69 bds_69 362 (dagTraceF m_69 s_69 8 f_69) cur_69) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_1 : treeBlockF 32 64 (dagCheckNodeV4 m_69 g_69 ep_69 bds_69 362 (dagTraceF m_69 s_69 8 f_69) cur_69) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_2 : treeBlockF 64 96 (dagCheckNodeV4 m_69 g_69 ep_69 bds_69 362 (dagTraceF m_69 s_69 8 f_69) cur_69) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_3 : treeBlockF 96 128 (dagCheckNodeV4 m_69 g_69 ep_69 bds_69 362 (dagTraceF m_69 s_69 8 f_69) cur_69) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_4 : treeBlockF 128 160 (dagCheckNodeV4 m_69 g_69 ep_69 bds_69 362 (dagTraceF m_69 s_69 8 f_69) cur_69) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_5 : treeBlockF 160 192 (dagCheckNodeV4 m_69 g_69 ep_69 bds_69 362 (dagTraceF m_69 s_69 8 f_69) cur_69) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_6 : treeBlockF 192 224 (dagCheckNodeV4 m_69 g_69 ep_69 bds_69 362 (dagTraceF m_69 s_69 8 f_69) cur_69) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_7 : treeBlockF 224 256 (dagCheckNodeV4 m_69 g_69 ep_69 bds_69 362 (dagTraceF m_69 s_69 8 f_69) cur_69) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_8 : treeBlockF 256 288 (dagCheckNodeV4 m_69 g_69 ep_69 bds_69 362 (dagTraceF m_69 s_69 8 f_69) cur_69) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_9 : treeBlockF 288 320 (dagCheckNodeV4 m_69 g_69 ep_69 bds_69 362 (dagTraceF m_69 s_69 8 f_69) cur_69) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_10 : treeBlockF 320 352 (dagCheckNodeV4 m_69 g_69 ep_69 bds_69 362 (dagTraceF m_69 s_69 8 f_69) cur_69) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_11 : treeBlockF 352 362 (dagCheckNodeV4 m_69 g_69 ep_69 bds_69 362 (dagTraceF m_69 s_69 8 f_69) cur_69) = true := by decide +kernel
theorem nj_69_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_69 g_69 ep_69 bds_69 362 (dagTraceF m_69 s_69 8 f_69) cur_69) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_69_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_69_1 h1 h2)
theorem nj_69_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeV4 m_69 g_69 ep_69 bds_69 362 (dagTraceF m_69 s_69 8 f_69) cur_69) i = true := block_join nj_69_1 (fun _ h1 h2 => treeBlockF_at nb_69_2 h1 h2)
theorem nj_69_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeV4 m_69 g_69 ep_69 bds_69 362 (dagTraceF m_69 s_69 8 f_69) cur_69) i = true := block_join nj_69_2 (fun _ h1 h2 => treeBlockF_at nb_69_3 h1 h2)
theorem nj_69_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeV4 m_69 g_69 ep_69 bds_69 362 (dagTraceF m_69 s_69 8 f_69) cur_69) i = true := block_join nj_69_3 (fun _ h1 h2 => treeBlockF_at nb_69_4 h1 h2)
theorem nj_69_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeV4 m_69 g_69 ep_69 bds_69 362 (dagTraceF m_69 s_69 8 f_69) cur_69) i = true := block_join nj_69_4 (fun _ h1 h2 => treeBlockF_at nb_69_5 h1 h2)
theorem nj_69_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeV4 m_69 g_69 ep_69 bds_69 362 (dagTraceF m_69 s_69 8 f_69) cur_69) i = true := block_join nj_69_5 (fun _ h1 h2 => treeBlockF_at nb_69_6 h1 h2)
theorem nj_69_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeV4 m_69 g_69 ep_69 bds_69 362 (dagTraceF m_69 s_69 8 f_69) cur_69) i = true := block_join nj_69_6 (fun _ h1 h2 => treeBlockF_at nb_69_7 h1 h2)
theorem nj_69_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeV4 m_69 g_69 ep_69 bds_69 362 (dagTraceF m_69 s_69 8 f_69) cur_69) i = true := block_join nj_69_7 (fun _ h1 h2 => treeBlockF_at nb_69_8 h1 h2)
theorem nj_69_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeV4 m_69 g_69 ep_69 bds_69 362 (dagTraceF m_69 s_69 8 f_69) cur_69) i = true := block_join nj_69_8 (fun _ h1 h2 => treeBlockF_at nb_69_9 h1 h2)
theorem nj_69_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeV4 m_69 g_69 ep_69 bds_69 362 (dagTraceF m_69 s_69 8 f_69) cur_69) i = true := block_join nj_69_9 (fun _ h1 h2 => treeBlockF_at nb_69_10 h1 h2)
theorem nj_69_11 : ∀ i, 0 ≤ i → i < 362 → (dagCheckNodeV4 m_69 g_69 ep_69 bds_69 362 (dagTraceF m_69 s_69 8 f_69) cur_69) i = true := block_join nj_69_10 (fun _ h1 h2 => treeBlockF_at nb_69_11 h1 h2)
theorem nc_69 : ∀ i, 0 ≤ i → i < 362 → (dagCheckNodeV4 m_69 g_69 ep_69 bds_69 362 (dagTraceF m_69 s_69 8 f_69) cur_69) i = true := nj_69_11
theorem lb_69 : LowerBin m_69 s_69 g_69 9 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_69 kn_69 sub_69 gl_69 rc_69 nc_69

def m_70 : Nat := 0xffff0000ffff0000
def s_70 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_70 : Nat := 0x1170000131f0000
def ep_70 : Nat := 0x12080000000000000000000000160000000c000001060000020e000001120000131000000114000010100000
theorem epk_70 : ep_70 = edgePack m_70 g_70 := by decide +kernel
def bds_70 : List (Nat × List Nat × Nat × Nat) := [(m_21, s_21, 7, g_21), (m_53, s_53, 5, g_53), (m_50, s_50, 5, g_50), (m_32, s_32, 5, g_32), (m_34, s_34, 5, g_34), (m_51, s_51, 5, g_51), (m_0, s_0, 4, g_0), (m_33, s_33, 5, g_33), (m_13, s_13, 4, g_13), (m_42, s_42, 4, g_42), (m_16, s_16, 5, g_16), (m_11, s_11, 4, g_11), (m_9, s_9, 4, g_9)]
theorem kn_70 : KnownBin bds_70 := by
  intro b hb; simp only [bds_70, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_21
  · exact lb_53
  · exact lb_50
  · exact lb_32
  · exact lb_34
  · exact lb_51
  · exact lb_0
  · exact lb_33
  · exact lb_13
  · exact lb_42
  · exact lb_16
  · exact lb_11
  · exact lb_9
theorem sub_70 : ∀ b ∈ bds_70, m_70 &&& b.1 = b.1 := by intro b hb; simp only [bds_70, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_70 : ∀ b ∈ bds_70, canon b.1 g_70 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_70, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_70_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xee01da0b8ca7102e201c4038806f86df01bc0b7806ec1dd03ba037406e02c9cb5ed6bc05549a6133852682498e78eace8d33aa058286219dc02c0001 0x1e350029501f35a1d35606b4e06b4207a5e04a5a04a5607a5205a4e01a4a01a4605a4202a3e02a3d02939029310192d029290192502921029480594403b5c193500595c029500985c180501602809824099540282c1105c1005403b4f06b4b03b4706b431b24f1a24b172471524306a3f03a3b03a3706a330294f0294b02947029430293f0293b0293a02937039360292f0812e0292b0292702923029220984f1404b09847130430583f0982f1202b098270f0230281f03c5f06c5b03c5706c532935f2835b243572035306b4f03b4b03b4706b4302a5f02a5b02a5702a5302a4f02a4d02a4b02a4a02a4703a4602a4502a3f0723e02a3b02a3702a3302a320295f0795e0295b0295a029570495602953029520294f0594e0294d0293f1c13e0293b0193a029370193602933029320292f0292e0292d028160e01407a6c04a6404a4c05a480c24404a400696002948059440ab5c03b5402b4c03a3c02a3802a3405a30029280592407b5e04b5a04b5607b5205b4e05b4d06a490aa4101a3d02a3901a3502a310594d059450193d02939019350293102929029210393a039360292e0292d03a4a03a4602a3e02a3d0795e029520594e0294d0193a019360592602925028160801406c5f0b45b06c5708c5301b5f08b5b01b5708b5301b4f06b4b01b470a34305a5f07a5e05a5b04a5a05a5704a5605a5305a5205a4f0924e05a4b03a4a05a4703a4605a4305a4202a3f02a3e02a3d0595f0595e0295b0595702953089520594f0594e0294b0594702943071420193b0193a029390193701936029330293101927019260192506b4f06b4b06b4706b4301a4f01a4b01a4701a4301a3f01a3b01a3701a330294f0294b02947029430293f0293b02937029330192f0192e0192701923019220884f0884b08847088430683f0683b0683706833018270281f06c5f06c5b06c5706c5301b5f01b5b01b5701b5301b4f01b4e01b4b01b4701b4306b4202a5f02a5b02a5702a5302a4f02a4b02a4702a4301a3f01a3e02a3d01a3701a3501a3301a320195f0795e0195b0195a019570495601953019520194f0694e0194b0194a019470394601943019420193701936019350192f0292e0192d018160501406c5e08c5201b4d01b4507a5e04a5a04a5607a5201a4e01a4d01a3e01a3a01a3601a320594d059450193e0193901932029310592d02929059250292106c5f08c5b06c5708c5301b5f01b5e01b5b04b5a01b5701b5601b5307b5201b4f01b4e01b4b03b4a01b4701b4601b430334201a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3e01a3d0595f0295b05957029530594f0294b05947029430193f0193e0593d0192f0192e0192b0192901923019220292106c5f06c5b06c5706c5301b5f08b5b01b5708b5301b4f06b4e06b4b01b4706b4306b4202a5f08a5e02a5b02a5702a5302a5202a4f06a4e02a4b02a4702a4302a4202a3f02a3d01a3b01a3a01a3701a3602a350295f0795e0295b0295a029570495602953029520294f0694e0294b0294a029470394602943029420293f0593e0293d0192f0192e0192da234fa034b9e3479d3439b24f9a24b8d247822438123f7f23b79237752337314f7114b68147661435d13f5113b2b1370d1330612f0412b02127011230001f 15 32767 6 63 11 2047 20 1048575
def cc_70_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xda17680d516e5cb902e40b902e40b416d00b402bc596665809602580901a3826d84cbb3200a49221c7451a0c6020a3824109001c20118001 0xed71c1a80595c052a0fc171a9a603a3405270164d1e81a4135e806b4f8d59e1a903b4e076940ed181da107a5e094b4129583d2901a4e054940a9180d2103a3e0747a0e5381ca10593d05272164d414988592d03252164940c9083b5c706a01657014a83705c6a4980a910149405924680480ed3c1da583b4707686e893dc925b6247664860e8fc151d83a37074661653c14a585947052860e4fc1c9f0293b052660e4c82c978292b0b24e0a48c65ae09b50074b8bc9402c2e02850132983251065a789b4b1968e26d0c1d2783a4b0748e0e90c151fb114f60296b851d68a18993f19276324dc4c998392f072560e49c1c918584f050961611c14218583f0705e0a0ac14118581f050361605c140983c5f078bc0f16c262d03c59a08b00f15c1e2b03c530f8a40f1467a2803b5f076b60ed5c1da982b4f0569c0ad36692fcc25b904af0c94c1d2783a4e0349b089301d2583a490748e069141d2183a4276482c89001d1f83a3b0746e0e8cc2caf8295b0b2ae0a54c1ca78394e0b29a0e4fc1c9f0293b052720a4cc1c99029310b25e0a4ac2c93829230709cb0130152c05a540f2d8125900cae02958542a806540d80a1f14c03288124f0149c0893405260680503cae0495403288784f0c80a01b5c032b8261704c2e0b854078d89d1802d3602a604c2d8065a00cb2029600f2b812550e89e019344a0d85c0504c122202c130481e4f0149c2313405260840d0a80a02a34 14 16383 6 63 11 2047 19 524287
def cc_70_2 : Nat → List (Nat × Nat) := unpackCursorV4 0x948ef6cdec03c84760cec01d413a807092e101be13589612891c4f4b98d7308458249e49285228a3f186270b8316042c004c3060e00ae01000008000 0xc04b80e9502d2606a480d48816902f81203c5f0d8b60f15c362985b5f0d6bc16d6c25ad05b57096ac16d4c2da902b4f0569c0ad37292fe425bc24af7894c352783a4b0748e1a90c2d1f81a3d0b4761a8e42d1b81a350b466168c42caf8295b0b2ae0a54c14a58394a052920e51c1ca302943052820e4dc1c9b039350b25e164b8149585927052461a4880cae02958b82a8065403cb604964092780a4e0449a02930036a0065701e36594600b4d80a982c0b601968032c80a582b8360785c090a80a8e02d1a0796c092c81e4f0149c5513405261500d01da503b460f4bc12968252b07a520349c0e9281d2301a420547c0a8f41ca702942052720a4c40c96829290324a0a4841e2f83c5b078ae0f14ed9afda35bac6af4cd4c1da783b4b0768e0ed0c152f82a5b054ae0a94c152783a4e0549a0a91c152282a43054840a8fc151d82a37054660a57c3caf0295b052b40a55c24ab02953052a40a51c1ca3029450527f484f8149d8193a0526e064d81499829320525e0a4b8149683b4f056960ed1c1da183a4f074960e91c1d2184a3f09476128dc25198394f052960a50c249f8293b0926e0a4cc2c978292b0b24e0a48c1da782b4b0768e0ed0c1d2783a4b0748e0e90c3d1f87a3b0f46e1e8cc1ca78294b05286164fc149d8593705266164bc149585927052460ed601d1804c680f8c007172722c03c54038a00693209203104c09ad01f5800dae40350114b80e9601d2a04a50600b80ed400da003a3003260260f0262c07c5003498e090178260bb58136a012d203da00193c7e2600f1b00e3401c64968c0131603e2803b6c946c006931f1200596c052c1241b1702603b5803478260f03e2835240098b01f1400d263d240132991450026b407d60036b8f0d42392e03a58074a81e942312603a440525016491682e440240769e0ed2c1da383b430349e0692c0d2381a430347e068ec0d1b81a330b29e0a52c2ca3829430727e0a4ec14998192f032560649c0c9183a34 15 32767 6 63 11 2047 19 524287
def cc_70_3 : Nat → List (Nat × Nat) := unpackCursorV4 0x97d791998bd785997d616ebb6c496ac669465c35569649f3445637b33780321632002c962c022b822b80288c1c711325057703c602c402810280004900010000 0x1da783b4b0768e0ed0c0d2781a4b03486068fc0d1d81a37034660e53c1ca58394707286124fc249d8493709266064bc0c9581927032460ed3c1da583b47076860693c0d2581a4903486069040d1f81a3b0346e068cc1ca78394b0728e0e50c349f8693b0d26e1a4cc0c978192b0324e0648c2da785b4b0b68e16d0c1d2783a4b0748e0e90c1d1f83a3b0746e0e8cc0ca78194b0328e0650c0c9f8193b0326e064cc0c978192b032460ed3c1da583b47076860693c0d2581a4703486068fc0d1f01a3b034660e8c814a78294b0528e0a50c149f8293b0526e0a4cc0c978192b0324e0648c45a788b4b1168e22d0c1d2783a4b0748e0e90c1d1f8194f032960651c0ca18193f0325e064ac0c918684f0d0961a11c34218683f0d0761a0dc34198382f070560e09c1c118181f030360605c0c0981c5f038bc0716c262d01c59fc8b00715c0e2b01c530f8a407147ea2803b5f076b60ed5c1da981b4f0369c0ed340d2f81a5b034ae0694c0d2781a4e0349a068fc0d1f01a3b03472068cc1d1901a310d2be1a56c34ab869530329e065382ca6fc14c03296065240ca381945032860650814a0fb1400727e0e4ec1c9b839330325e064ac0c93819230309de81303e2e0ab48036881e9b0253201a4c0f49006910252003c6c038c0231403d3604a58114a006d201da002a3c0d280164b0349003c5f118bde116c1e2b88c53118a406d7c45ad81b57116a606d3c0da683b4b0769406d1c1da301b45114be1e978552d84a5aee4ae12958452987a520349e069380d2683a3f0747c0e8f444af8695bd22ae1a54c34a78394b0728e1a50c509f8193b0d272064dc3499869311525e164b4349582929ec24e164943491829210d8bc1f14815af03b5a076ac0ad482da705b4d0347a228e40d1a88a31052b20a5442ca6859450927a0a4e4249a829310b25c1a488162f82c5e058ba1ad7c25ad84b570f6a616d3c1da685b4be869216d1c1da285b430b6821e97c252d84a570f4a61693c0d2685a4b114921691c0d2285a430b482228fc351d86a37114660a56c24ad02959092ae1255814a9829510928e1251824a28593f05276164dc14998592f0b25c0a4ac2c93829231124413164362884b5a096ac06978252d04a56034a41a9381d2503a460d4840a8f8151e8495e052a40a4e414988192d0525206494149084c5f098b613164262b84c530d8a212d7c25ad84b57096a61ad3c35a586b470d6860a97c252f02a5d054ae0a954152982a520549e0a92c152382a430547e0a8ec151b82a33052ae1255814aa8294f0d29c0a52c14a5029470728c0a50c14a10293fe427c0a4ec0c9d029370326c0a4cc14990292f0525c0a4b4262d04c56076bc0ad6815ab03b520969c12d343524ec2410347bc08e40d1a8aa31052b20a5442ca6859450b27a0a4e42c9a82931096b412d5845a76b342034bc0a968152b01a52dc49c0e9281d230aa420947c128f424af049520b27a164d42c96819290b24a064840d2205924094a80e8d01e366c460036d9acd83513604a68094c82a9803d2e04a540525016490162f82c5e058ba12d7c1dae84b5b096b212d5c1daa84b53de6a212d3c25a584b47096861297c0d2e84a5b094b21295c0d2a84a53da4a21293c252584a4709486228fc351d86a37d24661257c24af0595d0929e1253814a582949052861250814a08593f05276164dc14998592f052561649c149186b4f096961ad2425a386b430d6821e93c252584a470f4861a8fc351d86a370d4660a53c14a5829470527e0a4ec149b829330525e224b8149582927052460a4882c278683f0d0761a0dc34198882f110562209c44118281f0d8be1316c362c84c570d8a61b1443daf84b5b096ae1ed4c35a786b4b0d68e1ad0c152f82a5d054b60a968152b84a56054aa0a93c152582a47054860a8fc451f02a3b0546e0a8cc15190295f0b2bc0a57414a78694e052960a52814a383946052860a508149f8893e05276064e8149b81936052660a4c814978292e0525a0a05b380a01b5c0b6b01ad500da8029580b2a816930252406a440948006d101e36634600d6d806da00db205b600b2d80a583103602b44 16 65535 6 63 11 2047 19 524287
def cc_70_4 : Nat → List (Nat × Nat) := unpackCursorV4 0xa2b194f78fd483b176f371176a1c6a006a006a0068c568c0678561595b9755d74da13efb3b4e365435443501350035003482348034412b251df511330cd10033 0x3c5f03c5e04c5d03b5f03b5e03b5d03b4f03b4e03b4b03b4903b4304b4203b4103a5f01a5d03a5b03a5903a5701a5503a539f25104a4f04a4b04a4704a4303a3f03a3b03a3703a330395f0595d0395b02959039570395503953029510494f0494b04947049430393f0393b03937039330692f0692b069270692303c5f03c5d04c5b04c5a03c5704c5603c5503b5f03b5e03b5d04b4f04b4e04b4d07a5f04a5b08a5904a5707a5307a5108a4f03a4b08a4903a4708a4308a4107a3f01a3d07a3b08a3907a3701a3507a3307a310795f0495b069590495706953069510694f0394b03947069430793f0593d0693b02939079370593506933029310892f0692b089270692307c5e07c5207b5e03b5a03b5607b5201b4e01b4d01a5901a5101a4d01a4501a3d01a3901a3501a310593d02939059350293101c5f07c5e01c5d07b5f04b5b04b5707b5301b4f01b4d01b4b9c34901b4703b4501b4301b4101a5b04a5a01a5901a5701a5601a5301a5101a4701a4601a4501a3f01a3b01a3701a330795f0495b04957079530194f0194d0194b02949019470594501943019416513f5b13b4d137291330192f0192b019270192304c5f04c5b04c5904c5704c5308c5101b5f04b5e01b5d01b5701b5504b5304b5201b4f08b4b01b4708b4301a5701a5601a5504a4f08a4e04a4b03a4a04a4703a4604a4304a4204a3f07a3e04a3d0495f0495b04957049536414f5a14b4c147281430893f0193b01937089330492f0492d0492b029290492705925049230292103b4f03b4b03b4703b4301a4f01a4b01a4301a3f01a3b01a3701a330494f0494b04947049430393f0393b03937039330192f0192b019270192304c5e04c5a04c5604c5203b5e04b5a04b5603b5201b4e01b4d01a5901a5101a4d01a4901a4501a4101a3d01a3901a3501a316314d591494a145271410593d02939059350293104c5807c5001a4c382409504c0795c049541e13c019349301404b4f04b4b04b4704b4301a4f01a4b01a4901a4301a4101a3f01a3b01a3701a330494f0494b04947049439713f9613b94137921330192f0192b019270192304b4f04b4b04b4704b4305a4f05a4b05a4705a4304a3f04a3b04a3704a330194f0194b01947019430193f0193b019330192f0192b019270192304b4f04b4b04b4704b4301a4f01a4b01a4301a3f01a3b01a3701a330294f0294b02947029430293f0293b02937029330192f0192b019270192304b4f09a4f0ba4b0ba4709a4304a3f04a3b04a3704a330194f0193f0193b019330192f0192b01927019230984f0b84b0b847098430483f0483b04837048336202f5702b49027250230181f0181b018170181301c5f01c5e04c5d01b5f01b5e03b5d9935c01b5b01b5901b5701b5501b5301b52983519135004b4f04b4b04b4704b4301a5f01a5e01a5d01a4f01a4e01a4b01a4901a4304a4201a4101a3f01a3b01a3701a330195f0195e0595d9015c0195b0195901957019550195301952029518f1500494f0494b04947049436113f5613b48137241330192f0192b01927019230185e8e05c07c5e04c5d01b4d01b4503a5a03a5604a4607a4504a3e04a3d0292902921078268a02407c5e07c5201b5e03b5a03b5601b5207b4e07b4d08a4908a4101a3d04a3901a3504a316014d461450593d02939059350293107b4e04b4d01a3d01a350795c88018870140992407b4f04b4b8a34904b4707b4307b4101a4f01a4d04a4b01a4701a4501a3f08a3b01a3708a330194f0993f8913b09937861330492f0784f0484b04847078435f03f5403b44037210330882f0182b01827088238501f0981b098178401307c5f04c5b8c45904c5707c5307c5101b5f01b5d04b5b04b5a01b5704b5601b5501b4f08b4b01b4708b4301a5f01a5e01a5d07a4f8b24e07a4b03a4a07a4703a4607a4307a4204a3f04a3e04a3d0795f0495b04957079535e14f5314b43147201430893f0193b01937089330792f0592d0792b0292907927059250792302921078268302403c5f08c5b03c5708c5301b5f07b5e01b5b01b5a01b5704b5601b5301b5201b4f8034e01b4d01a5f01a5b01a5701a5301a4b03a4a01a4901a4701a4601a4301a4101a3701a3601a350895f0695b08957069530694f0394b03947069430193f0193d0193b02939019370593501933019310192f0192b0192901927019230692103c5e08c5201b4d01b4601b4507a5e04a5a04a5607a5201a4e01a4d01939069310592d02929059250292103c5f03c5e03c5b03c5703c5308c5201b5f08b5b01b5708b5301b4f03b4e01b4d01b4701b4503b4303b4203a5f07a5e03a5b03a5a03a5704a5603a5303a5201a4701a4601a4503a3f8023e03a3d0695f0695b06957069530394f0394b03947039430693f0193b01937069330392f0392d0392b0292903927059250392302921 16 65535 6 63 11 2047 20 1048575
def cc_70_5 : Nat → List (Nat × Nat) := unpackCursorV4 0x25a361d535418d4018 0x7b4f03a4b03a4903a4703a4303a4103a370794f0494b04947079430893f0893b08937089330392f0392b03927039230684f0484b04847068430683f0683b06837068330382f0382b03827038230681f0681b068170681303c5f07c5e03c5d03b5b04b5a03b5903b5703b5603b5303b5103b4703b4603b4507a5f04a5b04a5707a5303a4f01a4d03a4b08a4903a4701a4503a4303a4103a3f03a3b03a3903a3703a3308a310695f0495b04957069530394f0394d0394b02949039470594503943029410393f0393b03937039330692f0692b069270692303846a304404c5e04c5204b5a04b5608b4e0ab4201a5e03a5a03a5601a5207a4e01a4a01a4607a4204a3e04a3d0592d02929059250292103c5f04c5e03c5d03c5703c5504c5304c5203b5703b5603b5504b4f07b4e04b4d04a5f04a5b04a5904a5704a538c25108a4f03a4b03a477824304a3f01a3d04a3ba123904a3701a3504a3304a310495f0495b049590495704953069510694f0394b03947069430493f0493d0493b02939049370593504933029310b12f0692b089270692303c5e03c5904c5203c5104b5a04b5603b4a03b4601a5e04a5a04a5601a5201a4e03a4a03a4601a4203a3e03a3d06939069310592d029290592502921 14 16383 6 63 11 2047 20 1048575
def cur_70 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (cc_70_5 (Nat.sub p 160)) (cc_70_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_70_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_70_2 (Nat.sub p 64)) (cc_70_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_70_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def f_70 : Nat → Nat × Nat := unpackForestF 0xa308802d3e851c80b4b9f4a202d1c05a1ce3490149e0292e39ae473519227f244ee54264913793029244ce39a84715c8e2a11c1700523c1c598349d08d26109dc381887029084ce100fc2013830480290c051fc023e01476f5161ea283d14c7a280f4130051bbb45b764aeec49c0519ba3490129ee44f804a5b8239696a2dc939a528b54606a6c0d49b1a51980947670280250d792faf25b628c0c41b1792bafa5c5f048bc94c049fae154526bea4d6d5e302b96c570d8a4d5d509a2a034526a6a44f8049d964582c8a09d160b12f9625b498c092d81243616257444b88893114a0220242c4a658930f1af1e35a3f0b878d58f41a1e3522c4826693ccd259bb50370b86691cd1261a0243348658900b4a79694b2f4a05a51cb4a19604c0126e5455039af8735b258c04a5b094360735721268440b0841a073531d6b43cd4075ab0713e0f49e1e92c61a80c0500f48e2c0a03d218784b0f0861e0ac402e080540f0461c050049986244078b60ed0c1d270401407284024bc140a0092b036840249c04918001f 8 11
set_option maxHeartbeats 0 in
theorem rc_70 : dagCheckRootsV4 m_70 g_70 ep_70 164 bds_70 (dagTraceF m_70 s_70 8 f_70) (cur_70 0) s_70 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_0 : treeBlockF 0 32 (dagCheckNodeV4 m_70 g_70 ep_70 bds_70 164 (dagTraceF m_70 s_70 8 f_70) cur_70) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_1 : treeBlockF 32 64 (dagCheckNodeV4 m_70 g_70 ep_70 bds_70 164 (dagTraceF m_70 s_70 8 f_70) cur_70) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_2 : treeBlockF 64 96 (dagCheckNodeV4 m_70 g_70 ep_70 bds_70 164 (dagTraceF m_70 s_70 8 f_70) cur_70) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_3 : treeBlockF 96 128 (dagCheckNodeV4 m_70 g_70 ep_70 bds_70 164 (dagTraceF m_70 s_70 8 f_70) cur_70) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_4 : treeBlockF 128 160 (dagCheckNodeV4 m_70 g_70 ep_70 bds_70 164 (dagTraceF m_70 s_70 8 f_70) cur_70) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_70_5 : treeBlockF 160 164 (dagCheckNodeV4 m_70 g_70 ep_70 bds_70 164 (dagTraceF m_70 s_70 8 f_70) cur_70) = true := by decide +kernel
theorem nj_70_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_70 g_70 ep_70 bds_70 164 (dagTraceF m_70 s_70 8 f_70) cur_70) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_70_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_70_1 h1 h2)
theorem nj_70_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeV4 m_70 g_70 ep_70 bds_70 164 (dagTraceF m_70 s_70 8 f_70) cur_70) i = true := block_join nj_70_1 (fun _ h1 h2 => treeBlockF_at nb_70_2 h1 h2)
theorem nj_70_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeV4 m_70 g_70 ep_70 bds_70 164 (dagTraceF m_70 s_70 8 f_70) cur_70) i = true := block_join nj_70_2 (fun _ h1 h2 => treeBlockF_at nb_70_3 h1 h2)
theorem nj_70_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeV4 m_70 g_70 ep_70 bds_70 164 (dagTraceF m_70 s_70 8 f_70) cur_70) i = true := block_join nj_70_3 (fun _ h1 h2 => treeBlockF_at nb_70_4 h1 h2)
theorem nj_70_5 : ∀ i, 0 ≤ i → i < 164 → (dagCheckNodeV4 m_70 g_70 ep_70 bds_70 164 (dagTraceF m_70 s_70 8 f_70) cur_70) i = true := block_join nj_70_4 (fun _ h1 h2 => treeBlockF_at nb_70_5 h1 h2)
theorem nc_70 : ∀ i, 0 ≤ i → i < 164 → (dagCheckNodeV4 m_70 g_70 ep_70 bds_70 164 (dagTraceF m_70 s_70 8 f_70) cur_70) i = true := nj_70_5
theorem lb_70 : LowerBin m_70 s_70 g_70 9 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_70 kn_70 sub_70 gl_70 rc_70 nc_70

def m_71 : Nat := 0xffff0000ffff
def s_71 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_71 : Nat := 0x155700001f7f
def ep_71 : Nat := 0xa28000000000000000000000042000000600000040200000e0800001002000010200000155400001040
theorem epk_71 : ep_71 = edgePack m_71 g_71 := by decide +kernel
def bds_71 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3), (m_36, s_36, 5, g_36), (m_39, s_39, 5, g_39), (m_8, s_8, 4, g_8), (m_22, s_22, 6, g_22), (m_38, s_38, 5, g_38), (m_7, s_7, 4, g_7), (m_35, s_35, 4, g_35), (m_31, s_31, 4, g_31), (m_58, s_58, 6, g_58), (m_14, s_14, 5, g_14)]
theorem kn_71 : KnownBin bds_71 := by
  intro b hb; simp only [bds_71, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_3
  · exact lb_36
  · exact lb_39
  · exact lb_8
  · exact lb_22
  · exact lb_38
  · exact lb_7
  · exact lb_35
  · exact lb_31
  · exact lb_58
  · exact lb_14
theorem sub_71 : ∀ b ∈ bds_71, m_71 &&& b.1 = b.1 := by intro b hb; simp only [bds_71, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_71 : ∀ b ∈ bds_71, canon b.1 g_71 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_71, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_71_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xcd07283c223080be12f80ba12e80b906c87b00ac00af06b81a916a40a806982993619382120417b19b4e6c05ac15e352d33e34ad301a8001 0x504002a3000c9601e4800349807a40100ae07c5503c298029400e89a0120600b6b008b500d9a4006d000349807a400c8a60165000f24001b580b9a8016d202c6801414000c9e0384c02627807930098a20128c0284a81214c03ca00444d0090300793002dae022d401e4bc07a5203d25038918052bc0795a068ab00a5481129c0594a02ca301e508090b43645f1aa2d8c515c588a62b35a015a9016d28506842615f128ad88455c382a61a14f0c0a585451c202860193d06098812168112b805954044a601a510032b801a6c03d300245b00b2c80614c02ca2016d74116b205b55045a8806574072b20195501ca880e524072820385a0142c00e128030340795000cae0231680c8ac02b5e045ad014d58056a40794903ca08064f4092720193502498812168078be0a45b0422b80f14c034be03a5b00d2b80e94c0349e07a4b00d2381e90c052bc07156020a70165180925c0485a00c1500f178078a401a4d00d2280a578072b403956014a90064b8032540192600c9100e168078be03c5b01e2b80f14c074b402a5202d25008908032be0195b00cab80654c0329e0194b00ca380650c0325a0385a00c0959cd3ecc6975c347a99a1d4493e9c4974b247a2921cd88fe644772f23795119c9c53e4829713147850a1c204fe062770113771099b784bd82256b412755091aa413c090969704a488239c4118090866903f0241d99c0dc090663802f0241582c09c090460301f0240d80405c090260001f 14 16383 6 63 11 2047 21 2097151
def cc_71_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xca9ca0c81c80c80aed8558217857427407407406c46a16436406025083ab3a03621cd1a11050c20c00c00c0044040002 0x45ae05b54824a81e8e00d1a401440f270fc4d024083d3500f4b4f0959d92707a42052bc1e569d0ab029521129c165282ca307942090b59517f222de0457b68a60a97ad12b5624e0b48d5057e98adcf157942a72053e28a5c31477c286e44a40c928485a0908412048141037358056a016d2151a0048580d69022d002db434360662d8c8580141005a48114800a8c02d2408a400b6b022d4181a402b405e488b852168a2048481149c169282d2308a420325a1e4a40c9287921090b41208814100195c0f2a0a9178462902a5e114b4a495815290894d2c28a064b43c94819250f242121680c1027358036a0064f0789804858072981e501223623460036d088d800c9e07930 12 4095 5 31 11 2047 19 524287
def cc_71_2 : Nat → List (Nat × Nat) := unpackCursorV4 0x9a53426847675ae81c8b9059aac541a35460849081a7340680d018224c4806a8d01a02143883406004800800 0xa8d0141c5f3440549978912e8a45c1440909016d7445ac85b55116a2065743cac819550f2a212168142c0484a090641204ac8a808c5ab08ac0ad7845ad57356056a51c52444a08193d0f272064d43c988485a030b006972a92a048580f470068d03c9c0393409020f44a00c925246ca28c1409b00d323c1280324812180151a028389c2b93455260a20293896268120600d2649244762500649024244735c0b6a8164e2309a0481884281109700d2a41140090a1089300d2204830 11 2047 4 15 11 2047 19 524287
def cc_71_3 : Nat → List (Nat × Nat) := unpackCursorV4 0xdd07701db07195c507140c1127259b0664299025c2883db5b5f396c45a0550653054814534c9325344931104383091424009001c2001c000 0x1824018240582404b4904b4102a4e03a4206a3e7e2320994d099457d12d069250284e068420383e7c0320182d0582a0382601825038247601a03816049447a25002a4c09a447914404c5e03c5d06b5e8735202b4e02b4203a4d852458423d06a350395e831520294e029420193d0593a0393601935039347512a039268205e800520284e0384d0284c0384a038467f0457b044028420183e0183d7302a780260381e0581d0582405934760440284c0984403c5d0394a039460393e75132019250284e0384a03846028427403e0583a05836730320182504b4f04b4e04b4d06a4f8f24302a3f06a3b06a3702a330293f8e13d8d1378c1358a12f069270384f880430283f0383b03837028330382f0682b03827770237201b0381702b5d04b5902b5504b5106b4906b410195d0795901955079510485a028580484a0483a07a4801a44079480394401b4c05c6c08c606e36c01b646c1380193408b5001b5c07a5a6c25608a4e07a420295e0795a6b156029520494e0194a01946049420485a05c5f06c5b05c5706c5302b5e7035604b4e0695f6f15b6d157069530894f0594b05947089436a139019350485a0484a06a5e06a5205a4a05a460295e0695a06956029520194e0494a04946019420485a06c5a02c5205b5f05b5b05b5705b5304b4d0695f0695b06957069530194d681410593f0593b05937059330485a048320284802a5c662540485808a5c05a5408a4c06a44048405924c05a446326c05a645824c05a446216c6116004860 14 16383 6 63 11 2047 20 1048575
def cc_71_4 : Nat → List (Nat × Nat) := unpackCursorV4 0x86030c021803d967b00ee21c26aea7559e9c3d380264346987560ea0198f2c1c42586678cc0121e24002a784c209800d181610242038407000818004 0x5a4403a5a03a5603a4e9e24201a3d01a350295e0395a03956029529d14e0594a059469c14201936019350482d038250481d04819048150481101a350295e039569a14e059460392e048190481502b4d02a3f02a3b02a3702a330283f0283b02837028330382f0382b038270382302b4f06b4b06b4702b4302a4fa824ba724702a43a523f06a3b06a37a32330294f0394b03947029430393f0693b039379f1330392f9b12b03927991230484798046048450483f0483b04837048330482f0482b04827048230481f0381b038170481306c5a06c5602b5e04b5a04b5602b5206949089410193d0793901935079310485a0484a0483a03a5a03a5603a4e07a420195e0395a03956019520894e0594a05946079420385a0182a0181a04c50039340485805c6c08c6001a6c07a6003a449416c079600295c9315404858048180481004c5d05b5d9635102b4f06b4b06b4702b430195d951510294f0394b03947029430393f0693b03937921330484a04848028420483a048320381a0481204c5d05b5d06b4a06b4605a5d02a4e04a4a04a4602a4206839870310182d90029018258002102b4d02a3f02a3b02a3702a33029360283f0283b02837028330382f0382b038270382302b4d05a5d06a5905a5506a5102a3d06a3906a3502a310295e0293e0293c069260185d0385901855038510283d0383903835028310381506a4f09a4b06a4709a430294e069260384f0984b03847098430382f0682b03827850230381504c5d06b4a06b4602a4e06a4a06a4602a42059360592606839840310182d8b029018257302103c5d0195d0394a039460393e831320185d0184e0384a03846028428903e0583a0583680032019347e04406a3403934039248605c0985479024019347d044059347c04404b4802b400284c0484481024039340285c0183c0581c 15 32767 6 63 11 2047 20 1048575
def cc_71_5 : Nat → List (Nat × Nat) := unpackCursorV4 0x989530066004c0092972406460c88184b2fc3581e2f045d82b321660294e5202a3052c6a1cf3a26614cac5909421002c585800908118223004210021 0x5b5808b5001b4c05b4801b4407b40b9150bf14801944048300483001b5c05b5801b54bd35005b48bc3400195cbb150b8140048500483001b4401b4401b4403c5e03c5201b5e02b5201b4d05b4a01b4601b4501b4403a5a03a56b924db824501a3e07a3d0395a039560194e0194d0193eb713d0385a038560183e0183203b4f03b4b03b4703b4303a460184f0184b01847018430183f0183b018370183303c5f03c5b03c5703c5301b5f01b5e01b5b03b5a01b5701b5601b5302b5201b4f01b4e01b4b05b4a01b4701b4601b43c034203a5f03a5a03a5703a56be24fba24701a3f01a3eab23d0195f0195b0395a0195701956019530194f0194e0194b0194701943b61420192b01929019210385b0385a03856038530484b048430183eb503c0183b01839018330183204831048300181b018130895c059540894c069440195c01a6c07a60b216c059640295cb0154ae14c0594405b5d08b5905b5508b5103b4db03450195d0395901955039510394903941019250384a079500195c08c5aae45602b5e08b5aad35602b5207949079410193d0793901935079319a05a03a5a01a5601a4e07a4201a350295e0395a03956029520894e0594a0594607942019350385a03c5fb345bb145703c5301a5f03a5b01a5703a5301a4f07a4b01a4707a4301a350295eaf156ac14e05946ab12e9905a02c5e02b5f02b5b02b5702b5306b4905b450295f0295b029570295303949019450393f0393b03937039330285a9804402b5e06b4602a5606a4e05a4603935039290192504835048290482505b5d06b5905b5506b5102a5e02a5d02a4e02a4206a3a06a360195d0395901955039510392d039250485d048590482d0482506c5a06c5602b5e06b5a06b5602b5205a4a05a4605a3605a3506949a21410193da6139019359c1310484d048450483d04839048350483105b4602a5e06a5606a4ea412901925048290482501a44a103c0483002c5e02c52a234d06b4502a5e02a5201a4d05a4a03a4601a4503a449e23a03a360295e0395a03956029520194e0194d9c13aa01360392e0592d03856048550484d048450482d038250481d048190481504811 15 32767 6 63 11 2047 20 1048575
def cc_71_6 : Nat → List (Nat × Nat) := unpackCursorV4 0x912d1926300c3c98312fd25e6538526f06de01bc0350a6a00c345840ac905882b0055a1a597480c7c50ee29d813a827404bcb1645259c15d802a0001 0x3c5f03c5b03c5703c5303b5602a5e03a56e124ee024c05a46df2440195f0195b01957019530194f0194b019470194301939019250385a03a5c01a4c07a400895c059540894c0694806944079400195c01a6c07a6003a4cdc16c059680596407960c714c0594401a6c07a600196c0396801964029600295c0995401934ce25007a4801a440895c059540194c05948019440794001a5c07a50cd2400195c059580195407950c514c059440485002a5e03a5d07a5502a5205a4a05a4601a3601a3501956019550394e079420393d039350292d029250385a03856059480594406934d523ad42360294e029420593a0693601926019250384a0384601c5e03c5d01b5e01b5901b52d6351d33500195ed215d0294e029420593a0593601926019250384a038460192403c5a03c5601b5a03b5607b4e01b4d0295e029520594a0594601936d013501926019250385a0385601a4401a4401b50059347604403c5e03c52ce34dcd34502a5e02a5207a4d05a4a05a4607a4505a4401a3601a350795acc1560194e0194d0793d079350592d059259e05a7505601a6407a580296c07958039500193407c5e03c5d05b5d08b5905b5508b5101a5d01a5503a4d09a450195d0195503949039410192d0192504859048510384a0384607a5001a4c079580795005944079500195c0484008c5ac745602b5e08b5ac635602b5207b4e07b4d08a4dc524501a3d01a3507949079410193d019359d05a740560484904841048390483101a5c07a400895c05948079400295e0795a09956029520894e0794dbd136079350792e0792d9c05a73056048190481103c5fdd45bdb45703c5303b5fda357d934fd834701a5f03a5bd725a01a57d125603a5301a4fcf24e07a4b01a4707a43cb24201a3d01a3701a350395f0295e0795b0995aca157c91560395302952c814fc414e0794b0594ac31470594607943c21420193701936019350485b9b05a72056038530484b048430182b048230481b04819048130481103c5e03c5208b4dbc34502a5e03a5a03a5602a5201a4e01a4d07a3abd2360194d0194501929019210385a03856048290482104830 15 32767 6 63 11 2047 20 1048575
def cc_71_7 : Nat → List (Nat × Nat) := unpackCursorV4 0xc801c08fb517b481a819a20c8aaf7e19778d760374835eac5e805d03588958805586558055014f8b4f804d844d014d004c8140193f813e0316500d91070d000e 0x8604405c6c08c6006b4401a6c07a6003a4403a34fe16c0796809964079600295cf5154e91348505402c5e02c5205b4605b4506a5e06a5201a4d08a4a08a4601a4501a44ce23ab92360895af41560194d019450893d089350592e0592da205a8405601a4402c5e02c5206b5a06b5605b4e08b4d06a5e06a5201a4d05a4a05a4601a4501a44cd23ab82360695a069560594efb14d0592e0592d0685a068560584e0584202b4e02b4201a3601a350394a039460a93d0a935f212def1250384a0384601b4f01b4e01b4b01b4701b4302b4203a4f03a4b03a4703a4301a3ff923d01a3b01a3701a3501a330394f0394b0394a0394703946039430193f0193e0a93df112f0792bee127079230384f0384b0384a0384703846038430183f0183b01837018334102f0482b14027048230781f0481be40170481302c5e02c5208b4d06b4502a5e02a5201a4d05a4a03a4601a4503a4407a3a03a3603956079550394e0394d0793a099360392e0692d0385a03856048190481102c6c01c6003c5001a6c05a6006a5003a440296c07958039500194c0592c7f05406a34039340392405950019347d04407c5e03c5d02b5e02b5d01b5902b5503b5201b5101b5002b4e06b4902b4203b4109a5d09a5503a4df5245f423d06a350295e0195d03959019550695203951059500294e0394902942039410193d0593a039360193503934cc12a0392604859048510384d0384a03846930457b044f234c0aa4c01a4408c5c01b5c05b54f125407a4805a3801a3407948bd1340ab4c01b44ef24c07920ed03c04830ed14401c5c05c5408b5cee25405a4801a4407a380793807930ec04c0484008b5002a50079507904404a3ce705402b5e09b5a09b5602b5201b4e01b42ea25ae925608a4e08a4207a3e07a3d05939059310792907921a005a78056e803e04839e603204831048304002d1102504810e43540492c0481003c5f03c5e06c5b05c5703c5303c5203b5fff35bfd35703b5308b4ffc34d05b4b05b47fa34508b4301a5f06a5e03a5b01a5703a5306a5201a4f01a4d05a4b05a4a01a4705a4601a45f824401a3f07a3bcb23a01a37b623607a330395f0295e0795bf715af6157f315603953029520194f0194e0194df013f0793bc213aeb137e5136079330592f0592e0592d0385f0485b9f05a9205777056038530884f0484b05847048433e03f0483b10037048330782f0182b01827048230781f0481b04819e3017048130481103c5e03c5a03c5603c5202b5e03b5a03b5602b520194d0194901945019410193d0193901935019310385a03b4f03b4b03b4703b430194f0194b01947019430193f0193b01937019330384a03b4f03b4b03b4703b4303a460194f0194b01947019430193f0193b01937019330384a 16 65535 7 127 11 2047 20 1048575
def cc_71_8 : Nat → List (Nat × Nat) := unpackCursorV4 0xcb4365a02fd617494ba00dce06de136e81b7405b806d41142cf96d545aba201aff227f803f809ce5ce08d5b2aaa469059a82013d081b468bf36394d15cd817300a02000a 0x228c00b290019446a09447c1300908002b4f01da580ed1c0568602a4f01d2580e91c0548608a3f9011dc788dc114660194f00ca700652c0328e01943014a10064fc032760693a00c9b8064d8032660192f00c95b4c4a80324e0192600c9180a13c070960384a01c2380e118050860883f0241dc740dc090665102f0241588c09c090460181f00c0d80605c0302603c5a01e2b016d341169205b45045a080e968074ac01a4600d228065340328a0192d00c9280e168070ac04849024208120a40904201b4c045a80171b0118c11a36c00db4006d90116c0069488c89c0064d00369808b5002e360231822e4d801a640152e4589522a2500192400e2f807178078ba01b5f00daf016d76466b801b5b00dac806d5c036aa01b5300da9484d46386a002b4f01da580ed1c0568601a5f8d92e80696c034ae01a5500d2980a93c0749603a4701521c608fc0d47606a378a11980657c032bc0195d00ca7806538032960194900ca180a508032820193f00c9d81a4e80326e0193600c998064bc03256d112a00c93806498032460185f00c2d806164030ae018530242880a13c070960384a01c2380e118050866d03f0241d81a0dc090664f02f0241588409c090460181f00c0d80605c0302602b4f015a580ad1c0368602a4f0152580a91c0548606a3f0351d81a8dc0d4660194f014a580651c052860193f01c9d8064dc072660192f01c9580649c072460284f0142580a1280508e028460142181a0fc0907606837024199380bc09056200270241180e07c030360181701c09806d3c0569602b47015a180a93c0549602a47015218168fc0b47605a3702d1980653c052960294a00ca380a518052860193f01c9f00e4ec0326e0393302c990064bc072560192701c9180a13c050960284a0142380a118050860583f0241d8160dc090664d02f0241587c09c090460381f00c0d80605c0702602b4f015a580ad1c056860194f014a580651c052860193f01c9d8064dc072660284a00daf006d480d69c05b4a02da301ad08054bc02a5a0152b00a9480d49c06a4a0352301a9080547c02a3d014ad00a5580729c0694201c9c80e4c40325a0392900c9280e484050b4028560241c8120c49805a048290e8128120840327807930015a780ad2c0568e02b4300d2780a92c0548e02a430351f81a8ec0d46e06a3300ca780a52c0529401947014a300a50c0327e0393e01c9d8064dc072660693200c9780e4ac0324e039230142780a12c05094028470142300a10c0d07e0483b0341b8120ce1c05e0482b8681381208c0703e0181b00c0b80e04c0569e02b4b015a380ad0c0329e0294b00ca380a50c0327e0393b00c9b80e4cc0509402c5f0162d80b15c058a602b5f015ad80ad5c056a606b4f035a581ad1c0d68601a5f00d2e80a96c054b401a570152b0069540349e03a4e01d2580691c0748606a4200d1f80e8ec0346e03a3300caf806578032ba0294f034a700a536242980294b014a500a51c0b28c02945888a200a50c052840293f0149ec404f0052760293a0149bc3c4d80526b0c1340149980a4bc0725c0292d0142f80a16c050b4028570142b00a14c0d09e0484b0342381210c9407e0483b0e01b8120cc0705e0182b00c1380e08c0503e0281b0140d01206409030028170140b42c05005026028110162f00f168078ac02c5201dad00ed580f69208b4101d2d00e9580349c01a4d0451f0228c80329a0194500c9c8064c40325a0192501c2d00e158090920484102414812084078be03c5b01e2d00f15c078ac03c5300daf80ad78036b601b5a00dab80ed58036a601b5200da7c10d380369a03a5f01d2d80e95c074a608a4f02d2581691c1148601a3f00d1e8068ec0346f0923500d1980657c032bc0195b00cab80654c072a40194b02ca50065240328e0194600ca18065040326e0193600c9a8064bc03256cf12a00c93806498032460385f01c2d80e168070ae0385601c2982213c0909605847024218060fc030760483900c1b8060cc030624802f0241586809c090460181f00c0d80605c0302605a340162f00b1480b68c05b450352d01a9580349a01a4502cad01a55a0e28c05945044970164b40d0b406856015af01ad680d6ac02b5200da5006d180d4b406a5602d250169180b47c05a3d034ad01a5580b29c0594203c9c81e4c40f252079210342d01a158090720483102414812084078bc03c52045a6816d14034bc03a5200d268169280348c01a4500d2201e8e80346c0295e01cad00e558052a40194e00ca681e4e97a26c0192e02c9680e168070ac048190240880f17c078bc05c5b02e2b80f14c078a403b5f035ad81ad5c076a605b4f831a6816d2c0b68e05b4502da180697c074b606a5a00d2b81a958074a601a4f02d270069340348e01a4502d218169080347e07a3b00d1b81e8cc072be0295e02cad8165680b2ae0695601ca980a5480328e0194600ca28164fc0b2760593a02c9bc144d80b2660592f820970164b4070be0485b0342d01a15c0d0ac0385302c2781212c0b08e048432281f8120ec3006e0483303c178060ac0304e0482302c0f81206c090320581702409812044078b403c56015af00ed68076ac02b5202da5016d180b49405a4600d1b0068d4072b40195600ca70065240b284019417c8a00064f40326a0192d00c9280e168070ac048390241880717c038bc01c5b01e2d00715c038ac01c530162900ed7c076b603b5a01dab80ed58076a601b4f00da7016d34074be03a5b01d2b80e94c0349f0224d00d2580691c0348a01a4302d1f8168ec0b46e05a3300caf80656c072b40195700cab00654c0329e0194e00ca68064fc0327c0193b00c9c8064cc0b264019317c0980064bc032560192700c9180e17c070b60385a01c2b80e158070a60184f00c258061240308e01843024208160fc09076058370241990c0bc09056150270241180607c030360181700c098120800d8a808b5c02daa00e9500748807a3800d1a3a85100f27100134 17 131071 7 127 11 2047 21 2097151
def cc_71_9 : Nat → List (Nat × Nat) := unpackCursorV4 0x9f08cec1a62292c899502ca6063d2d1c05809b3e245e41aeb0e700b358519f1ab1bc554728c3d45029c0d4949a1a61001a59cd2a8494c105b9618aa0b81806ac00060000 0x5c5e0362e816d7a866ba02b4e015a10168d80b46a0595e02cac81654a842a33f15000c9e8064d40d0940684602e32023160056d808b58035a80168d0118bc06c5d015ae80ad540d69206b4102d2e8169540d49a09a4502d1d0168d8032ba0795900caa81e544090b2048510342501a1180b8d808c60015b601ada00b6c802b60015ae026d500b46808a500452601e9000b2b00194400dae01e96a324ac08a4e03d2101e8e97e46c0295e03cad4e4558052a40194a00ca30164e80b26c0792e03c96a98169160ac04829024108120640902205c5803da6022540032780893002e2f81b16e888b405c579f22b01b14c0d6be02b5e045ad826d6a7a6af3c356035a980ad480d4bf3b25702d2501691c0b48c05a3702d1b0168d40d2bf2615b8c0ab81a54c1129e0594b830a481651c11286fc1410449f8064f674277381399b89b8064d411266c21316c895af849c090b6a505a4502b01214c09096048430241d8120e409066048310240d81204c0d4bc06a5a0352b01a9480b49c05a4a02d23016908052bc0695a034ab00a5480329c0594a02ca30065080d0b405b4f02da5816d1c0b6860694f034a581a51c0d2860593f02c9d8164dc0b2660684a01da780ed2c0768e03b4301d2300653c032960194700ca18064fc032760193700c9980e1280b8be05c5b02e2b81714c0d6ac05b4e0152f01a9580b48c0695f034ad81a55c0d2a60594f02ca581651c0b287351299a094006496662480685a0352f01a9480b49405a4603d1d2ec8d8052bc0695a034ab00a5480329c0194203c9d2f44d80b25c0592d0342d01a1580903204811035a301693c0b49605a4702d2181a13c0d09606847034218160bc0b0560582702c1181717c058bc05c5b0362d01715c0b8ac05c5301629016d7c0b6b606b5a02dab816d580b6a606a5f0352d01a95c0d4ac05a4f02d274b49340b47e05a3e02d1901a57c0d2b606957034a981653c0329a0594b02ca481651c0328a05943988a08164fc0b2760593902c9b8164cdf4262d812b5d09381216c0d0b4068560242981613a600980484b0242481210c0b08404841024200120ec090660481b0240980ad740d6b202b55035a881ad240d68205a3600cae81e564032aa07951034a6c585140d09406c5a02e2b00ad780d6b406b56015a90169180b46c05949044a08064f40f2720193503c9881a168036b807a5a8a92b0229380f4840295e03cad4b0558052a40894e00ca50065180f284a405a02e2f81b16c0b8ae06c5302da300a97a5c4ad2d24e034afc9456e282ae06953044a781652c0b28e0894395894806495460b402c5901628816d740d6b205b55035a8806978034ba02a4e0152101a8e80d46c0195d00caa80a5280328c0193e034990064b40324a048590242880a1280508c02b4a0152780a92c0548e02a4300c2780612c0308e0184300c178060ac0304e0182300e2f80b178038ba02b5f015ad80ad5c056a601b4f00da6806d2c0d69201b4702da2806d0c0368202a5f0152d80a95c054a601a4f00d2680692c0348f2924500d2181a8fc0d47606a370351980656c052b40195900cab806558032a60195100ca38065180328a0193f00c9f0064ec0326e01933034990064bc032560192700c9180a17c050b60285a0142b80a158050a60184f00c25806128090920484800c2380611a500880184300c2081a0fc0907606837024199500bc09056260270241180607c030360181700c0981a9600f49001a4402cac022540072980794801ca201e5000f47001a3403c9c00e4d0058be03c5b01e2b80b14c056be03b5b01dab80ad4e4c69e06b4b035a3c94d0c034be02a5e00d2e80695c034aa02a530152900693c0749606a4a00d2380e9180748601a3f01d1db5c8e80346e03a3601d1980655c032ac0195501ca780e538072960594a01ca380e51807286f714201c9f80e4ec132740393701c9b00e4cc0525e0292e0149680a17c070b60385a01c2b80e158050a66f04f0242581a11c090865303f0241d8940dc090660382f00c1580609c070460381f01c0d80e0640702e038130240880ad3c0769603b47015a180a93c0749603a47015218168fc0b47605a3702d1980653c032960194700ca18064fc032760193700c998064bc032560192700c9180a13c070960384a01c2380e118050860583f0241d8160dc090665202f0241589009c090460181f00c0d80605c0302601b40045200120c0058bc03c5a01e2b00b148056bc03b5a01dab00ad480369c01b4d0452681a9240d48a08a410451ec888d4032bc0295200ca6816528032920694800ca3006514032880194100c9e8164e8032720193600c9a8064d003262d612a00c9300e168070ac0884d0242481a114090820483902418b544e00d25001924 17 131071 7 127 11 2047 21 2097151
def cc_71_10 : Nat → List (Nat × Nat) := unpackCursorV4 0xbdc058ec2789f358d92514920247050cae7bd5382b9b41aafd55486a36dd0c1e7e8f3a0a99a6cb2363db71b868c038531a228e0e0683e640d2406800281814000a00000a 0xad3c0569c05b4b02da380ad0c0568402a4f0352581a91c0548605a3f9f91e8168ec0b46e05a3502d1980a53c0d29606947014a180e4fc0727a0293b02c9b8164d40b2676112f03c95d7c49c0f2460284f0242581a1280d08e06846014218160fc0907605837024199840bc09056320270241181e07c090375e0170240981717c0b8bc06c5d015af80ad78056ba02b4f015a7016d2c0b69202b43015a1016d040b4bf6525d02d2d81695c0b4aa05a530152781a92c0d48e02a4302d1fcf88f40b47605a3702d1a8168cc072be0595e00caed905700b2b60595901cab8065540b2a605952b10a8d745400529e0394b01ca380a50c0727e0393d02c9d80e4dc0726a0593301c97b6c4ac0724eb112302c2f81216c090b205857024298121440509e0484b0342501a11c0d08c0284302c1f8120ec0b06e04833300178120ac6204e048230400f80e06c0702e04813015a780ad2c0568e02b43014a780a52c0528e0294301c9f80e4ec0726e039330142500b168058ac02b5e015a901ad380d68402a5e0152d00a958054a406a4e02d250169180d48402a3e0151e80e524072820193d01c9c8064d4072620392d01c9480e494072420285a0142b0120e4090625f02d024148bc0940904205b48045a000ad3c0569602b4a015a380ad180568602a4f0152580a91c0548606a3f02d1d8168dc0d4660294f014a580a51c052860393f01c9d80e4e40726e0393301c9880e4bc072560392701c9180a13c050960284a0142380a118050860683f0241d8160dc090675902f02415d6009c090460381f01c0d80e05c0702602b4f015a580ad1c0568602a4f0152580a91c0548606a3f02d1d8168dc0d4660294f014a580a51c052860393f01c9d80e4dc072660392f01c9580e49c072460284f0142580a1280508e028460142181a0fc0907605837024199740bc090562e0270241180e07c070360381701c0980ad3c0569602b4a015a380ad180568601a4f00d2580691c0348601a3f00d1d8068e40346e01a3300d1880a53c0529602947014a181a4fc0b27605937034998064bc032560192700c9180a13c050960284a0142380a118050860683f0241d8160dc090660182f00c1580609c030465c01f0240d8b405c0902602b4f015a580ad1c0568602a4a0142780a12c0508e0284301c1f80e0ec0706e038330162f80b174058b602c5a0162b80b1580b8aa02b5f015af00ad740569e06b4e015a680a97c054b602a570152981a93c0b49605a470352180a8fc0547a02a3b0151d56c8e00546e02a36ad11ad5c8d0054660295f014ad80a55c052a60394f01ca580e5240728e0394301ca080a4fc0327a0293b0149d00e4e6ac270029370149b0064d6aa268029330149880e4bc072560392701c9180a17c050b60285a0142b80a158050a60684f0242581611c090860283f0141d80a0e809072048380141b80a0daa8068028330141896c0bc090562c0270241180e07c070360381701c0980ad280549e02a4b0152380a90c0509e0284b0142380a10c0705e0382b01c1380e08c056be02b5b015ab80ad4c0569e02b4d015a581ad240568e05b45015a180ad04054b402a570152b00a91c0548c09a450351f81a8dc052be0295b014ab80a54c0529e0194d014a580e5240528e01945014a180a5040727e0393b01c9b80e4cc07256039270142d80a168050ac8e0540142980a12c05094048490242400a11aa408802843014208120ec090660381b01c0981b1680d8ac02b5e035ad01ad58056a405a4602d1b01a524112820193d03c9c8064d40f2620685a01d2d00e9580749c07a4200d1a806578072b40395600ca90225380b2940594603ca10064d4070b402c5f0362d81b15c058a602b5e035a302695aa049c05a46014af80e56c072ae0295301ca781a52c0728eff14301c9ad3c4a40324aa805a0362d01b158056bc02b52035a7022d341149a05a4a02d2301a9140547a05a3a0351b00a8d40546806949044a08064f40f2720193503c9881a1680d0ac04849024208120e40906203a5a01d2b00e9380f48401a3d03d1d00e8d80346a0195e00ca90225380b2940594603ca10064f4052740293601c9a80a4d00725c0792d01c2d00e15807052048210240c8120440d6be05b5d04dad826d640d6ae05b5504da9d34d440569e06b4b035a380ad0c054be02a5e0152e80a93c0549c02a429d91f81a8e80d46e06a3601caf806574132b60995901cab806554132a74c151014a780e52c0728e0294301c9f81a4ec0726efd13301c96b684ac0724e039250242d812164090a60485102425a9c1291a08c8c044014218120ec090660381b0240980ad3c0569602b47015a180a53c0529602947014a180e4fc072760393701c9980a1280569e02b4b015a380ad0c0548c0294f014a580a51c052860393f01c9d80e4dc072660284a015a780ad2c0568e02b43014a780a52c0528e0294301c9f80e4ec0726e039330142500ad3c0569602b47015a180a9180329e0194b00ca380650c0327e0193b00c9b8064cc0509402b4f015a580ad1c056860294a0142780a12c0508e0284301c1f80e0ec0706e038330162f80b16c058ae02c53015ab00a9780d49d4a24c02d23524910052be0295b014ab80a54c0729e0394b01ca380e50c072534812800c92d1c490050b404828a301200b1780d8ba08c5501629016d580b6aa02b4d015a28169180b48a06a3a0351b0065340328a069390449881a1680d0ac01a4c00d2200e5100569c02b4202d1b0168d40327a03935a0896d004940d09406846 17 131071 7 127 11 2047 21 2097151
def cc_71_11 : Nat → List (Nat × Nat) := unpackCursorV4 0x8d18868d604d3acb30941baa1a0304ab030303000006 0x58bc02c52015ad00ad580b69a05b450152f00a9480549c02a4d02d1d0168d80329a0394900ca280e504072720393101c9680e494050b402856024248121040569402a4f0152580a91c054860284f0142580a11c050860382f01c1580e09c0704602c5f0162f00b174056b602b5a02dac80ad5c056ac02b53015a880ad1c0568c05b450152f80a96c054ae02a530152780a9340549602a47b492280a90c0b47e05a3b02d1b8168cc052be0295b014ab80a54c0529e0194d014a580e5240528e01945014a180a5040727e0393b01c9c80e4dc072660393101c9780e4ac0724e039230142f80a16c050b4028570142b00a14c0509e0284b014250121240909002847014235a0110050860284102c1f8120ec0b06e04833328178120ac6c04e0482301c0f80e06c0702e038130162f80b1780b8ba05c5702e2a80b14c058a405b5702dab016d540569e02b4e015a680a97c0d4b606a570152981a93e8849a05a4b02d2381a9140d48606a3f04d1e81a8ec0d46e06a350351980a57c072b603957014a980e53c0729a0594b01ca380e5140d2860393f00c9e81a4ec0d2720393700c9a81a4cdee2620392f6e89580e49d662460285f0242d81a1680d0ae068560142981a13c09096058470242181a0fc09076048390341b8120cc090626402f024158d409c090460a01f01c0d80e05c0902606c5d0362a80ad74056aa05a5602d2a81a9280d48c05a3a02d1b0065740f2b20195503ca8812164090a20684a034230120a40904201b4f00da5806d1c0368601a4f00d2580691c0348602a3f01d1d80e8dc054660194f00ca580651c032860293f01c9d80e4dc052660592f02c9581649c0b2460184f00c2580611c030860283f01c1d80e0e80706e03836014198160bc09056058270241198807c0903633017024098164c00f240048300162f00b14a8469a05b450152f00e968074ac02a5201d270069340749805a4a01d230069140748805a4201d1f01e8e80746c07a3200caf00e568072ac0195200ca7006534052940294601ca280a510032840793ab189b00e4b80b25a0385a01c2b01e0b4070520382502410812064090234134c01d260169100369805b44a012601e482c007804830 16 65535 7 127 11 2047 21 2097151
def cur_71 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_71_11 (Nat.sub p 352)) (cc_71_10 (Nat.sub p 320)) (Nat.blt p 352)) (cc_71_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (Bool.rec (cc_71_8 (Nat.sub p 256)) (cc_71_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_71_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (cc_71_5 (Nat.sub p 160)) (cc_71_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_71_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_71_2 (Nat.sub p 64)) (cc_71_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_71_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def f_71 : Nat → Nat × Nat := unpackForestF 0xb4245b404400b4f00b4baea5dae95cb1936ae951af12fb003caf127af017ae95000b47aa238aa235ac02fac027aa234aa138aa134aa03400b43a904400a4fa7a4ea792900a4ba6351a615100a47a324ca3244a3128a3124a302400a439bc5a9fb5d9f951a012da01259f9509bc569bb579bb569ba579b93b9c9569b9399b93700a3f99929999289992400a3b981419804c00a3795a5695a4e961569592900a3394245940440094f92b4f92b430094b8a35c912358a3518ea3b8f84c8ea378e8378a3508a25d8cb6c8c9388a23f8aa6c8aa548a9288a233009478594c859448593c859368682f8682785934858140094384a350093f839468234d821368212e0093b8124d009378013471b5b7f16c71b5771b4d7d94d71b457ca3d71a447195a719577a2457a23d719567934c78a547193f77a4c76254769447604c719377325a732567303e7385473032719367235471817009336fa4e6fa4c6fa440092f6145b6e16c61457613576134f613476125a693516a23a6a236693506915d61256681356124e6634d66345661566124261157611566114f62c5662b5662a456114e61147611420092b5ab425f9485aa4f5db505db405d9505aa475ba4d5ba455b93d5a9425a83c0092755c5b5916c55c57583455595656c5656b565594e5592e009230084f4c24b4c247531394c23f521294c2335034d5083c501364c1334e2424e14e4e1424c12b4d14e4c1234c0460084a49351491514996c49954491330084748029392433913d3913739135458293912f4483e390433c3524305c3c2453c23d3c1523c05e408243c0523c0453e2323e12d3e0323c0443ca503c9443c026390233b044399323983e398323901b00846353563515b3736c3515735a5635956351390083f3414100837332541cc5f1cc5b30a6c3096c309601cc572e3442e2442e1482e1441cc531ca562c9502bc562bb561ca4e2aa541c95f1c95b2846c284602826c1c9572595c2595425944259341c95324a441c94f2335c231341c94b2225c1c9472124c1fa541f9441f9341c9431eb501d2561d24e1d1561c9290082f1bb580645f0645b193601916c191600645716b4816a441694816944064530635a14c5e14a560634213b580615f0615b1146c1146011360061570e95c0e9540e94c0e934061530db480614f0c94c0614b0b3500b3400614708a54099440894c089340614306a5e06a460695606131008270245b0496c024570215602c5602b560214e0081f01242008170001f 9 11
set_option maxHeartbeats 0 in
theorem rc_71 : dagCheckRootsV4 m_71 g_71 ep_71 362 bds_71 (dagTraceF m_71 s_71 8 f_71) (cur_71 0) s_71 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_0 : treeBlockF 0 32 (dagCheckNodeV4 m_71 g_71 ep_71 bds_71 362 (dagTraceF m_71 s_71 8 f_71) cur_71) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_1 : treeBlockF 32 64 (dagCheckNodeV4 m_71 g_71 ep_71 bds_71 362 (dagTraceF m_71 s_71 8 f_71) cur_71) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_2 : treeBlockF 64 96 (dagCheckNodeV4 m_71 g_71 ep_71 bds_71 362 (dagTraceF m_71 s_71 8 f_71) cur_71) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_3 : treeBlockF 96 128 (dagCheckNodeV4 m_71 g_71 ep_71 bds_71 362 (dagTraceF m_71 s_71 8 f_71) cur_71) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_4 : treeBlockF 128 160 (dagCheckNodeV4 m_71 g_71 ep_71 bds_71 362 (dagTraceF m_71 s_71 8 f_71) cur_71) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_5 : treeBlockF 160 192 (dagCheckNodeV4 m_71 g_71 ep_71 bds_71 362 (dagTraceF m_71 s_71 8 f_71) cur_71) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_6 : treeBlockF 192 224 (dagCheckNodeV4 m_71 g_71 ep_71 bds_71 362 (dagTraceF m_71 s_71 8 f_71) cur_71) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_7 : treeBlockF 224 256 (dagCheckNodeV4 m_71 g_71 ep_71 bds_71 362 (dagTraceF m_71 s_71 8 f_71) cur_71) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_8 : treeBlockF 256 288 (dagCheckNodeV4 m_71 g_71 ep_71 bds_71 362 (dagTraceF m_71 s_71 8 f_71) cur_71) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_9 : treeBlockF 288 320 (dagCheckNodeV4 m_71 g_71 ep_71 bds_71 362 (dagTraceF m_71 s_71 8 f_71) cur_71) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_10 : treeBlockF 320 352 (dagCheckNodeV4 m_71 g_71 ep_71 bds_71 362 (dagTraceF m_71 s_71 8 f_71) cur_71) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_11 : treeBlockF 352 362 (dagCheckNodeV4 m_71 g_71 ep_71 bds_71 362 (dagTraceF m_71 s_71 8 f_71) cur_71) = true := by decide +kernel
theorem nj_71_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_71 g_71 ep_71 bds_71 362 (dagTraceF m_71 s_71 8 f_71) cur_71) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_71_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_71_1 h1 h2)
theorem nj_71_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeV4 m_71 g_71 ep_71 bds_71 362 (dagTraceF m_71 s_71 8 f_71) cur_71) i = true := block_join nj_71_1 (fun _ h1 h2 => treeBlockF_at nb_71_2 h1 h2)
theorem nj_71_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeV4 m_71 g_71 ep_71 bds_71 362 (dagTraceF m_71 s_71 8 f_71) cur_71) i = true := block_join nj_71_2 (fun _ h1 h2 => treeBlockF_at nb_71_3 h1 h2)
theorem nj_71_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeV4 m_71 g_71 ep_71 bds_71 362 (dagTraceF m_71 s_71 8 f_71) cur_71) i = true := block_join nj_71_3 (fun _ h1 h2 => treeBlockF_at nb_71_4 h1 h2)
theorem nj_71_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeV4 m_71 g_71 ep_71 bds_71 362 (dagTraceF m_71 s_71 8 f_71) cur_71) i = true := block_join nj_71_4 (fun _ h1 h2 => treeBlockF_at nb_71_5 h1 h2)
theorem nj_71_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeV4 m_71 g_71 ep_71 bds_71 362 (dagTraceF m_71 s_71 8 f_71) cur_71) i = true := block_join nj_71_5 (fun _ h1 h2 => treeBlockF_at nb_71_6 h1 h2)
theorem nj_71_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeV4 m_71 g_71 ep_71 bds_71 362 (dagTraceF m_71 s_71 8 f_71) cur_71) i = true := block_join nj_71_6 (fun _ h1 h2 => treeBlockF_at nb_71_7 h1 h2)
theorem nj_71_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeV4 m_71 g_71 ep_71 bds_71 362 (dagTraceF m_71 s_71 8 f_71) cur_71) i = true := block_join nj_71_7 (fun _ h1 h2 => treeBlockF_at nb_71_8 h1 h2)
theorem nj_71_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeV4 m_71 g_71 ep_71 bds_71 362 (dagTraceF m_71 s_71 8 f_71) cur_71) i = true := block_join nj_71_8 (fun _ h1 h2 => treeBlockF_at nb_71_9 h1 h2)
theorem nj_71_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeV4 m_71 g_71 ep_71 bds_71 362 (dagTraceF m_71 s_71 8 f_71) cur_71) i = true := block_join nj_71_9 (fun _ h1 h2 => treeBlockF_at nb_71_10 h1 h2)
theorem nj_71_11 : ∀ i, 0 ≤ i → i < 362 → (dagCheckNodeV4 m_71 g_71 ep_71 bds_71 362 (dagTraceF m_71 s_71 8 f_71) cur_71) i = true := block_join nj_71_10 (fun _ h1 h2 => treeBlockF_at nb_71_11 h1 h2)
theorem nc_71 : ∀ i, 0 ≤ i → i < 362 → (dagCheckNodeV4 m_71 g_71 ep_71 bds_71 362 (dagTraceF m_71 s_71 8 f_71) cur_71) i = true := nj_71_11
theorem lb_71 : LowerBin m_71 s_71 g_71 9 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_71 kn_71 sub_71 gl_71 rc_71 nc_71

def g_72 : Nat := 0x1171557131f1f7f
def ep_72 : Nat := 0x12080a280000144000000c6000160042000c006001060402020e0e0801121002131010200114155410101040
theorem epk_72 : ep_72 = edgePack fullMask g_72 := by decide +kernel
def bds_72 : List (Nat × List Nat × Nat × Nat) := [(m_63, s_63, 8, g_63), (m_65, s_65, 8, g_65), (m_69, s_69, 9, g_69), (m_68, s_68, 9, g_68), (m_71, s_71, 9, g_71), (m_70, s_70, 9, g_70), (m_67, s_67, 8, g_67), (m_30, s_30, 6, g_30), (m_62, s_62, 8, g_62), (m_66, s_66, 7, g_66), (m_61, s_61, 8, g_61), (m_64, s_64, 8, g_64), (m_25, s_25, 5, g_25), (m_57, s_57, 5, g_57), (m_40, s_40, 5, g_40), (m_4, s_4, 4, g_4), (m_28, s_28, 5, g_28), (m_52, s_52, 5, g_52), (m_60, s_60, 5, g_60)]
theorem kn_72 : KnownBin bds_72 := by
  intro b hb; simp only [bds_72, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_63
  · exact lb_65
  · exact lb_69
  · exact lb_68
  · exact lb_71
  · exact lb_70
  · exact lb_67
  · exact lb_30
  · exact lb_62
  · exact lb_66
  · exact lb_61
  · exact lb_64
  · exact lb_25
  · exact lb_57
  · exact lb_40
  · exact lb_4
  · exact lb_28
  · exact lb_52
  · exact lb_60
theorem sub_72 : ∀ b ∈ bds_72, fullMask &&& b.1 = b.1 := by intro b hb; simp only [bds_72, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_72 : ∀ b ∈ bds_72, canon b.1 g_72 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_72, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_72_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xb1b36ade3da944aa6232a055d972939155d8868f8256179a8b73f5b6e75864d9a6004d5a45c5683c52b3d49d8e454493c1933358c2e84d25692200561bb451605b118480bf590714e03d340013c00001 0x7e7e07e7d01d6d07d6901d6507d610ac7e08c7a08c7609c720ac6e09c6d0ac6c09c6a09c6909c680ac6609c650ec6406c6206c6106c6007b7a07b7908b7607b7108b6607b6507b5d07b5506b4d01b4906b4501b410496d0596904965059610494d0594904945059410287d028750286d0386902865038610284d038490284503841038390383101d6f01d6b01d6701d6309c6f09c6b09c6709c6301c5f01c5e09c5d07b6f07b6b07b6707b6301b5f01b5e07b5d06b4f01b4b01b4901b4301b410496f0596b04967059630195f0195b01957019530494f0594b04947059430493f0593b04937059330286f0386b02867038630185f0185e0185b0185701853018520284f0384b02847038430283f0383b02837038330281f0381b028170381301d6f09d6b01d6709d6309c6f0ac6e09c6b08c6a09c6708c6609c6309c621e36f07b6b0fb6707b6307b5f09b5d01b5b01b571d35507b5306b4f06b4d01b4b01b4909b4706b4507b4301b410496f0596b04967059630495f0195b01957059530494f0494d0594b05949049470494505943059410493f0593b04937059330286f0386b02867038630285f0185b01857038530284f0284d0384b03849028470284503843038410283f0383b02837038330281f0381b02817038132b56f2956b27567255632346f0bc6b214670bc632045f0bc5b1f4570bc530bb4e0aa6e08a661c25e01a5606a460496f0596b04967059630495f0595b04957059530494f0594b049470594305929049250286f0386b02867038630285f0385b02857038530284f0384b028470384303829028250281f0381b028170381301d6f01d6b01d6901d6701d6301d6107c6f07c6b07c6707c6301c5f01c5b01c5701c5306b6f06b6e06b6b06b6a06b6706b660ab6309b6201b5f01b5e01b5b01b5a01b5701b5601b5301b5201b4f01b4e01b4701b4301b4206a6f06a6701a5f01a5706a4f01a4706a3f06a3d01a3701a350496f0596b04967059630195f0195b01957019530494f0594b04947059430493f0493d0593b05939049370493505933059310592b049270286f0386b02867038630185f0185b01857018530284f0384b02847038430283f0283d0383b03839028370283503833038310382b028270281f0381b028170381301e7f0ae7e01e7d01d7b08d7a01d7901d7701d7601d7301d7101d6701d6601d6506c7f06c7e06c7b08c7a06c7706c7606c730ac7201c6f01c6e01c6d01c6c01c6b01c6a06c691a46801c6701c6606c6506c6401c6301c6201c6101c6001c5f01c5e01c5b01c5a01c5901c5801c5701c5601c5301c5206c511145007b7f07b7b07b7707b7301b6f01b6d01b6b07b6901b6707b6501b6301b6101b5f01b5b01b5701b5306a7f06a7701a6f01a6d01a6706a6501a5f01a5706a4f06a4e06a4d06a3f06a3e07a320497f0597b04977059730196f0196d0196b05969019670496501963019610195f0195b01957019530494f0494d0594b05949049470494505943059410493f0593b04937059330592b049270287f0387b02877038730186f0186d0186b0186a03869038680186701866028650286401863018610185f0185b01857018530284f0284d0384b03849028470284503843038410283f0383b02837038330382b028270281f0381b028170381301d6f08d6e06d6b01d6708d6308d6208c6f07c6b08c6707c6307c5f01c5b01c5707c5306b6f06b6e01b6b01b6a06b6701b6606b6306b6206b5f06b5e01b5b01b5a01b5701b5609b5309b5207b4f07b4e08b4707b4307b4206a6f06a6706a5f01a5706a4f06a4706a3f06a3d06a3706a350496f0596b04967059630495f0195b01957059530494f0594b04947059430493f0493d0593b05939049370493505933059310592b049270286f0386b02867038630285f0185b01857038530284f0384b02847038430283f0283d0383b03839028370283503833038310382b028270281f0381b028170381301e7f08e7e01e7d01e7701e7508e7308e7201d7701d7601d7508d6f0ad6e08d6d06c7f06c7e06c7b08c7a06c7908c7806c7706c7606c7308c7206c710ac7006c6f06c6e01c6b01c6a01c6701c6606c6309c6206c5f06c5e06c5d06c5c06c5b08c5a06c591845806c5706c5606c5506c5406c5308c5206c5108c5008b7f07b7b08b7707b7307b6f01b6b01b6707b6308b5f08b5d07b5b07b5908b570cb5507b5307b5106a7f06a7706a6f01a6706a5f06a5d06a5706a5506a4f06a4e06a4d06a3f06a3e07a320497f0597b04977059730496f0196b01967059630495f0495d0595b05959049570495505953059510494f0494d0594b05949049470494505943059410493f0593b04937059330592b049270287f0387b02877038730286f0186b01867038630285f0285d0385b03859028570285503853038510284f0284d0384b03849028470284503843038410283f0383b02837038330382b028270281f0381b028170381301d6f01d6e01d6b01d6901d6701d6308d6201d6107c6f07c6b07c6707c6301c5f01c5b01c5701c5306b6f06b6e08b6b08b6a06b6706b6606b6306b6201b5f01b5e01b5b01b5a01b5701b5601b5301b5201b4f01b4e01b4701b4301b4206a6f06a6701a5f01a5706a4f06a4e01a4707a4206a3f06a3d01a3701a350496f0596b04967059630195f0195b01957019530494f0594b04947059430493f0493d0593b05939049370493505933059310592b049270286f0386b02867038630185f0185b01857018530284f0384b02847038430283f0283d0383b03839028370283503833038310382b028270281f0381b028170381301e7f01e7e08e7d01d7f01d7e01d7d01d6f01d6e01d6b01d6901d6308d6201d6101c7f01c7e06c7d06c7c01c7b01c7a01c7901c7801c7701c7601c7501c7401c7301c7206c711647006c6f06c6e06c6b08c6a06c6706c6606c6308c6201c5f01c5e01c5b01c5a01c5701c5601c5301c5201b7f07b7d01b7b01b7901b7701b7501b7307b7107b6f07b6b07b6707b6301b5f01b5b01b5701b5301a7f06a7d01a7701a7506a6f06a6701a5f01a5706a4f06a4e06a4d06a3f06a3e07a320197f0497d0197b01979019770197501973059710496f0596b04967059630195f0195b01957019530494f0494d0594b05949049470494505943059410493f0593b04937059330592b049270187f0287d0187b01879018770187501873038710286f0386b02867038630185f0185b01857018530284f0284d0384b03849028470284503843038410283f0383b02837038330382b028270281f0381b028170381301d6f08d6b01d6706d630ac6f07c6b08c6707c6307c5f01c5b01c5707c5306b6f01b6e06b6b06b6a06b6706b6601b6301b6206b5f06b5e01b5b01b5a01b5701b5608b5308b5207b4f07b4e0ab4707b4307b4206a6f06a6706a5f01a5706a4f06a4706a3f06a3d06a3706a350496f0596b04967059630495f0195b01957059530494f0594b04947059430493f0493d0593b05939049370493505933059310592b049270286f0386b02867038630285f0185b01857038530284f0384b02847038430283f0283d0383b03839028370283503833038310382b028270281f0381b028170381301d6f08d6b01d6706d6301c6f07c6b08c670ac6308c5f01c5b01c5709c5306b6f06b6e06b6b06b6906b6706b630ab6206b6106b5f06b5e01b5b06b5901b5706b5309b5206b5106b4f06b4e06b4706b4309b4206a6f06a6706a5f01a5706a4f06a4e06a470ca4206a3f06a3e06a3d0496f0596b04967059630495f0195b01957059530494f0594b04947059430493f0493d0593b0493704935059330592b049270286f0386b02867038630285f0185b01857038530284f0384b02847038430283f0283d0383b0283702835038330382b028270281f0381b028170381301e7f01e7d08e7b08e7a01e7708e7601e7501d7f01d7e01d7d08d6f08d6e08d6d06c7f06c7e06c7b08c7a06c7908c7806c7706c7606c730ac7206c710ac7006c6f06c6e01c6b01c6a06c6901c6801c6701c6606c6309c6206c6109c6006c5f06c5e06c5d06c5c06c5b0ac5a06c591445806c5706c5606c5506c5406c5309c5206c5109c500ab7f07b7b08b7707b7307b6f01b6b01b6707b6309b5f0ab5d07b5b0ab5a07b590bb580ab570ab560cb551335407b5307b5106a7f06a7706a6f01a6706a5f06a5d0aa5a06a5706a5606a5506a5406a4f06a4e06a4d06a3f06a3e07a320497f0597b04977059730496f0196b01967059630495f0495d0595b05959049570495505953059510494f0494d0594b05949049470494505943059410493f0593b04937059330592b049270287f0387b02877038730286f0186b01867038630285f0285d0385b03859028570285503853038510284f0284d0384b03849028470284503843038410283f0383b02837038330382b028270281f0381b028170381301d6f09d6e01d6d07c6f07c6b07c6707c6301c5f01c5d01c5b01c5707c5501c5306b6f08b6b08b6a08b6708b6609b6301b5701b5609b5501b4f01b4701b4306a6f06a6701a5f01a5d01a5706a5506a4f01a4706a3f01a370496f0596b04967059630195f0195b01957019530494f0594b04947059430493f0593b04937059330592b049270286f0386b02867038630185f0185b0185a0185701856018530284f0384b02847038430283f0383b02837038330382b028270281f0381b028170381301d6f1156e09d6b01d6709d6309d620e46f07c6b0fc6707c6307c5f09c5d01c5b01c570945507c5309b6f0ab6e09b6b08b6a09b6708b6609b6309b6206b5f06b5e06b5d01b4f01b4e09b4707b4301b4206a6f06a6706a5f06a5d01a5706a5506a4f06a4706a3f06a3d06a3706a350496f0596b04967059630495f0195b01957059530494f0594b04947059430493f0493d0593b05939049370493505933059310592b049270286f0386b02867038630285f0185b01857038530284f0384b02847038430283f0283d0383b03839028370283503833038310382b028270281f0381b028170381307e7e09e7207d7e01d7a01d7607d7207d6e09d6d06c7e08c7a06c7908c7806c760ac7206c710ac7006c6e01c6a01c6607c6206c5e06c5d06c5c09c5a06c590ec5806c5606c5506c5409c5206c5109c5007b6d07b6507b5d01b5907b5501b5106a5d06a5506a4e06a4d06a3e07a320495d0595904955059510494d0594904945059410285d0385902855038510284d03849028450384107e7e07e7d07d7e09d7207d6e01d6d01d6c07d6901d6509d6207d6109d6007c7a07c7908c7607c7108c6607c6507c5d07c550ab7e08b7a08b7609b720ab6e09b6d0ab6c09b6a09b6909b680ab6609b6510b6406b5e06b5d01b4e01b4206a6d06a6506a5d06a5506a3d06a350496d0596904965059610493d0593904935059310287d028750286d0386902865038610283d03839028350383107e7f07e7e07e7d07d7f08d7b07d770ad7307d6f01d6d0ad6b0f56907d6701d650ad630ad6106c7f06c7e06c7b08c7a06c7908c7806c7706c7606c730ac7206c710ac7006c6f06c6e06c6d06c6c06c6b08c6a06c6706c6606c6506c6406c5f06c5e06c5b01c5a06c5701c5606c530e45207b7b08b7a07b7908b7708b7607b7307b7108b6708b6608b6507b5f07b5b07b5707b5306a7f06a7706a6f06a6d0aa6a06a6706a6606a6506a6406a5f06a5706a4f06a4e06a4d06a3f06a3e07a320497f0597b04977059730496f0496d0596b05969049670496505963059610495f0595b04957059530494f0494d0594b05949049470494505943059410493f0593b04937059330592b049270287f0287d0387b0287702875038730286f0286d0386b03869028670286503863038610285f0385b02857038530284f0284d0384b03849028470284503843038410283f0383b02837038330382b028270281f0381b028170381308e7a07e7601d7e07d7a07d7601d7207d6e08d6d06c7e08c7a06c7908c7806c7608c7206c710ac7006c6e01c6a06c6901c6801c6607c6206c6109c6006c5e06c5d06c5c09c5a06c590ec5806c5606c5506c5409c5206c5109c5007b6d01b6a01b6607b6507b5d01b5a01b5909b5607b550ab5401b5106a5d06a5506a4e06a4d06a3e07a3205969059610495d0595904955059510494d05949049450594103869038610285d0385902855038510284d03849028450384107e7f07e7e07e7d07d7f01d7d08d7b08d7907d7701d7508d730c57107d6f08d6b07d6708d6306c7f06c7e06c7d06c7c06c7706c7606c7506c7406c7308c7206c6f06c6e06c6b08c6a06c6908c6806c6706c6606c6308c6206c610ac6006c5f06c5e06c5b01c5a06c5701c5606c530fc5208b7f08b7e0ab7d08b6f08b6e07b6b07b6907b6308b6207b6107b5f07b5b0bb5a07b570cb5607b5306a7f06a7e06a7d06a7c06a7706a7508a7206a6f06a6706a5f06a5706a4f06a4e06a4d06a3f06a3e07a320ba300497f0497d0597b05979049770497505973059710496f0596b04967059630495f0595b04957059530494f0494d0594b05949049470494505943059410493f0493d0593b0493704935059330592b049270287f0287d0387b03879028770287503873038710286f0286d0386b0286702865038630285f0385b02857038530284f0284d0384b03849028470284503843038410283f0383b02837038330382b028270281f0381b028170381301e7f07e7b01e7707e7307d7f07d7e07d7b08d7a07d7707d7607d730ad7207d6f07d6e07d6d06c7f06c7e06c7b08c7a06c7706c7606c730ac7206c6f06c6e01c6b01c6a06c6901c6801c6701c6606c6307c6206c6109c6006c5f06c5e06c5d06c5c06c5b01c5a01c5701c5601c5501c5407b7f07b7b07b7707b7301b6b01b6a07b6901b6701b6607b6307b6101b5701b5601b5506a7f06a7706a6f01a6706a5f06a5d07a5a06a5706a5606a5506a5406a4f06a4e06a4d06a3f06a3e07a320497f0597b04977059730496f0196b01967059630495f0495d0595b05959049570495505953059510494f0494d0594b05949049470494505943059410493f0593b04937059330592b049270287f0387b02877038730286f0186b01867038630285f0285d0385b03859028570285503853038510284f0284d0384b03849028470284503843038410283f0383b02837038330382b028270281f0381b028170381301d6f01d6e01d6b01d6701d630ad6207c6f07c6b07c6707c6301c5f01c5e07c5d09b6f09b6b09b6709b6301b5f01b5e09b5d01b4f01b4e01b4701b4301b4206a6f06a6701a5f06a5d01a5701a5506a4f01a4706a3f01a370496f0596b04967059630195f0195b01957019530494f0594b04947059430493f0593b04937059330592b049270286f0386b02867038630185f0185e0185b0185701853018520284f0384b02847038430283f0383b02837038330382b028270281f0381b028170381301e7f01e7e01e7b08e7a01e7701e7601e730ae7201d7f01d7b01d7701d7301d6f01d6e01d6d06c7f06c7e06c7b08c7a06c7706c7606c730ac7201c6f01c6e06c6d06c6c01c6701c6601c6501c6401c6301c6201c5f01c5e01c5b01c5a01c5901c5801c5701c5601c5301c5206c510945007b7f07b7b07b7a07b770cb7607b7301b6f01b6e07b6d01b5f01b5e01b5b01b5901b5301b5207b5106a7f06a7701a6f01a6e06a6d06a6c01a6701a6501a6201a5f01a5706a4f06a4e06a4d06a3f06a3e07a320497f0597b04977059730196f0496d0196b01969019670196501963059610195f0195b01957019530494f0494d0594b05949049470494505943059410493f0593b04937059330592b049270287f0387b02877038730186f0186e0286d0286c0186b018690186701865018630186203861038600185f0185b01857018530284f0284d0384b03849028470284503843038410283f0383b02837038330382b028270281f0381b02817038131956f1756b155671256306c6f06c6e06c6b08c6a06c6706c6606c630ac6206c5f06c5e06c5b01c5a06c5701c5606c53104520d36f0bb6b0b3670bb630a35f0bb5b083570bb5306a6f06a6706a5f06a5706a4f06a4e06a4d06a3f06a3e0ba320496f0596b04967059630495f0595b04957059530494f0494d0594b05949049470494505943059410493f0593b04937059330592b049270286f0386b02867038630285f0385b02857038530284f0284d0384b03849028470284503843038410283f0383b02837038330382b028270281f0381b028170381301d6f01d6d01d6701d6507d6301c6701c6607c5f07c5e07b6f07b6b07b6707b6307b5f01b5b01b5707b5307b4f07b4d06b4b06b4907b4707b4507b4306b410496f0596b04967059630495f0195b01957059530494f0494d0594b05949049470494505943059410493f0593b04937059330286f0386b02867038630285f0185b01857038530284f0284d0384b03849028470284503843038410283f0383b02837038330281f0381b028170381301e7f07e7e01e7d01e7701e7507e7308e7201d7701d7601d7507d6f07d6e08d6d07c7f07c7b07c7707c7307c6f01c6b01c6707c6307c5f07c5d07c5b07c5907c5707c5507c5307c5107b4608a7e08a7607a6e09a6c01a6601a6408a5e08a5c08a560625406a4e0497f0597b04977059730496f0196b01967059630495f0495d0595b05959049570495505953059510494f0594b0494705943059290592804925049240287f0387b02877038730286f0186b01867038630285f0285d0385b03859028570285503853038510284f0384b028470384303829028250281f0381b028170381301d6f01d6d07d6b08d6a01d6707d6601d6501c6f01c6e07c5f07c5e07b6f07b6b07b6707b6307b5f01b5b01b5707b5307b4f07b4d06b4b06b4907b4707b4507b4306b4107a360496f0596b04967059630495f0195b01957059530494f0494d0594b05949049470494505943059410493f0593b04937059330286f0386b02867038630285f0185b01857038530284f0284d0384b03849028470284503843038410283f0383b02837038330281f0381b028170381301e7f01e7d07e7b08e7a01e7707e7601e7501d7f01d7e01d7d07d6f07d6e08d6d07c7f07c7b07c7707c7307c6f01c6b01c6707c6307c5f07c5d07c5b07c5907c5707c5507c5307c5107b460aa7e08a7607a6e01a6609a5e09a5c0aa560425406a4e0497f0597b04977059730496f0196b01967059630495f0495d0595b05959049570495505953059510494f0594b0494705943059290592804925049240287f0387b02877038730286f0186b01867038630285f0285d0385b03859028570285503853038510284f0384b028470384303829028250281f0381b028170381301d6f07d6b09d6a01d6707d6607d6307c6f07c6e07c6b08c6a07c6707c6607c6309c6207b6f07b6b07b6707b6307b5f01b5b07b5901b5707b5307b5107b4f01b4d07b4b06b4901b4701b4506b4306b410496f0596b04967059630495f0195b01957059530494f0494d0594b05949049470494505943059410493f0593b04937059330286f0386b02867038630285f0285d0185b0185702855038530284f0284d0384b03849028470284503843038410283f0383b02837038330281f0381b028170381307d6f0556b07d67035630bc6f07c6b0bc6707c6307c5f07c5b07c5707c530bb460aa6e08a660225e01a5606a4e0496f0596b04967059630495f0595b04957059530494f0594b0494705943059290592804925049240286f0386b02867038630285f0385b02857038530284f0384b028470384303829028250281f0381b0281703813a645fa445ba24579e4539c35f9a35b98357963539334f9234b8d3478b3438025f7525b69257582534e24f4724b41247352432d23f1b23b07237012330495f0595b04957059530494f0594b04947059430493f0593b04937059330492f0592b04927059230285f0385b02857038530284f0384b02847038430283f0383b02837038330282f0382b02827038230281f0381b02817038130003f 20 1048575 8 255 11 2047 20 1048575
def cc_72_1 : Nat → List (Nat × Nat) := unpackCursorV4 0x9b44595b59918438b56386d488125b7d53d792437464c714326b95b62e8b6210d5d1505745d4e58f4895c433563f0433955b352432fb572b7442605721d431c4591a0241415f119280bc5d05f5d0005f 0x1d6f1f5ac1d671f58c7c6f1f1b47c671f1947c631f17c1c5b0715c7c5322d9c8b661ad7c6b5e06d6c1b5a06d5c1b561ed4c6b521ed3c7b4e125bc596b1259c59631257c195b0655c59531253c594b1251c5943124fc493d164ec5939124dc4935164cc59310a1bc386b0a19c38630a17c185b0615c38530a13c384b0a11c38430a0fc283d0e0ec38390a0dc28350e0cc38310a07c381b0a05c3813079fc7e7b079dc7e731f5fc8d7e1f5f47d771f5d47d731f5c87d6f075ac1d671f58c7c77231d87c751f1bc7c6e071ac1c6a0719c1c661f18c7c621f17c7c5e1f1741b66229f88a761a9b87a5e1e9707a56e09507a4e1e9307a46f8910497f165ec4977165cc496f065ac19671658c495f1656c49571654c494f12534594b16524494712514594316504592912494287f0e1ec28770e1cc286f061ac18670e18c285f0e16c28570e14c284f0a134384b0e12428470a11438430e10438290a094281f0e06c28170e04c7d6f1f5b41c6f071b48c6b1b1a41c67071946c631b1841c5f2316c1c572314cab6f2adb48b5f1ed6c7b531ed3c1b4b06d1c7b43125bc496d165ac59691259c49651658c59611257c595b1255c59531253c194b0651c5943124fc593b124dc59330a1bc286d0e1ac38690a19c28650e18c38610a17c385b0a15c38530a13c184b0611c38430a0fc383b0a0dc38330a07c381b0a05c38131f9fc7e7e1f9f41d7f235f81d7d075f08d7b235e41d77075d48d73235c89d71275c01d6f235ac1d672358c8c7f231f8ac7d231bc8c6e1f1ac7c691f18c8c621f1847c5f0716c1c571f14c8b7e1adf01b56229fbc27c229d88a74229b8aa6c229988a641a9787a4e2e930ca46dc910497f125f4597b165e44977125d45973165c4496f165ac49671658c495f0656c19571654c494f1652c49471650c592912494287f0a1f4387b0e1e428770a1d438730e1c4286f0a1b4386b0a19c28650e18c285f0616c18570e14c284f0e12c28470e10c38290a094281f0e06c28170e04c1d6f1f5ac1d671f58c7c6f1f1b47c6b1f1a87c67231987c651f17c1c5b0715c7c532adbcab6e1ad7c6b5e06d6c1b5a06d5c1b561ed4c6b521ed3c7b4e06958496f165ac49671658c495f0656c19571654c494f1652c49471650c493f124f4593b164e44937124d45933164c4286f0e1ac28670e18c285f0616c18570e14c284f0e12c28470e10c283f0a0f4383b0e0e428370a0d438330e0c4281f0e06c28170e04c1e7f1f9ec1e771f9cc7d7f1f5f47d7b1f5e87d77235d87d751f5bc1d6b0759c7d631f1fcac7e1f1f47c6f1f1b81c6b071a81c67071987c631f1887c5f1f1787c5d06d98aa7e229d86a6e1e9787a561e9387a4c1e91ba244125fc597b125dc5973125bc196b0659c59631257c595b1255c59531253c494d1652c59491251c49451650c5941164a449250a1fc387b0a1dc38730a1bc186b0619c38630a17c385b0a15c38530a13c284d0e12c784a0e12438480a11c78460a11428440e10c38410e0a428250a07c381b0a05c3813075bc7d6b0759c7d63231bc8c6e2319c8c63231886c5f0716c1c571f14c7b6722d987b651ed7c7b5e06d6c1b571ed4c7b521ed3cdb4e1ed34496f165ac49671658c495f0656c19571654c494f1652c49471650c493f164ec4937164cc286f0e1ac28670e18c285f0616c18570e14c284f0e12c28470e10c283f0e0ec28370e0cc281f0e06c28170e04c7d6f1f5b87d6d071bc8c6e231ac8c690719c8c63231889c610717c8c5b0715c8c5322dbc8b6e22d7c8b5e22d6c8b5922d4c8b5232d446b4f06d2c1b4726d0c8a6e125bc596b1259c59631257c595b1255c59531253c194b0651c5943124fc593b124dc59330a1bc386b0a19c38630a17c285d0e16c28570a15438530a13c184b0611c38430a0fc383b0a0dc38330a07c381b0a05c3813075bc9d6b0759c9d63331bcac6e371ac8c6a3319c8c663718cac621b17c6c5e0716c1c5a0715c1c562714c6c5232dbc7b6be0da8cb67dcd987b631ed7c9b5e06d6c1b571ed4c9b52125bc596b1259c59631257c195b0655c59531253c494d1652c59491251c49451650c5941124fc593b124dc59330a1bc386b0a19c38630a17c185b0615c38530a13c284d0e12c38490a11c28450e10c38410a0fc383b0a0dc38330a07c381b0a05c3813075bc9d6b0759c9d63fd1bfd46bed19f94632717c1c5b0715c9c5306d58aa6e229986a5e2e93b6246125bc596b1259c59631257c195b0655c59531253c594b1251c5943164a449250a1bc386b0a19c38630a17c185b0615c38530a13c384b0a11c38430e0a428250a07c381b0a05c3813075bc6d6b0759c7d631b1bc6c6e1b1ac1c6a0719c1c661b18c6c621f17c7c5e0716c1c5a0715c1c561b14c6c521edbc7b6b1ed9c7b631ed7c1b5b06d5c7b531ed3c7b4d1ed1c7b451ed0c6a6f1a99c6a5f0695c6a4f1a9346a471a9146a3f1a8dc496f165ac49671658c495f0656c19571654c494f12534594b16524494712514594316504493f164ec4937164cc592b1249c286f0e1ac28670e18c285f0616c18570e14c284f0a134384b0e12428470a11438430e104283f0e0ec28370e0cc382b0a09c281f0e06c28170e04c1e7f1f9f81e7d079dc1e751f9cc8e72075dc1d76075d47d6f1f5b88d6d1f1fc7c7b1f1dc7c731f1bc1c6b0719c7c631f17c7c5d1f16c7c591f15c7c551f14c7c511adfc8b7e1adec6b7a1addc8b761adcc6b721adbc7b6e06dac1b6a06d9c1b661ad8c6b621ad7c8b5e1ad748b5c1ad6c6b5a1ad646b581ad5c8b561ad5743541ad4c6b521ad446b501a9fc6a771a9bc1a671a97c6a5d1a95c6a551e9286a471a9186a371a8d86a35125fc597b125dc5973125bc196b0659c59631257c495d1656c59591255c49551654c59511253c594b1251c5943124fc493d164ec5939124dc4935164cc5931164ac49270a1fc387b0a1dc38730a1bc186b0619c38630a17c285d0e16c38590a15c28550e14c38510a13c384b0a11c38430a0fc283d0e0ec38390a0dc28350e0cc38310e0ac28270a07c381b0a05c38131edb87b621ed787b521ad346a4d1a9146a3d1a8d4493d124d4283d0a0d41d6f1f5ac1d671b58c1c6f1f1ac7c671f18c7c5f0716c1c571f14c6b6f2adb86b6b1ad9c6b631ad886b5f1ed781b5b06d5c6b531ad486b4fc8d386b4d1a9bc6a671a97c1a571a93c6a471a8dc6a361a8d4496f165ac49671658c495f0656c19571654c494f1652c49471650c493f124f4593b124dc4935164cc592b1249c286f0e1ac28670e18c285f0616c18570e14c284f0e12c28470e10c283f0a0f4383b0a0dc28350e0cc382b0a09c281f0e06c28170e04c1d6f1f5ac1d671b58c1c6f071b86c6b1b1a86c671b1986c63071887c5f1f1781c5b071681c57071586c531b1487b6f1edac7b671ed8c7b5f06d6c1b571ed4c7b4f1ed347b471ed147b431a9bc6a671a97c1a571a93c6a4d1a91c6a451a8fc7a3a1a8dc6a36125bc596b1259c59631257c195b0655c59531253c494d1652c59491251c49451650c5941124fc593b124dc5933164ac49270a1bc386b0a19c38630a17c185b0615c38530a13c284d0e12c38490a11c28450e10c38410a0fc383b0a0dc38330e0ac28270a07c381b0a05c3813079fc1e7d1f9ec8e7a079dc7e76079d41d7f075f81d7d1f5bc7d6e235b47c7f1f1ec7c771f1cc7c6f071ac1c671f18c7c5f1f1747c5b1f1687c591f1607c572b1587c55c51507c531f1446b7f2adf86b7b1ade86b7722dd86b731adc86b6f1edb81b6b06da81b6706d986b631ad886b5f26d786b5d26d706b5b1ad686b591ad606b572ad586b55c0d506b531ad486b511ad406a7f1a9dc6a6f0699c6a5f1a9746a571a9547a4a1a91c6a461a8dc6a361a8d4497f165ec4977165cc496f065ac19671658c495f12574595b16564495712554595316544494f1652c49471650c493f124f4593b164e44937124d45933164c4592b1249c287f0e1ec28770e1cc286f061ac18670e18c285f0a174385b0e16428570a15438530e144284f0e12c28470e10c283f0a0f4383b0e0e428370a0d438330e0c4382b0a09c281f0e06c28170e04c1d6f1f5ac1d671f58c7c6f1f1b87c6b231a87c671f1987c63271886c5f1b1786c5d1edbc7b6b1ed9c7b631ed7c1b5b1ed641b571ed4c7b511ed3c1b4d1ed2c1b4706d146a6f1a99c6a5f1a9741a571a9546a4f1a9346a471a9146a3f1a8dc496f165ac49671658c495f12574195b0655c49551654c494f12534594b16524494712514594316504493f164ec4937164cc592b1249c286f0e1ac28670e18c285f0616c18570e14c284f0a134384b0e12428470a11438430e104283f0e0ec28370e0cc382b0a09c281f0e06c28170e04c7d6fcd5ac7d67bd58cbc6f1f1acbc671f18c7c5f1f16c7c571f14c6b6f2adb86b6b1ada86b6722d986b631ad886b5fb8d786b5b06d686b5706d586b531ad486a6f1a99c6a5f1a95cba4a1a91c6a461a8dc6a361a8d4496f165ac49671658c495f1656c49571654c494f1652c49471650c493f124f4593b164e44937124d45933164c4592b1249c286f0e1ac28670e18c285f0e16c28570e14c284f0e12c28470e10c283f0a0f4383b0e0e428370a0d438330e0c4382b0a09c281f0e06c28170e04cad6f275b81c6b0719c1c630715c1c551edbc7b6b1ed9c7b6306d7c1b5d06d6c1b591ad5c6b5506d4c1b5106d3c1b4b06d1c1b43125bc596b1259c59631257c495d1656c59591255c49551654c59510653c194b0651c1943124fc593b124dc59330a1bc386b0a19c38630a17c285d0e16c38590a15c28550e14c38510613c184b0611c18430a0fc383b0a0dc38330a07c381b0a05c3813079fcae7e079f41d7b235e81d79075dc1d76075cc1d710759c1d66075947c7f1f1ec7c771f1cc1c6f071b41c6b1f1a41c671f1941c63071841c5f0716c1c570714c7b4e2a9f88a76069b81a6c0699ac264069781a561a918497f165ec4977165cc196f065b4196b165a4196712594196306584195f0656c19570654c494f1652c49471650c592912494287f0e1ec28770e1cc186f061b4186b061a838690e1a018670619828650a190186306184185f0616c18570614c284f0e12c28470e10c38290a094281f0e06c28170e04c1d6f0759c8d630719c1c662717c9c5e22dbc7b6b22d9c7b631ed7c1b5b06d5c7b5322d3c6b4d1ed2c7b491ad1c6b451ed0c7b41125bc596b1259c59631257c195b0655c59531253c494d1652c59491251c49451650c5941124fc593b124dc59330a1bc386b0a19c38630a17c185b0615c38530a13c284d0e12c38490a11c28450e10c38410a0fc383b0a0dc38330a07c381b0a05c3813079fc8e7e079f41e77079d48e73239c81d77075d81d75235bcad6e235b48c7f1f1ec8c771f1cc7c6f071ac1c671f18c8c5f231747c5b1f1648c57331547c531f1447b4e229f88a76269b81a66229788a5c2295aa2541a918497f165ec4977165cc496f065ac19671658c495f12574595b16564495712554595316544494f1652c49471650c592912494287f0e1ec28770e1cc286f061ac18670e18c285f0a174385b0e16428570a15438530e144284f0e12c28470e10c38290a094281f0e06c28170e04c8d6f235b41c6f071b41c5f0716c1c531adbc6b6d06dac1b6906d9c1b6506d8c1b611ed7c7b5b1ed5c7b5306d3c1b4b06d1c1b431e8f8496f125b4596b165a4496712594596316584495f1656c49571654c194f0652c19470650c493f164ec4937164cc286f0a1b4386b0e1a428670a19438630e184285f0e16c28570e14c184f0612c18470610c283f0e0ec28370e0cc281f0e06c28170e04c1e7f079f88e7d075fc1d7e075f41d6f075b81d6b075a41d63235881d61071fc7c7d071ec1c79071dc1c75071cc7c711f1bc7c6b1f19c7c630717c1c5b0715c1c531ed381a7ea09f01a76069d08a6e229981a5e069586a46065fc497d065ec1979065dc1975065cc5971125bc596b1259c59630657c195b0655c19531253c594b1251c5943164a44925061fc287d061ec1879061dc1875061cc38710a1bc386b0a19c38630617c185b0615c18530a13c384b0a11c38430e0a428250a07c381b0a05c3813075bc8d6b0759c1c6f071b88c5f23178ab6f1edac8b671ed8c7b5f06d6c1b571ed4cab4f1ad347b4b1ed246b471ad147b431ed04496f165ac49671658c495f0656c19571654c494f12534594b16524494712514594316504493f164ec4937164cc286f0e1ac28670e18c285f0616c18570e14c284f0a134384b0e12428470a11438430e104283f0e0ec28370e0cc281f0e06c28170e04c1e7f079f48e7b239e81e77239d81e75075fc1d7e075f48d6f235b88d6d2b1fc7c7b231dc7c731f1bc1c6b0719c7c632717cac5d1f16c7c592b15ccc551f14c7c512ad586b541ed38aa7e229d89a6e069989a5e26970aa56989506a46125fc597b125dc5973125bc196b0659c59631257c495d1656c59591255c49551654c59511253c594b1251c5943164a449250a1fc387b0a1dc38730a1bc186b0619c38630a17c285d0e16c38590a15c28550e14c38510a13c384b0a11c38430e0a428250a07c381b0a05c38131f9f89e721f5f81d7a075d87d721f5b89d6d1f1b47c651f1741c591f1541c511ed38aa7e229d87a6e069989a5e269709a56469506a46125745959125545951164a449250a17438590a15438510e0a428251f9fc7e7e1f9f47d7f235ec7d772b5cc7d6f075b4ad6b915a47d6707594ad632b5847c7b231e87c79231dc8c761f1cc7c712319c8c66231947c5f1f16c7c571f14cab661ad907b4e2a9f8aa7c229d88a741a9b86a6c229986a64789781a561a918497f165ec4977165cc496f125b4596b165a4496712594596316584495f1656c49571654c494f1652c49471650c592912494287f0a1f4387b0a1dc28750e1cc286f0a1b4386b0e1a428670a19438630e184285f0e16c28570e14c284f0e12c38490a11c38430e10438290a094281f0e06c28170e04c8e7a1f9d81d7e1f5e87d76075c87d6e235b47c6d1f1947c5d071647c55071447b4e229f88a761e9b81a66269789a5c269591a541a918596916584495d1656449551654459291249438690e184285d0e16428550e14438290a0947e7f1f9f87e7d1f5fc1d7d235ec8d791f5dc1d75235ce25711f5bc8d6b1f59c8d63231fc8c7e2b1f48c6f231b87c6b1f1a47c63231887c611f17c7c5b1f15c7c5322df86b7c1ed388a7e1a9f06a761a9d08a6e2a9b08a6622990fa5e069586a46125fc497d165ec5979125dc4975165cc5971125bc596b1259c59631257c595b1255c59531253c594b1251c5943164a449250a1fc287d0e1ec38790a1dc28750e1cc38710a1bc286d0e1ac28670a19438630a17c385b0a15c38530a13c384b0a11c38430e0a428250a07c381b0a05c3813079fc7e7b079dc7e731f5fc7d7e1f5ec8d7a1f5dc7d761f5ccad721f5bc7d6e1f5b47c7f1f1ec7c771f1cc1c6b071a87c690719c1c661f18c7c610715c1c56071547b561ad507b4e2a9f88a761e9b89a6c069981a641a9786a5c069581a541a918497f165ec4977165cc496f065ac19671658c495f12574595b16564495712554595316544494f1652c59491251c594316504592912494287f0e1ec28770e1cc286f061ac18670e18c285f0a174385b0e16428570a15438530e144284f0e12c28470e10c38290a094281f0e06c28170e04c1e7f079f81e7b239e81e77079d81e732b9c81d7f075ec1d77075cc1d6f075b81d6d1f1fc7c7b1f1dc7c73071bc1c6e1f1b41c5f071781c5b071641c53071487c5106db86b6c1ed38aa7e229d81a6e1a9b01a66069901a5e749701a56069506a46125fc597b125dc5973065bc496d065ac19690659c19650658c59610657c195b0655c19531253c594b1251c5943164a449250a1fc387b0a1dc3873061bc186e0a1b4286c061ac18690619c18650618c18620e18438600617c185b0615c18530a13c384b0a11c38430e0a428250a07c381b0a05c3813 20 1048575 8 255 11 2047 18 262143
def cc_72_2 : Nat → List (Nat × Nat) := unpackCursorV4 0xaa92da7534a7005a313f9ec4599e4e96a3490f5b8828d8275b79c8b7415b6b1906545d5c1935675a511564ce43475594492c405443a85d35e4a32c322cd5f2408d1df611528d0f65c0a05605b450005b 0x36bf07d7a0faec1f5c80eb70cd6d19ad8075980eb281d6403ac42b1f83e3907c6d038cc071940e320ab7e036f422dd80db901b66036ca32d780dae89b5c0f69c125742cac849550b2a21253424a28193d0b272124d40c988285d070b20a1541c288183d070720a0d40c1886d7e0faf4235d856b909d6e19ada275b00eb501d6619aca33590563f0ac72198da071a80e330cc65198c82adf83dbd08b76156e432db865b681b5e036ba06d700da701b4d03698125742cac849550b2a21253424a28493d25274164e42c9c129360926a124d02c988285d070b20a1541c288283d070720a0d41c1881c56156dc2ad88249e8493503ade075ac0eb381d630d8de1f1ac46338ac63038be071780e2b81c53038a406dbc55b701b6b036ce06d8c0db101b57036ac06d540da7dc34e0369a125bc2cb5849670b2c60657c0cad81957032a61253c2ca5849470b286064fc0c9e8193b0326e124d40c998286f070d60a19c1c318185f030b60615c0c298284f070960a11c1c218183f03076060dc0c198281f070360a05c1c0981d6f03adc075ac0eb481d6703ac62b5880eb081c6f038d60719c0e3181c5f038bc0717435b787b6b116ce2ad8c0daf81b5e0369e06d380da581b490368606d0865a081a5e092de165ac24b385963032be125740cad81957032aa0654c0ca78194b0328e0650c249f8593b0926e164cc14378386b050ce0e18c0c2f8185e030b60615c0c29818520309e0612c0c23818430507e0e0ec141b838330503e0e06c140b8381315ade235ac46b38ad630d8de1b1b8463587c6a118ce23198563186c62198be2717af22d81c5a198ae0715aea2989c52156de2adb845b588b67156c62ad8865af8bb5bb66b432d5ed1ab0bb53092de165ac24b385963092be1656c24ab859530929e125342ca5859490928e125142ca1859410927e124f42c9d849370926a164cc14378386b050ce0e18c142f8385b050ae0e14c14278284d070960e124142382845070860e104141f8383b0506e0e0cc140f8381b0502e0e04c56b788d6b11ace2b58c563788c6b118ce2b18f422fe645bc88af8914c45b306a6ebe4bc069585d2759246092de165ac24b385963092be1656c24ab859530929e1652c24a3859430b2521249414378386b050ce0e18c142f8385b050ae0e14c14278384b0508e0e10c1c14838280504a0a090140f8381b0502e0e04c36b786d6d0fad61f5a436b386d650dac61b5840e3781c6d038ce071944e3181c5f118b60715c4e2986b6f0d6da1adac35b488b67116ca1ad8c35b086b5f0f6b622d5c3da987b4f0369606d1c3da186a6f034da0699c0d3286a5f0d4ae1a93c0d2386a3f0d46e125bc24b68596b0b2d21259c24b2859630b2c21257c2cad849570b2a61253c0ca5819470b286124fc2c9d849370b266164ac24938286f050da0e1ac1c3482867050ca0e18c1c308285f070b60a15c1c298284f030960611c1c218283f070760a0dc1c198382b0504e0a07c1c0d82817070261f9fc3f3f07e7d03afe235ec0ebb89d7303ade075b44eb589d6903ace075944eb189d610d8fe2b1f8363d86c7a0d8ee231d8363986c720d8de2b1b836368ac6c0d8d61b1a8363486c680d8ce2b1983632d74640d8c61b188363086c600f6f622de83dbc88b77116ec1edcc3db888b67116cc22d943daf81b5b036ae1ed4c35a786b4d0d6961ed2435a38cb450d6861ad04353f86a770d4de1a9b4353386a65034b40695c0d2b01a470348c06914351f86a37092fe165ec24bb85973092de125b42cb585969092ce125942cb185961092be0656c0cab859530929e125342ca5859490928e125142ca1859410927e164ec249b859330b2561249c143f8287d070f60a1dc143a83873050de0a1b41c3583869050ce0a1941c3183861050be0616c0c2b838530509e0a1341c25838490508e0a1141c21838410507e0e0ec141b83833070560a09c140f8381b0502e0e04c36b786d6e0dad61b5a846b388d660dac61b5880e3787c6b038ce1f18c0e2f81c5d038ae071543e2987b6f0d6d61ed9c3db186b5f0d6ba1ed6c3dac86b570d6aa1ad4c35a887b4f0369606d1c3da186a6f0d4ce1a97c0d2e81a57034aa1a93c0d2386a3f0d46e125bc2cb5849670b2c61257c24ae8595b0b2b21255c24aa859530b2a21253c0ca5819470b286124fc2c9d849370b266164ac24938286f070d60a19c1c318285f050ba0e16c1c2c82857050aa0e14c1c288284f030960611c1c218283f070760a0dc1c198382b0504e0a07c1c0d8281707026079fc3f3d81e770fce61b5fc46bf06d7b0daf41b5dc46bb06d730dae41f1fc463f07c7d0f8ee1f1d43e3987c720f8de071ac0e3387c630d8be1b174362d87c590d8ae1f154362986c510f6ee22dd83dba87b6f0f6dc06dac0db501b67036cc1ed8c3db106b5f0d6bc1ad7435ae06b5b0d6b41ed643dac06b570d6ac1ed56a9aa06b530d6a41ad4435a807b4f0f69c1ed34353f86a77034d40699c0d3301a57034ac06954352786a470d47e1a8f4351b86a35092fe165ec24bb85973092de065ac0cb385963092be125742cad85959092ae125542ca9859510929e1652c24a3859430927e124f42c9d859390926e124d42c99859310b2561249c143f8387b050ee0e1cc14378186b030ce0e18c142f8285d070b60e164142b82855070a60e14414278384b0508e0e10c141f8283d070760e0e4141b82835070660e0c41c15828270503e0e06c140b838130dade1b5b83eb587d6a0dace1b59836b186d62038de231ac0e3388c63038be07174462d81c57038aa22dbc3db586b670f6c62ad7c55ae86b5b0d6b21ad5c35aa86b530d6a21ed3c0da581b470f6861a9bc353381a5f034ba1a95c0d2a86a4f0348e1a8fc351b8496f0b2d61259c2cb18495f092ba1656c2cac84957092aa1654c2ca88494f032960651c2ca18493f0b276124dc2c998592b0924e0a1bc1c3582867070c60a17c142e8385b070b20a15c142a83853070a20a13c0c2581847070860a0fc1c1d82837070660e0ac14138281f070360a05c1c0987e7f0fcfc1f9f40ebf81d7d11af6235e40ebb81d7511ae6275c40eb788d6b03ace2358c363f88c7e0d8fb4d1f0363d86c7a0d8f21b1e0363b88c760d8ea231d0363986c720d8e21b1c0363788c6e0d8d61b1a8363388c660d8c61b18845bf88b7e156fa22dbc45b707b6b0f6d21ed8c45b107b610f6be06d6c0dab87b530d69e1ad3435a587b490d68e32d1435a186b410d4fe1a9f8353e86a7c0d4ee1a9d4453906a6f0d4ce069680d2b81a560348e069180d2286a3f0d46e125fc24be8597b0b2f2125dc24ba859730b2e2125bc2cb5849670b2c61257c0cad819570b2a61253c24a68594b0b2921251c24a2859430b282124fc2c9d849370b266164ac24938287f050fa0e1ec1c3c82877050ea0e1cc1c388286f050da0e1ac143382865070c60a17c0c2d81857070a60a13c14268384b070920a11c142283843070820a0fc1c1d82837070660e0ac14138281f070360a05c1c098ad6f15adc1b5ac36b506d670dacc1b58c36b101c6f0f8d60719c3e3181c5f038ba0715c0e2a87c530f6de1edac3db386b630d6be1ad743dad87b590d6ae1ad5435a986b510f69e06d2c0da387b430d4de1a99c352f81a5d034ae06954352781a4a0348e06918351f86a37092de165ac24b385963092be125742cad85959092ae125542ca9859510929e0652c0ca3859430927e164ec249b859330b2561249c14378386b050ce0e18c142f8285d070b60e164142b82855070a60e14414278184b0308e0e10c141f8383b0506e0e0cc1c15828270503e0e06c140b8381303cfe1f9ec0f3b87e730dafe2b5f836bd86d7a0daee235d836b986d720f8fe1f1f43e3d87c7a0f8ee231d83e3a87c6f038d60719c3e3186c5f0d8ba1b16c3e2c86c570f8aa1b14c362887b7f156fc1edf43db787b6e0f6da26db00db581b6a036ce06d983db281b640f6c61ed8835af86b5e0d6ba1ad7035ad86b5a0f6b21ed6035ab86b560f6ab44d5035a986b520d6a21ad403da787b4e0f69a1a9fc353b81a6a034ce069980d2b81a56034aa1a93c352386a3f0d47a1a8dc351a8497f0b2f6125dc2cb98496f032d60659c2cb18495f092ba1656c2cac84957092aa1654c2ca88494f0b2961251c2ca18493f0927a164ec2c9c849370926a164cc2c988592b0924e0a1fc1c3d82877070e60a1bc0c3581867070c60a17c142e8385b070b20a15c142a83853070a20a13c1c2582847070860a0fc141e8383b0f0740e0e41c1c028370f06c0a0d4141a03833070620e0ac14138281f070360a05c1c098cd6f15adc375ac46b50cd6711acc3758c56b101c6f138d60719c4e3181c5f038ba0715c0e2a89c53196de1edac65b387b630d6be1ad7835ae87b4f1369c06d2c0da387b43136841a9bc353386a5f034ba0695c0d2a86a4f0348e1a8fc351e86a370d46a125bc2cb5849670b2c61257c24ae8595b0b2b21255c24aa859530b2a21253c0ca5819470b286124fc2c9d849370b266164ac24938286f070d60a19c1c318285f050ba0e16c1c2c82857050aa0e14c1c288284f030960611c1c218283f070760a0dc1c198382b0504e0a07c1c0d8281707026075bc4eb581d6713ac61b1bc563706c6b0d8d41b19c463306c630d8c558dbea1b5d2367a06c626d7c0dad81b57136a61ad3c35a686b4b176921ad1e79a286b430d6821a9bc353381a5a034ae069580d2381a460348a1a8fc351b8496f0b2d61259c2cb18495f032b60655c2ca98494f0929a1652c2ca4849470928a1650c2ca08493f0b276124dc2c998592b0924e0a1bc1c3582867070c60a17c0c2d81857070a60a13c14268384b070920a11c142283843070820a0fc1c1d82837070660e0ac14138281f070360a05c1c0987d6f0fadc071bc0e3581c67038c60717c0e2e81c5b038b20715c0e2a81c53038a21edac3db387b630f6ae1ed540da781b4b0368e06d0c24b78596b092ce1658c24af8495d0b2b61656424ab849550b2a6165440ca78194b0328e0650c249f8593b0926e164cc14378386b050ce0e18c142f8285d070b60e164142b82855070a60e1440c278184b0308e0610c141f8383b0506e0e0cc140f8381b0502e0e04c3f3f87e7e0fcfa075fc0ebd81d7703ae6075bc0eb681d6b03ad20759c0eb281d6303ac21f1ec3e3d07c790f8ee231d83e3987c710f8ce231983e3281c5f038b60715c0e2981b5e154fc229d855370aa6c154cd349900d2b07a4e0f48c125fc2cbd849770b2e6125bc24b68596b0b2d21259c24b2859630b2c20657c0cad81957032a61253c2ca5849470b286164a424928287f050fa0e1ec143b82875070e60a1bc14368386b070d20a19c143283863070c20617c0c2d81857030a60a13c1c2582847070860e0a414128281f070360a05c1c0981d6f0fad60759c0eb187c6f0f8d61f18c3e2f81c5b038ae0714c453309a560f48c125bc2cb5849670b2c61257c2cad849570b2a61253c2ca5849470b286164a414378386b050ce0e18c142f8385b050ae0e14c14278384b0508e0e10c1c148281f070360a05c1c0987d6f0fada071bc0e3681c6b038d20719c0e3281c63038c20717c0e2d81c57038a61edbc3db687b5f0f6b61ed4c0da781b4b0368e06d0c0d270496f092da165ac2cb484967092ca1658c2cb08495f0b2b61255c2ca98194f032960651c0ca18493f0b276124dc2c998286f050da0e1ac1c3482867050ca0e18c1c308285f070b60a15c1c298184f030960611c0c218283f070760a0dc1c198281f070360a05c1c0987e7f0fcfc1f9f40ebf81d7e03afa075f00ebd81d7903aee075d40eb988d7203ae32d5c00eb781d6b03ace0758c3e3f88c7e0f8fa1f1bc463707c6b0f8d21f18c3e3107c61038be0716c0e2b81c53036bc229fa513e08a76114e8229b8453301a560f49c1e91824bf8497d0b2f6165e424bb849750b2e6165c424b78596b092ce1658c0caf8195b032ae0654c24a78594b0928e1650c2c9484925050fe0a1f41c3d83879050ee0a1d41c3983871050de0a1b41c3582867050ca0e18c0c2f8185b030ae0614c14278384b0508e0e10c1c14828250503e0e06c140b8381303ade075ac0eb381d630f8de2b1b83e3587c6a0f8ce231983e3187c62038be071780e2d81c5a038ae071580e2981c520f6de1edac3db387b63036be06d6c0dad01b57036ac06d4c24b78596b092ce1658c0caf8195b032ae0654c24a78494d0b2961652424a3849450b28616504249f8593b0926e164cc14378386b050ce0e18c0c2f8185b030ae0614c14278284d070960e124142382845070860e104141f8383b0506e0e0cc140f8381b0502e0e04c0eb781d6b03ace0758e623787c6b928ce1f18c0e2f81c5b038ae0714c0daf0aa6e114cc069585d2748246092de165ac24b385963032be0656c0cab819530929e1652c24a3859430b2521249414378386b050ce0e18c0c2f8185b030ae0614c14278384b0508e0e10c1c14828250503e0e06c140b8381303ade075ac0eb381d63038de071b80e3581c6a038ce071983e3187c62038be071780e2b81c53038a406dbc3db587b690f6ce1ed8c3db081b5f036b606d5c0da987b4f0f69a06d2c0da481b470368a06d0c0da086a6f0d4ce0697c0d2b86a4f0d49a1a91c352286a3f0d46e125bc2cb5849670b2c60657c0cad81957032a61253c24a68594b0b2921251c24a2859430b282124fc2c9d849370b266164ac24938286f050da0e1ac143382865070c60617c0c2d81857030a60a13c14268384b070920a11c142283843070820a0fc1c1d82837070660e0ac14138281f070360a05c1c0987e7f0fcfc1f9f40ebf81d7e03af6235e80ebb81d7603ae62b5c80eb781d6e03ada075b00eb58ad6a03ad3195a00eb381d6603aca075900eb18ad6203ac22b5800e3f81c7b038ee071cc0e3781c6d038d6071a40e3381c65038c6071843dbd87b7a0f6f21eddc45bb07b730f6e21ed9c45b307b65036be1ed740dad81b59036ae06d540da987b510369e06d2c0da381b430d4fe1a9dc353786a6d0d4ce1a9940d2f81a5e0d4ba0693c0d2701a420d47e1a8dc24bf8597b092ee165cc24b78496d0b2d6165a424b3849650b2c6165840caf8495d032b6065640cab81955032a6165440ca78194b0328e0650c249f8593b0926e164cc2c9584927050fe0a1f41c3d82877050ea0e1cc14378286d070d60e1a4143382865070c60e1840c2f8285d030b6061640c2b81855030a60e1440c278184b0308e0610c141f8383b0506e0e0cc1c15828270503e0e06c140b8381303ade075ac0eb381d63038de071b83e3587c6a038ce071980e3181c62038be071780e2b81c53038a41edbc3db587b69036ce1ed8c3db081b5f036b606d5c0da987b4f0f69a06d2c0da481b470368a06d0c0da086a6f0d4ce0697c0d2f01a57034a41a93c352686a470d48a1a8fc351b8496f0b2d61259c2cb18195f032b60655c0ca98494f0929a1652c2ca4849470928a1650c2ca08493f0b276124dc2c998592b0924e0a1bc14368386b050ce0a1941c318185f030b60615c0c298284f0509a0e12c1c24828470508a0e10c1c208283f070760a0dc1c198382b0504e0a07c1c0d82817070261f9fc3f3f07e7d03afe075f80ebe81d7c03af6235e80ebc88d7803aee075d80eba81d7403ae6235c80eb8c457003ade075b80eb588d6a03ace075980eb188d62038fe071f40e3d81c79038ee071d40e3981c71038de071ac0e3381c630f6fe22df83dbe87b6f116dc1edac3db487b630f6c41ed840daf87b5d036b606d640dab81b55036a61ed440da781b4b0368e06d0c353f86a7d0d4ee1a9d4353786a67034be06978352e81a4f0349c06908351f86a37092fe125f42cbd85979092ee125d42cb985971092de165ac24b385963032be125740cad81959032ae065540ca9859510329e0652c0ca3819430927e164ec249b859330b2561249c143f8287d070f60e1e4143b82875070e60e1c414378286d070d60a19c143283863030be0a1740c2d81859030ae061540c29838510309e0612c0c23818430507e0e0ec141b83833070560a09c140f8381b0502e0e04c0eb781d6b03ace0758c3e3787c6e0f8d6231a83e3387c660f8c62b1880e2f81c5e038ae0714c0e2907b6f0f6d61ed9c3db181b5f036b606d680dab81b56036a606d1c0da301b450d4de1a99c0d2f81a570d49e1a934352386a450d47e1a8f4351b86a35092de165ac24b385963032be0656c0cab819530929e125342ca5859490928e125142ca1859410927e164ec2c9c849370b266164c42c9584927050de0e1ac143383863030be0616c0c2b818530509e0a1341c25838490508e0a1141c21838410507e0e0ec141b83833070560a09c140f8381b0502e0e04c0eb781d6e03ad6235a80eb381d6603ac62b5880e3781c6b038ce0718e29b787b6b866ce1ed8c0dafc235d036b606d640dab81b55036a62ed440da781b4b0368e06d0c353786a67034be06978352e81a4f0349c06908351f86a37092de165ac24b385963032be125740cad81959032ae065540ca9859510329e0652c0ca3819430927e164ec249b859330b2561249c14378386b050ce0e18c0c2f8285d030b6061640c2b81855030a60e1440c278184b0308e0610c141f8383b0506e0e0cc1c15828270503e0e06c140b838130fade1f5b80e3788c6b038ce2718c0e2f81c5d0d8b61b1640e2b81c55138a61b1443db588b6a116ce22d983db188b57116aa1ed3c0da581b470f686125bc2cb5849670b2c61257c24ae8595b0b2b21255c24aa859530b2a21253c0ca5819470b286124fc2c9d849370b2660a1bc1c3582867070c60a17c142e8385b070b20a15c142a83853070a20a13c0c2581847070860a0fc1c1d82837070660a07c1c0d82817070261f9fc3f3f07e7d03afe235ec0ebb89d7303ade075b44eb589d6903ace075944eb189d610f8f6231e83e3c88c77118ec1f1cc3e3888c67118cc231943e2f81c5b038ae1f14c0dab0aa7e154f8229d8453a0aa6e154d82a99a013206a5e0f49c3291824bf8597b092ee165cc24b78496d0b2d6165a424b3849650b2c61658424af8195b032ae1654c24a78594b0928e1650c2c9484925050fe0a1f41c3d82877050ea0e1cc14378286d070d60e1a4143382865070c60e184142f8185b030ae0e14c14278384b0508e0e10c1c14828250503e0e06c140b83813 20 1048575 8 255 11 2047 19 524287
def cc_72_3 : Nat → List (Nat × Nat) := unpackCursorV4 0xaec43a9557a51449f25f9af439525d90c468c24a8784a846327e264782607265c69b8b64c4f5f15b5628f5035f4748f4195b37f9a329562ce5b2894522e5b1e74718067138480db5d0984304e4a0004e 0x75bc0eb581d6703ac6231bc3e3588c670f8c60717c0e2b81c53036de06db80db581b6a0d6ce1ad980db181b62036ae06d583da787b4e092de165ac24b385963032be0656c0cab819530929e1652c24a3859430927e124f42c9d859390926e124d42c9985931050de0e1ac143383863030be0616c0c2b818530509e0e12c1423838430507e0a0f41c1d838390506e0a0d41c19838310503e0e06c140b8381303cfe079ec0f3b81e7311afe1f5ec46bb87d7303ade075b85eb681d6703aca0758c0eb101c7f118fc071ec0e3d01c77118ec071cc0e3901c67038cc071940e2f8bc5e038ba22df8353b01a6e034cc1e9785d2b01a4e034980691bf1220497f0b2f6125dc2cb98196f032d60659c0cb18495f0b2b61255c2ca98194f0329a0652c2ca4819470928a0650c0ca0859290924a0a1fc1c3d82877070e6061bc0c3581867030c60a17c1c2d82857070a60613c0c268184b070920611c142281843030820e0a414128281f070360a05c1c0981d6f03adc1b5ac36b501d6703acc0758c0eb101c6f038d60719c0e3181c5f038ba22dbc3db588b670f6c636d7c4dae81b4f0369606d0c45370496f0b2d61259c2cb18495f092ba1656c2cac84957092aa1654c2ca88194f032960651c0ca18493f0b276124dc2c998286f070d60a19c1c318285f050ba0e16c1c2c82857050aa0e14c1c288184f030960611c0c218283f070760a0dc1c198281f070360a05c1c0981e7f03cfc079ec473d01e7911cf0079dc0f3b01e7311ce4079c4573801d7f03af6075dc0eb981d6f03adc075b4463f87c7b118ee1f1cc0e3781c6e1f8da0717c0e2f01c5b038b20714c0e290bc51116fc1a9d80d377c26c034cc069900d2f01a560f49c3291824bf8597b092ee165cc0cb78496d032d6065a40cb381965032c6165840caf8195b032ae0654c24a78594b0928e1650c2c9484925050fe0e1ec143b83873030de061b814368286c030d6061a40c3381865030c6061881c3083860030be0616c0c2b818530509e0e12c142383843070520a094140f8381b0502e0e04c0eb788d6b03ace2358c463787c6b118ce1f18c3e2f81c5b038ae22dbc3db708b6b0d6d41ad9c35b307b630f6c426d7c4daf01b4f0369c125bc2cb5849670b2c61257c0cad819570b2a61253c2ca5849470b286124fc249e8593b0b272124dc249a859330b2620a1bc1c3582867070c60a17c0c2d81857070a60a13c1c2582847070860a0fc141e8383b070720a0dc141a83833070620a07c1c0d8281707026079fc473d81e7711ce6235fc3ebd88d770fae61f5bc5eb681d6b03ad40759c0eb30bd65118fe231f83e3d88c7a118ee231d83e3988c720f8de3f1b85e3681c5f038bc0717445bf0bb460d6881a9d84d3701a660f4bc2e9583d2707a4c1748de891024bf8597b092ee165cc24b78196b032ce1658c24af8595b092ae1654c24a78494d0b2962e5282ca4859480928e2e51824a2849440b286165042c9484925050fe0e1ec143b83873050de061ac0c3383863050be0e16c142b838530509e0a1341c25838490508e0a1141c2183841070520a094140f8381b0502e0e04c0eb781d6e11ad6235a846b388d6611ac6075880e3788c6b038ce2318c0e2f81c5d116de1edac45b387b63136be26d784dae87b4f1369c06d2c3da189b42092de165ac24b385963092be125742cad85959092ae125542ca9859510929e0652c0ca3859430927e164ec249b85933050de0e1ac143383863050be0a1741c2d83859050ae0a1541c29838510509e0612c0c23838430507e0e0ec141b838330503e0e06c140b8381303ade235ac46b501d6711acc2358c0e3781c6e0d8d61b1a8463386c66118c60718845b788b6b116ce22d8c4daf81b5b036ae26d4c4da789b4d136961ed244da3f8345136861ed0424b78596b092ce1658c24af8195b032ae1654c24a78494d0b2961652424a3849450b28616504249f8593b0926e164cc14378386b050ce0e18c142f8185b030ae0e14c14278284d070960e124142382845070860e104141f8383b0506e0e0cc140f8381b0502e0e04c46b788d6b11ace2358c463788c6e118d61b1a8363386c66118c61f188662f89c5e218b607168662b81c56218a62714845b788b6b116d422d9c45b308b63196be2ed6c65ab8bb53092de165ac24b385963092be1656c24ab859530929e125342ca5859490928e125142ca1859410927e164ec249b85933050de0e1ac143383863050be0e16c142b838530509e0a1341c25838490508e0a1141c21838410507e0e0ec141b838330503e0e06c140b8381311ade235ac46b388d63118de231ac463388c63fe8bff516fda2bf9453116dc1a99bb92f01a561749dd891824b78596b092ce1658c24af8595b092ae1654c24a78594b0928e1650c2c9484925050de0e1ac143383863050be0e16c142b838530509e0e12c142383843070520a094140f8381b0502e0e04c0eb788d6b03ace2358c0e3781c6e118d6231a8463388c66118c607188362f86c5e038b6071685e2c81c57038ac1b14c362906c510d8a022dbc3db588b670f6c61ed7c4daf01b5b176b206d5c3da989b52136a226d3c4da709b4d0d4de1a99c352f81a570d49e1a934352386a450d47e1a8dc24b78596b092ce1658c24af8195b032ae1654c24a78494d0b2961652424a3849450b28616504249f8593b0926e164cc2c9584927050de0e1ac143383863050be0616c0c2b838530509e3213814268284c070960e12414238284507086321081c20838400507e0e0ec141b83833070560a09c140f8381b0502e0e04c0eb788d6b11ad40759c46b308d63038de071b8463388c63038c41b17c362f06c5d116de22dac45b388b63136be06d6f81ac81b57136a626d444da789b4d136961ed244da3f4345136861ed04353786a670d4be1a9740d2b86a550d49e1a934352386a450d47e1a8dc24b78596b092ce1658c24af8495d032b60655c24aa859530929e125342ca5859490928e125142ca1859410927e164ec249b859330b2561249c14378386b050ce0e18c142f8185b070b20615c1c29838510509e0a1341c25838490508e0a1141c21838410507e0e0ec141b83833070560a09c140f8381b0502e0e04c46b787d6e11ace2358c46b108c6f118d62319c46318cc5f038ba4316c4e2c90c57038aa3314c4e2888b6f116d622da845b388b66116c61ad5c35ab06b551969e2ed2c65a38bb430d4de1a99c352f86a5d0d4ae1a954352786a470d47e1a8f4351b86a35092de165ac24b385963092be125742cad85959092ae125542ca9859510929e1652c24a3859430927e164ec249b859330b2561249c14378386b050ce0e18c142f8285d070b60e164142b82855070a60e14414278384b0508e0e10c141f8383b070720a0dc1c1983831070560a09c140f8381b0502e0e04c0ebf81d7d0daf61b5e40ebb81d750dae6275c40eb788d6b03ace2358c363f86c7e0f8fa1f1f0363d86c7a0d8f21b1e0363b86c760d8ea1b1d0363986c72138e2271c03e3788c6e118d6231a83e3388c66118c6231883e2f8bc5e178ba1adfc65be86b7b0d6f21addc35ba86b730f6e222dbc3db588b670f6c606d6c0dad0bb59036ae06d583da98bb510368e06d180da286a7f0d4fc1a9f4353786a6e114c41a97c0d2b86a4f0d49a1a91c352286a3f0d46e125fc24be8597b0b2f2125dc24ba859730b2e2125bc2cb5849670b2c61257c0cad819570b2a61253c24a68594b0b2921251c24a2859430b282124fc2c9d849370b266164ac24938287f050fa0e1ec1c3c82877050ea0e1cc1c388286f070d60a19c1c318285f030b60615c1c298284f0509a0e12c1c24828470508a0e10c1c208283f070760a0dc1c198382b0504e0a07c1c0d8281707026075bc0eb381d63118de1f1ac463387c63138be27174362d89c57178aa1f14c0db781b6b036d406d9c45b301b63036ae26d580daa81b4f1369c06d34353781a670d4be0695c352786a470347e068f40d1b86a35092de165ac24b385963092be1656c24ab859530929e1652c24a3859430327e064f40c9d819370926a064cc2c9584927050de0e1ac143383863050be0e16c142b838530509e0e12c1423838430307e060ec1c1c8183703066060c41c15828270503e0e06c140b8381303ade075b80eb381d6303ac4071bc0e3581c67038c60717c0e2e81c5b038b20715c0e2a81c53038a222dbc3db588b670f6c61ad7c35ae86b5b0d6b21ad5c35aa87b530f6a206d3c0da581b47036861a9bc0d3386a5f0d4ba0695c0d2a81a4f0348e1a8fc351b8496f0b2d61259c2cb18495f092ba1656c2cac84957092aa1654c2ca88194f032960651c0ca18493f0b276124dc2c998592b0924e0a1bc1c3582867070c60a17c142e8385b070b20a15c142a83853070a20613c0c2581847030860a0fc1c1d82837070660e0ac14138281f070360a05c1c0981d7f03afc075f40ebe01d7b03af2075dc0eba81d730dae4075c782b801d6f03ad60759c0eb186c7f178fa1b1ec363c86c770d8ea1b1cc3e3888c6f0f8d62319c3e3181c5f038bc2f1740e2b81c55038a6071480dbf86b7e036fbbcdf00dbd81b7a036f206de00dbb86b76036ea1add00db981b72036e206dc00db788b6e036d606da80db388b66036c606d880dab81b56036aa06d3c5da701b4d0d4fe1a9f8353e86a6f0d4dc229880d2f81a570d49e1a91c0d1f81a3d0346e1a8d424bf8497d0b2f6165e424bb849750b2e6165c424b78596b092ce1658c0caf8195b032ae0654c24a78594b0928e1650c0c9f8193d03276164e40c9b8493503266064c42c9584927050fe0a1f41c3d83879050ee0a1d41c3983871050de0e1ac143383863030be0616c0c2b818530509e0e12c1423838430307e060f40c1d838390306e0a0d40c1981831070560a09c140f8381b0502e0e04c0eb781d6b03ace0758c0e3781c6e038ce0718c0e3101c5f038bc0716c0e2d01c57038ac0714c0e2908b6f0f6d622d9c3db181b5f036b606d640dab81b53176a236d3c4da686b4b0d6921ad1c35a286b430d6821a9bc353701a67114c40697c0d2b86a4f0d49a0691c0d2286a3f0d46e125bc2cb5849670b2c60657c0cad81957032a61253c24a68594b0b2921251c24a2859430b282124fc2c9d849370b266164ac24938286f070d60a19c1c318185f030b60615c0c298284f0509a0e12c1c24828470508a0e10c1c208283f070760a0dc1c198382b0504e0a07c1c0d8281707026075fc0ebf01d7d03af8075ec36bd01d790daf0075dc0ebb01d7503ae8075cc36b901d71daae0075bc0eb701d6b11ad40759c0eb301d6311ac4071fc0e3e81c7b038f2071dc0e3a81c73038e2071bc0e3581c67038c60717c0e2f01c5d0d6fe32df435bd86b790d6ee1add435b987b71116de1edac45b387b63036be06d787dae81b4f0369c06d2c0da481b43036842ed04353f86a7e0d4fa1a9bc353708a62034be1a9740d2b81a550349e0691c351f86a37092fe125f42cbd85979092ee125d42cb985971092de165ac24b385963032be125740cad81959032ae065540ca9859510329e0652c0ca3819430927e164ec249b859330b2561249c143f8287d070f60e1e4143b82875070e60e1c414378386b050ce0e18c0c2f8185e050ba0a1700c2d81859030ae061540c2981852070a20e1400c278184b0308e0610c141f8383b0506e0e0cc1c15828270503e0e06c140b838130fade1f5b846b388d630fac4071bc463581c67118c60717c0e2e86c5b0d8b20715c0e2a89c53138a222dbc3db588b670f6c61ad7c35ae86b5b036b21ad5c35aa81b53036a21ed3c0da581b470d6861a9bc353386a5f0d4ba1a95c352a86a4f0348e1a8fc351b8496f0b2d61259c2cb18495f092ba1656c2cac84957092aa1654c2ca88494f032960651c2ca18493f0b276124dc2c998592b0924e0a1bc1c3582867070c60a17c142e8385b070b20a15c142a83853070a20a13c0c2581847070860a0fc1c1d82837070660e0ac14138281f070360a05c1c0981d7f0dafc075f40ebe06d7b0daf2075dc0eba86d730dae4275c44eb801d6f11ad60759c46b186c7f178fa1b1ec363c86c770d8ea1b1cc3e3888c6f0f8d62319c3e3187c5f178ba0716c0e2d01c57038ac2f15435bf86b7e176fbacdf035bd86b7a0d6f21ade035bb86b760d6ea1add035b986b720f6e21edc045b788b6e176da2adb03db588b6a116ce22d9845b288b640f6c622d883daf8fb5e176ba06d3c0da701b4d0d4fe1a9f8353e86a6f0d4dc22988352f81a570d49e1a91c351f86a3d174741a8dc351b06a350d468125fc24be8597b0b2f2125dc24ba859730b2e2125bc2cb5849670b2c61257c0cad819570b2a61253c2ca5849470b286124fc249e8593b17274164e42c9c049371726c124d4249a059330b262164ac24938287f050fa0e1ec1c3c82877050ea0e1cc1c388286f070d60a19c1c318285f030b60615c1c298284f070960a11c1c218283f0507a0e0ec1c1c828370506a0e0cc1c188382b0504e0a07c1c0d82817070261b1bc0e3686c6b0d8d21b19c0e3286c63e68c22317c462d88c57118a61adbf91b686b6b0d6d21ad9c35b286b63176c222d7c45ad88b57116a7c4d3f71a5ec347d46861a9bc353706a6d0d4be1a978452906a4f0d48e1a8fc351b8496f092da165ac2cb484967092ca1658c2cb08495f0b2b61255c2ca98494f0b2961251c2ca18493f0b276124dc2c998592b0924e0a1bc14368386b070d20a19c143283863070c20a17c1c2d82857070a60a13c1c2582847070860a0fc1c1d82837070660e0ac14138281f070360a05c1c0981e7f11cf6079dc4f3987d7f15afc235ec46bd07d7711aec275cc56b907d6f17adc2f5b4563f87c7b118ee1f1cc0e3581c6a178d20719c0e3307c63178c20715c0e2b01c55116ec1a9f84d3709a6c034cc069904d2f09a5c0f4ac1e9503d270ca46092fe165ec24bb85973092de065ac0cb385963092be125742cad85959092ae125542ca9859510929e1652c24a3859430b25212494143f8387b050ee0e1cc14378186b030ce0e18c142f8285d070b60e164142b82855070a60e14414278384b0508e0e10c1c14838280504a0a090140f8381b0502e0e04c0eb781d6b03ace0758c563787c6b118ce1f18c0e2f8bc5d038ae071540e2986b6f0d6dc06dac0db501b67036cc06d8c0db101b57036ac1ed3c3da70496f0b2d61259c2cb18195f032b60655c0ca98494f0b2961251c2ca18493f0927a164ec2c9c849370926a164cc2c988286f070d60a19c1c318185f030b60615c0c298284f070960a11c1c218283f0507a0e0ec1c1c828370506a0e0cc1c188281f070360a05c1c0981e7f03cf6079dc0f398ad7f0faf6235dc3eb981d6f03adc2f5b40eb381d6503ac6075880e3f8ac7e038f6071e80e3b88c76038e6071c80e3381c66038ca0717c5e2f01c5d116ec1a9f80d3701a660f4bc1e9705d2b5b2540349c069300d2367244092fe165ec24bb85973032de065ac0cb381963092be1656c24ab859530329e065340ca5859490328e125140ca1819410b25212494143f8387b050ee0e1cc0c378186b030ce0618c142f8385b050ae0e14c0c278184d030960e1240c238284503086061041c14838280504a0a090140f8381b0502e0e04c0eb781d6e03ad6075a80eb381d660dac61b5880e3781c6b038ce0718c0e2f81c5d156de1edac45b387b631b6be26d740da781b4b03686125bc2cb5849670b2c61257c24ae8595b0b2b21255c24aa859530b2a20653c0ca58194703286124fc2c9d849370b2660a1bc1c3582867070c60a17c6c2f0285d050b80e16c1c2c82857050aa0e14c6c2903851070a00613c0c2581847030860a0fc1c1d82837070660a07c1c0d8281707026079fc0f3f01e7b11cf4079e4473c01e7703cec079cc573901e7115ce0075fc0ebd81d7703ae6075bc0eb701d6d158fe1f1ec463b87c73038de071b86e3681c5f038bc0716c0e2c81c53038a42f14445bb01b6e0d6d81a9f80d376526c034cc069900d2f6125c034ac069503d2707a4c1948d6891024bf8597b092ee165cc0cb78496d032d6065a40cb381965032c6165840caf8195b032ae0654c24a78594b0928e1650c2c9484925050fe0e1ec143b83873030de061b814368286c030d6061a40c3381865030c6061881c3083860030be0616c0c2b818530509e0e12c142383843070520e0a01412828240503e0e06c140b8381303ade235ac0eb389d63158de1f1ac463387c630f8be2f1740e2d81c5a038ae071585e2a86b6f0d6dc1edac3db508b670f6cc2ad8c35b109b5f136bc06d3c0da708a66092de165ac24b385963092be0656c0cab859530929e1652c24a3859430927e124f42c9d859390926e124d42c9985931050de0e1ac143383863050be0616c0c2b838530509e0e12c1423838430507e0a0f41c1d838390506e0a0d41c19838310503e0e06c140b8381303cfe239ec0f3b89e7315afe1f5ec46bb87d730fade2f5b40eb581d6a03ace075985eb28ac7f158fc1f1ec463d08c77118ec1f1cc563907c6f1b8dc2f1b40e2f81c5e038ba22dd8353f09a6e034cc1e9785d2b07a4e0f4982e91b19220497f0b2f6125dc2cb98496f032d60659c2cb18495f0b2b61255c2ca98494f0929a1652c5ca5059490b2901251c5ca304945092881650c2ca0859290924a0a1fc1c3d82877070e60a1bc0c3581867070c60a17c1c2d82857070a60a13c14268384b070920a11c142283843070820e0a41c1402825050480a07c1c0d8281707026075bc0eb701d6b03ace0758c56b101c6f038d60719c363181c5f038bc2717455b787b6b116ce1ed8c0daf81b5e136ba26d3c4da707b4b0f6921ed0c4da107b41092de165ac24b385963032be125740cad81957032aa0654c24a78594b0928e1650c249f8593b0926e164cc14378386b050ce0e18c0c2f8185e030b60615c0c29818520509e0e12c1423838430507e0e0ec141b838330503e0e06c140b8381315ade2b5b846b581d6a03ace0759856b18ad62038de231ac0e3389c63038be0717455b787b6b116ce1ed8c4daf89b5e136ba1ed3c4da701b4b0f68626d0824b78596b092ce1658c24af8495d0b2b61656424ab849550b2a61654424a78194b0328e1650c249f8593b0926e164cc14378386b050ce0e18c142f8c85e050ba0a1701c2d83859050ae0a1541c298c852070a20e14014278184b0308e0e10c141f8383b0506e0e0cc140f8381b0502e0e04c0eb78ad6e11ad60759c4eb189d62138de1b1b8463581c6a038ce07198363186c62156de22dac45b38ab63136be26d740dad81b57c26aa26d4c4da789b4d136961ed244da3e0345136861ed0424b78596b092ce1658c24af8495d032b60655c24aa859530929e125342ca5859490928e125142ca1859410927e164ec249b85933050de0e1ac143383863050be0616c0c2b838530509e0a1341c25838490508e0a1141c21838410507e0e0ec141b838330503e0e06c140b83813 20 1048575 8 255 11 2047 19 524287
def cc_72_4 : Nat → List (Nat × Nat) := unpackCursorV4 0xd9a63d3169ccc65c6369c0063b916fb2c65abf6da58679b2a690ea48ab63848637f058748a86eb5d63dae5d6675736350c674af5d4555a3fb5a3708b3155b28a8b22f5b19d921405d0ad930575600057 0x1d6f01d6d08d6b08d6a01d6708d6601d6501c6f01c6e01c6d08c5f08c5e08c5d0ab6f08b6b08b670ab6309b5f01b5b01b5709b5309b4f0ab4d0ab4b0bb490ab479f34509b430ab410aa6f08a6b08a670aa6309a5f01a5b01a5709a5309a4f06a4d0aa4b0aa4706a4509a432f23f2523b12237032330496f0596b04967059630495f0195b01957059530494f0494d0594b05949049470494505943059410493f0593b04937059330492f0592b04927059230286f0386b02867038630285f0185b01857038530284f0284d0384b03849028470284503843038410283f0383b02837038330282f0382b02827038230281f0381b028170381301d6f0ad6e08d6b01d6709d6309d6209c6f0ac6e08c6b01c6a01c6701c6607c6307c6209c5f09c5e09c5d0ab6f07b6b08b6707b6307b5f09b5d01b5b01b579135507b5308b4f08b4d01b4b01b4909b4708b4507b4301b410aa6f08a6b08a670aa6309a5f01a5b01a5709a5309a4f06a4d09a4b09a4706a4509a4307a3f2423b0f23707a330496f0596b04967059630495f0195b01957059530494f0494d0594b05949049470494505943059410493f0593b04937059330492f0592b04927059230286f0386b02867038630285f0185b01857038530284f0284d0384b03849028470284503843038410283f0383b02837038330282f0382b02827038230281f0381b02817038130ad6f0ad6e0ad6d0ac6f08c6b08c670ac630ac5f01c5d0ac5b9d4590ac5701c550ac530ac5108b6b08b6a0bb6908b6708b660ab630ab6108b5708b5608b559534f0bb4b903470bb430aa6f08a6b08a670aa630aa5f06a5d0aa5b0aa5706a550aa535624f4c24b452473f2430ba3f2323b0d2370ba330496f0596b04967059630495f0495d0595b05959049570495505953059510494f0594b04947059430493f0593b04937059330492f0592b04927059230286f0286d0386b0286702865038630285f0285d0385b03859028570285503853038510284f0384b02847038430283f0383b02837038330282f0382b02827038230281f0381b028170381301d6f07d6b08d6a01d6707d6607d6301c6f01c6e07c6b08c6a07c6707c6607c6301c6207c5f07c5e07c5d07b6f07b6b07b6707b6307b5f01b5b07b5901b5707b5307b5107b4f01b4d07b4b07b4901b4701b4507b4307b4108a6f08a6b08a6708a6307a5f01a5b01a5707a5307a4f06a4d07a4b07a4706a4507a4307a3f07a3b07a3707a330496f0596b04967059630495f0195b01957059530494f0494d0594b05949049470494505943059410493f0593b04937059330492f0592b04927059230286f0386b02867038630285f0185b01857038530284f0284d0384b03849028470284503843038410283f0383b02837038330282f0382b02827038230281f0381b028170381307d6f08d6b07d6708d6308c6f08c6e0bc6d08c6708c6507c6308c6207c5f07c5b07c5707c5308b6708b6608b6507b5f9b35e07b5b01b5a07b5701b5607b5308b5207b4f0ab4e08b4d08a6f08a6b08a6708a635425f07a5b07a573d25307a4f0ba4b0ba4707a4307a3f06a3d08a3b08a3706a3507a330496f0596b04967059630495f0595b04957059530494f0594b04947059430493f0493d0593b05939049370493505933059310492f0592b04927059230286f0386b02867038630285f0385b02857038530284f0384b02847038430283f0283d0383b03839028370283503833038310282f0382b02827038230281f0381b028170381301d6f08d6b08d6a01d6708d6608d6301c6f01c6e07c6b07c6a08c6708c6608c6301c6208c5f08c5e08c5d08b6f07b6b08b6707b6307b5f09b5d01b5b01b578f35507b5309b4f09b4d01b4b01b4909b470ab4507b4301b4108a6f08a6b08a6708a6309a5f01a5b4b25901a5709a5309a5109a4f06a4d09a4b09a4706a4509a4307a3f2223b0c23707a330496f0596b04967059630495f0195b059590195705953059510494f0494d0594b05949049470494505943059410493f0593b04937059330492f0592b04927059230286f0386b02867038630285f0185b038590185703853038510284f0284d0384b03849028470284503843038410283f0383b02837038330282f0382b02827038230281f0381b028170381308d6f08d6e08d6d08c6f01c6d08c6b08c6908c6701c6508c639946108c5f08c5b08c5708c5308b6f08b6e0ab6d08b5f08b5e08b5b08b5908b5308b520bb519434f0bb4b8e3470bb4308a6f06a6d08a6b08a6706a6508a6308a5f08a5b08a5708a535224f4924b432473b2430ba3f2123b0b2370ba330496f0496d0596b05969049670496505963059610495f0595b04957059530494f0594b04947059430493f0593b04937059330492f0592b04927059230286f0286d0386b03869028670286503863038610285f0285d0385b0285702855038530284f0384b02847038430283f0383b02837038330282f0382b02827038230281f0381b028170381301d6f07d6e07d6b01d6707d6309d6207c6f07c6e07c6b01c6a01c6701c6607c6309c6207c5f07c5e07c5d07b6f07b6b07b6707b6307b5f01b5b07b5901b5707b5307b5107b4f01b4d07b4b07b4901b4701b4507b4307b410aa6f08a6b08a670aa6307a5f09a5d01a5b01a5707a5507a5307a4f06a4d07a4b07a4706a4507a4307a3f07a3b07a3707a330496f0596b04967059630495f0495d0195b0195704955059530494f0494d0594b05949049470494505943059410493f0593b04937059330492f0592b04927059230286f0386b02867038630285f0185b01857038530284f0284d0384b03849028470284503843038410283f0383b02837038330282f0382b02827038230281f0381b028170381307d6f08d6b07d670ad630ac6f0ac6d07c6b08c6a08c6708c660bc6507c5f07c5b07c5707c530ab6f0ab6e0ab6d07b5f9735e07b5b01b5a07b5701b5607b530ab5207b4f08b4e08b4d0aa6f08a6b08a670aa635025f07a5b07a573925307a4f0ba4b0ba4707a4307a3f06a3d0aa3b0aa3706a3507a330496f0596b04967059630495f0595b04957059530494f0594b04947059430493f0493d0593b05939049370493505933059310492f0592b04927059230286f0386b02867038630285f0385b02857038530284f0384b02847038430283f0283d0383b0a83a0383903838028370a836028350283403833038310282f0382b02827038230281f0381b028170381307e7f07e7e07e7d01d7f07d7b01d7707d7301d6f01d6d07d6b0ad6a07d6909d6801d6707d6601d6501d6407d6307d6107c7f07c7e07c7d07c7c07c7b08c7a07c7707c7607c7507c7407c730ac7201c6f01c6e01c6d01c6c07c6b08c6a07c6908c6807c6707c6601c6501c6407c630ac6207c6109c6007c5f07c5e07c5d07b7b07b7a07b7907b7708b7607b7307b7107b6708b6607b6501b5b01b5a07b5901b5701b5607b5307b5101b4701b4601b450aa7f08a7b08a770aa730aa6f06a6d0aa6b0aa6706a650aa6307a5f01a5b01a5707a5307a4f06a4d07a4b07a4706a4507a4307a3f07a3b07a3707a330497f0597b04977059730496f0496d0596b05969049670496505963059610495f0195b01957059530494f0494d0594b05949049470494505943059410493f0593b04937059330492f0592b04927059230287f0287d0387b0287702875038730286f0286d0386b03869028670286503863038610285f0185b01857038530284f0284d0384b03849028470284503843038410283f0383b038390283703833038310282f0382b02827038230281f0381b028170381307e7f07e7e07e7d01d7f07d7e01d7d01d7c07d7b07d7901d7701d7507d7308d7207d7109d7001d6f07d6b01d6707d6307c7f07c7e01c7d01c7c07c7b08c7a07c7908c7801c7701c7601c7501c7407c7308c7207c7109c7007c6f07c6e07c6d07c6c07c6b08c6a07c6707c6607c6507c6407c6308c6207c5f07c5e07c5d07b7f08b7e07b7d07b6f08b6e07b6b07b6907b6307b6207b6101b5b01b5a07b5901b5701b5607b5307b5101b4701b4601b4508a7f06a7d08a7b08a7706a7508a7308a6f08a6b08a6708a6307a5f01a5b01a5707a5307a4f06a4d07a4b07a4706a4507a4307a3f07a3b07a3707a330497f0497d0597b05979049770497505973059710496f0596b04967059630495f0195b01957059530494f0494d0594b05949049470494505943059410493f0593b04937059330492f0592b04927059230287f0287d0387b03879028770287503873038710286f0286d0386b0286702865038630285f0185b01857038530284f0284d0384b03849028470284503843038410283f0383b02837038330282f0382b02827038230281f0381b028170381301d6f09d6b01d6709d6307c6f0ac6e09c6b08c6a07c6708c6609c630ac6207c5f0bc5e0bc5d9536f07b6b9436707b6301b5b01b5a0bb5901b5701b5607b530bb5101b4701b4601b458726f7f26b712676826309a5f01a5b01a5709a5309a4f06a4d07a4b07a4706a4509a4307a3f2023b0a23707a330496f0596b04967059630495f0195b01957059530494f0494d0594b05949049470494505943059410493f0593b04937059330492f0592b04927059230286f0386b02867038630285f0185b01857038530284f0284d0384b03849028470284503843038410283f0383b02837038330282f0382b02827038230281f0381b028170381301d6f01d6b01d6701d630bc6f07c6b0bc6707c6301c5f01c5e0bc5d01c5701c5501c5301c5201b6f0ab6e01b6b01b6a01b6708b6601b6301b6201b5701b5601b5501b4f0bb4e01b4d8526f7d26b6e2676626301a5f01a5b01a5701a5307a4f0ba4b0ba4707a4301a3f01a3d01a3b01a3706a3501a330496f0596b04967059630195f0195b01957019530494f0594b04947059430193f0193d0193b05939019370493501933019310492f0592b04927059230286f0386b02867038630185f0185b01857018530284f0384b02847038430183f0183d0183b03839018370283501833018310282f0382b02827038230281f0381b028170381301d6f01d6e01d6b01d6701d630ad6201c6f01c6b01c6707c6301c5f01c5e09c5d01b6f07b6b07b6707b6301b5f01b5e07b5d07b4f01b4b01b4901b4701b4301b410aa6f08a6b08a670aa6301a5f01a5b01a5701a5309a4f09a4b09a4709a4307a3f07a3b07a3707a330496f0596b04967059630195f0195b01957019530494f0594b04947059430493f0593b04937059330492f0592b04927059230286f0386b02867038630185f0185e0185b0185701853018520284f0384b02847038430283f0383b02837038330282f0382b02827038230281f0381b028170381307e7f07e7e07e7d01d7f01d7e01d7b08d7a01d7908d7801d7701d7601d730ad7201d710ad7001d6f01d6e01d6d01d6c01d6b08d6a01d6908d6801d6701d6601d6501d6401d630ad6201d6109d6001c7f01c7b01c7701c7301c6f01c6d01c6b0ac6a01c699146801c6701c6601c6501c6401c6301c6101c5f01c5e01c5d07b7b07b7a07b7907b7708b7607b7307b7107b6708b6607b6501b5f01b5e07b5d01b4f01b4e01b4b01b4901b4301b4207b410aa7f08a7b08a770aa730aa6f06a6d0aa6b0aa6706a650aa6301a5f06a5d01a5b01a5701a5501a5301a4f01a4b01a4701a4307a3f07a3b07a3707a330497f0597b04977059730496f0496d0596b05969049670496505963059610195f0495d0195b01959019570195501953059510194f0194b01947019430493f0593b04937059330492f0592b04927059230287f0287d0387b0287702875038730286f0286d0386b03869028670286503863038610185f0185e0285d0285c0185b018590185701855018530185203851038500184f0184b01847018430283f0383b02837038330282f0382b02827038230281f0381b028170381301d6f01d6b08d6a01d6701d6601d6301c6f07c6b01c6701c6301c5f01c5e09c5d07b6f07b6b01b6707b6301b5f01b5e07b5d07b4f01b4b01b4901b4701b4301b4108a6f08a6b08a6708a6301a5f01a5b01a5701a5309a4f09a4b09a4709a4307a3f07a3b07a3707a330496f0596b04967059630195f0195b019590195701953059510494f0594b04947059430493f0593b04937059330492f0592b04927059230286f0386b02867038630185f0185e0185b0185901857018530185203851038500284f0384b02847038430283f0383b02837038330282f0382b02827038230281f0381b028170381307e7f07e7e07e7d01d7f01d7e01d7d01d7c01d7b08d7a01d7908d7801d7701d7601d7501d7401d7308d7201d710ad7001d6f01d6e01d6b08d6a01d6908d6801d6701d6601d6308d6201d610ad6001c7f01c7e01c7d01c7c01c7b01c7901c7701c7501c7308c7201c718f47001c6f01c6b01c6701c6301c5f01c5e01c5d07b7f08b7e07b7d07b6f08b6e07b6b07b6907b6307b6207b6101b5f01b5e07b5d01b4f01b4e01b4b01b4901b4301b4207b4108a7f06a7d08a7b08a7706a7508a7308a6f08a6b08a6708a6301a5f06a5d01a5b01a5701a5501a5301a4f01a4b01a4701a4307a3f07a3d07a3b07a370ca3507a330497f0497d0597b05979049770497505973059710496f0596b04967059630195f0495d0195b01959019570195501953059510194f0194b01947019430493f0493d0593b0493704935059330492f0592b04927059230287f0287d0387b03879028770287503873038710286f0286d0386b0286702865038630185f0185e0285d0285c0185b018590185701855018530185203851038500184f0184b01847018430283f0283d0383b0283702835038330282f0382b02827038230281f0381b028170381301d6f01d6e01d6b08d6a01d6701d6601d630ad6201c6f01c6b01c6701c6301c5f01c5e01c5d9036f07b6b8e36707b6301b5f01b5e8c35d01b4f01b4e01b4b01b4901b4301b420bb418326f7b26b6c2676426301a5f06a5d01a5b01a5701a5501a5301a4f01a4b01a4701a4307a3f1f23b0823707a330496f0596b04967059630195f0495d0195b01959019570195501953059510194f0194b01947019430493f0593b04937059330492f0592b04927059230286f0386b02867038630185f0185e0285d0285c0185b018590185701855018530185203851038500184f0184b01847018430283f0383b02837038330282f0382b02827038230281f0381b028170381301d6f01d6b01d6701d6307c6f07c6e07c6b08c6a07c6707c6607c6309c6201c5f01c5e07c5d07b6f07b6b07b6707b6301b5b01b5a01b5901b5701b5601b5307b5101b4701b4601b450da6f0fa6b0fa670da6301a5f01a5b01a5701a5307a4f06a4d07a4b07a4706a4507a4307a3f07a3b07a3707a330496f0596b04967059630195f0195b01957019530494f0494d0594b05949049470494505943059410493f0593b04937059330492f0592b04927059230286f0386b02867038630185f0185b01857018530284f0284d0384b03849028470284503843038410283f0383b02837038330282f0382b02827038230281f0381b028170381301d6f09d6b01d6709d630bc6f07c6b0bc6707c6307c5f0bc5d01c5b01c5a01c5701c560bc550bb6f0ab6e07b6b08b6a0bb6708b6607b630ab6207b5f8c35e0bb5d01b4f01b4e01b4d8126f7926b6a2676226309a5f01a5b01a5709a5307a4f0ba4b0ba4707a4307a3f06a3d0ba3b0ba3706a3507a330496f0596b04967059630495f0195b01957059530494f0594b04947059430493f0493d0593b0b93a0593905938049370b936049350493405933059310492f0592b04927059230286f0386b02867038630285f0185b01857038530284f0384b02847038430283f0283d0383b03839028370283503833038310282f0382b02827038230281f0381b028170381301d6f08d6b01d6709d630ac6f0ac6e08c6b01c6a01c6701c660ac630ac6206c5f06c5e01c5b01c5a01c5701c5606c5306c520ab6f07b6b08b6a08b6708b6607b6307b5f09b5e01b5b01b5707b5309b5209b4f09b4e09b4d06a6f06a6706a5f01a5706a4f06a4d06a4706a4506a3f06a370496f0596b04967059630495f0195b01957059530494f0494d0594b05949049470494505943059410493f0593b04937059330592b049270286f0386b02867038630285f0185b01857038530284f0284d0384b03849028470284503843038410283f0383b02837038330382b028270281f0381b028170381301d6f0ad6e08d6b01d6709d6309d6209c6f08c6b01c6a01c6701c6606c5f06c5e06c5d0ab6f08b6b08b670ab6309b5f01b5b01b5709b5309b4f09b4d09b4b07b4909b478a34509b4307b4106a6f06a6706a5f06a5d01a5706a5506a4f06a4d06a4706a4506a3f06a370496f0596b04967059630495f0195b01957059530494f0494d0594b05949049470494505943059410493f0593b04937059330592b049270286f0386b02867038630285f0185b01857038530284f0284d0384b03849028470284503843038410283f0383b02837038330382b028270281f0381b028170381308d6f07d6d08d6708d650ad6311c6f01c6d0cc6b09c690cc6701c6511c6309c610ac5f08c5b08c570ac5306b6f06b6e06b6d0ab5f0ab5e08b5b08b570ab530ab520cb4f0bb4b0cb470bb4306a6f06a6d06a6706a6506a5f06a5706a4f06a4706a3f06a3d06a3706a350496f0496d0596b05969049670496505963059610495f0595b04957059530494f0594b04947059430493f0593b04937059330592b049270286f0286d0386b03869028670286503863038610285f0385b02857038530284f0384b02847038430283f0383b02837038330382b028270281f0381b028170381301d7f08d7b01d7709d7301d6f01d6d06d6b09d6901d6701d6506d6306d6107c7f0ac7e08c7b08c7a07c7708c7609c730ac7206c6f06c6e06c6d06c6c06c6b06c6a09c6909c6806c6706c6607c6507c6406c6306c6206c6106c6007c5f0bc5e0bc5d0ab7f07b7b08b7707b7306b6f06b6d06b6b07b6906b670cb6506b6306b6101b5b01b5a0bb5901b5701b5607b530bb5101b4701b4601b4508a7a06a7706a7606a6706a6606a6506a5f01a5706a4f06a4d06a4706a4506a3f06a370497f0597b04977059730496f0496d0596b05969049670496505963059610495f0195b01957059530494f0494d0594b05949049470494505943059410493f0593b04937059330592b049270287f0387b02877038730286f0286d0386b03869028670286503863038610285f0185b01857038530284f0284d0384b03849028470284503843038410283f0383b02837038330382b028270281f0381b028170381301d6f01d6d01d6701d6501d6301c6f01c6d01c6b01c6901c6701c6501c6301c6101c5f01c5b01c5701c5306b6f06b6d07b6b07b6906b6706b6506b6306b610ab5f07b5b08b5707b5301b4f01b4b01b4701b4301a6f01a6d06a6706a6501a5f06a5701a4f01a4706a3f06a370496f0496d0596b05969049670496505963059610495f0595b04957059530194f0194b01947019430493f0593b04937059330592b049270286f0286d0386b03869028670286503863038610285f0385b02857038530184f0184b01847018430283f0383b02837038330382b028270281f0381b028170381301d7f01d7b01d7701d7301d6f01d6d01d6b01d6901d6701d6501d6301d610ac7f07c7b08c7707c7306c6f06c6d06c6b07c6906c670bc6506c6306c6101c5f01c5e0bc5d01c5701c5501c5301c5201b7f0ab7e01b7b01b7a01b7708b7601b7301b7201b6f06b6e01b6d06b6c01b6b01b6a01b6901b6801b6706b6601b658636401b6301b6201b6101b6001b5701b5601b5501b4f0bb4e01b4d08a7a06a7706a7606a6706a6606a6501a5f01a5706a4f06a4701a3f01a3d01a3706a350497f0597b04977059730496f0496d0596b05969049670496505963059610195f0195b01957019530494f0594b04947059430193f0193d0193b05939019370493501933019310592b049270287f0387b02877038730286f0286d0386b03869028670286503863038610185f0185b01857018530284f0384b02847038430183f0183d0183b03839018370283501833018310382b028270281f0381b028170381301d6f01d6b01d6701d6301c6f01c6b01c6a01c6701c6601c5f01c5e01c5b01c5a01c5701c5601c5301c520ab6f07b6b08b6707b6301b5f01b5b01b5701b530db4f09b4d06b4b06b4906b4706b4506b4306b4101a6f06a6701a5f01a5706a4f06a4d01a4701a4506a3f06a370496f0596b04967059630195f0195b01957019530494f0494d0594b05949049470494505943059410493f0593b04937059330592b049270286f0386b02867038630185f0185b01857018530284f0284d0384b03849028470284503843038410283f0383b02837038330382b028270281f0381b028170381301d7f01d7e01d7b08d7a01d7701d7601d730ad7201d6f01d6e01d6d01d6c01d6b06d6a01d698456801d6701d6601d6501d6401d6306d6201d6106d6001c7f01c7b01c7701c7301c6f01c6d01c6b01c6901c6701c6501c6301c6101c5f01c5e01c5d0ab7f07b7b08b7707b7306b6f06b6d06b6b07b6906b670cb6506b6306b6101b5f01b5e0db5d01b4f01b4e01b4b01b4901b4301b420bb4108a7a06a7706a7606a6706a6606a6501a5f01a5e06a5d06a5c01a5701a5501a5201a4f01a4706a3f06a370497f0597b04977059730496f0496d0596b05969049670496505963059610195f0495d0195b01959019570195501953059510194f0194b01947019430493f0593b04937059330592b049270287f0387b02877038730286f0286d0386b03869028670286503863038610185f0185e0285d0285c0185b018590185701855018530185203851038500184f0184b01847018430283f0383b02837038330382b028270281f0381b028170381307d6f07d6d08d6707d650ad6301c6f01c6d09c6b09c6901c6701c6506c6306c6101c5f08c5b01c5709c5306b6f06b6d01b6b01b6906b6706b6506b6301b610ab5f07b5b08b5707b5307b4f01b4b01b4706b4306a6f06a6d06a6706a6506a5f08a5a06a5706a5606a4f01a4706a3f06a370496f0496d0596b05969049670496505963059610495f0595b04957059530494f0194b01947059430493f0593b04937059330592b049270286f0286d0386b03869028670286503863038610285f0385b02857038530284f0184b01847038430283f0383b02837038330382b028270281f0381b028170381301d7f08d7b01d7709d7301d6f01d6d06d6b09d6901d6701d6506d6306d610ac7f07c7b08c7707c7306c6f06c6d06c6b07c6906c670bc6506c6306c6107c5f0bc5d01c5b01c5a01c5701c560bc550ab7f0ab7e0ab7d0ab7c07b7b08b7a08b7708b760bb7508b7407b730ab7206b6f06b6e06b6d06b6c06b6b06b6a07b6907b6806b6706b660bb658236406b6306b6206b6106b6007b5f0db5e0bb5d01b4f01b4e01b4d08a7a06a7706a7606a6706a6606a6506a5f01a5706a4f06a4706a3f06a3d06a3706a350497f0597b04977059730496f0496d0596b05969049670496505963059610495f0195b01957059530494f0594b04947059430493f0493d0593b0b93a0593905938049370b936049350493405933059310592b049270287f0387b02877038730286f0286d0386b03869028670286503863038610285f0185b01857038530284f0384b02847038430283f0283d0383b03839028370283503833038310382b028270281f0381b02817038130ac6f08c6b08c670ac6306c5f01c5d06c5b8945906c5701c5506c5306c510ab6f08b6b08b670ab6306b5f06b5d06b5b0bb5906b578835506b5306b518734f8534b833478134308a6a06a6706a6606a5706a5606a5506a4f06a4706a3f06a370496f0596b04967059630495f0495d0595b05959049570495505953059510494f0594b04947059430493f0593b04937059330592b049270286f0386b02867038630285f0285d0385b03859028570285503853038510284f0384b02847038430283f0383b02837038330382b028270281f0381b028170381301e7f08e7b01e7708e7307d7f08d7e08d7b08d7a07d7708d7608d7308d7207d6f0bd6e0bd6d08c7f07c7b08c7707c7301c6b01c6a0bc6901c6701c6607c630bc6101c5701c5601c5508b7e06a7609a6e01a6609a5e09a5c07a5607a5407a4e0ca460497f0597b04977059730496f0196b01967059630495f0495d0595b05959049570495505953059510494f0594b049470594305929049250287f0387b02877038730286f0186b01867038630285f0285d0385b03859028570285503853038510284f0384b028470384303829028250281f0381b0281703813 20 1048575 8 255 11 2047 20 1048575
def cc_72_5 : Nat → List (Nat × Nat) := unpackCursorV4 0x16f699df3c1da5abc6a06b377193cfc6f5e006f 0x7d6f09d6e07d6b07d6a07d6708d6607d6307d6201c6f01c6b01c6701c6301c5f01c5d01c5b01c5901c5701c5501c5301c5107b6f0ab6e07b6b07b6707b6307b6201b5f01b5e01b5d01b4f01b4b01b4a01b4701b4601b430aa6f08a6b08a670aa6307a5f06a5d07a5b07a5706a5507a5301a4f01a4b01a4701a4307a3f07a3b07a3707a330496f0596b04967059630495f0495d0595b05959049570495505953059510194f0194b01947019430493f0593b04937059330492f0592b04927059230286f0386b02867038630285f0285d0385b03859028570285503853038510184f0184b01847018430283f0383b02837038330282f0382b02827038230281f0381b028170381301d6f0ad6e01d6d01c6b08c6a01c6901c6701c6601c6301c6101c5701c5601c550ab6f07b6b08b6707b6301b5f01b5d01b5b0bb5901b57a735501b5301b5101b4f01b4b01b4701b430aa6f08a6b08a670aa6301a5f01a5d01a5b01a5706a5501a5301a4f01a4b01a4701a4307a3f2b23b1923707a330496f0596b04967059630195f0195d0195b05959019570495501953019510194f0194b01947019430493f0593b04937059330492f0592b04927059230286f0386b02867038630185f0185d0185b0185a03859038580185701856028550285401853018510184f0184b01847018430283f0383b02837038330282f0382b02827038230281f0381b028170381301d6f08d6b01d6708d6308c6f08c6e08c6b01c6a01c6701c6607c6307c6209c5f09c5e01c5b01c5a01c5701c5609c5309c5208b6f07b6b08b6a08b6708b6607b6307b5f09b5e01b5b01b5707b5309b5208b4f08b4e08b4d08a6f08a6b08a6708a6309a5f01a5b01a5709a5310a4f06a4d0ca4b0ca4706a4510a4307a3f0ca3b0ca3707a330496f0596b04967059630495f0195b01957059530494f0494d0594b05949049470494505943059410493f0593b04937059330492f0592b04927059230286f0386b02867038630285f0185b01857038530284f0284d0384b03849028470284503843038410283f0383b02837038330282f0382b02827038230281f0381b028170381301d6f08d6e01d6d01d6701d6508d6308d6201c6701c6601c6508c5f0ac5e08c5d08b6f08b6b08b6708b6309b5f01b5b01b5709b5308b4f08b4d08b4b0bb4908b47a534508b4308b4108a6f08a6b08a6708a6309a5f01a5b01a5709a5308a4f06a4d08a4b08a4706a4508a433323f2923b17237052330496f0596b04967059630495f0195b01957059530494f0494d0594b05949049470494505943059410493f0593b04937059330492f0592b04927059230286f0386b02867038630285f0185b01857038530284f0284d0384b03849028470284503843038410283f0383b02837038330282f0382b02827038230281f0381b028170381307d6f08d6d07d6b07d6907d6707d6507d6308d6101c6f01c6d01c6b01c6901c6701c6501c6301c6101c5f01c5b01c5701c5301b6701b6601b6507b5f07b5b07b5a07b5708b5607b5301b4f01b4b01b4a01b4701b4601b4307a6f06a6d07a6b07a6706a6507a6308a5f08a5b08a5708a5301a4f01a4b01a4701a4307a3f07a3b07a3707a330496f0496d0596b05969049670496505963059610495f0595b04957059530194f0194b01947019430493f0593b04937059330492f0592b04927059230286f0286d0386b03869028670286503863038610285f0385b02857038530184f0184b01847018430283f0383b038390283703833038310282f0382b02827038230281f0381b028170381301d6f01d6e08d6d01c6f01c6e01c6d01c5f01c5e01c5b01c5901c5308c5201c5101b6fa336d01b6b01b6901b6701b6501b630bb6108b5f07b5b08b5707b5301b4f01b4b01b4701b4301a6f06a6d01a6b01a6701a6501a6308a5f08a5b08a5708a5301a4f01a4b01a4701a4307a3f2723b1523707a330196f0496d0196b01969019670196501963059610495f0595b04957059530194f0194b01947019430493f0593b04937059330492f0592b04927059230186f0286d0186b01869018670186501863038610285f0385b02857038530184f0184b01847018430283f0383b02837038330282f0382b02827038230281f0381b028170381301d7e07d7a08d760ad7208d6e01d6a01d6609d620ac7e06c7a07c7606c7209c6e01c6a01c6606c620ab7e0ab7209b6e09b6209b5e09b5d06b4e06b4d06b4c09b4506b4206b4106b400ca5a0ca5806a5606a5506a5406a4606a4506a3d0ca3a06a3606a3506a340495d0595904955059510494d0594904945059410493d0493505929059210285d0385902855038510284d0384902845038410283d0283501d7e07d7a08d760ad7208d6e01d6a01d6609d620ac7e0ac7209c6e09c6209c5e09c5d0cb560cb540cb460cb440aa7e07a7609a6e01a6606a5e06a5c06a4e06a4c09a4609a440495d0595904955059510494d0494505939059290592804925049240285d0385902855038510284d02845038290282501d6f08d6b01d6709d6301c6f01c6e07c6b07c6a08c6708c660ac6301c6208c5f08c5e01c5b01c5a01c5701c5609c5308c520ab6f0ab6e07b6b08b6707b630ab6207b5f09b5e01b5b01b5707b5309b5209b4f09b4e09b4d0aa6f08a6b08a670aa6309a5f01a5b01a5709a53a124f06a4d0ca4b0ca4706a45a024307a3f3123d0ca3b0ca371323507a330496f0596b04967059630495f0195b01957059530494f0494d0594b05949049470494505943059410493f0493d0593b0493704935059330492f0592b04927059230286f0386b02867038630285f0185b01857038530284f0284d0384b03849028470284503843038410283f0283d0383b0283702835038330282f0382b02827038230281f0381b0281703813 17 131071 7 127 11 2047 20 1048575
def cur_72 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (cc_72_5 (Nat.sub p 160)) (cc_72_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_72_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_72_2 (Nat.sub p 64)) (cc_72_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_72_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def f_72 : Nat → Nat × Nat := unpackForestF 0xa76aa0317e95a280c5ba36da0315e8127d02439f68a0314e762c80b5f9b6bc02d6e663080b57976bc02d4e51b7ca3670169e02d2e46344736f8f8e11cd9c05a3c635e0168714d16062cc0b558169f0cd9205a5c25688168f04d9205a180a5f768befc911da2dbe26c768aef4911da29bc345764bcec918052dba3456a8c2d4db5a9a7b7d706f6f8d4d2db6b8353476b6f8d4d0c052bacc5f67488b316d95362cc5763488b314d81aab0345594bcb516d6a29ae34e5a6b4b4d59652300a53578c89edbd55aa27b6b538f89ed9d45aa27b634f68a0293d35322446f4aae0949f12233a4246014968d5a109b7a2570426ce84d740523a0264368de7c910da359e27c368ce74910da319bb6a376cc6c91805219a3542ead664d38c22a183542eac65cd78051f962641cade5495072b59427c1cace4c95072b1925691c8de455c472338e45f1c8ae3adbc75aa8e25e01476351a022b78c45808ad62d1c022b389c58136a81158c46b7044520ead21d14821b786571086ce10d7c2628043570146e0c9500ab58225402ac60497805198003f 8 11
set_option maxHeartbeats 0 in
theorem rc_72 : dagCheckRootsV4 fullMask g_72 ep_72 168 bds_72 (dagTraceF fullMask rootStock 11 f_72) (cur_72 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_72_0 : treeBlockF 0 32 (dagCheckNodeV4 fullMask g_72 ep_72 bds_72 168 (dagTraceF fullMask rootStock 11 f_72) cur_72) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_72_1 : treeBlockF 32 64 (dagCheckNodeV4 fullMask g_72 ep_72 bds_72 168 (dagTraceF fullMask rootStock 11 f_72) cur_72) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_72_2 : treeBlockF 64 96 (dagCheckNodeV4 fullMask g_72 ep_72 bds_72 168 (dagTraceF fullMask rootStock 11 f_72) cur_72) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_72_3 : treeBlockF 96 128 (dagCheckNodeV4 fullMask g_72 ep_72 bds_72 168 (dagTraceF fullMask rootStock 11 f_72) cur_72) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_72_4 : treeBlockF 128 160 (dagCheckNodeV4 fullMask g_72 ep_72 bds_72 168 (dagTraceF fullMask rootStock 11 f_72) cur_72) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_72_5 : treeBlockF 160 168 (dagCheckNodeV4 fullMask g_72 ep_72 bds_72 168 (dagTraceF fullMask rootStock 11 f_72) cur_72) = true := by decide +kernel
theorem nj_72_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 fullMask g_72 ep_72 bds_72 168 (dagTraceF fullMask rootStock 11 f_72) cur_72) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_72_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_72_1 h1 h2)
theorem nj_72_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeV4 fullMask g_72 ep_72 bds_72 168 (dagTraceF fullMask rootStock 11 f_72) cur_72) i = true := block_join nj_72_1 (fun _ h1 h2 => treeBlockF_at nb_72_2 h1 h2)
theorem nj_72_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeV4 fullMask g_72 ep_72 bds_72 168 (dagTraceF fullMask rootStock 11 f_72) cur_72) i = true := block_join nj_72_2 (fun _ h1 h2 => treeBlockF_at nb_72_3 h1 h2)
theorem nj_72_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeV4 fullMask g_72 ep_72 bds_72 168 (dagTraceF fullMask rootStock 11 f_72) cur_72) i = true := block_join nj_72_3 (fun _ h1 h2 => treeBlockF_at nb_72_4 h1 h2)
theorem nj_72_5 : ∀ i, 0 ≤ i → i < 168 → (dagCheckNodeV4 fullMask g_72 ep_72 bds_72 168 (dagTraceF fullMask rootStock 11 f_72) cur_72) i = true := block_join nj_72_4 (fun _ h1 h2 => treeBlockF_at nb_72_5 h1 h2)
theorem nc_72 : ∀ i, 0 ≤ i → i < 168 → (dagCheckNodeV4 fullMask g_72 ep_72 bds_72 168 (dagTraceF fullMask rootStock 11 f_72) cur_72) i = true := nj_72_5
theorem lb_72 : LowerBin fullMask rootStock g_72 12 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_72 kn_72 sub_72 gl_72 rc_72 nc_72

def wg : List Gate := [⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [1, 8]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.and, [3, 9]⟩, ⟨GateOp.or, [3, 10]⟩, ⟨GateOp.or, [7, 11]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.and, [4, 15]⟩, ⟨GateOp.and, [13, 14]⟩, ⟨GateOp.or, [16, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276677288 * 2 ^ 32 + 3974160512) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276677288 * 2 ^ 32 + 3974160512)) (13 - 1) := by
  rw [show canon fullMask (4276677288 * 2 ^ 32 + 3974160512) = g_72 by decide]
  exact lb_72

end PEqualNP.Outside.L_meta_48009

theorem PEqualNP.Outside.L_meta_48009 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677288 * 2 ^ 32 + 3974160512) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677288 * 2 ^ 32 + 3974160512) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_48009.table2_from_lowerBin (4276677288 * 2 ^ 32 + 3974160512) 13 PEqualNP.Outside.L_meta_48009.root_lb PEqualNP.Outside.L_meta_48009.wg 18 rfl PEqualNP.Outside.L_meta_48009.wfits PEqualNP.Outside.L_meta_48009.weval
