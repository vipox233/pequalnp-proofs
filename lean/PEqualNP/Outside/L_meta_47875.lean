import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_47875

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

def dagLocalF (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  let (fuel, ws, _) := state
  Bool.rec
    (Bool.rec true
      (knownClosesF bounds state)
      (dagPartF ws goal (Nat.xor mask goal)))
    true (Nat.blt (Nat.add fuel 1) (lenN ws))

theorem dagLocalF_eq {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    dagLocalF mask goal bounds state = dagLocal mask goal bounds state := by
  obtain ⟨fuel, ws, hist⟩ := state
  unfold dagLocalF dagLocal; dsimp only
  rw [lenN_eq, dagPartF_eq, knownClosesF_eq hgoals]
  cases Nat.blt (fuel + 1) ws.length <;> cases dagPart ws goal (mask ^^^ goal) <;> rfl

def dagRefF (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (parent token : Nat)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  match links parent token with
  | none => false
  | some dest =>
    Bool.rec false
      (match states dest with
       | none => false
       | some saved => Bool.rec false (eqListN saved.2.1 state.2.1) (Nat.beq saved.1 state.1))
      (Nat.blt dest count)

theorem dagRefF_eq (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (parent token : Nat)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    dagRefF count states links parent token state = dagRef count states links parent token state := by
  unfold dagRefF dagRef
  cases links parent token with
  | none => rfl
  | some dest =>
    dsimp only
    cases Nat.blt dest count
    · rfl
    · dsimp only
      cases states dest with
      | none => rfl
      | some saved =>
        dsimp only
        rw [eqListN_eq]; cases Nat.beq saved.1 state.1 <;> rfl

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

def dagCheckChildrenF (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  let (fuel, ws, hist) := state
  let n := lenN ws
  Bool.rec
    (Bool.rec
      (Bool.rec false
        (treeBlockF 0 n (fun a =>
          let x := getDN ws a
          treeBlockF (Nat.add a 1) n (fun b =>
            let y := getDN ws b
            treeBlockF 0 4 (fun op =>
              forceW (binOpF mask op x y) (fun z =>
                Bool.rec
                  (Bool.rec
                    (treeBlockF 0 4 (fun keep =>
                      let keepA := Nat.beq (Nat.land keep 1) 1
                      let keepB := Nat.beq (Nat.land (Nat.shiftRight keep 1) 1) 1
                      let newLen := Nat.add (Nat.add (Nat.sub n 1) (Bool.rec 0 1 keepA)) (Bool.rec 0 1 keepB)
                      Bool.rec
                        (forceWs (insertSortedF z (dropValF (Bool.rec true false keepA) x (dropValF (Bool.rec true false keepB) y ws))) (fun ws' =>
                          let ch := (Nat.sub fuel 1, ws', (z, x, y) :: hist)
                          let tok := Nat.add (Nat.shiftLeft (Nat.add (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2) op) 2) keep
                          Bool.rec (dagLocalF mask goal bounds ch) true (ref tok ch)))
                        true (Nat.blt fuel newLen)))
                    true (memN z ws))
                  true (Nat.beq z 0))))))
        (Nat.blt n 17))
      true (Nat.beq fuel 0))
    false (memN goal ws)

theorem makeTokenF_eq (a b op keep : Nat) :
    Nat.add (Nat.shiftLeft (Nat.add (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2) op) 2) keep =
    makeToken a b op keep := by
  unfold makeToken
  change ((((a <<< 4) + b) <<< 2) + op) <<< 2 + keep = _
  simp only [Nat.shiftLeft_eq]

theorem dagCheckChildrenF_eq {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    dagCheckChildrenF mask goal bounds ref state = dagCheckChildren mask goal bounds ref state := by
  obtain ⟨fuel, ws, hist⟩ := state
  unfold dagCheckChildrenF dagCheckChildren; dsimp only
  simp only [lenN_eq, memN_eq, treeBlockF_eq]
  cases ws.contains goal
  · cases Nat.beq fuel 0
    · cases Nat.blt ws.length 17
      · rfl
      · dsimp only
        simp only [Bool.not_false, Bool.true_and, Bool.false_or]
        congr 1; funext a
        simp only [getDN_eq]
        congr 1; funext b
        congr 1; funext op
        simp only [binOpF_eq, forceW_eq]
        cases Nat.beq (binOp mask op (ws.getD a 0) (ws.getD b 0)) 0
        · cases ws.contains (binOp mask op (ws.getD a 0) (ws.getD b 0))
          · dsimp only; simp only [Bool.false_or]
            congr 1; funext keep
            simp only [insertSortedF_eq, dropValF_eq, forceWs_eq, makeTokenF_eq, dagLocalF_eq hgoals]
            cases Nat.beq (keep &&& 1) 1 <;> cases Nat.beq ((keep >>> 1) &&& 1) 1
            all_goals dsimp only
            all_goals simp only [Bool.false_eq_true, ite_true, ite_false, Bool.not_true, Bool.not_false]
            all_goals cases Nat.blt fuel _
            all_goals try rfl
            all_goals cases ref (makeToken a b op keep) _ <;> cases dagLocal mask goal bounds _ <;> rfl
          · rfl
        · rfl
    · rfl
  · rfl

def dagCheckNodeF (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some st => dagCheckChildrenF mask goal bounds (dagRefF count states links (Nat.add i 1)) st

theorem dagCheckNodeF_eq {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (links : Nat → Nat → Option Nat) (i : Nat) :
    dagCheckNodeF mask goal bounds count states links i = dagCheckNode mask goal bounds count states links i := by
  unfold dagCheckNodeF dagCheckNode
  cases states i with
  | none => rfl
  | some st =>
    have href : dagRefF count states links (Nat.add i 1) = dagRef count states links (i + 1) := by
      funext tok s; exact dagRefF_eq count states links (i + 1) tok s
    rw [href]; exact dagCheckChildrenF_eq hgoals _ st

def dagCheckRootsF (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (stock : List Nat) (fuel : Nat) : Bool :=
  treeBlockF 0 (Nat.shiftLeft 1 (lenN stock)) (fun token =>
    forceWs (subsetWordsF stock token) (fun ws =>
      let st := (fuel, ws, [])
      Bool.rec (dagLocalF mask goal bounds st) true (ref token st)))

theorem dagCheckRootsF_eq {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool)
    (stock : List Nat) (fuel : Nat) :
    dagCheckRootsF mask goal bounds ref stock fuel = dagCheckRoots mask goal bounds ref stock fuel := by
  unfold dagCheckRootsF dagCheckRoots
  have hpow : Nat.shiftLeft 1 (lenN stock) = 2 ^ stock.length := by
    rw [lenN_eq]; change 1 <<< stock.length = _; rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [hpow, treeBlockF_eq]
  congr 1; funext tok
  simp only [subsetWordsF_eq, forceWs_eq, dagLocalF_eq hgoals]
  cases ref tok (fuel, subsetWords stock tok, []) <;> cases dagLocal mask goal bounds (fuel, subsetWords stock tok, []) <;> rfl

def unpackF (data width idx : Nat) : Nat :=
  Nat.land (Nat.shiftRight data (Nat.mul idx width)) (Nat.sub (Nat.shiftLeft 1 width) 1)

def unpackForestF (data pBits tBits : Nat) : Nat → Nat × Nat := fun i =>
  let w := Nat.add pBits tBits
  let code := unpackF data w i
  (Nat.shiftRight code tBits, Nat.land code (Nat.sub (Nat.shiftLeft 1 tBits) 1))

def unpackLinksF (index data idxW sizeBits tokBits destBits steps : Nat) : Nat → Nat → Option Nat :=
  fun parent tok =>
    let entry := unpackF index idxW parent
    let sz := Nat.land entry (Nat.sub (Nat.shiftLeft 1 sizeBits) 1)
    let off := Nat.shiftRight entry sizeBits
    let w := Nat.add tokBits destBits
    (Nat.rec (motive := fun _ => Nat → Nat → Option Nat) (fun _ _ => none)
      (fun _ next lo hi =>
        Bool.rec none
          (let mid := Nat.shiftRight (Nat.add lo hi) 1
           let code := unpackF data w mid
           let key := Nat.land code (Nat.sub (Nat.shiftLeft 1 tokBits) 1)
           Bool.rec
             (Bool.rec (next (Nat.add mid 1) hi) (next lo mid) (Nat.blt tok key))
             (some (Nat.shiftRight code tokBits)) (Nat.beq tok key))
          (Nat.blt lo hi)) steps) off (Nat.add off sz)

theorem lowerDagF {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {links : Nat → Nat → Option Nat}
    (hgm : Masked mask goal) (hgnz : goal ≠ 0)
    (hcs : stock.all (fun w => Nat.beq (canon mask w) w) = true)
    (snd : stock.Nodup)
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hroots : dagCheckRootsF mask goal bounds
      (dagRefF count (dagTraceF mask stock fuel forest) links 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeF mask goal bounds count
      (dagTraceF mask stock fuel forest) links i = true) :
    LowerBin mask stock goal (fuel + 1) := by
  have htr : dagTraceF mask stock fuel forest = dagTrace mask stock fuel forest := by
    funext i; exact dagTraceF_eq mask stock fuel forest i
  rw [htr] at hroots hnodes
  have hr : dagCheckRoots mask goal bounds (dagRef count (dagTrace mask stock fuel forest) links 0) stock fuel = true := by
    have href : dagRefF count (dagTrace mask stock fuel forest) links 0 = dagRef count (dagTrace mask stock fuel forest) links 0 := by
      funext t s; exact dagRefF_eq count _ links 0 t s
    rw [href, dagCheckRootsF_eq hgoals] at hroots; exact hroots
  have hn : ∀ i, 0 ≤ i → i < count → dagCheckNode mask goal bounds count (dagTrace mask stock fuel forest) links i = true := by
    intro i h1 h2
    have h := hnodes i h1 h2
    rwa [dagCheckNodeF_eq hgoals] at h
  exact lowerDag hgm hgnz hcs snd hknown hsub hr hn

theorem treeBlockF_at {lo hi : Nat} {f : Nat → Bool} (h : treeBlockF lo hi f = true) :
    ∀ {i : Nat}, lo ≤ i → i < hi → f i = true := by
  rw [treeBlockF_eq] at h; exact treeBlock_at h

def m_0 : Nat := 0x3000300030003000
def s_0 : List Nat := [0x1000100010001000, 0x300000003000, 0x30003000]
def g_0 : Nat := 0x100010003000
def bds_0 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_0 : KnownBin bds_0 := by intro b hb; simp [bds_0] at hb
theorem sub_0 : ∀ b ∈ bds_0, m_0 &&& b.1 = b.1 := by intro b hb; simp [bds_0] at hb
theorem gl_0 : ∀ b ∈ bds_0, canon b.1 g_0 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_0] at hb
def f_0 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_0 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_0 : dagCheckRootsF m_0 g_0 bds_0 (dagRefF 1 (dagTraceF m_0 s_0 3 f_0) l_0 0) s_0 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_0_0 : treeBlockF 0 1 (dagCheckNodeF m_0 g_0 bds_0 1 (dagTraceF m_0 s_0 3 f_0) l_0) = true := by decide +kernel
theorem nc_0 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_0 g_0 bds_0 1 (dagTraceF m_0 s_0 3 f_0) l_0) i = true := fun _ h1 h2 => treeBlockF_at nb_0_0 h1 h2
theorem lb_0 : LowerBin m_0 s_0 g_0 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_0 sub_0 gl_0 rc_0 nc_0

def m_1 : Nat := 0x5050000050500000
def s_1 : List Nat := [0x1010000010100000, 0x50000000500000, 0x50500000]
def g_1 : Nat := 0x10000010500000
def bds_1 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_1 : KnownBin bds_1 := by intro b hb; simp [bds_1] at hb
theorem sub_1 : ∀ b ∈ bds_1, m_1 &&& b.1 = b.1 := by intro b hb; simp [bds_1] at hb
theorem gl_1 : ∀ b ∈ bds_1, canon b.1 g_1 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_1] at hb
def f_1 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_1 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_1 : dagCheckRootsF m_1 g_1 bds_1 (dagRefF 1 (dagTraceF m_1 s_1 3 f_1) l_1 0) s_1 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_1_0 : treeBlockF 0 1 (dagCheckNodeF m_1 g_1 bds_1 1 (dagTraceF m_1 s_1 3 f_1) l_1) = true := by decide +kernel
theorem nc_1 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_1 g_1 bds_1 1 (dagTraceF m_1 s_1 3 f_1) l_1) i = true := fun _ h1 h2 => treeBlockF_at nb_1_0 h1 h2
theorem lb_1 : LowerBin m_1 s_1 g_1 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1 sub_1 gl_1 rc_1 nc_1

def m_2 : Nat := 0xaa000000aa00
def s_2 : List Nat := [0x220000002200, 0xa0000000a00, 0xaa00]
def g_2 : Nat := 0x20000002a00
def bds_2 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_2 : KnownBin bds_2 := by intro b hb; simp [bds_2] at hb
theorem sub_2 : ∀ b ∈ bds_2, m_2 &&& b.1 = b.1 := by intro b hb; simp [bds_2] at hb
theorem gl_2 : ∀ b ∈ bds_2, canon b.1 g_2 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_2] at hb
def f_2 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_2 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_2 : dagCheckRootsF m_2 g_2 bds_2 (dagRefF 1 (dagTraceF m_2 s_2 3 f_2) l_2 0) s_2 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_2_0 : treeBlockF 0 1 (dagCheckNodeF m_2 g_2 bds_2 1 (dagTraceF m_2 s_2 3 f_2) l_2) = true := by decide +kernel
theorem nc_2 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_2 g_2 bds_2 1 (dagTraceF m_2 s_2 3 f_2) l_2) i = true := fun _ h1 h2 => treeBlockF_at nb_2_0 h1 h2
theorem lb_2 : LowerBin m_2 s_2 g_2 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2 sub_2 gl_2 rc_2 nc_2

def m_3 : Nat := 0xaa000000aa
def s_3 : List Nat := [0x2200000022, 0xa0000000a, 0xaa]
def g_3 : Nat := 0x20000002a
def bds_3 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_3 : KnownBin bds_3 := by intro b hb; simp [bds_3] at hb
theorem sub_3 : ∀ b ∈ bds_3, m_3 &&& b.1 = b.1 := by intro b hb; simp [bds_3] at hb
theorem gl_3 : ∀ b ∈ bds_3, canon b.1 g_3 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_3] at hb
def f_3 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_3 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_3 : dagCheckRootsF m_3 g_3 bds_3 (dagRefF 1 (dagTraceF m_3 s_3 3 f_3) l_3 0) s_3 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_3_0 : treeBlockF 0 1 (dagCheckNodeF m_3 g_3 bds_3 1 (dagTraceF m_3 s_3 3 f_3) l_3) = true := by decide +kernel
theorem nc_3 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_3 g_3 bds_3 1 (dagTraceF m_3 s_3 3 f_3) l_3) i = true := fun _ h1 h2 => treeBlockF_at nb_3_0 h1 h2
theorem lb_3 : LowerBin m_3 s_3 g_3 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_3 sub_3 gl_3 rc_3 nc_3

def m_4 : Nat := 0x4444444400000000
def s_4 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_4 : Nat := 0x4044400000000
def bds_4 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_4 : KnownBin bds_4 := by intro b hb; simp [bds_4] at hb
theorem sub_4 : ∀ b ∈ bds_4, m_4 &&& b.1 = b.1 := by intro b hb; simp [bds_4] at hb
theorem gl_4 : ∀ b ∈ bds_4, canon b.1 g_4 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_4] at hb
def f_4 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_4 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_4 : dagCheckRootsF m_4 g_4 bds_4 (dagRefF 1 (dagTraceF m_4 s_4 3 f_4) l_4 0) s_4 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_4_0 : treeBlockF 0 1 (dagCheckNodeF m_4 g_4 bds_4 1 (dagTraceF m_4 s_4 3 f_4) l_4) = true := by decide +kernel
theorem nc_4 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_4 g_4 bds_4 1 (dagTraceF m_4 s_4 3 f_4) l_4) i = true := fun _ h1 h2 => treeBlockF_at nb_4_0 h1 h2
theorem lb_4 : LowerBin m_4 s_4 g_4 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_4 sub_4 gl_4 rc_4 nc_4

def m_5 : Nat := 0x5050505000000000
def s_5 : List Nat := [0x1010101000000000, 0x50005000000000, 0x505000000000]
def g_5 : Nat := 0x10105000000000
def bds_5 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_5 : KnownBin bds_5 := by intro b hb; simp [bds_5] at hb
theorem sub_5 : ∀ b ∈ bds_5, m_5 &&& b.1 = b.1 := by intro b hb; simp [bds_5] at hb
theorem gl_5 : ∀ b ∈ bds_5, canon b.1 g_5 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_5] at hb
def f_5 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_5 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_5 : dagCheckRootsF m_5 g_5 bds_5 (dagRefF 1 (dagTraceF m_5 s_5 3 f_5) l_5 0) s_5 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_5_0 : treeBlockF 0 1 (dagCheckNodeF m_5 g_5 bds_5 1 (dagTraceF m_5 s_5 3 f_5) l_5) = true := by decide +kernel
theorem nc_5 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_5 g_5 bds_5 1 (dagTraceF m_5 s_5 3 f_5) l_5) i = true := fun _ h1 h2 => treeBlockF_at nb_5_0 h1 h2
theorem lb_5 : LowerBin m_5 s_5 g_5 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_5 sub_5 gl_5 rc_5 nc_5

def m_6 : Nat := 0x5500550000000000
def s_6 : List Nat := [0x1100110000000000, 0x500050000000000, 0x550000000000]
def g_6 : Nat := 0x100150000000000
def bds_6 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_6 : KnownBin bds_6 := by intro b hb; simp [bds_6] at hb
theorem sub_6 : ∀ b ∈ bds_6, m_6 &&& b.1 = b.1 := by intro b hb; simp [bds_6] at hb
theorem gl_6 : ∀ b ∈ bds_6, canon b.1 g_6 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_6] at hb
def f_6 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_6 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_6 : dagCheckRootsF m_6 g_6 bds_6 (dagRefF 1 (dagTraceF m_6 s_6 3 f_6) l_6 0) s_6 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_6_0 : treeBlockF 0 1 (dagCheckNodeF m_6 g_6 bds_6 1 (dagTraceF m_6 s_6 3 f_6) l_6) = true := by decide +kernel
theorem nc_6 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_6 g_6 bds_6 1 (dagTraceF m_6 s_6 3 f_6) l_6) i = true := fun _ h1 h2 => treeBlockF_at nb_6_0 h1 h2
theorem lb_6 : LowerBin m_6 s_6 g_6 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_6 sub_6 gl_6 rc_6 nc_6

def m_7 : Nat := 0xaa00aa
def s_7 : List Nat := [0x220022, 0xa000a, 0xaa]
def g_7 : Nat := 0x2002a
def bds_7 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_7 : KnownBin bds_7 := by intro b hb; simp [bds_7] at hb
theorem sub_7 : ∀ b ∈ bds_7, m_7 &&& b.1 = b.1 := by intro b hb; simp [bds_7] at hb
theorem gl_7 : ∀ b ∈ bds_7, canon b.1 g_7 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_7] at hb
def f_7 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_7 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_7 : dagCheckRootsF m_7 g_7 bds_7 (dagRefF 1 (dagTraceF m_7 s_7 3 f_7) l_7 0) s_7 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_7_0 : treeBlockF 0 1 (dagCheckNodeF m_7 g_7 bds_7 1 (dagTraceF m_7 s_7 3 f_7) l_7) = true := by decide +kernel
theorem nc_7 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_7 g_7 bds_7 1 (dagTraceF m_7 s_7 3 f_7) l_7) i = true := fun _ h1 h2 => treeBlockF_at nb_7_0 h1 h2
theorem lb_7 : LowerBin m_7 s_7 g_7 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_7 sub_7 gl_7 rc_7 nc_7

def m_8 : Nat := 0x3300330000000000
def s_8 : List Nat := [0x1100110000000000, 0x300030000000000, 0x330000000000]
def g_8 : Nat := 0x100130000000000
def bds_8 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_8 : KnownBin bds_8 := by intro b hb; simp [bds_8] at hb
theorem sub_8 : ∀ b ∈ bds_8, m_8 &&& b.1 = b.1 := by intro b hb; simp [bds_8] at hb
theorem gl_8 : ∀ b ∈ bds_8, canon b.1 g_8 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_8] at hb
def f_8 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_8 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_8 : dagCheckRootsF m_8 g_8 bds_8 (dagRefF 1 (dagTraceF m_8 s_8 3 f_8) l_8 0) s_8 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_8_0 : treeBlockF 0 1 (dagCheckNodeF m_8 g_8 bds_8 1 (dagTraceF m_8 s_8 3 f_8) l_8) = true := by decide +kernel
theorem nc_8 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_8 g_8 bds_8 1 (dagTraceF m_8 s_8 3 f_8) l_8) i = true := fun _ h1 h2 => treeBlockF_at nb_8_0 h1 h2
theorem lb_8 : LowerBin m_8 s_8 g_8 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_8 sub_8 gl_8 rc_8 nc_8

def m_9 : Nat := 0xf000f0000000000
def s_9 : List Nat := [0x500050000000000, 0x300030000000000, 0xf0000000000]
def g_9 : Nat := 0x100070000000000
def bds_9 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_9 : KnownBin bds_9 := by intro b hb; simp [bds_9] at hb
theorem sub_9 : ∀ b ∈ bds_9, m_9 &&& b.1 = b.1 := by intro b hb; simp [bds_9] at hb
theorem gl_9 : ∀ b ∈ bds_9, canon b.1 g_9 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_9] at hb
def f_9 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_9 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_9 : dagCheckRootsF m_9 g_9 bds_9 (dagRefF 1 (dagTraceF m_9 s_9 3 f_9) l_9 0) s_9 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_9_0 : treeBlockF 0 1 (dagCheckNodeF m_9 g_9 bds_9 1 (dagTraceF m_9 s_9 3 f_9) l_9) = true := by decide +kernel
theorem nc_9 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_9 g_9 bds_9 1 (dagTraceF m_9 s_9 3 f_9) l_9) i = true := fun _ h1 h2 => treeBlockF_at nb_9_0 h1 h2
theorem lb_9 : LowerBin m_9 s_9 g_9 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_9 sub_9 gl_9 rc_9 nc_9

def m_10 : Nat := 0x5555000000000000
def s_10 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_10 : Nat := 0x115000000000000
def bds_10 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_10 : KnownBin bds_10 := by intro b hb; simp [bds_10] at hb
theorem sub_10 : ∀ b ∈ bds_10, m_10 &&& b.1 = b.1 := by intro b hb; simp [bds_10] at hb
theorem gl_10 : ∀ b ∈ bds_10, canon b.1 g_10 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_10] at hb
def f_10 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_10 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_10 : dagCheckRootsF m_10 g_10 bds_10 (dagRefF 1 (dagTraceF m_10 s_10 3 f_10) l_10 0) s_10 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_10_0 : treeBlockF 0 1 (dagCheckNodeF m_10 g_10 bds_10 1 (dagTraceF m_10 s_10 3 f_10) l_10) = true := by decide +kernel
theorem nc_10 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_10 g_10 bds_10 1 (dagTraceF m_10 s_10 3 f_10) l_10) i = true := fun _ h1 h2 => treeBlockF_at nb_10_0 h1 h2
theorem lb_10 : LowerBin m_10 s_10 g_10 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_10 sub_10 gl_10 rc_10 nc_10

def m_11 : Nat := 0x3333000000000000
def s_11 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_11 : Nat := 0x113000000000000
def bds_11 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_11 : KnownBin bds_11 := by intro b hb; simp [bds_11] at hb
theorem sub_11 : ∀ b ∈ bds_11, m_11 &&& b.1 = b.1 := by intro b hb; simp [bds_11] at hb
theorem gl_11 : ∀ b ∈ bds_11, canon b.1 g_11 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_11] at hb
def f_11 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_11 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_11 : dagCheckRootsF m_11 g_11 bds_11 (dagRefF 1 (dagTraceF m_11 s_11 3 f_11) l_11 0) s_11 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_11_0 : treeBlockF 0 1 (dagCheckNodeF m_11 g_11 bds_11 1 (dagTraceF m_11 s_11 3 f_11) l_11) = true := by decide +kernel
theorem nc_11 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_11 g_11 bds_11 1 (dagTraceF m_11 s_11 3 f_11) l_11) i = true := fun _ h1 h2 => treeBlockF_at nb_11_0 h1 h2
theorem lb_11 : LowerBin m_11 s_11 g_11 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_11 sub_11 gl_11 rc_11 nc_11

def m_12 : Nat := 0xf0f000000000000
def s_12 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_12 : Nat := 0x107000000000000
def bds_12 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_12 : KnownBin bds_12 := by intro b hb; simp [bds_12] at hb
theorem sub_12 : ∀ b ∈ bds_12, m_12 &&& b.1 = b.1 := by intro b hb; simp [bds_12] at hb
theorem gl_12 : ∀ b ∈ bds_12, canon b.1 g_12 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_12] at hb
def f_12 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_12 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_12 : dagCheckRootsF m_12 g_12 bds_12 (dagRefF 1 (dagTraceF m_12 s_12 3 f_12) l_12 0) s_12 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_12_0 : treeBlockF 0 1 (dagCheckNodeF m_12 g_12 bds_12 1 (dagTraceF m_12 s_12 3 f_12) l_12) = true := by decide +kernel
theorem nc_12 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_12 g_12 bds_12 1 (dagTraceF m_12 s_12 3 f_12) l_12) i = true := fun _ h1 h2 => treeBlockF_at nb_12_0 h1 h2
theorem lb_12 : LowerBin m_12 s_12 g_12 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_12 sub_12 gl_12 rc_12 nc_12

def m_13 : Nat := 0xf0f0000
def s_13 : List Nat := [0x5050000, 0x3030000, 0xf0000]
def g_13 : Nat := 0x1070000
def bds_13 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_13 : KnownBin bds_13 := by intro b hb; simp [bds_13] at hb
theorem sub_13 : ∀ b ∈ bds_13, m_13 &&& b.1 = b.1 := by intro b hb; simp [bds_13] at hb
theorem gl_13 : ∀ b ∈ bds_13, canon b.1 g_13 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_13] at hb
def f_13 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_13 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_13 : dagCheckRootsF m_13 g_13 bds_13 (dagRefF 1 (dagTraceF m_13 s_13 3 f_13) l_13 0) s_13 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_13_0 : treeBlockF 0 1 (dagCheckNodeF m_13 g_13 bds_13 1 (dagTraceF m_13 s_13 3 f_13) l_13) = true := by decide +kernel
theorem nc_13 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_13 g_13 bds_13 1 (dagTraceF m_13 s_13 3 f_13) l_13) i = true := fun _ h1 h2 => treeBlockF_at nb_13_0 h1 h2
theorem lb_13 : LowerBin m_13 s_13 g_13 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_13 sub_13 gl_13 rc_13 nc_13

def m_14 : Nat := 0xff000000000000
def s_14 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_14 : Nat := 0x17000000000000
def bds_14 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_14 : KnownBin bds_14 := by intro b hb; simp [bds_14] at hb
theorem sub_14 : ∀ b ∈ bds_14, m_14 &&& b.1 = b.1 := by intro b hb; simp [bds_14] at hb
theorem gl_14 : ∀ b ∈ bds_14, canon b.1 g_14 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_14] at hb
def f_14 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_14 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_14 : dagCheckRootsF m_14 g_14 bds_14 (dagRefF 1 (dagTraceF m_14 s_14 3 f_14) l_14 0) s_14 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_14_0 : treeBlockF 0 1 (dagCheckNodeF m_14 g_14 bds_14 1 (dagTraceF m_14 s_14 3 f_14) l_14) = true := by decide +kernel
theorem nc_14 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_14 g_14 bds_14 1 (dagTraceF m_14 s_14 3 f_14) l_14) i = true := fun _ h1 h2 => treeBlockF_at nb_14_0 h1 h2
theorem lb_14 : LowerBin m_14 s_14 g_14 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_14 sub_14 gl_14 rc_14 nc_14

def m_15 : Nat := 0xff0000000000
def s_15 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_15 : Nat := 0x170000000000
def bds_15 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_15 : KnownBin bds_15 := by intro b hb; simp [bds_15] at hb
theorem sub_15 : ∀ b ∈ bds_15, m_15 &&& b.1 = b.1 := by intro b hb; simp [bds_15] at hb
theorem gl_15 : ∀ b ∈ bds_15, canon b.1 g_15 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_15] at hb
def f_15 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_15 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
set_option maxHeartbeats 0 in
theorem rc_15 : dagCheckRootsF m_15 g_15 bds_15 (dagRefF 1 (dagTraceF m_15 s_15 3 f_15) l_15 0) s_15 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_15_0 : treeBlockF 0 1 (dagCheckNodeF m_15 g_15 bds_15 1 (dagTraceF m_15 s_15 3 f_15) l_15) = true := by decide +kernel
theorem nc_15 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_15 g_15 bds_15 1 (dagTraceF m_15 s_15 3 f_15) l_15) i = true := fun _ h1 h2 => treeBlockF_at nb_15_0 h1 h2
theorem lb_15 : LowerBin m_15 s_15 g_15 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_15 sub_15 gl_15 rc_15 nc_15

def m_16 : Nat := 0x4444444444444444
def s_16 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_16 : Nat := 0x4044400440444
def bds_16 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
theorem kn_16 : KnownBin bds_16 := by
  intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_4
theorem sub_16 : ∀ b ∈ bds_16, m_16 &&& b.1 = b.1 := by intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_16 : ∀ b ∈ bds_16, canon b.1 g_16 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_16 : Nat → Nat × Nat := fun _ => (0, 0)
def l_16 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsF m_16 g_16 bds_16 (dagRefF 0 (dagTraceF m_16 s_16 4 f_16) l_16 0) s_16 4 = true := by decide +kernel
theorem nc_16 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_16 g_16 bds_16 0 (dagTraceF m_16 s_16 4 f_16) l_16 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_16 : LowerBin m_16 s_16 g_16 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_16 sub_16 gl_16 rc_16 nc_16

def m_17 : Nat := 0x5050505050505050
def s_17 : List Nat := [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050]
def g_17 : Nat := 0x10105010501050
def bds_17 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_17 : KnownBin bds_17 := by
  intro b hb; simp only [bds_17, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_17 : ∀ b ∈ bds_17, m_17 &&& b.1 = b.1 := by intro b hb; simp only [bds_17, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_17 : ∀ b ∈ bds_17, canon b.1 g_17 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_17, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_17 : Nat → Nat × Nat := fun _ => (0, 0)
def l_17 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsF m_17 g_17 bds_17 (dagRefF 0 (dagTraceF m_17 s_17 4 f_17) l_17 0) s_17 4 = true := by decide +kernel
theorem nc_17 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_17 g_17 bds_17 0 (dagTraceF m_17 s_17 4 f_17) l_17 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_17 : LowerBin m_17 s_17 g_17 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_17 sub_17 gl_17 rc_17 nc_17

def m_18 : Nat := 0x3030303030303030
def s_18 : List Nat := [0x1010101010101010, 0x30003000300030, 0x303000003030, 0x30303030]
def g_18 : Nat := 0x10101010103030
def bds_18 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_18 : KnownBin bds_18 := by
  intro b hb; simp only [bds_18, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_18 : ∀ b ∈ bds_18, m_18 &&& b.1 = b.1 := by intro b hb; simp only [bds_18, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_18 : ∀ b ∈ bds_18, canon b.1 g_18 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_18, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_18 : Nat → Nat × Nat := fun _ => (0, 0)
def l_18 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsF m_18 g_18 bds_18 (dagRefF 0 (dagTraceF m_18 s_18 4 f_18) l_18 0) s_18 4 = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_18 g_18 bds_18 0 (dagTraceF m_18 s_18 4 f_18) l_18 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_18 : LowerBin m_18 s_18 g_18 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_18 sub_18 gl_18 rc_18 nc_18

def m_19 : Nat := 0xaa00aa00aa00aa00
def s_19 : List Nat := [0x2200220022002200, 0xa000a000a000a00, 0xaa000000aa00, 0xaa00aa00]
def g_19 : Nat := 0x20000002a00
def bds_19 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_19 : KnownBin bds_19 := by
  intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_19 : ∀ b ∈ bds_19, m_19 &&& b.1 = b.1 := by intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_19 : ∀ b ∈ bds_19, canon b.1 g_19 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_19 : Nat → Nat × Nat := fun _ => (0, 0)
def l_19 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsF m_19 g_19 bds_19 (dagRefF 0 (dagTraceF m_19 s_19 4 f_19) l_19 0) s_19 4 = true := by decide +kernel
theorem nc_19 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_19 g_19 bds_19 0 (dagTraceF m_19 s_19 4 f_19) l_19 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_19 : LowerBin m_19 s_19 g_19 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_19 sub_19 gl_19 rc_19 nc_19

def m_20 : Nat := 0x5500550055005500
def s_20 : List Nat := [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500]
def g_20 : Nat := 0x100150011001500
def bds_20 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
theorem kn_20 : KnownBin bds_20 := by
  intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_6
theorem sub_20 : ∀ b ∈ bds_20, m_20 &&& b.1 = b.1 := by intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_20 : ∀ b ∈ bds_20, canon b.1 g_20 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_20 : Nat → Nat × Nat := fun _ => (0, 0)
def l_20 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsF m_20 g_20 bds_20 (dagRefF 0 (dagTraceF m_20 s_20 4 f_20) l_20 0) s_20 4 = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_20 g_20 bds_20 0 (dagTraceF m_20 s_20 4 f_20) l_20 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_20 : LowerBin m_20 s_20 g_20 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_20 sub_20 gl_20 rc_20 nc_20

def m_21 : Nat := 0xaa00aa00aa00aa
def s_21 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_21 : Nat := 0x200020002002a
def bds_21 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_21 : KnownBin bds_21 := by
  intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_21 : ∀ b ∈ bds_21, m_21 &&& b.1 = b.1 := by intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_21 : ∀ b ∈ bds_21, canon b.1 g_21 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_21 : Nat → Nat × Nat := fun _ => (0, 0)
def l_21 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsF m_21 g_21 bds_21 (dagRefF 0 (dagTraceF m_21 s_21 4 f_21) l_21 0) s_21 4 = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_21 g_21 bds_21 0 (dagTraceF m_21 s_21 4 f_21) l_21 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_21 : LowerBin m_21 s_21 g_21 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_21 sub_21 gl_21 rc_21 nc_21

def m_22 : Nat := 0x3300330033003300
def s_22 : List Nat := [0x1100110011001100, 0x300030003000300, 0x330000003300, 0x33003300]
def g_22 : Nat := 0x100130011003300
def bds_22 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_22 : KnownBin bds_22 := by
  intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_22 : ∀ b ∈ bds_22, m_22 &&& b.1 = b.1 := by intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_22 : ∀ b ∈ bds_22, canon b.1 g_22 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_22 : Nat → Nat × Nat := fun _ => (0, 0)
def l_22 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsF m_22 g_22 bds_22 (dagRefF 0 (dagTraceF m_22 s_22 4 f_22) l_22 0) s_22 4 = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_22 g_22 bds_22 0 (dagTraceF m_22 s_22 4 f_22) l_22 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_22 : LowerBin m_22 s_22 g_22 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_22 sub_22 gl_22 rc_22 nc_22

def m_23 : Nat := 0xcc00cc00cc00cc
def s_23 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_23 : Nat := 0x400440044004c
def bds_23 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_23 : KnownBin bds_23 := by intro b hb; simp [bds_23] at hb
theorem sub_23 : ∀ b ∈ bds_23, m_23 &&& b.1 = b.1 := by intro b hb; simp [bds_23] at hb
theorem gl_23 : ∀ b ∈ bds_23, canon b.1 g_23 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_23] at hb
def f_23 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_23 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsF m_23 g_23 bds_23 (dagRefF 64 (dagTraceF m_23 s_23 5 f_23) l_23 0) s_23 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_23_0 : treeBlockF 0 32 (dagCheckNodeF m_23 g_23 bds_23 64 (dagTraceF m_23 s_23 5 f_23) l_23) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_23_1 : treeBlockF 32 64 (dagCheckNodeF m_23 g_23 bds_23 64 (dagTraceF m_23 s_23 5 f_23) l_23) = true := by decide +kernel
theorem nj_23_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_23 g_23 bds_23 64 (dagTraceF m_23 s_23 5 f_23) l_23) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_23_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_23_1 h1 h2)
theorem nc_23 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_23 g_23 bds_23 64 (dagTraceF m_23 s_23 5 f_23) l_23) i = true := nj_23_1
theorem lb_23 : LowerBin m_23 s_23 g_23 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_23 sub_23 gl_23 rc_23 nc_23

def m_24 : Nat := 0xf000f000f000f000
def s_24 : List Nat := [0x5000500050005000, 0x3000300030003000, 0xf0000000f000, 0xf000f000]
def g_24 : Nat := 0x100010003000
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_24 : KnownBin bds_24 := by
  intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_24 : ∀ b ∈ bds_24, m_24 &&& b.1 = b.1 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_24 : ∀ b ∈ bds_24, canon b.1 g_24 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_24 : Nat → Nat × Nat := fun _ => (0, 0)
def l_24 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsF m_24 g_24 bds_24 (dagRefF 0 (dagTraceF m_24 s_24 4 f_24) l_24 0) s_24 4 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_24 g_24 bds_24 0 (dagTraceF m_24 s_24 4 f_24) l_24 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_24 sub_24 gl_24 rc_24 nc_24

def m_25 : Nat := 0xf000f000f000f00
def s_25 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_25 : Nat := 0x100070001000f00
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_25 : KnownBin bds_25 := by
  intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_25 : ∀ b ∈ bds_25, m_25 &&& b.1 = b.1 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_25 : ∀ b ∈ bds_25, canon b.1 g_25 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_25 : Nat → Nat × Nat := fun _ => (0, 0)
def l_25 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsF m_25 g_25 bds_25 (dagRefF 0 (dagTraceF m_25 s_25 4 f_25) l_25 0) s_25 4 = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_25 g_25 bds_25 0 (dagTraceF m_25 s_25 4 f_25) l_25 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_25 : LowerBin m_25 s_25 g_25 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_25 sub_25 gl_25 rc_25 nc_25

def m_26 : Nat := 0xf000f000f000f0
def s_26 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_26 : Nat := 0x10005000500070
def bds_26 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_26 : KnownBin bds_26 := by intro b hb; simp [bds_26] at hb
theorem sub_26 : ∀ b ∈ bds_26, m_26 &&& b.1 = b.1 := by intro b hb; simp [bds_26] at hb
theorem gl_26 : ∀ b ∈ bds_26, canon b.1 g_26 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_26] at hb
def f_26 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_26 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsF m_26 g_26 bds_26 (dagRefF 64 (dagTraceF m_26 s_26 5 f_26) l_26 0) s_26 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_26_0 : treeBlockF 0 32 (dagCheckNodeF m_26 g_26 bds_26 64 (dagTraceF m_26 s_26 5 f_26) l_26) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_26_1 : treeBlockF 32 64 (dagCheckNodeF m_26 g_26 bds_26 64 (dagTraceF m_26 s_26 5 f_26) l_26) = true := by decide +kernel
theorem nj_26_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_26 g_26 bds_26 64 (dagTraceF m_26 s_26 5 f_26) l_26) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_26_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_26_1 h1 h2)
theorem nc_26 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_26 g_26 bds_26 64 (dagTraceF m_26 s_26 5 f_26) l_26) i = true := nj_26_1
theorem lb_26 : LowerBin m_26 s_26 g_26 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_26 sub_26 gl_26 rc_26 nc_26

def m_27 : Nat := 0x5555000055550000
def s_27 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_27 : Nat := 0x115000011550000
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_27 : KnownBin bds_27 := by
  intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_27 : ∀ b ∈ bds_27, m_27 &&& b.1 = b.1 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_27 : ∀ b ∈ bds_27, canon b.1 g_27 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_27 : Nat → Nat × Nat := fun _ => (0, 0)
def l_27 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsF m_27 g_27 bds_27 (dagRefF 0 (dagTraceF m_27 s_27 4 f_27) l_27 0) s_27 4 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_27 g_27 bds_27 0 (dagTraceF m_27 s_27 4 f_27) l_27 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_27 sub_27 gl_27 rc_27 nc_27

def m_28 : Nat := 0x3333000033330000
def s_28 : List Nat := [0x1111000011110000, 0x303000003030000, 0x33000000330000, 0x33330000]
def g_28 : Nat := 0x113000011130000
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
theorem kn_28 : KnownBin bds_28 := by
  intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_11
theorem sub_28 : ∀ b ∈ bds_28, m_28 &&& b.1 = b.1 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_28 : ∀ b ∈ bds_28, canon b.1 g_28 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_28 : Nat → Nat × Nat := fun _ => (0, 0)
def l_28 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsF m_28 g_28 bds_28 (dagRefF 0 (dagTraceF m_28 s_28 4 f_28) l_28 0) s_28 4 = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_28 g_28 bds_28 0 (dagTraceF m_28 s_28 4 f_28) l_28 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_28 : LowerBin m_28 s_28 g_28 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_28 sub_28 gl_28 rc_28 nc_28

def m_29 : Nat := 0xf0f00000f0f00000
def s_29 : List Nat := [0x5050000050500000, 0x3030000030300000, 0xf0000000f00000, 0xf0f00000]
def g_29 : Nat := 0x10000010500000
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_29 : KnownBin bds_29 := by
  intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_29 : ∀ b ∈ bds_29, m_29 &&& b.1 = b.1 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_29 : ∀ b ∈ bds_29, canon b.1 g_29 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_29 : Nat → Nat × Nat := fun _ => (0, 0)
def l_29 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsF m_29 g_29 bds_29 (dagRefF 0 (dagTraceF m_29 s_29 4 f_29) l_29 0) s_29 4 = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_29 g_29 bds_29 0 (dagTraceF m_29 s_29 4 f_29) l_29 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_29 : LowerBin m_29 s_29 g_29 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_29 sub_29 gl_29 rc_29 nc_29

def m_30 : Nat := 0xff000000ff0000
def s_30 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_30 : Nat := 0x17000000570000
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
theorem kn_30 : KnownBin bds_30 := by
  intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_14
theorem sub_30 : ∀ b ∈ bds_30, m_30 &&& b.1 = b.1 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_30 : ∀ b ∈ bds_30, canon b.1 g_30 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_30 : Nat → Nat × Nat := fun _ => (0, 0)
def l_30 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsF m_30 g_30 bds_30 (dagRefF 0 (dagTraceF m_30 s_30 4 f_30) l_30 0) s_30 4 = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_30 g_30 bds_30 0 (dagTraceF m_30 s_30 4 f_30) l_30 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_30 : LowerBin m_30 s_30 g_30 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_30 sub_30 gl_30 rc_30 nc_30

def m_31 : Nat := 0xff000000ff00
def s_31 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_31 : Nat := 0x170000003f00
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_31 : KnownBin bds_31 := by
  intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_31 : ∀ b ∈ bds_31, m_31 &&& b.1 = b.1 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_31 : ∀ b ∈ bds_31, canon b.1 g_31 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_31 : Nat → Nat × Nat := fun _ => (0, 0)
def l_31 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsF m_31 g_31 bds_31 (dagRefF 0 (dagTraceF m_31 s_31 4 f_31) l_31 0) s_31 4 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_31 g_31 bds_31 0 (dagTraceF m_31 s_31 4 f_31) l_31 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_31 sub_31 gl_31 rc_31 nc_31

def m_32 : Nat := 0xff000000ff
def s_32 : List Nat := [0x5500000055, 0x3300000033, 0xf0000000f, 0xff]
def g_32 : Nat := 0x570000007f
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_32 : KnownBin bds_32 := by
  intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_32 : ∀ b ∈ bds_32, m_32 &&& b.1 = b.1 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_32 : ∀ b ∈ bds_32, canon b.1 g_32 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_32 : Nat → Nat × Nat := fun _ => (0, 0)
def l_32 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsF m_32 g_32 bds_32 (dagRefF 0 (dagTraceF m_32 s_32 4 f_32) l_32 0) s_32 4 = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_32 g_32 bds_32 0 (dagTraceF m_32 s_32 4 f_32) l_32 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_32 : LowerBin m_32 s_32 g_32 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_32 sub_32 gl_32 rc_32 nc_32

def m_33 : Nat := 0x5555555500000000
def s_33 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_33 : Nat := 0x115155500000000
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4), (m_5, s_5, 4, g_5), (m_6, s_6, 4, g_6), (m_10, s_10, 4, g_10)]
theorem kn_33 : KnownBin bds_33 := by
  intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_4
  · exact lb_5
  · exact lb_6
  · exact lb_10
theorem sub_33 : ∀ b ∈ bds_33, m_33 &&& b.1 = b.1 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_33 : ∀ b ∈ bds_33, canon b.1 g_33 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def f_33 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def l_33 : Nat → Nat → Option Nat := unpackLinksF 0x8e11c1fc3f07c2f81b43606c0d45a0b40662cc15c2b0542a8148a18420841009f13e0784f01d12b0540a814128050098921222440809001e21e00b001 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d347d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 11 4 10 6 5
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsF m_33 g_33 bds_33 (dagRefF 43 (dagTraceF m_33 s_33 6 f_33) l_33 0) s_33 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_0 : treeBlockF 0 32 (dagCheckNodeF m_33 g_33 bds_33 43 (dagTraceF m_33 s_33 6 f_33) l_33) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_1 : treeBlockF 32 43 (dagCheckNodeF m_33 g_33 bds_33 43 (dagTraceF m_33 s_33 6 f_33) l_33) = true := by decide +kernel
theorem nj_33_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeF m_33 g_33 bds_33 43 (dagTraceF m_33 s_33 6 f_33) l_33) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_33_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_33_1 h1 h2)
theorem nc_33 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeF m_33 g_33 bds_33 43 (dagTraceF m_33 s_33 6 f_33) l_33) i = true := nj_33_1
theorem lb_33 : LowerBin m_33 s_33 g_33 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_33 sub_33 gl_33 rc_33 nc_33

def m_34 : Nat := 0xaaaaaaaa
def s_34 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_34 : Nat := 0x22a2a
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
theorem kn_34 : KnownBin bds_34 := by
  intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_7
theorem sub_34 : ∀ b ∈ bds_34, m_34 &&& b.1 = b.1 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_34 : ∀ b ∈ bds_34, canon b.1 g_34 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
def l_34 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsF m_34 g_34 bds_34 (dagRefF 0 (dagTraceF m_34 s_34 4 f_34) l_34 0) s_34 4 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_34 g_34 bds_34 0 (dagTraceF m_34 s_34 4 f_34) l_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_34 sub_34 gl_34 rc_34 nc_34

def m_35 : Nat := 0xcccccccc00000000
def s_35 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_35 : Nat := 0x4044400000000
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
theorem kn_35 : KnownBin bds_35 := by
  intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_4
theorem sub_35 : ∀ b ∈ bds_35, m_35 &&& b.1 = b.1 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_35 : ∀ b ∈ bds_35, canon b.1 g_35 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_35 : Nat → Nat × Nat := fun _ => (0, 0)
def l_35 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsF m_35 g_35 bds_35 (dagRefF 0 (dagTraceF m_35 s_35 4 f_35) l_35 0) s_35 4 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_35 g_35 bds_35 0 (dagTraceF m_35 s_35 4 f_35) l_35 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_35 : LowerBin m_35 s_35 g_35 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_35 sub_35 gl_35 rc_35 nc_35

def m_36 : Nat := 0x3333333300000000
def s_36 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_36 : Nat := 0x113131300000000
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
theorem kn_36 : KnownBin bds_36 := by
  intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_8
theorem sub_36 : ∀ b ∈ bds_36, m_36 &&& b.1 = b.1 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_36 : ∀ b ∈ bds_36, canon b.1 g_36 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
def l_36 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsF m_36 g_36 bds_36 (dagRefF 0 (dagTraceF m_36 s_36 4 f_36) l_36 0) s_36 4 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_36 g_36 bds_36 0 (dagTraceF m_36 s_36 4 f_36) l_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_36 sub_36 gl_36 rc_36 nc_36

def m_37 : Nat := 0xf0f0f0f000000000
def s_37 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_37 : Nat := 0x10105000000000
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
theorem kn_37 : KnownBin bds_37 := by
  intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_5
theorem sub_37 : ∀ b ∈ bds_37, m_37 &&& b.1 = b.1 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_37 : ∀ b ∈ bds_37, canon b.1 g_37 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
def l_37 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsF m_37 g_37 bds_37 (dagRefF 0 (dagTraceF m_37 s_37 4 f_37) l_37 0) s_37 4 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_37 g_37 bds_37 0 (dagTraceF m_37 s_37 4 f_37) l_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_37 sub_37 gl_37 rc_37 nc_37

def m_38 : Nat := 0xf0f0f0f00000000
def s_38 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_38 : Nat := 0x107070700000000
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_38 : KnownBin bds_38 := by
  intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_38 : ∀ b ∈ bds_38, m_38 &&& b.1 = b.1 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_38 : ∀ b ∈ bds_38, canon b.1 g_38 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
def l_38 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsF m_38 g_38 bds_38 (dagRefF 0 (dagTraceF m_38 s_38 4 f_38) l_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_38 g_38 bds_38 0 (dagTraceF m_38 s_38 4 f_38) l_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_38 sub_38 gl_38 rc_38 nc_38

def m_39 : Nat := 0xf0f0f0f
def s_39 : List Nat := [0x5050505, 0x3030303, 0xf000f, 0xf0f]
def g_39 : Nat := 0x1070f0f
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
theorem kn_39 : KnownBin bds_39 := by
  intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_13
theorem sub_39 : ∀ b ∈ bds_39, m_39 &&& b.1 = b.1 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_39 : ∀ b ∈ bds_39, canon b.1 g_39 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_39 : Nat → Nat × Nat := fun _ => (0, 0)
def l_39 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsF m_39 g_39 bds_39 (dagRefF 0 (dagTraceF m_39 s_39 4 f_39) l_39 0) s_39 4 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_39 g_39 bds_39 0 (dagTraceF m_39 s_39 4 f_39) l_39 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_39 : LowerBin m_39 s_39 g_39 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_39 sub_39 gl_39 rc_39 nc_39

def m_40 : Nat := 0xff00ff0000000000
def s_40 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_40 : Nat := 0x100170000000000
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6), (m_8, s_8, 4, g_8), (m_9, s_9, 4, g_9), (m_15, s_15, 4, g_15)]
theorem kn_40 : KnownBin bds_40 := by
  intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_6
  · exact lb_8
  · exact lb_9
  · exact lb_15
theorem sub_40 : ∀ b ∈ bds_40, m_40 &&& b.1 = b.1 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_40 : ∀ b ∈ bds_40, canon b.1 g_40 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def f_40 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def l_40 : Nat → Nat → Option Nat := unpackLinksF 0x8e11c1fc3e17c0f81b43516a0d05a0340662cc15c2a1522a41482184027c4f81e13c0780e89d02b05049893024248088910220404801001e21e00b001 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b407c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 11 4 10 6 5
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsF m_40 g_40 bds_40 (dagRefF 43 (dagTraceF m_40 s_40 6 f_40) l_40 0) s_40 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_0 : treeBlockF 0 32 (dagCheckNodeF m_40 g_40 bds_40 43 (dagTraceF m_40 s_40 6 f_40) l_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_1 : treeBlockF 32 43 (dagCheckNodeF m_40 g_40 bds_40 43 (dagTraceF m_40 s_40 6 f_40) l_40) = true := by decide +kernel
theorem nj_40_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeF m_40 g_40 bds_40 43 (dagTraceF m_40 s_40 6 f_40) l_40) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_40_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_40_1 h1 h2)
theorem nc_40 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeF m_40 g_40 bds_40 43 (dagTraceF m_40 s_40 6 f_40) l_40) i = true := nj_40_1
theorem lb_40 : LowerBin m_40 s_40 g_40 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_40 sub_40 gl_40 rc_40 nc_40

def m_41 : Nat := 0xff00ff00000000
def s_41 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_41 : Nat := 0x17005700000000
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
theorem kn_41 : KnownBin bds_41 := by
  intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_14
theorem sub_41 : ∀ b ∈ bds_41, m_41 &&& b.1 = b.1 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_41 : ∀ b ∈ bds_41, canon b.1 g_41 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
def l_41 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsF m_41 g_41 bds_41 (dagRefF 0 (dagTraceF m_41 s_41 4 f_41) l_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_41 g_41 bds_41 0 (dagTraceF m_41 s_41 4 f_41) l_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_41 sub_41 gl_41 rc_41 nc_41

def m_42 : Nat := 0xff00ff
def s_42 : List Nat := [0x550055, 0x330033, 0xf000f, 0xff]
def g_42 : Nat := 0x57007f
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
theorem kn_42 : KnownBin bds_42 := by
  intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_7
theorem sub_42 : ∀ b ∈ bds_42, m_42 &&& b.1 = b.1 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_42 : ∀ b ∈ bds_42, canon b.1 g_42 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_42 : Nat → Nat × Nat := fun _ => (0, 0)
def l_42 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsF m_42 g_42 bds_42 (dagRefF 0 (dagTraceF m_42 s_42 4 f_42) l_42 0) s_42 4 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_42 g_42 bds_42 0 (dagTraceF m_42 s_42 4 f_42) l_42 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_42 sub_42 gl_42 rc_42 nc_42

def m_43 : Nat := 0xffff000000000000
def s_43 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_43 : Nat := 0x117000000000000
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10), (m_11, s_11, 4, g_11), (m_12, s_12, 4, g_12), (m_14, s_14, 4, g_14)]
theorem kn_43 : KnownBin bds_43 := by
  intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_10
  · exact lb_11
  · exact lb_12
  · exact lb_14
theorem sub_43 : ∀ b ∈ bds_43, m_43 &&& b.1 = b.1 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_43 : ∀ b ∈ bds_43, canon b.1 g_43 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def f_43 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def l_43 : Nat → Nat → Option Nat := unpackLinksF 0x8e11c1fc3e17c0f81b43516a0d05a0340662cc15c2a1522a41482184027c4f81e13c0780e89d02b05049893024248088910220404801001e21e00b001 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b407c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 11 4 10 6 5
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsF m_43 g_43 bds_43 (dagRefF 43 (dagTraceF m_43 s_43 6 f_43) l_43 0) s_43 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_0 : treeBlockF 0 32 (dagCheckNodeF m_43 g_43 bds_43 43 (dagTraceF m_43 s_43 6 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_1 : treeBlockF 32 43 (dagCheckNodeF m_43 g_43 bds_43 43 (dagTraceF m_43 s_43 6 f_43) l_43) = true := by decide +kernel
theorem nj_43_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeF m_43 g_43 bds_43 43 (dagTraceF m_43 s_43 6 f_43) l_43) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_43_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_43_1 h1 h2)
theorem nc_43 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeF m_43 g_43 bds_43 43 (dagTraceF m_43 s_43 6 f_43) l_43) i = true := nj_43_1
theorem lb_43 : LowerBin m_43 s_43 g_43 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_43 sub_43 gl_43 rc_43 nc_43

def m_44 : Nat := 0xffff00000000
def s_44 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_44 : Nat := 0x175700000000
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
theorem kn_44 : KnownBin bds_44 := by
  intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_15
theorem sub_44 : ∀ b ∈ bds_44, m_44 &&& b.1 = b.1 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_44 : ∀ b ∈ bds_44, canon b.1 g_44 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_44 : Nat → Nat × Nat := fun _ => (0, 0)
def l_44 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsF m_44 g_44 bds_44 (dagRefF 0 (dagTraceF m_44 s_44 4 f_44) l_44 0) s_44 4 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_44 g_44 bds_44 0 (dagTraceF m_44 s_44 4 f_44) l_44 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_44 : LowerBin m_44 s_44 g_44 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_44 sub_44 gl_44 rc_44 nc_44

def m_45 : Nat := 0xffff0000
def s_45 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_45 : Nat := 0x11570000
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
theorem kn_45 : KnownBin bds_45 := by
  intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_13
theorem sub_45 : ∀ b ∈ bds_45, m_45 &&& b.1 = b.1 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_45 : ∀ b ∈ bds_45, canon b.1 g_45 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
def l_45 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsF m_45 g_45 bds_45 (dagRefF 0 (dagTraceF m_45 s_45 4 f_45) l_45 0) s_45 4 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_45 g_45 bds_45 0 (dagTraceF m_45 s_45 4 f_45) l_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin m_45 s_45 g_45 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_45 sub_45 gl_45 rc_45 nc_45

def m_46 : Nat := 0xaaaaaaaaaaaaaaaa
def s_46 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_46 : Nat := 0x2020200022a2a
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_19, s_19, 5, g_19), (m_21, s_21, 5, g_21), (m_34, s_34, 5, g_34), (m_2, s_2, 4, g_2)]
theorem kn_46 : KnownBin bds_46 := by
  intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_19
  · exact lb_21
  · exact lb_34
  · exact lb_2
theorem sub_46 : ∀ b ∈ bds_46, m_46 &&& b.1 = b.1 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_46 : ∀ b ∈ bds_46, canon b.1 g_46 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def f_46 : Nat → Nat × Nat := unpackForestF 0xb4f2d2f950e140b47850204051510382d0c01f 3 11
def l_46 : Nat → Nat → Option Nat := unpackLinksF 0xe1c34e1972243a70a8601 0x15a0234036810541c2829404080715081c534f9696cd1c5a1801f 7 3 11 4 4
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsF m_46 g_46 bds_46 (dagRefF 11 (dagTraceF m_46 s_46 6 f_46) l_46 0) s_46 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_0 : treeBlockF 0 11 (dagCheckNodeF m_46 g_46 bds_46 11 (dagTraceF m_46 s_46 6 f_46) l_46) = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 11 → (dagCheckNodeF m_46 g_46 bds_46 11 (dagTraceF m_46 s_46 6 f_46) l_46) i = true := fun _ h1 h2 => treeBlockF_at nb_46_0 h1 h2
theorem lb_46 : LowerBin m_46 s_46 g_46 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_46 sub_46 gl_46 rc_46 nc_46

def m_47 : Nat := 0x5555555555555555
def s_47 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_47 : Nat := 0x115155511551555
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_33, s_33, 7, g_33)]
theorem kn_47 : KnownBin bds_47 := by
  intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_33
theorem sub_47 : ∀ b ∈ bds_47, m_47 &&& b.1 = b.1 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_47 : ∀ b ∈ bds_47, canon b.1 g_47 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_47 : Nat → Nat × Nat := fun _ => (0, 0)
def l_47 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsF m_47 g_47 bds_47 (dagRefF 0 (dagTraceF m_47 s_47 7 f_47) l_47 0) s_47 7 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_47 g_47 bds_47 0 (dagTraceF m_47 s_47 7 f_47) l_47 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_47 : LowerBin m_47 s_47 g_47 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_47 sub_47 gl_47 rc_47 nc_47

def m_48 : Nat := 0xcccccccccccccccc
def s_48 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_48 : Nat := 0x4044400440c4c
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_23, s_23, 6, g_23)]
theorem kn_48 : KnownBin bds_48 := by
  intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_23
theorem sub_48 : ∀ b ∈ bds_48, m_48 &&& b.1 = b.1 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_48 : ∀ b ∈ bds_48, canon b.1 g_48 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_48 : Nat → Nat × Nat := fun _ => (0, 0)
def l_48 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsF m_48 g_48 bds_48 (dagRefF 0 (dagTraceF m_48 s_48 6 f_48) l_48 0) s_48 6 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_48 g_48 bds_48 0 (dagTraceF m_48 s_48 6 f_48) l_48 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_48 : LowerBin m_48 s_48 g_48 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_48 sub_48 gl_48 rc_48 nc_48

def m_49 : Nat := 0x3333333333333333
def s_49 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_49 : Nat := 0x113131311133333
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 5, g_18), (m_22, s_22, 5, g_22), (m_28, s_28, 5, g_28), (m_36, s_36, 5, g_36)]
theorem kn_49 : KnownBin bds_49 := by
  intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_18
  · exact lb_22
  · exact lb_28
  · exact lb_36
theorem sub_49 : ∀ b ∈ bds_49, m_49 &&& b.1 = b.1 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_49 : ∀ b ∈ bds_49, canon b.1 g_49 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def f_49 : Nat → Nat × Nat := unpackForestF 0x1f 1 5
def l_49 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x1f 2 1 5 1 2
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsF m_49 g_49 bds_49 (dagRefF 1 (dagTraceF m_49 s_49 6 f_49) l_49 0) s_49 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_0 : treeBlockF 0 1 (dagCheckNodeF m_49 g_49 bds_49 1 (dagTraceF m_49 s_49 6 f_49) l_49) = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeF m_49 g_49 bds_49 1 (dagTraceF m_49 s_49 6 f_49) l_49) i = true := fun _ h1 h2 => treeBlockF_at nb_49_0 h1 h2
theorem lb_49 : LowerBin m_49 s_49 g_49 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_49 sub_49 gl_49 rc_49 nc_49

def m_50 : Nat := 0xf0f0f0f0f0f0f0f0
def s_50 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_50 : Nat := 0x10105010503070
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_26, s_26, 6, g_26), (m_17, s_17, 5, g_17), (m_18, s_18, 5, g_18), (m_24, s_24, 5, g_24), (m_29, s_29, 5, g_29), (m_37, s_37, 5, g_37), (m_0, s_0, 4, g_0), (m_1, s_1, 4, g_1), (m_5, s_5, 4, g_5)]
theorem kn_50 : KnownBin bds_50 := by
  intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_26
  · exact lb_17
  · exact lb_18
  · exact lb_24
  · exact lb_29
  · exact lb_37
  · exact lb_0
  · exact lb_1
  · exact lb_5
theorem sub_50 : ∀ b ∈ bds_50, m_50 &&& b.1 = b.1 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_50 : ∀ b ∈ bds_50, canon b.1 g_50 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_50 : Nat → Nat × Nat := unpackForestF 0x25109b2714593ca6c9c1140169f25b4e92d1c002d2e454a12295c914a848a172450a000b478f09fc784de4107b1e1358f01fc780de3d27b1e035005a1c7293e3948600a4e8dd1e00292e3505b191258cc96c640940148713349899a1c564fe2b26f1583f8ac1bc4cd062907b1312789c9ec4c09c014851194588c22c3897a204a51002d87092c3a94a1d25b0e0250051dc341321728b0c14c85c22c1c97a1504909a5284c16c1c4961124907a5283c96c1c0940146705a5c82c924108ee094b904233004a7c0c4d20069701a3480c9a400d0e0029d0013c004a5bd2d71e96a2fd23b7ec923f48cde96a0f4a507da303ec9b1e9476f8c607c5363e4d41f1248f4a337b895bdc48de90b8f523b7ac923d48cde90a0009477991a3cc4d1cc696f2134731a1bc40d5cc29cefa3b77d19b98061dd284e601576c9239a8edcd466e683f7341dbab141d5480e6837749a03a48c1d0288e803c73419b9a0bdcd046e6014004a1b5714dab6bee3b5171c22b56d79c5268d5b53705aeb824d9c106ad5b526ad2f356949bd4bad595e6dc9b36e055b8072dc0316dc0a356549ab07eda14c6ac1db560ddaf6a4d7a5e6bd293560d5ad078d61446ac198024fda7030d381569c0a0024eda506ad04526812f343179a14bcd004d0049bb385399c278ce01500499b34115974bccc25265c128024bd9502a009236492e32409186476c825c61919b1ad718d068c313f62a283141318626ec3a5c61c1230c4bc0109ec20345f9a5b024d181068bf3435f8272fc0f001096b3b5c59da8af08ed79048bc23359da82ce941748c0ba26c59d1dadf1816f4d8b83505bc122ce8cd6c256b612359cae2d08ed69048b423359ca800211d64268b20344e1a5ac40d138686af94457c2227093d5bac0ad95c56c2e27091d58268ac0344e11faac4d53809ca9a3b54d19a700b14c49ca6242530a729c4c14c28ca613e4e013294091394769ca3351c1a2724fd39276a1450509202841313926e9fb404fd1827a9113d2789c9334ec122724bd392469c02400421a1114d086be99b514cca2a10d7931068843534b5aea5a4d52d06c843524212f210949082be9314c498a224c051082a68414f420a1a440d10827e9024c4209da104dd158bc8ac524552f22a949152bc8c014454a922a4f9152648413544ca6222911110288413343d2ea101790906c848164281ca140c509028840520041fa080b10404c820240041da044d4f38a479a5e3ccaf9f7580fb2b87e0303ec0a1e654cf46bc7a3523d12f1e8578f50287a1523cca68020dcf128874a4f3bc921d290ce909c7483c3a8a71d4508e904c0083339ca29b8978dc2be7193438c0a1b854cdd6bc6eb52374af1bc050dd2a46e125004179b4098010466ba3435c9a190d2cd42686a034321a19a44d8c849c6414e3392219c570c809e65a5c32ca619011cc94686403f0040f98a4d0c50685ab4b3091a1840d0b5686601442d52797c570b548e5e1342d51f9740d8b529c5b94d2dca296a138b504c0081b2c12c160950b02a85805409e2f956920ab488559442ac2204f14c276bc5223829d201488d0a42685203409da99449209c8a24e23a27da01388d89c26c4e03609da912e8e0974684b93425c1a04ed2c934704a25024d1a04ed0c274be4834909d2f11d180274a642c51215a89128d88906c42b50214ae90c9408529c13a5209d278f4d787a6a43d25e1fdae0f49487a26c3d1351e81b0f40d42749c3bb5c1dc9e04e92c74ac03a35009d238e1140706803814c1b9aa0dc530274862dc5e1a9220d41105b8a43414416daf0cb140652682db5216da48b6d045b2bc3035016ca90b65345b27a2e35016c9a84e9082747e13a33155280ac500550881394f12d2f0969484b2bc2825012ca90965244b2822583a12c1b04e538484802405c09ca388a5384525c1394210c1a04e4fc3f4a0201300fca204e13c334bc19a520ccaf074940332a4199490cca0866138330841983a0cc1b04e1382f4b817a400bcae04e11c2a29c151420a8270540b8270841413409c1f80205c250680134b0851a0424d0210680134307c120128ec1b2500e14006c920128cc190680493f0249d829140144800a04c0249b822d001146007a4403c9e0124cc0d0480492f024918140f80903c011240101c8080c4040520202100c0a004138010260001f 10 11
def l_50 : Nat → Nat → Option Nat := unpackLinksF 0x4360219870cc08601c2b1615810ac08501c280214010a00850042802118b080383c141e020c8b0583828141402078b004e802040101fc90fe407f00bf801fa86fd407e41bef0df780fbc07de03ef01f780fbc07d42bea01f386f9c07c81bdc21ee00f7007b023d801ec00f4087a003d001e410ee4f77203b805dc00edc176623b301d902ec8075443aa01d482ea4074243923dc900e480720139001c782e1c870e038605c300e180708138401c200e004700037e09bf00df806fa0b7b09bd80dec06f6037711bb02dd806ec037409b78adbc06de036d09b680db406d80b6a09b110d8416c2035d11ae80d6836b4035809ac00d6006ac135505a78cd3c069c0b4e01a682d3016960b4a05a308d18068c034409a200d0436800b40019b92cb4a6561329099480ca4064a2325019184c8c06460323018f88c7036321b19018b84c5c062e0317018b80c5426241b0e118682c28360e1b07018380c1c05f662fb017d02bd845bebadf016f80b7c05b81adc016c86b6015b002d8016792b1c85881ac4016008ae8657402b8095c00ac8655832ac015582aac055602a9095480aa0155002a8015208a90054802a2095100a8805401298214c00a5c152e0297014a84a54052a0291114880a3c251e028f014702a302518028c014600a20450e0a87014380a1425002a800140009f824fc027e013e829ec24e642720539009b844dc026b0d35029a804cc226601328299404c2226005300097434ba025b092d8096c04b21259012c0295c14ae0255092a02938649c024d05268093404980a4b0525029241492024511228091404861243012006900047e0a3f011b128b0a45412280914008a00448222401110488804440222010f0886c34301a14110a0085004260a0f11058881c440e02031101027fc33f819fc00fe007f003f801fc00fe007ec13f601fb00f7987bc03dc09ee00f5087a803d011e800f4007a003d001e608f186731739801cc00e600724339201c60ce28270c238601c300e180704237a21bd00de806f4037a01bd00de026cc935641ab00d38869c034621a00cd0006800340019c10cb0c6580328119208c900644131c198e00c700638031c018d04c38c6046302018004c00060002fc117e00bf005f022f8017a08bb085d802ec017210b9005c802de196f00b70259882cc016600b20459002c8016208b10057842bc015b0cad8056812b4015808ac0056002a8215010a4105200290014800a40050c5284094200a082500126e49331099804cc026409320099004b4525a012a0c95004a802520928049382470b238011c008e00470022c3115048a02448221c210d04868042052100106088300418020c010600800c400020000ff047b903c851e208f10078803c401e008ef0477803b811dc00e428718238c01bc28dc086d0434c71a408d1046880334419808c6186300318018c00c30c6180308118400c2005f862fc017e00bf005f802f8117810bc005e002ec115680a80c5382298114c00a5045106288014208a1005080280114000a0005000280012c5096004b0024841240092004708238011a088c04460022c1110188800438221c010e0086044300218010c008600430021800f8507c003e001f000f02078003c001e000f00074103a001cc10aaf05404290414410a008500026081300096084b00258012810901048002382114208808430421800fc407e003f001e840f400722039001c020e0007000360816140b00058002c0016000a0404e08231000c40001 0x25109a590452c40ac9e534b228a580169322f47497a5028b270452bc0bc98d3a304a125a3892528490572472a12305c91428390db22e4c0e11448b5303844f1c529ce113e9041e95a0d4ac02a9a36c8b13025a1122b4c09683c8f49e95a4d53109c9683e2ac0b47297a2f4a515250728a7c864fdc027b211379009aa6c13e3f07e9603d8f81bc780d4aa02f1bb4e8e927c7290dbf25ed19274ac17a0009ca902f1ba3c8d41694c094a502b1992d2989294805a3424b1902528c0bc5c4fe2d26f1603f8ac1b94205e2907a4f0352740ac4e4f49e26a4e0168c1a4c5ed0e2a682df13f8a093a540fe2604e4d817830a6c485159309b118458312f44294a0b2bcf395288016932094d803a4c01564d2f43c94a1d25a4c9256482f2ca148c60344b8168892f41457e052b6fa957794a9c3e495910bec185b5cc2bac614e1c04a6b01f3100d92c05c240270d04c860a64125361928ac804d85c22c2a092094bd0a252810ad3e255a1305a4982530c0c84604611248c825e8412941e4b49324ac105a5bc2b1a8078220250b25e820afc0456df02aef195384892b1e17d800b6b705758429c1c094d303e6081b2480b84004e0c4b9059248252e380d060a477042336f09f11e1352907e7f83739417c0c4d20446901934815a5c04d0e0129d0013c7dd24be8905fb248fe23b7e919bef181f64d8f786c7b0303e4491f26a0f58507d2303e69b1f1248f706c7a8303de4adee246f59247b11dbd48cdfe6b8feb517e5a83f0941f5476f82337b42e3d2141db028f3a347989a3c0061da028f213477c0c3b20512807af10357811dbbe8ccfc088dd24e4a0a73ba5092609c7d84638c1f3b649118268dca4c74c203a40c1d68a0eaa403d4a63a20c1d3680e92306e1263a2511d00786f1247691dbb28cdb727cec03f75c1dba80ddcf066e702f73411bcad2de3686db24e784a724a13cfa08e7103f7780c3b8055cc028e446c7149a386d81bd2d8e1c5d721a8b1c135c708ae1c6c7149a386d75c226c4083d7041a9000b5b004a298151f81eb5e0d45202adea5d14426b720e5b8062dd9366e80ab6e050576b88b1346d0240f6111ad068da14c130920f41107b078d603012c0a31cd79b16a4d825e6bd2931a179600a49104e3c4210f60f83107a6001a1540b35a0f1ac2885c05c0c4261d6091ca8a6e4b5f719af388d4dc06a4dfa5e6f929378579b62a4c605f57829a4813cf0086da83f1e41eb660edb206ed70356ac199a2074bf0362a0171280ab52061a802ad381457428b160f5a506ad083d68a2f317149a14bc1894d1f0a2b141795c0a45f01a1200b349149a34bccf14d6242fab414da009a5e81b11c0b8620f47a06a230150c4a70ee5091109c77842678a733a4f12309e7704311012b380558809acd0456212f330949870bcac8522f00d086059994bcc305f55c29b2e094bb036210176540ab2697192048c825c639ae102d40512b8c683462e28314131884b8c38244b1a0b228ed8f4664794d6309fb124dd8625e8703e6101a3044d181068c1b4b601a1afe1397e078baa495c920af20917a476bc2335d6302e89b16d2d8b51605c0122e0d41690a0b94605c5362d85b1682c0b78245b495ad848d69048b523b5a119af8d717b6a2bbb505d9282e68ed6e466b595c59ca829405165268b20345501629209162068a982c5201228e05160288a884c57c2229e09142028aed60570ae2b61714d0489d8145649a2b00d14c048a893d5589aaa88ed53466a724451c1a29c4c1420989d824545272a09094f29ca69465309f2181394a048a383442c262805013f260a245050d2027c4c142098a03404fd1827c9113d2788504c4ec122928ed48466a313f5149da824dd3c2669d12f4e491a120f963696b0b4357927ab491d5747e8414e554272a40b14b04c9c0244d2362620d12f6c08786c4be2ea68d451d29a999454be362620d12f6ba4093d4b89aa5a0d88025a8d9250f40b0fc4f51a26a1e016475ae102d41192681d85c4609a22e91128298939444980a062d0116288910340d80a22a910312981a8244440a082d71202903e9444881a2264d1204983e1440d0120fa4f112260198144600a23b1791c8a48da5e46929232579172a43e94e0c4a6a2c4f9152646781d0fc0aa26531124886715c0c4a62220510f4ba1d84d42c1ca140c50d06c860164240a26d14d356be9935e4c1a9a58d492b4bc952524a4afa4a54d2429e919434849f8f24f51f2768f1374509aa204cd0e0bc840523340f9720683e02e190164181620a099040487f1513e09ea044d4f727a7c4503d8a61ea530fc0607f5603d12e1fa570fb0287a8143e5af1f0d48f74bc7b15e3d0a90620f47a06a6601d0bc0aa03149004bc7f95f3e8a99e6534ed09a6501f0b80b9e25102d2481884c3ac120584d0ef248750341dc120624f47c26a158160c5270ee908eb29c751423c1279dc90c2924c7684e3b01e1d2098e129a739453852e1be490de2486ea343909a1c6050de02870b5e381a91be578dd2a46481d0a00a9cc978e52be711533709299007c2702e6d0263611a1ae4d0d52686a0343489b08c054ce09a658450c41e8f40d4cf4886715c0c4a6056050cc4b83d15c32ca61928d0d669669b43345271a0538cd09e650473201f96a054c62686283430d1a1840d0c02885c05c0c42608c090be2b83e05c2dc261784d0ba06c158162e0a696e5143127a3e1350c5270ee9084629c1584e311a5982d0cbf49e5ea472ed1f972538b609c5a8262cd2c1649506c480589542c02a144d406b28035140285b0118980694a040a4c2b92415a9105f480561442ac221008f8674642993e0f41f14e9008b4c0542382991a14a4d0a406833250289240c09009f68045150224a81431448e4a2442501f9270c8908a04744f236148a713a4d83c09c4e03618d281348e0994684c13425c1a03c0401d0400e01025128036040624a04aa3824d1a034040874c043c5d241a4902d045127c1d83e23a3010edb05049c45236218a70c05083a09c44836219281191448b6a24435013d2710e5748529c2f9420e4270f09605e4a01f944154220300407f4a03fb5c1011e0ac930826bc40b521dda70bcd34804bc3f2521f49b0f84d47b06c3d0351c0a20f0d704e4b83b93c0e02e02e080724a00b0101c52002a04075ac03a3500c52e0de9002f2b82405c04c0802408011040394501c5a00e05301004007810179ae0ded504d4b83714c0dc2e01c080666a035a441a8220d0510668a0301501949a0c0d40404882b044171a80d9178698a433b5e191a90c6d24626822ba4d125228c25785f2a41894e178a68ba4f45b26a2084d0c0228504d0430680601002c100ac110562802ba500c5260aa110502a02825014d2f0a4948512bc27952138a489a5043609c168421301d0960d8314b824a40118ae0901704629c2292e0d427058108430682024410098082940314981f9440e8a80749403d4bc1e2520ecaf072548382921b9410d82706a10834074198360c52e0609002f2b81585c0b4a70585082b09c1502e0a09a15f17caa8a654b5e28da9936d4896696493432452f91e9788d4a64225220d278f29387649639a471b5218b49085947e2c233150a78945384728e221421089f87c13c3209c170470a42104e0fc080200f8140789204a0d01b2480d92408d1a0444d01a2481083407c120385001d2500d9240641a00e13005028091400449802d140154800813005026024d00114600824403c9e00c13004038068240281f0080c81e4760d2330609f82e4ec1326e071330309781648c0307c0481e01c1c80c0c4050520202100c0a048d2c20686041240082749ad3e4a697223478eda1c7093a3649718a43895214368ee0d4670394f7fca5bd051dcb286d513f6989db3e4dd9b266cb12f65091b0a13d7d096b30474dc21a0e0fd03076790373a0199b60bcd90466381f2d00d84c05c010260001f 17 6 11 10 7
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsF m_50 g_50 bds_50 (dagRefF 594 (dagTraceF m_50 s_50 8 f_50) l_50 0) s_50 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_0 : treeBlockF 0 32 (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_1 : treeBlockF 32 64 (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_2 : treeBlockF 64 96 (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_3 : treeBlockF 96 128 (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_4 : treeBlockF 128 160 (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_5 : treeBlockF 160 192 (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_6 : treeBlockF 192 224 (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_7 : treeBlockF 224 256 (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_8 : treeBlockF 256 288 (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_9 : treeBlockF 288 320 (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_10 : treeBlockF 320 352 (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_11 : treeBlockF 352 384 (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_12 : treeBlockF 384 416 (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_13 : treeBlockF 416 448 (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_14 : treeBlockF 448 480 (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_15 : treeBlockF 480 512 (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_16 : treeBlockF 512 544 (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_17 : treeBlockF 544 576 (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_18 : treeBlockF 576 594 (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) = true := by decide +kernel
theorem nj_50_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_50_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_50_1 h1 h2)
theorem nj_50_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := block_join nj_50_1 (fun _ h1 h2 => treeBlockF_at nb_50_2 h1 h2)
theorem nj_50_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := block_join nj_50_2 (fun _ h1 h2 => treeBlockF_at nb_50_3 h1 h2)
theorem nj_50_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := block_join nj_50_3 (fun _ h1 h2 => treeBlockF_at nb_50_4 h1 h2)
theorem nj_50_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := block_join nj_50_4 (fun _ h1 h2 => treeBlockF_at nb_50_5 h1 h2)
theorem nj_50_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := block_join nj_50_5 (fun _ h1 h2 => treeBlockF_at nb_50_6 h1 h2)
theorem nj_50_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := block_join nj_50_6 (fun _ h1 h2 => treeBlockF_at nb_50_7 h1 h2)
theorem nj_50_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := block_join nj_50_7 (fun _ h1 h2 => treeBlockF_at nb_50_8 h1 h2)
theorem nj_50_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := block_join nj_50_8 (fun _ h1 h2 => treeBlockF_at nb_50_9 h1 h2)
theorem nj_50_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := block_join nj_50_9 (fun _ h1 h2 => treeBlockF_at nb_50_10 h1 h2)
theorem nj_50_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := block_join nj_50_10 (fun _ h1 h2 => treeBlockF_at nb_50_11 h1 h2)
theorem nj_50_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := block_join nj_50_11 (fun _ h1 h2 => treeBlockF_at nb_50_12 h1 h2)
theorem nj_50_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := block_join nj_50_12 (fun _ h1 h2 => treeBlockF_at nb_50_13 h1 h2)
theorem nj_50_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := block_join nj_50_13 (fun _ h1 h2 => treeBlockF_at nb_50_14 h1 h2)
theorem nj_50_15 : ∀ i, 0 ≤ i → i < 512 → (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := block_join nj_50_14 (fun _ h1 h2 => treeBlockF_at nb_50_15 h1 h2)
theorem nj_50_16 : ∀ i, 0 ≤ i → i < 544 → (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := block_join nj_50_15 (fun _ h1 h2 => treeBlockF_at nb_50_16 h1 h2)
theorem nj_50_17 : ∀ i, 0 ≤ i → i < 576 → (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := block_join nj_50_16 (fun _ h1 h2 => treeBlockF_at nb_50_17 h1 h2)
theorem nj_50_18 : ∀ i, 0 ≤ i → i < 594 → (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := block_join nj_50_17 (fun _ h1 h2 => treeBlockF_at nb_50_18 h1 h2)
theorem nc_50 : ∀ i, 0 ≤ i → i < 594 → (dagCheckNodeF m_50 g_50 bds_50 594 (dagTraceF m_50 s_50 8 f_50) l_50) i = true := nj_50_18
theorem lb_50 : LowerBin m_50 s_50 g_50 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_50 sub_50 gl_50 rc_50 nc_50

def m_51 : Nat := 0xf0f0f0f0f0f0f0f
def s_51 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_51 : Nat := 0x107070701070f0f
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_25, s_25, 5, g_25), (m_38, s_38, 5, g_38), (m_39, s_39, 5, g_39), (m_12, s_12, 4, g_12)]
theorem kn_51 : KnownBin bds_51 := by
  intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_25
  · exact lb_38
  · exact lb_39
  · exact lb_12
theorem sub_51 : ∀ b ∈ bds_51, m_51 &&& b.1 = b.1 := by intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_51 : ∀ b ∈ bds_51, canon b.1 g_51 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def f_51 : Nat → Nat × Nat := unpackForestF 0x2d3c5a5c25c168e51515a21234368844d05a1801f 4 11
def l_51 : Nat → Nat → Option Nat := unpackLinksF 0xe1c3862a5424c882ac601 0x19a0425c546864d15a21b4468a888d089a534f9696ed1c5a1801f 7 3 11 4 4
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsF m_51 g_51 bds_51 (dagRefF 11 (dagTraceF m_51 s_51 6 f_51) l_51 0) s_51 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_0 : treeBlockF 0 11 (dagCheckNodeF m_51 g_51 bds_51 11 (dagTraceF m_51 s_51 6 f_51) l_51) = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 11 → (dagCheckNodeF m_51 g_51 bds_51 11 (dagTraceF m_51 s_51 6 f_51) l_51) i = true := fun _ h1 h2 => treeBlockF_at nb_51_0 h1 h2
theorem lb_51 : LowerBin m_51 s_51 g_51 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_51 sub_51 gl_51 rc_51 nc_51

def m_52 : Nat := 0xff00ff00ff00ff00
def s_52 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_52 : Nat := 0x100170011003f00
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_40, s_40, 7, g_40), (m_19, s_19, 5, g_19), (m_20, s_20, 5, g_20), (m_22, s_22, 5, g_22), (m_24, s_24, 5, g_24), (m_25, s_25, 5, g_25), (m_31, s_31, 5, g_31), (m_0, s_0, 4, g_0), (m_2, s_2, 4, g_2), (m_6, s_6, 4, g_6)]
theorem kn_52 : KnownBin bds_52 := by
  intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_40
  · exact lb_19
  · exact lb_20
  · exact lb_22
  · exact lb_24
  · exact lb_25
  · exact lb_31
  · exact lb_0
  · exact lb_2
  · exact lb_6
theorem sub_52 : ∀ b ∈ bds_52, m_52 &&& b.1 = b.1 := by intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_52 : ∀ b ∈ bds_52, canon b.1 g_52 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_52 : Nat → Nat × Nat := unpackForestF 0x3342200b4fcb27202d2f24a880b47016878cd240527e212901497844e6fda8e014ebf2a20291ef41200a430147f744a4051dd1c58a38a1465328ca0d794faf29764172bca3d8014af2874650291a7d234ba468f48d0e901fd385ca70a9480ee901bd2033a3098028de4094c894f912973a1727428489479b0813495244a1c881f910372a962552848817920b9241524409c80240146708d26111fc6254844771116220a04404c8446f0a9521412422330129ef6d3deda5bfa507f0b8f6d1df11c3e0347b6860252d49ae293517247ee48edd4263923773048e48cd49a82925c524a0dd181491fb5c606b4d8a48ed8e3031b60676a0c650191ae3225063098a48dd6e302da6c5f6a0b64a171a82e1505b048a48cd4c97a992b566a0ac0c14c93aa15c53246a417004a392c592569e9c4d095a5a4a50492b894111242e12b47452688c0b1141a12b434149a8450105229294e266924c8fc991d9d1403a09874100991b9b828370484c8cc981f9303b3249864900981b9783c2f0684c0cc98179302b2a69054d00981394230272684c08c940a009430127e444b8049d8e4581c8a03893071200e04c0126e1f16c56300aa60152d82c05054b007b57132781e56c3cab8793b0f26e024cc34120092f0b2880b16c241a02b42054860c50414a70092b036840249c04918001f 8 11
def l_52 : Nat → Nat → Option Nat := unpackLinksF 0x244090864018e123808d863608d823418d023218c822c38b02263880e200878616485820c583020c08302044810204081020028001fc27d11f407d01f407d01f407d01f407c09f007c01d8c7129c027001c007001be16e0db806d85b416d01b406d01b406c09b006c01ac264b584761018406101821608182060817c35f017c05e096e55b816e05b816e05a896a05a8166257915e055915605581560548952053894645181460518142250814204f0d3a14d893604c893204c812c348951e247051c046851a0468114342950a042810a0428106241810413f10e8a3984e223880de23688d813600d423294c813200c422f8cbe02f80bc12e08b802e00b802e00b802e00b232c80b202b88ae02b80ae02b80aa22a80aa02988a602980a6029049e327809c1268480d1c9c7011c006e11b806e01b806e01b80645188462018806201880601161058015845601504540119c4601104440108442010043e10f803c10d103400c8432000e0001 0x3342209a42502a23450f2c9c8512bc92a38cd2710948c941c22722a4c461216014e1528582d46fca88a133bd0491a57e08adb69574f2a71657e04adb51574d2a7744a6252f4025a664ac989499da85905c4229960052d0a7d994bb128f5e50ea02e53854ad69f58d2eada3d53438809efe12d8c23a4843a907f4c0ee941bd2033b88b16f1421cafbf15b622ae9054ed8a65a941ae28146131f52d2f2569b28134502782e4e8509b08134952592c4aa50930b92415280a7cf94b9c28f3250e1427be04b5b08e8a10c2414cc01f970372805e4409c215f7b2b6b455d10a984139a125320092312a454588928110132192a428248e6931a8fe2d1dc3a378446700941fc2e3ea387c06904d3e05a5bf3477b686dc935b124b424561482ce501d4262f92873048ee8fdd91dba23772466dd1816436364606b4d8b01b15c1e3394064098ced41582e32b5c576a0c8941a6303436066280aa1b18c262f9285d048a81317da82eb50542b8b854186303026c5e250a61b16c122bb5056060a85716497ac12b5524ea648de5ae3c351716a0e0971bd2836a3f6a476c48dd6919a905c3f02886570f80a271343d02884930f0121d84c3b0989411131282595c4129892170e40a1b824460586e0911c9a2283436028845010d26a0a453c28076130e8201c0283704866930c9201803c2f068500c0ada41534027040508c09c9a1fb493e47e7a8ece51b9b2333507e680ecc41b970332d05e580aca41393023508b29ed3d35a5a43474468680538940a1134e2225c411607e280f24c1d480381304d240b014198c0309805cb60a960132780c5706a2d8a357074762456c44ab8813b0f26e1a0902ca204834064b80c5042a2d84342074860a5380da16634fca69790d1f1da1e2a4fc34977c91ef121dda3fb9477448de3d19c194f7a296a251c90a19193f21276364dc38998612f042560449c04918001f 14 5 11 8 6
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsF m_52 g_52 bds_52 (dagRefF 206 (dagTraceF m_52 s_52 8 f_52) l_52 0) s_52 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_0 : treeBlockF 0 32 (dagCheckNodeF m_52 g_52 bds_52 206 (dagTraceF m_52 s_52 8 f_52) l_52) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_1 : treeBlockF 32 64 (dagCheckNodeF m_52 g_52 bds_52 206 (dagTraceF m_52 s_52 8 f_52) l_52) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_2 : treeBlockF 64 96 (dagCheckNodeF m_52 g_52 bds_52 206 (dagTraceF m_52 s_52 8 f_52) l_52) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_3 : treeBlockF 96 128 (dagCheckNodeF m_52 g_52 bds_52 206 (dagTraceF m_52 s_52 8 f_52) l_52) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_4 : treeBlockF 128 160 (dagCheckNodeF m_52 g_52 bds_52 206 (dagTraceF m_52 s_52 8 f_52) l_52) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_5 : treeBlockF 160 192 (dagCheckNodeF m_52 g_52 bds_52 206 (dagTraceF m_52 s_52 8 f_52) l_52) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52_6 : treeBlockF 192 206 (dagCheckNodeF m_52 g_52 bds_52 206 (dagTraceF m_52 s_52 8 f_52) l_52) = true := by decide +kernel
theorem nj_52_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_52 g_52 bds_52 206 (dagTraceF m_52 s_52 8 f_52) l_52) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_52_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_52_1 h1 h2)
theorem nj_52_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_52 g_52 bds_52 206 (dagTraceF m_52 s_52 8 f_52) l_52) i = true := block_join nj_52_1 (fun _ h1 h2 => treeBlockF_at nb_52_2 h1 h2)
theorem nj_52_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_52 g_52 bds_52 206 (dagTraceF m_52 s_52 8 f_52) l_52) i = true := block_join nj_52_2 (fun _ h1 h2 => treeBlockF_at nb_52_3 h1 h2)
theorem nj_52_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_52 g_52 bds_52 206 (dagTraceF m_52 s_52 8 f_52) l_52) i = true := block_join nj_52_3 (fun _ h1 h2 => treeBlockF_at nb_52_4 h1 h2)
theorem nj_52_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_52 g_52 bds_52 206 (dagTraceF m_52 s_52 8 f_52) l_52) i = true := block_join nj_52_4 (fun _ h1 h2 => treeBlockF_at nb_52_5 h1 h2)
theorem nj_52_6 : ∀ i, 0 ≤ i → i < 206 → (dagCheckNodeF m_52 g_52 bds_52 206 (dagTraceF m_52 s_52 8 f_52) l_52) i = true := block_join nj_52_5 (fun _ h1 h2 => treeBlockF_at nb_52_6 h1 h2)
theorem nc_52 : ∀ i, 0 ≤ i → i < 206 → (dagCheckNodeF m_52 g_52 bds_52 206 (dagTraceF m_52 s_52 8 f_52) l_52) i = true := nj_52_6
theorem lb_52 : LowerBin m_52 s_52 g_52 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_52 sub_52 gl_52 rc_52 nc_52

def m_53 : Nat := 0xff00ff00ff00ff
def s_53 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_53 : Nat := 0x1700570057007f
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_23, s_23, 6, g_23), (m_26, s_26, 6, g_26), (m_21, s_21, 5, g_21), (m_30, s_30, 5, g_30), (m_32, s_32, 5, g_32), (m_41, s_41, 5, g_41), (m_42, s_42, 5, g_42), (m_3, s_3, 4, g_3), (m_7, s_7, 4, g_7), (m_14, s_14, 4, g_14)]
theorem kn_53 : KnownBin bds_53 := by
  intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_23
  · exact lb_26
  · exact lb_21
  · exact lb_30
  · exact lb_32
  · exact lb_41
  · exact lb_42
  · exact lb_3
  · exact lb_7
  · exact lb_14
theorem sub_53 : ∀ b ∈ bds_53, m_53 &&& b.1 = b.1 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_53 : ∀ b ∈ bds_53, canon b.1 g_53 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_53 : Nat → Nat × Nat := unpackForestF 0xad24500b4fa6a5fa6a5daa46caa160aa060a6a57a9154a695ba6953a7854a685ba685300b47a5c5ea4b55a4b4500a4f9a35f9a35da1c6ca1960a18609a357a0c5e9a34d9f35c9f26c9a3479db4e9da5e9a3459c9549a15b9a1539b0549a05b9a05300a4798b5498a547245f97d6c7245b96b567245a9336c9326c9316c931609306c93060724578bc5e8bb5e8ba5e8b95e8fb5c8fa5c8b9528e05c8e0508b85e8c35c8c25c8c15c8b852724568ab5c87d6487b5c879388793487838878347245385b4985b4185a5e7235682b4982b4182a5e82a4682a447225681048810447214f7da5c7d9447d9347d8187e14c7d8147214b7c35c7c25c721477b14c7aa547214379148791447204f7595c75844758347582c7604c758247204b7435c7425c720477304c729547204300a377125d6d3457035d6d2456dc586dc546db546da546d2370094f6c3470094b6b2456635d6a3456625d68c6c68c6066237679276605c66a3766050009476515c5c34763a4d63a355c1466223f622375c1446034a60346602465c1365ea3b5ea375c1345da375c0185ca375c014009435ac6c5a96c55b5759a5d55a5658a5d559565635a563565625656156559360093b54a4d009375336c5316c4dc575235d4da564da4650b5d4d9564e45a4e4564e3564e1564d9460092b4c34a4c14a009274b25d473454a35d4724547c5847c5447b5447a54472370084f463470084b452454035d443454025d42c6c42c6040237419274015c40a3740150008473f05c363473da4d3da35360463c23f3c237360443a34a3a3463a2463603638a3b38a373603437a373602c36a37360240084334c6c3486c2fb5733a5d2f95632a5d2f8563035a3035630256300562f8360083b2ca4d2d3502d3482d25c2c927008372b36c2b06c25c572a35d259562594628b5d258562645a264562635626056258460082b2234a23350233482325c221472204a008272115c1e3472024d1e1461eb4a1eb461e1360081f1d05c1a3471c24d1a0461ab4a1ab461a0360081b19347008171806c014571706c013571605c013471524d012461434a0123611a4d122381214c11926011460f34a0fa380f94c0f146011360e04c0da37011240b35d0b3450b25d0b2450105606c5a09a5c06c5606b5606a4d06a3506926068260104601b5a0535c01b5601b4a01b4601a5601a46019460184601036008130001f 9 11
def l_53 : Nat → Nat → Option Nat := unpackLinksF 0x8501090a0f1c16482c10506090c08581010186030406080830101f37be607c82f901f013da37a48f481e80bce1788af101e10bc207840ef0dde03bc076c6ed81da0bb407680ec85d90394f7280e501c6238a17048e081bf137e06fc0df81bf037e06fc0dba1b7036a26cc4d889b1036206b86d701ae035826b00d601ac035236850d081a00b4006800d001a0034006610cc01980330064cac981930326064c0c9818e2b1c06380c58d89131206240c481890310160cac18183030036000bf857e0afc05f80bd8d7912f205e40bc817902f015ccab9817302e035c00b7856e0aa5c5480a78d4f029835300a6014c029805208a28d45028815100a08d41027c34f809f013a227404e429c81380a6274c4095992b025604a06940128024c249809301260246348c091812112420480290011f0a30746008c01142228044848901101220044008801100218441ca8289012202040407e90fd01f623ec07d80f911f203e407c80f901ea43c0a7708ee01d443a80738ce701c8339007200e401c8038086e8cdd01b8137006c8cd901ac335806b00d221a4034426880d00992732406198c30186030066000c0017c22f805f00be017632ec05d80b9117202e025c00b7096072c005800ac215802a845500a8115002a005400a80148427ca4e889d0138126c24b90932126024c047908f011a2234046808b1116022c045808b010e4208a40088000fe11f823d107a00ec41d803a087400e421c8039007010da31b4035886b00d221a4034806710c8318c230886100ba417402c905808a651482278c4e08963128225004a0090211462204440088010841f8c3f007c10f421e803d007a00f401b9837006e00d821b0036006c00d801b002e405c00b8016842d005a00b4016802d005a009500d2c01c8001 0xa0255ad245912649da4485a34912569f246539292b8298fa5c8ca5cab46c9fb6c9125caa960aa060a9154a7854ac25faba5da9a578b255a524d9ea479d24585235a895ba81535292ba705ba68532a82b17813a5c5ea5355a4b4591b649e35483a349fb5691b465b139350399035c8d35ca2c6c91b5c9f26ca2160a1860a0c5e9fb5c9f26c832349e34e9da5e82a349c9549b054a3b5fa335da13578b355a034d9eb479d345822369c15b9b9535a13b9a85b9a0533403b1681397c6896c549935498a548ab5497d6c9256486c6484a6496b5692355924588a45095b6c9526c9496c941609386c93060901508d0508f9508c8508e85c8c0509035c8fa5c8e05c8e85c8e0508d35c8ca5c8c15c9245e89c5d91b5e9125e9095e8f1528d85e8b8528ab5c8a5648646489b5c842648913888934880388783486b498634185a5e8324682a4484b498434183a5e8324682a448015881848810447b1447e0147e14c8025c7f9447f1347e8187d8147cb5c7c25c7a9407b14c7aa5479948791447805873044760147604c7815c77844770347682c7582474b5c7425c728407304c729549845f9745b9645a92c578b4568745385356822566d15f6c15b68157649538094f7d14b7b9477a1434705f4605b420573e8537884f7504b73847720432081f1c81b19017158137125d6ea556e2357035d6eb556da366f4586ec546e3546da5470b456fa456d2376c3476924d6b2455212a6934d6a3455993a6946c68c606786c668606792766a376ab5d69a5d682375913a5192a6705c660506515c6095463944601345d8185c8146424d60a4563a3562a3f622376134a60b46602465f23b5ea375da375ca3764b4763146619445f9365e1345d0185c0145b46c5a96c571645693459a5d5612658a5d5725557b5a5735656a56561565a357592564c2365815655936230251501154a4d5112a228271481153b6c5316c4f1644e9445235d4e13650b5d4f3554fc5a4f4564eb564e15652c5751a5651246501564d9462d845140114cb4a4c14a2c847138114b25d48a55482354a35d48b5547a364945848c544835447a544ab4549a4547237463474324d452452a02a4334d443453383a4346c42c604196c409604192740a3744b5d43a5d422374115c401503303a2982a3f05c3a8543d8443a0343782c368243e24d3aa453da353ca3f3c2373b34a3ab463a2463923b38a3737a3736a373eb473d0463b84439836380343702c360243546c3486c310643083433a5d3002632a5d3125531b5a3135630a5630056343573315622136320562f8362d1251301212810120102e3502db482d25c118102ea4d2c9272902a110122bb6c2b06c27064268442a35d2603628b5d2735527c5a2745626b56260562ac57299562914628056258462394510812100100f8102435023b482325c0f01024b4a229472204a0e8122115c1e9542024d1ea451f34a1eb4620b471f9461e1361d05c1a8541c24d1aa451b34a1ab461cb471b8461a0360d810193470d0101806c090640c054088441706c048640b054030340e0140d9241605c0385407844028340f9241524d0f12602026129441434a11946070461212412a381214c1324d119260182610144102380f94c10b4a0f146068460e04c0da370cb5d093550c3450ba5d04a550b24509a5c0a45a0945608b560824d03a4507a3507126068260535c05b5a04b560434a03b460325602a46021460184617c5716b5715b4714a4613a36111460e9360d1240a8560604601036acb4fa6347a424f99a4771a376c94f6b94b659475b9435513b541374d12b4b9274684f4584b3f847358432f03b2c0372502b218271d81f1981b18817008130001f 15 5 11 9 6
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsF m_53 g_53 bds_53 (dagRefF 347 (dagTraceF m_53 s_53 8 f_53) l_53 0) s_53 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53_0 : treeBlockF 0 32 (dagCheckNodeF m_53 g_53 bds_53 347 (dagTraceF m_53 s_53 8 f_53) l_53) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53_1 : treeBlockF 32 64 (dagCheckNodeF m_53 g_53 bds_53 347 (dagTraceF m_53 s_53 8 f_53) l_53) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53_2 : treeBlockF 64 96 (dagCheckNodeF m_53 g_53 bds_53 347 (dagTraceF m_53 s_53 8 f_53) l_53) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53_3 : treeBlockF 96 128 (dagCheckNodeF m_53 g_53 bds_53 347 (dagTraceF m_53 s_53 8 f_53) l_53) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53_4 : treeBlockF 128 160 (dagCheckNodeF m_53 g_53 bds_53 347 (dagTraceF m_53 s_53 8 f_53) l_53) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53_5 : treeBlockF 160 192 (dagCheckNodeF m_53 g_53 bds_53 347 (dagTraceF m_53 s_53 8 f_53) l_53) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53_6 : treeBlockF 192 224 (dagCheckNodeF m_53 g_53 bds_53 347 (dagTraceF m_53 s_53 8 f_53) l_53) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53_7 : treeBlockF 224 256 (dagCheckNodeF m_53 g_53 bds_53 347 (dagTraceF m_53 s_53 8 f_53) l_53) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53_8 : treeBlockF 256 288 (dagCheckNodeF m_53 g_53 bds_53 347 (dagTraceF m_53 s_53 8 f_53) l_53) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53_9 : treeBlockF 288 320 (dagCheckNodeF m_53 g_53 bds_53 347 (dagTraceF m_53 s_53 8 f_53) l_53) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53_10 : treeBlockF 320 347 (dagCheckNodeF m_53 g_53 bds_53 347 (dagTraceF m_53 s_53 8 f_53) l_53) = true := by decide +kernel
theorem nj_53_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_53 g_53 bds_53 347 (dagTraceF m_53 s_53 8 f_53) l_53) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_53_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_53_1 h1 h2)
theorem nj_53_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_53 g_53 bds_53 347 (dagTraceF m_53 s_53 8 f_53) l_53) i = true := block_join nj_53_1 (fun _ h1 h2 => treeBlockF_at nb_53_2 h1 h2)
theorem nj_53_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_53 g_53 bds_53 347 (dagTraceF m_53 s_53 8 f_53) l_53) i = true := block_join nj_53_2 (fun _ h1 h2 => treeBlockF_at nb_53_3 h1 h2)
theorem nj_53_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_53 g_53 bds_53 347 (dagTraceF m_53 s_53 8 f_53) l_53) i = true := block_join nj_53_3 (fun _ h1 h2 => treeBlockF_at nb_53_4 h1 h2)
theorem nj_53_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_53 g_53 bds_53 347 (dagTraceF m_53 s_53 8 f_53) l_53) i = true := block_join nj_53_4 (fun _ h1 h2 => treeBlockF_at nb_53_5 h1 h2)
theorem nj_53_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_53 g_53 bds_53 347 (dagTraceF m_53 s_53 8 f_53) l_53) i = true := block_join nj_53_5 (fun _ h1 h2 => treeBlockF_at nb_53_6 h1 h2)
theorem nj_53_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_53 g_53 bds_53 347 (dagTraceF m_53 s_53 8 f_53) l_53) i = true := block_join nj_53_6 (fun _ h1 h2 => treeBlockF_at nb_53_7 h1 h2)
theorem nj_53_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_53 g_53 bds_53 347 (dagTraceF m_53 s_53 8 f_53) l_53) i = true := block_join nj_53_7 (fun _ h1 h2 => treeBlockF_at nb_53_8 h1 h2)
theorem nj_53_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_53 g_53 bds_53 347 (dagTraceF m_53 s_53 8 f_53) l_53) i = true := block_join nj_53_8 (fun _ h1 h2 => treeBlockF_at nb_53_9 h1 h2)
theorem nj_53_10 : ∀ i, 0 ≤ i → i < 347 → (dagCheckNodeF m_53 g_53 bds_53 347 (dagTraceF m_53 s_53 8 f_53) l_53) i = true := block_join nj_53_9 (fun _ h1 h2 => treeBlockF_at nb_53_10 h1 h2)
theorem nc_53 : ∀ i, 0 ≤ i → i < 347 → (dagCheckNodeF m_53 g_53 bds_53 347 (dagTraceF m_53 s_53 8 f_53) l_53) i = true := nj_53_10
theorem lb_53 : LowerBin m_53 s_53 g_53 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_53 sub_53 gl_53 rc_53 nc_53

def m_54 : Nat := 0xffff0000ffff0000
def s_54 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_54 : Nat := 0x117000011570000
def bds_54 : List (Nat × List Nat × Nat × Nat) := [(m_43, s_43, 7, g_43)]
theorem kn_54 : KnownBin bds_54 := by
  intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_43
theorem sub_54 : ∀ b ∈ bds_54, m_54 &&& b.1 = b.1 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_54 : ∀ b ∈ bds_54, canon b.1 g_54 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_54 : Nat → Nat × Nat := fun _ => (0, 0)
def l_54 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsF m_54 g_54 bds_54 (dagRefF 0 (dagTraceF m_54 s_54 7 f_54) l_54 0) s_54 7 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_54 g_54 bds_54 0 (dagTraceF m_54 s_54 7 f_54) l_54 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_54 : LowerBin m_54 s_54 g_54 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_54 sub_54 gl_54 rc_54 nc_54

def m_55 : Nat := 0xffff0000ffff
def s_55 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_55 : Nat := 0x175700003f7f
def bds_55 : List (Nat × List Nat × Nat × Nat) := [(m_31, s_31, 5, g_31), (m_32, s_32, 5, g_32), (m_44, s_44, 5, g_44), (m_2, s_2, 4, g_2)]
theorem kn_55 : KnownBin bds_55 := by
  intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_31
  · exact lb_32
  · exact lb_44
  · exact lb_2
theorem sub_55 : ∀ b ∈ bds_55, m_55 &&& b.1 = b.1 := by intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_55 : ∀ b ∈ bds_55, canon b.1 g_55 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def f_55 : Nat → Nat × Nat := unpackForestF 0x63f18ee04c18dcb4458d0a5438d082418cc01f 4 10
def l_55 : Nat → Nat → Option Nat := unpackLinksF 0xe1c3862a5424c882ac601 0x68c204c5910c2458d0e346d112542092a3f98ede3718cc01f 7 3 10 4 4
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsF m_55 g_55 bds_55 (dagRefF 11 (dagTraceF m_55 s_55 6 f_55) l_55 0) s_55 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_0 : treeBlockF 0 11 (dagCheckNodeF m_55 g_55 bds_55 11 (dagTraceF m_55 s_55 6 f_55) l_55) = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 11 → (dagCheckNodeF m_55 g_55 bds_55 11 (dagTraceF m_55 s_55 6 f_55) l_55) i = true := fun _ h1 h2 => treeBlockF_at nb_55_0 h1 h2
theorem lb_55 : LowerBin m_55 s_55 g_55 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_55 sub_55 gl_55 rc_55 nc_55

def m_56 : Nat := 0xffffffff00000000
def s_56 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_56 : Nat := 0x117175700000000
def bds_56 : List (Nat × List Nat × Nat × Nat) := [(m_33, s_33, 7, g_33), (m_40, s_40, 7, g_40), (m_43, s_43, 7, g_43), (m_35, s_35, 5, g_35), (m_36, s_36, 5, g_36), (m_37, s_37, 5, g_37), (m_38, s_38, 5, g_38), (m_41, s_41, 5, g_41), (m_44, s_44, 5, g_44), (m_4, s_4, 4, g_4)]
theorem kn_56 : KnownBin bds_56 := by
  intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_33
  · exact lb_40
  · exact lb_43
  · exact lb_35
  · exact lb_36
  · exact lb_37
  · exact lb_38
  · exact lb_41
  · exact lb_44
  · exact lb_4
theorem sub_56 : ∀ b ∈ bds_56, m_56 &&& b.1 = b.1 := by intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_56 : ∀ b ∈ bds_56, canon b.1 g_56 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_56 : Nat → Nat × Nat := unpackForestF 0x244924c8924591228b224114005a7c7835d90e24b21c0963c11dc7823990947321253642426c782378f046b1fc9364141247f2419036991fc8e6404124802308fe46b1fc1363c09bc781358f249b1f44923c920c7c34c8f24731ec4923d5184792358f229b1e44d63c01bc780350016871da4d63b41ac6c34b8d86931d25b63a436c6c3478d868b1c4d763962e4713498e268b1c4176360a3c6c1458da6bb1bd172369a4c6d3458da2bb1b451636023c6c04500149f17e976350a2c6a0458bf49f17e93a340aec6805d8bf48f17e91a325ad4662588c94bd19295a3241ec5f9278bf24b182d6a3152c460a5e8c14ad1824f630492c5f8278bf04a00290e291af4523528a44bd1709122e092c5c0258a44a71648d62d5224591278b348916409e2912945804d8a426f158d4a2b6304562538a426b1525362a49ac520378a56a514d18229529c5203500147f0c717a27d2244f94589f08b0c714e259a3c4b24789648d12c9162652244b14789748912c11e18e294499558930ab0c6d7e240a2c4804586369f0c6d3a2362f431b4d88a2ab11415618d2fc4294f88528f10a13e21423c31a5e8634a510514a18d23431a3e87f4a90f358a1f6b043cb6287b4c10f29ba1e41ec319278738a70e6d7e1cda7c3a4518734a50c64961c52a43556286fac10d4d8a1b53043526e86a27b0d449618c13c324538646bf0c8d3e19628c3225286304a0028ee0f22f42f93585f06b07914e1689fc2d13785a07f0b40de0f22942b35c85626b0ac0d60f1a9c2992585304b07894e0f11f42845283c47309758a13630425c6e84b08b07853e11e2f423b538474a7078536106b14224608418dd082576104a2c1e04f83d8bd07ad4e0f529c1e04d00146ef9b17a0e5a23e6c528354a906a5560d42abe6b5f82d48d062d720c52241694782e6b905c9120b423be6b5e82b688f9ad4a09d2e41395d8270baf9ad1e0889fc1113782207f0440de085263e6b468188a5032d3e065a1c0c93f81926f0320fe0641bc0c24c7cd68afe0d3a0509ac0a0357f068701e4fe03c9bc0783f80f06efe0d0a0309ac060357f047f00a93e01521c0292f80524f00a0be01413bf823e80027f0004de0001fc000377f047aff3149ff1a83fe2447f96bcff2935fe41abf813f7f18a4fead41fd5223f8b5e7f149afe2535fc49abf803f7cd688f9a979fb0923f60247cd4a4f9a939f3526bf3c527e74bcf9a8f9f95a23e6a3d7e169cfc2939f84a73ef4547df8a8fbc0f5f3493bed35f7da68efb4949f3492beb34e7d649cfac139f4a2a3ea4547d227afa4495f3413be735f7ce68ef9c949f3412800a337c9472f928d5f241abb6b4b76d692f869b5f15363e1a617c30daedad1ddb5a2be03447ba8b2f7cdb1eea2abde3587ba48cf74095db525bb6a497b06daf6b1b1ed51c3d83497b34c0f60d15ec124bd806d76d48eeda915ea9ab3d53547ab6b0f540d5db51fbcf34d79e4baf4c091e792d3cf25679e4aaf3c951e79233cf12679f4b0f3c095db51dbc9c5a7938b2f27161e4e2b3cc35c7938a2f268e5e4ca73ca45479309aeda8dde45263c234578c692f18d05e311f3c613e784688f089b1e112b3c22547874a8f088f9e152c3c202576d466ef2d75e062e3bcb4977968aef2975de528bbe35c779492ef4901de522bb68477776b8edc8fddd52e3b723b7738a0edc8dddbda23b7a6c76f4b8edc8cddb42280094f73b6bce76d49d99ab3b33547676b8ecc155ced2fbaf26d75e4aaebc951d7922baf24475f490ebc095ced29bada4475b04ae7692dd61ae3ac05d73b48eeac095ced1dbaa25e73b472ea28e5d442eb9da3774f8a4e768d5d3494b9d95e74649ae8c905d25a63a3239747460e8c8d5cec1bb9e3527436b0e7897dd012a3a024c73c4a6e7892dcf123b9e15e73b06a0024fdb062f39aa39737078e6a8d5cd41ab60c5372847ee64d31ca11db9804c72846ee5c8f1cada239623472b048e508cdca01fb940376c18a4e46d71c8d1cb91a3572306ad82d4dc722d38e45971c8b0e39159c762838e0556c14bee09585c61a538c346704ac0e2d5a1c1136b8225e7044bae08971c442e38225570fac0e08935c35a738224c70b8c0e08915c1eb038394c707288e08499c15283820256c14a6e048e1be6b13804606f96dcdfcd71be5b137ca6e6fbac0df2989be41ab60a4f6f6688dec8e1bca29b7935e6f346ade4949b0526b783446e5ac4dcadb9bb6b0372b626eb8c0dca9b9ba12e3740246e54c4dca975b9412b60a436e2688dc4911b7a29b702466de6bcdbc979b0520b6db5c6db06ad828fdb612e36c0256c1466dac095b049f3665626d38c0d991b9b312eb662516cf6b8d98925b35203662456c109ed85179b09a9b644546c24bed8a951b15263612536c247ed848cdb04268009376bd4aad7c971af42ab2bc5f6b18dad62d29ac5a335c23d6b1688d62929ac523358a456b1488d64931ac422b2bc536aa8b2d55155ab02f3560526aa4a8d5415595dafb52c6e6a78a4d4a911a9422b2bb4f6a0ac4d44d79a812e35005d65768ed39165a722ab4e0556574bed16d3da662e345b4b68b68ed2cd71a522a34a23468b686d22db1a45ae345a3f68e8c0d1d141a2d1bb4584f68b08ecae97995d2934146e687488d05189a122a34236c6824dcd0411595d27b2ba4e67f4bccae9299deb733bd6267a8c0cf4d619dd3733ba4e6770bacae91d9ca29339c586736b0ce497d95d2332ba4266f268cd88fd9b4a63362376572bccc4d89989ad3313526674c0cc49b99952c33125e663480cc495995c13b2c45f65e688cbc92196229b2c35f65869ecb0d1d9612932c15e65704a0024bd94dacb2a3506530aab8d17d90e36b21b4a643692c86d2193426321b46643494c948f990d24321a46646270c8c4d190ca332234064308ab8d14d719af31e56163c4bcc7c1718f12b31e0255c66a6c70d298e1a331c1466288a2c6d5818a127b1a35c628496c631818c42e31424762f498c56d518ad2631624462b048c5090d8a017b140275c66a4b8cd39876b730ed62622ac0c449718763131036061d4dcc3a98987412ae334b61b48cc331498652f2e334a6138a4c2a0fd8541bb09c50613098b8cd1981ab730356260eac0c1cd5181a313063606064dcc129318241230326260649ac0c095719a1ae33425fd8b4c02d61805a42fea5e5fd4acbfa9317f412ae32535f0adcbe15897e6b02f84625f76c0be09b97ca2f2f94525f24bcbe49497c1262f80255c6496bc75b978eb12f65605e38c4bd4d8178d372f2c5e5e58a4bca979795292f1a4c5e304ab8c90d76a2faf01445da8a6bbc91177628aed3525db6a4bb4055718972e84625d08b4ba1149755b02e836e5d36b0ba0d79745a02e83565c607eb8f17d731a22e62485c78a6b8ed7971d29ae3a4b5c7486b8c0f400493ae12395c246ab844d549da5a93b495bc4dab7c9b16f130ade16d52768ea4ed156e5a22d9c595b76d8b671556d5ac2d9a465b324aa4e92d49d24ad4b6d5ae8d8b5c8e16a5a4ad62605a968ab529256a4b6a93a4752748ab46d5968daa2d23585a326aa4e8fd65da6acba5d59f248b2e96965d2b2cba555974a8b2e9196652c2cb92559704ca4e8ed6322d2c645958c8b0b19159645ae2c645158c472b1d151630a6ac604e52746eb149315f5a2ac2b49585682b0a8f96141f2beb4457d4d8afa9595f52a2c025457d47cafc9615f492a93a335726daaf51b15c9a4ab93455724daae49855d5b62b92495734a0ae491549ca3ab836c56747eadc9b159d1dab646056746ead0d115a1362b425c567466a4e515571ab2ae354563488ab8965585b62ae25555f4a8ab88e55762c2ae23552727ea9516952a2caa545854a8acaacd7152a28aaa25c54a4b2aa51815292aaa7b5454f4b0a94935531aa2a625454a482a9413949c9baa424453b8b2a8c9b14ee2aa9da5d5434a8a769694ed2b29da5553b4a8a7c9514ed2529e45853b48ca4e4bd4e5a42944595376c0a511554a1ad2943595286b0a50d594c52629435152e8b0a5c9514a1a5295c6052b8b0a50d194a09729403e52724e00213d2e1af25c3525206aca40d51485ae2901554b84bea309b54612aa8c25451848aa309114652428c1254b84a6a2a91145492a5c24b5126b8a245752e123a881254b8476a1c9792e11ca85a3950b2ba9708dd4262925c2354fe6ac9fcd514152227f2595036d89fc9554052a27f2394ff8b09fc8d52e0afa7a35c4f44ba9e89453e1ae27c25c4f44729eb1413d52027a2354b828e9da9753b528a7835c4ed4729dc9013b51aa5c1374e48a49d51613912fa73a5c4e74889c894d3911da722374b826a9a71b938522269c624df6a89a69b937522269a624d349a9b491134d25269a464d348a9ab17935629269a444d32dc9704bd302372683484c08c499cd51301b7265c6c4cb488980d89301a52603494c64bc98c949301a42603464c3498980d053009726003e4b824e9724a52e412a5c81f4ba4b09748e12e40ba5c05e00107e7eb1792c91ca5a13c4b246a9644d4fd629a52a3f4af69894a8ed2b4a6252a374ab478950d112a51a2541244a546694a4fd2949b9fac524a06b89408e52811aa501353f56a69331692662ca4cc584998ac935141264aa9faa5f481ac292ad29255a3240d60493ad09029b52052f240a5d4814b891c5712052aa4656048149a914d392052624446048148a90c94120492a41560482298904511204131faa5347f4708ed5891f63023b36e47b6b88ecd891d93723c5604764c48ec4d4fd527a39b444734708df14d1bdaf23823546f4a47ea9351b5a22315624626dc8d5581189b12344604624dc8ca971194922312624624ba8c4494fd521a2fb4445f4888b714d1752322db5e45b4bc7ea905161ae22c1353f547e8aa971154929faa334468b488d16511a2c22345644f4b888c9651363022325544a6a889496111926a23b544474a888c904fd4afa1cd624438c0872db9105ae21cb624394ba8729450f5ae21ca3943b4808728d50e4b71fa94f42f8a685ed790d5aa217a5f4324b88649110bd29a17a4f42f4867ea535095ae212a5d4254a2852d710a52e212a394268a084c9010951a9fa93f4234a881f5b908522207d6241e8c083d16103d3720e25c40f4c481e97903d2ea0bb5e4176a481e97103d2aa0a25c40f4a4823161044a620796e40f2bc7ea4bd035ac1fdd6e40b6907f75890262c1fdb6e406ac080c970fedb11fdb5e4034987f6d64feda91fdb513fe4bc7fc948feda81fe3503fb25c7ea49cfd8129fb01f3f74a07ec05cfd41f0008373f14aa7e4970fc4aa9a145f3e58da7cad28f95a31f623d3e56887ca928f95231f2a453e54887cc930f94a29a14533de8b27bd154f80af1f01523de4a87bc554d09af9ecc6e3db8a47b2910f64a29a134f3d4ac47acd78f512e1ea15d34268e7a1164f422a9e81553424be77ed3cf362e1dfb4b3bf68e794d70f222a1e42343bf68678adb0f15ae1dfa3f3c28c0785140efd1b9df94f3bf28e684978d09291db46e3bb48876d188ee22a1dc36c3b64dc76c514d09279a124e3b34bc684928eaeb71d5d623ae8c075cd60ead371d5a4e3ab2ba68491ce9a291d3c583a76b074c97cd09231a12423a3488731164e85361cc4553984b4730958e612a9cc25439b4a8730928e662c1cc2463422be7131b8e55221c4c623936a87129b8e45221c4a62389494712918e25229c5c5e38b8a4712910e24b71a114f3874a86ef5b8e15221bbd623828c0705160ddd371c025c3774c46ee978ddd2e9bdb5e37b6a46ee970ddd291bb94e3770bc68451cda2311b445a3688a46e4d80da1371b7b5836f6906d0978db1a81b63403684ac6d2578da4a91b424c34226e6cc950d62371ac4623634886b1178d622d1b025c3588ac6b1148d75b01ac26e35b6b06b0978d65a01ac25634224e69f17cd51a41aa24434f8a669ed48d3d2f9a7a4f34f48e684494d349a1a1a3f34b2986868dcd0c1f9a3c583472986860dcd149e1a182734302a6841780041799f35933f6a067c5549862f99746d32e69465cd24cb9a419c14c32e68c65c928cd51f19724832e48c664d00cb8a299793832f26865c11898629930b5e327ac264e978ca4ae193a5632724a4c2d4cc8da5191b4632308c627144c86b0189a4f31f6b862692cc723018e15c31348e634930c59aa18b24c31748862c490c4d2198992f31324e4c2d48985a718456e308ac461b580c352e18446230b6c06109b8c213118412526169660c918c122918225e2616945fd148c009f9801372fe8a05fc530985a3178d6e2f1ac45f3580be5aa178c622f76c05e29b8bd12617a1242f14c45e2934bc492930b432616845d1168bb1ac1763482e84bc5d0958ba1261741252614a65b75b8b6eb11725602db8c45c4d80b6d3716ec5e2dd8a45ba978b752916da4c2db24a4c292cb3ab71675622d7ac059d188b55b016726e2d08bc5a1148b412f1682522ce49859c494985219663482bf8b2594d80afe2a95fb5a2bf6b257ed60afdab161c582c34a857ed28b02301604582bf68c4c257cab63715e3482ad8c4574d50ab5b715bc6c2b748855ad88ab5a5156b492b24bc564948ab5a4156b462ae4b055c8e0ab4b713094f2ab6b05375b8aa5a414dd622a78b0536db8a92b015225c29b6c4536d78a6da914db5129e4bc53c948a6da814e25029b29c4c251ca2631144c5a2898a452cd80a253714a24c2894c4524d60a252f14824c2894b451cd00a252b14624c2894a45125b8a24af13093f2808be50ad20a15221404532806a6500d2ca01a194025e26127a4df1889be2d137c5227b6c04de9b89e1ac13c34826f4bc4ead409d5a0137a562722bc4e45489bd2613813c26f2dc4c24bc98a2f9361442628a64d49109a6289313522620be4c413c995a81310472634a44c40549841700082725f4704b6d649752812db5525b4b200517c9323692c23824c6924ac900931a292624a24c4924989209412612824024c48c4985189341a1260460028a649492090e2c9242602438aa48696890d2c921a582434ac004d7c9053411a36d23f490468d788f52811a3562344744688e48d11c11c35823446c4684d88d41211a0360026a64451b88c52411146222f4b0444db88b51c11136222249444492489daf113b522272bc44492088923111146223068444118009a790556e21f4b041558882a2f10e25820a8ba434960829b710c23820a6c4414d58829a710523a20a47241f17883e29107b4e20f2bc4148e08291b10513620b0484140d8009a59042581fcadc40c9207f2b10fe34e1fc6923f89787f1290fe2511fd69c3fad247f4af0fe25000268e37b5b87e5200fbc541f74b037b5887d52c0dec6e1f34803e31507c5240dec621ee6b83dc9406f62b0f5b5c1eb4a037b1547a5240ef45e1e74903bd148779a70f22481de69a3bc938779210ef2411df29c3bc9006f62a0deb6e1db47037ad886f5af0ec2581bd6ba37ad387522a0ea2481bd69a3a45007462a0dea3a1bd47239517872a290e535e1ca6a43945786f51c0e43401c58a838d150715b00dea361c32803851506f49b0e01401be8a837c0906f41b0013431bb6a83628fc6e52a0d8a3b1b78b03628dc6d5a40d93441b24d83649506c51980125e1a6ac234d184698af0d5b5c1ab6a034c558698a70d3c581a78a034c518009298d0b491a148c3444d0684230b045119c6bc3388d8674920ce0361606a232f1b065db00cb9481972882c0d3c64ab00c936c1922703244d0581a58c756018e2b831c540581a38c15601828c0313140624a00c14541826c03044e060e280c1b501836883044d0581a18c056016029e2fc970580a58bcc601796b82f51405e5a80b01471766802ec5305c92a0b914c1732882e4510580a18b846016027e2dc9305809d8b4c581698a02d51405a5b00b01371666802cc4f0585220b095c1634602c44d0584aa0b01330024a400493854ab70a95621528b22a5144562b00ac15c1526c42ac980548b70a916215229c2a4518009258a7b4914f28c2831485322c0a61541416be2944d0505a98a245e1448a4288d78511a90a21361416822848c4504af00124a12f8a42768fc4ed1d89da3713b46625f1404e23009c45812f4be2655804c92e099c501336982649304bd29897a4c12f480004918472b708e56211c8b223914449eb00943401274a8238d884953008e16e1212982425104849e08e16211c29c23cd40470a308e13d0024862344d8465a48012421128be22ad10455220894531136a22249780091f07cc6e0f98c41f31783e629085c6010b2981f2d884222808414c0f96b420b140414a607cb521034c01f25b84049e07c9620ff4b01f25783f62807c95a0fb4801f25583e4a900123b0f76b01d317c3d4a2074c530f269c1e44d83a5a907645e0ec8a41d8d783b1a90761360e96841d48c83a4af00123a0d88be1c8d203951e0722480d88a61c31743862886c3520db49e1b692c36d2386e24c0db4861b0d40361a406c34000246c16b1b82d63105ac5e0b58a41a1180345a00682440b56c419b1403352205ab5a0ca8a01949102d5a90642600b52dc188570310aa06213c0b52c41829603052405a95e0bf27816a5682e9a005e3400ba4a01749002d4ab05b96c0b727816a5482d49e8012330b36a814b17c2c4a2052c530ae69215c518295af054b5e0ab268152d482a49b052b4e0a66ba14c8f8294af00123209368a126914281aa05013809347e13a95027494049a3b09b2801268dc2649804b3440964d812c95024d1984a23e0932440045782452e04803e07e8a411cd701f9a983f25f087ac010e97021d260444500872500fc94c211af04225207e49a104d701f91f84025c07e4660fc4c0008a303245f0796900f29201e4a40324530772900e91441d4ae03a02e0646a40e31481c52f03234a06f4980c894c1b52603224b06b4980c890c195a78341340656860ccd041952103212000226c092d141252282fb5405f2700928fc1712a02e1280494760b45001251b82c1300556880aa9b01552a024a3305347c09248813da402794504f27a0920d8129a282524804a4740940401241300105e0474b808c0f80a62902235c0296a605297c0f6b001ea5c03d49807d1400f494014a5303a6bc0749480a52681c35c02947e06c9700a5198149300316900625140c49e81485e02a8a405d1400a92901594e02b2840549000a4130010460038be048d20091240121480038a604452007e2881015c01f05c006d480722900e25e00369403493000d2980c24c00349602c93000d2180834f013068020d0c045a0808242003240016d1402d24005a3a00b020006178012290044500044a400a538014a100224000308c0040d80040b80001f 12 11
def l_56 : Nat → Nat → Option Nat := unpackLinksF 0x1174062e60c5c428b78515e462b22c56018ab8314b3228c2c51808a3011460226e7c4c468980312f0625a144b408958512b022540c4a028940111c3222e2c458188a831130a226044442888811100621c14438088683101321f82c38d9871810e3021be24370386e010dc021ac3434c3868850d1021a00c3400868010c8221862c3042860810c006180043000860010b8221662c269984a8b094061260c23468440b08802110041f8a83c0d077060ee041d4283a03074020d454194583203064020c414184183081060060ac54144581c33034120660c0c818190103202064040b458158502b020540c0a80814830251204a040844810030200203e0c064680c81018060282404c1809810120601833fc5b7f706fee01fdc03fb807f48afe901fd203f9c27f284fe501fc80bf9007f182fd82dfb003f6007ea08fd401fa803f3c57e684fcd01f902bf2007e400fc219f820bf0407e002fc001f723bee017dc00fb315f6213ec407d784faf01f5a13eb407d602fac01f464be8817d100fa201f4403e8417cd0ef9a01f3013e6007cb04f9601f2a0be5407ca02f8b25f140be2807c500f8a01f120be0877b2baf6309ec40bd8417ac90f5709eac0bd5027a982f4929e9203d2407a480f4319e8603d0c079f88f3d09e7a03ce0579b04f3505e6613cc8179510f2a01e5403ca807918ef2109e400bc78278e82f1c05e2843c50078a00f1401e1a3bbc5c77688eec05dce2bb9c077380ee701dc42bb80277000ee001dbc13b78076f00edc09dae2bb58176a04ed401da803b5007678aecf01d9e03b3c076780eca15d9013b20076400ec801d9003b20076400ec801d7e4bae8575c82eb901d7203acc675902eb201d620bac407560aeac01d5803a90875200ea401d4803a90075200ea401d364ba6c074d80e9b01d3603a58574a82e9501d2a03a4c274980e9301d1253a20174400e8801d0c13a18074300e8601cf8539bcd7350ae6a01cd40399c373302e6409cc803990072f8ae5e05cb813970072e00e5c01cac33958072a82e5015ca003940072800e4a19c9403928072500e4419c880390c172102e3d15c7a038f4071e80e3719c32f385c270a84e1501c1e33834270602e0c01c1413828070092dfe0dbfc037ec36fd80dfa05bf4037e026fc00def25bda137ac26f580deb01bd01b7a006f382de701bce0377896ed86ddb01bb40b76806ec82dd025b9e0b73816e700dcc09b980373006e582dca05b940372806e482dba3db74036e416dc80db805b70036d826db00db505b6a036d016d1a2da301b440b68806d100da201b440366c76cc06d9801b2e0b65c06cb02d9601b2a0b62ca6c502d8a01b120b62406c402d8705b0e0361816c300d8505af6535ec06bd02d7a01af20b5e406bb84d7701aee035dc06ba06d7011aacd355026a904d5201aa40354806a882d4a1da940352806a482d4901a920352406a402d3f25a7e034fc069e06d3c01a78034e4369c80d3415a68034c0469800d3001a562b4ac069406d2801a482348c169102d2201a420b484069002d191da3203464068c02d1801a3003458268b00d1601a2c0343c767caccf7099ec0b3d8067a04cf4019d4533a0267382ce5099ca03388367100ce0099c00337c166e06cda099b403340a66782ccd099961332c066190cc20598403304166002cc00197e0b2c0f65704cae0195c032a0665400ca70594e0329c065302ca60194813290065104ca20193c23278064e04c9c0193803270064c86c99019300b20d564180c800d900031fc163f80c7e058fc031f8063e82c7d018e6531cc063980c71098e00b1c0063704c68198d003194363280c65018c80b190063182c63018c603184263080c61018ae5315c062b80c55098aa03150162a00c4f1589c0b138062508c490589203114462280c420d8820b104062002c3f0587c0b0f8061e82c3d018780b0c4b61880c3101862030c0161800c300185c130b8061700c2819820c3040060800c0f0580a53014060280c050180a03008360082c01018000affc15ff80bfe057dc82fb025f600bec017d802fa825f500be4197c412f8805ef86bdf017b232f5c25eb80bd40d7a802f3865e682bcc0579802f0c95e084bc00577e0aef815df00bbd0577a02ee835dd00bba0177012ee005dc00bb60976a0aed405d516ba80974e0ae9c05d302ba60174c02e9025d200b9c217360ae6c05cc84b99017300ae6005cc00b960972c02e5805c710b8e0171c02e3805c604b881171002e2005c382b870170c0ae0065bf82b7e056fa0adf405be02b7c016f60adec05bd02b70296e002dc005b800b6e096dc02db805b700b6e016dc02d9885a730b4e0169c02d34159f1eb3e0167c02cf8059e82b3d0167612ce4259c80b351166612ccc059980b300d66002cbc158b32b14096221ac40158800b0e0961c02c0cb58180b030160602be8957d00af8095ee0abd4257a80af5015e41abc8057804af0015e002bbc157588ae9095d202b6ce56d80adb015b40ab68056d00ad70d5ae02b58156b00ad60159852b30056504ac90558632b08156100ac20158012b00055e08abc015760aaec055d80ab80d57002adc155b80ab70156a12ad4055a80aab295540aaa0255400aa80154c12a98055282aa50153c3aa74154d84a9b015301aa60054b04a960152c02a58054b00a911552202a24854402a860950c02a0c354180a810950202a04054080a81014f82a9f0053a10a74014e60a9c4253880a70054dc129b8053682a661d4ca0a990153182a63014c40a988053082a61014c00a954b52a80a55014aa0294c252980a53014a60294c05268ca3561466128c4251880a2b19452128a0151400a260944c02874950d06a1a0142e1a85c050b02a160142812850050592a090940e1281c050380a040d4080280c150180a03013f44a7dc34fb809f6053ec027d414f6129eb053d40a7a804f4049e8013d00279c14f3029e6013ca0a79404eb1e9d6013aa0a75404ea029d4013a41274804e9009d1053a00a6fd14df809be0537c026f804df009be0136e3a6d034da009b305366026c814d9009b10534e5269814d3009a50534a0269014d1829a3013440a68804d0829972932e0265814cb009950532a0264c24c980993013260264034c60898c013180263004c58298b013140a62804c482989013100a5fc94bf8097f012fa125f014be0097b052f6025e424bc809760d2ec025d804b986973012e6025c424b880961412c20258014b00095f052bc0a57804ae8295d012ba0257404ae8095c052b80256c14a69c94d012961252c04a484949012920251c24a3029460128a0a51404a2809420d2840250804a00494001280024bd148ab49130922212444048880911012200a424748480909012100a4200484009080120e0a3f8947f008fe011f61a3ec047d808f80d1f0023cc5479808ef111de023bc04750a8ea011ce1a39c0473808e7011cc0a3980472828e5011c80a3900471828da251b402360246b048d6011ac02350246a008d4011a4123345466028cb05196023281465008c9051843a3080461008c10518202304045f848bf0117e022e0745b828b70116c0a2d8045a048b4011660a2c81459008b105162022c40458808b10115e122bc04501e89e0913c02274144e8089c0513802270044c868990113202264044c808960d12a0a254044a028940112802214f442808850110a02214044280883090fe221a5643384866050cc0219024320085a290b01215c142a84855010a41a1480428048500109e0a13034250484a01080520fc141e8483b09076020cc841902832010620a0c014180082f050407a078240f0081e0103032060040b828170102e02058140b00814090280204824090080e1101c0203024060080b050160202c0405808080cfe6a9fcc03f8067f000fde09fbc03f7027ee00fdc01fb413f6807e328fc601f8c03f0847e004fc001f7823ec0c7d800faa19f5403ea807d404fa801f4c13e9807d300fa211f4403e8807c728f8e01f1c03e2847c500f8809f1003df8a7be04f7c01ee843dc827b900f6a21ed403da807b308f6409ec803d8047b000f5a19eb403d6807aa0cf5401ea803d40479840f2e09e5c03cb0279600f2a09e5013c98279300f2409e4803c88279100f0c59e1803c30078600f0a09e1403c28078308f0601e0c03be8c77d00ef611de423bc8077900eee11ddc03bb8077508ee029dc003b78276f00ed819db003b6007690ced201da013b40076800ed001da003b28676404ec801d8c13b18076300ec211d8403a91e75200ea209d4403a68874d00e9809d2c13a58074710e8c09d1803a28274404e8609d0813a08273c14e7801cec13969c72d00e5a01cb40396027290ce22c1c4403888071004e0c51c1803830070600e0c01c0c33810270200e0209c001380006ff04dde81bb42376806ed00dda01bac2375806e518dc611b8c0370066e000db431b60236c006d50cdaa01b3c6367026cd04d9a01b109361046c104d8009afc135f806be04d7c01aec335d806bb00d7211ae4035c806b708d6c09ad80355966a908d5009aa00353826a700d4e01a9423528069d20d3809a70034d0469a00d3209a64034c8069708d2e01a5c03479068f00d1e01a3c03468468910d1201a2403440268800d0e09a1813430068600d0c01a1803428268500d08099d8e33a8267500ce8099d003390467200ce2099c013380067000ce0019c003370466e00cbe7997c032f0265e00cb61996c032d806580ccb00195c132b8065700cae0195c032a0665304ca60194c03221e64208c80118f8231f0063c08c78018f0031d0463a00c74018e0231c0063800c6a198b483168062c04c56098ac03150262904c52018a013138262700c4c0989803128262500c4809868a30d0061a00c3401860230c0061800c300186003081061000c1e0983c03070260e00c1c0183803060460c00c160982c03028c5ed60bda017b402f6025dd3cbba0177402ee805dc04bb80176822ec045d800ba82174822e9005d104ba20174402e7065b564b66116c032d7825af00b5a116b402d1165a200b440168802cc9259900b2e1165812ca0459400b280164432c88058f08b1e0163c02c70258a10b101162002bd1c57a00af4015e412bc8057900aec195d802ba8257500aea015aca2b58056908ad00958862b08256100ac20157c22af8055b10ab60156812ad0055a00aae1955c02ab0255600aac0155022aa0055400a945152412a38454700a8e0151422a28054404a88014f4729e0253a08a74014dc329b8053508a6a014d4029a8053500a60294c002941052704a4a1149402910652200a401148002900052000a400146c528d8051320a260144422888050f08a1e0143c02868450c04a180143002848650900a120141c227b224f4089e8013cc1279804f2049e4013c80277864ef009de013bc0277804ec0c9d6093ac0275804e9089b479368026c824d9009aa21354026a024d3049a60133c4267024cd049980932c1265024c51498a01310125b1c4b504968092cc1259804b204964012c41258804b004960012bc1257804ae0495c012b41256804ad00944592880251004a200940112800250004a00094001268624c04496089281125002490449200924012402248004900091c1123802470048b0c9160122812411048200902091fc223f8047e048f8111f0023e0047c008f6091ec023d024731c8b6c116c022c84459008ae1115c0222a44450088a010fc621f0243b0c876010ec021b884370086e010d03219044310485e1104dc209804100c8200103c12070240e008161902811fb283f6007ea08fd401f78c3ee047d810fb001f6003e8107d000f9821f2043e3047c210f1da1e2063c40078410f0801e0043c00077a18ef011de003bc0077800ef001da103b30476408ec801d8823957072808e5001c88638f0871e00e3421c68038a0c71400e2411c3843850870808e1001c2003840070800e1001be1037b046f408de801bc8235d706b808d6821ac82355106a610d4421a78434c0c69608d2811a4823480467e48cad4194063280064e08c9c01910a3220063c20c78018e8231d0063028c60018c003160862c00c58018a043140062608c4c0188063100062000c3821868230d0061a00c340182902f4445dc30bb80175082e9045d200b9c2173022e5045ca00b8c2171802e2045c208b840170802e1005c200b840170802db185b600b64216c802d8045aa18b54016a022d2085a400b441168802cf0855720aac0155022aa0055208aa01153042a60054a08a940152802a20c53c20a70214d042990453200a60114a862940452800a4c1148062823850400a04114080280044f0409e0013b82277004ec089b881370026e004dc009b801350826a004d4009a8013500266104ca08994013202260104be08978112f0025d044b418968012d0025a004b400964112b06250184a00093821268224b0849408928012500248084882090c1121802400c480008fc111f0223a10474008e0211b822350846a008cc2119802320445c208b411168022a0c454008a80114822280444820858e10b002160042a08854010906212004240083c31078020e0441c008302105041fb3c3f6007ec00fc061f8003f0007d430fa801f20c3e4007c800f9001f1043e2007ac60f5801ea043ca2878c20f1801e3003c60078810ef081de003bc0077020ed821db003b60076c00ec841d60c3ac0075800e80c1d00039e0873c00e6061cc003980072c10e4061c80038e0871c00e3801c7003881870820e0821be0c37c006bcf0d7801ae04356186ac00d5021aa0034e1869c00d3021a30c3460068810d10019f0c33e0067c00ce0619c003380066040cc00198003282065000c982193003240864800c80418f0431a1063400c58418a042f6785ec00bc84179002ec185d800bb001730c2e6005cc00b980172042e4005b060b60016b042cc2859410b280165002c61058030b00015f042ba1057400ae8015d002ba0057010ac08158002b00054860a900151042a20053830a70014e0029a0852830a50014a0028c2051410a280141102820050010a00014000280004f4309e8013d00276104ec009d0213904272004e0109c001350c26a004d4009984133002487849000900811e0823420468008d001170c22e0045c008b02116002203044000880010e0820a484101081821030020600400308000100001fc103f4107d840fb001f4083e8007d000f70c1ee003d42076120ec001d6083a03074000e7041ce003981073000e6001cc0039410700a0e0001c000374306e800dc041b80036c106d800d1281a0083400068000cf04192303240063840c70018c083084061000c20017e182fc005f020be0017a082f4005e020bc00178002e8205d000b90416a202aca055020a904152002a40053060a60014c002902051820a108142002801050000a00013a18274004d8409b001360026c004c060980013000260004c00094101164822c0045020870c10e002181043000850410a00214004280084040fe281fc003f8007c0c0f8001ec103d8007a040f4001e8003d0007a000ee181d4203a80073080e6001cc00388406e0c0c85018c103180063000c408170602e0005a080b400164102a88055000aa00148302900051040a20014010280004f0409e0013c00268404d0009808120402400048000900012000220804208084001002020000400007c100ec30189401474002980001 0x12f01725c02e7e20bccf813b5e92f65324f221176441a8c30a4d91549322891620d20c5123983a462e7253644ca2b5e12f65224e96c136448229f802f33d04e4b405daec97b289273ef05e67809c9640bc3a2608654c1216d1642d22c811456ba27ac964d5ad896c879258f708a7dc0f4cd81a9f502d90e04ae4a51d9249aa5104733406a4ae05e2762cbf445890b69d13a96642d1cc8514d64c28b1fe4d5ae496b2412590909a66e1163d01a9f682d33304b072901c90a3b5b92d4a108e7d60b49540bc81a48901469200d1241412481b4c647269202092401183231248984b320c935ad924b262459044832048e63fd1ab229268fe09a49e1163c81a9270158a04970ae91d280239f282f33104f1f09223d91a47ab448fa2491f0d30cc01a47b1248f546065e0909340a44b2598fb49a7d4924cdd22c7ca418f74731e88d63cca69279458f226a65c0989300b44fa4b85648ee4651dac497b219279108bb220d7627925c4aa4985548f0709062f11ec86a3b90c4732108de41d1abf5a3172228eed44f63f49bc7e1356b025ec8449d27c23a9203d8f106f1e00d4f901799682724b02f1c85563b89ac6e8558ed06ad5e4bcf8c179248178ea2dae3c59638ca2c7486d49b0cb1b8115ab8979f102f24702f1cad620c918472c5c8e66bae3cd56391a4c71b458304651c417490c2ac6d04589447706c8cd4801fa4c8373de05f1bcd620bd1846f45c8df6ba936d56375a4c6e34582d4651b657490caac6d14589347706a8cdd989fb8e1376aa25f1ad176185a6c7634b8eb6931d0d1e39da2c5e3418d64a31768fa2491dc1a23382c464c82536384a3c7014576527ee364ddaa49799604d8d908f1b011547c1fa4c0373dd05e48405dd90a7b8a94751e09e92411c9000bc56c608a68c0e1c556354a2c6592548b0ab1a811631012b8614560024e912114bac1391f0178d12bae20555d8ca6b851458ca24b1a01752342aa8e84d48708b1860960ad183b113d5ff24ea380f4ba81391e0178cc6b9198961c20aa3839448b48bd19ad69c41ab465a5e8ca4ace0c55a3241e91b8358c104a46c0562e5a7c2a34751809e90a11cba01bc62b5c8c54b09061512082211a8148b28bd18cd69235ab46225e8c34ad1844f48dc9ac609254810ac46805a2e1a7c29b4775e29ee0851d7f49bc6b35d8b769f162d3a149a3c153428d64bb1a693e34927441a4a8cf48f19c919fad213ae94f70328ebf84dda2496c641278c724aa2e13d200239738373bd05b18009e2fc1291981788d472d504bcf701791901723002e45c05e2e9224561458b924b14a1162e012c5a9258b304b16a9122cd2245b2358b424f16409c8b00bc5804d22508b1520d48900ac56a518ad8c115cd4a2b129c48a4b5a30be8b011cf64179118148aa29a44a5162a49a9110168a64a314d18229da9452a53890496f5457db6ca3b5292f8bd6bd178d4a201a73f4b4d8bb4bd16e94e2c529447a4b88e495118926145233f4a4185146d1028d5ea4afb6d14762627b15e4de2ac9ab5212f5a20be8ae11cc441ec540378a406a7b00bc8840bafd9372e606e44005e2852245014587724b13e1161a012c4c93589706b0fe4961c412c4ca4489748913ad1e27123c4da4689a48b13051d7e89bc3f12789608e5ca0de1c01390f0178942ab0ec49624c2ac338258294891225161d492c4804586604b0428d08740bc46c5e818488f5057d6842f90d8177a72bb1165561e892ad005d88a0ab0d80961ee36436c6c88829f10e51d7d893c4304f88508e5c209c8640b90b8178828a4fca8c1e84afacd05f21602efcad108540bc3eb6087f4a90fb5821edb643da6087eac4f4edba1f1b143d26e7a02dd0f20f48341ac3502520c02b0e89821d228c3bc538766bf0ead3e1cd292cc05f51509e5b60de1bdb0438a5486fac10dadb21b530105814870ac4b40dba1b9b143626e86b27a41a4d61a892acb86e20a02d0ca98219628c344538676bf0ccd3e191293cf15f75b29ebe04de28a2f44f4538958a5124d7e23da7c4734e88c69b09ed15f91a1444a5f8844bd10694a20523427a4588047cfc88f5e74afbad14f5ef26ecfc4b61e093c391255960bea2813cb681b9d902d86904f0c60948240bc0b23020702f02a9020512042845c81348109c575e5c9ec301358450bab200f617c1ac26b6c8124a1022942111b640825080f4a10a092607d20c0724085d27f0b84dda8c97c2d83f85a06e7ae0bc8140bbf445c8586b909057615c9ac1f05d85606b08e57615092c1e85d85304afca8f08100bc284527e5478f2c57d63c2f90181784dad8ffc901ff520426c607fb460ff28c213ab142646e7978c4ff08c1e54b742105d20209b0961161262f4243538474a70508cd6342fa8903f3d405f0895b1fdd203fb2408448c0fe88c1fc9183f8a30845ac50871b9642313f82308422ba404536104a2ac606e83f8bd07cd4e0f529c13a337932beeb04fda8097c30c5e85e8a70b314a155a9c27b4e7e669b0a494e145273f524d85147d09e8e609919c10232817462fde8c1e48afc2514f84629ac24515d5c9fb4f92f58b0bf08013e0f02697e84551107e7a60bc7ec0bc0b34c5ee26e5b20dc7e80b8fc017839688fd08f97b49b96c0371f602f06e9520d8aabee1258350aafa00960c49ac170358326b90629120bdae41724481669906691a0c0a3c168471f402e3e405e0ada20f80178294b9050575f6c92c1385d7cf04b04a4fe0909bc1183f82206e3de05e085260f681781e69f03ad0de44a7c0e13f81b26eb1413e0681fc0c8371ec02f03f14a061263c815f5890be3d405c7a00bbff14d78e27b02a4d5fdc26ac383d81406affad71fd9ae40913f81126f0200fe03c1b8f30177fa29afc64f60349abf11257f309afb00f60301abeb82580a49f01290de34a7c0412f80724eb0c13e01817c028271e502f0064fe0089bc0083f80006e3c605dff62e3feb507fc488ffd149fedaf3c73527fa49afc68f5e30af3f09267f209a3c40f5fe41abfb45c7f66a0fea911fde293fa35e5876a4fe6935f611ebf914d1e227afe24d56142f3eb02681669d026d0e039a1405a3f80447cffe8f5e2ca7bfc13f7e024eb0813dfc01fbea8271dd02ef145757a493ac185d2d404e3b805dfb4923f60241da02e3b205df95a20eb8177e88a4fce979e18afabf85f1d602e3aa05df95a20e98177e369cfc4939f84a73ef83d1c706a384055f7e2a3f04547de07a3880d5f48128e08157dc6befb6d1df69292be85f45508e59c0ddf61a73eba4e7d427a38e4d5f58270df8167d48a837c051f562a3e993d1c426afa44946f40b3e835f7cf68ef9c949e10afb6c1475e326f07517a0e22941a35f82c6bd054d49fa5a6bf234a82668f040d1a05da2bf7b447ee4bcfd6949fa9273f4a4d7e647cfc88f5e0cafb6b9475e226ece04b5f7493bec92557c0be8a811cb341b9d202d7d104ef9a0946f00bbdab547874a8f30d61f012c3dfa597b44aaf968e5f291abc00557c906a7440bcb2c13bdf2487b36a8f8a9b1f1936bd2a697994caf88985ef524bd92457c30da8a0195dfc229d002f2c904e146055f01a23de254798488f7cdb1e622c3de3587bf8b2f7b155ec5aabd8a557a5494f76919dec2a9cf82d7ba04aa0813d13823bc3c547b66b0f6d1b1e1db63daa387b34c0f631b9eddb6bccb657b4692f64d15ec524bd806d2c50caef21154081fa260370a202a142055eadac3d6b567ac6a8f50925e851ab3712e1ba0baeec155ea81a84f815791488f0e951e1d2a3d302409e02af31161e7d2c3d434d79668af4e975e952d3d22567a34aaf44951e85233cb2457a024c370175dd02a9cd02d79e04a138055e3d203cc46c7986b8f1c901e30903ca45479c8b4f37165e6a2c3ccc567978a2f2cd39e19a6bcb239790462f168c1e54a733612e1b60baee4155e4c2695f84509a02af22931e3da4bc734178d47cf184f86d026bb884509802a366175dc02a84b81509602af0e951e152c3c834578b688f149b1e252b3c425478647c362175db82abc202509502af02d61e062e3be25877a6a8ef8d71de9203c135d4506aaf00d25dfda2bbf25d39f4b258a955df528bbda4977948aeeed71dd52e3b9c50771460ee2d11dc1363b7a5c77647eee88eddc91bbb723373969af90d2df1da4be13477c168aed4d0590526bdca4b7b8492f5e91deb922b44a417a947ef3a8ede491bbc1a3374c27ccd64b86c026bbc04776d08a9fa0fd1141b9cb82f2be04e124054e581795e82739405e57609dd9dae3b256d7696aced0d51d913095c85d7660aae840d5d041abafa487646daec89b5d8d2abb125476148aec0911cfc229c802d75e04aeb8911cf822bad8257596b8eb0175cf41aba934575248ae90114e3c16bab0257544bce9a5795782fa140477526bcea48e5d442e95805574606ae9f1495702fa1283774d252e78094e240f956817749490e8ed11d25a63a3a3074b49a71e924ac122ba5241748472e8c8d5b589a3a1b587414a8e80931d11a93a125f73f4a6e7c92dcf523b9e15e6d628ced6d79da9a93b2a5f75d4a6eb492dd5d23b1323d755476ea68e5d411bba7235670462e98579b54a336a93655b0be84811c5781eba283773b06a7100bcab0139c302f2aa04ee04d71bc12839b83c71a4c2e02975bbd28b7ea3d738472e6c8d5b9d18b6a05d55507ae6a0d5c01b639924872e468e32d81cc9a638c26072d460e60131cb91e39602472c468e5ad11bad363958246d36d8120051c5d28b99a3f731476e5e8ddca919b9483f72806e7080bcaa01384781508e02adecd71bdd2e3713506e34a0e4cd71bd52eb70a51725472e488d5b242eb9183508d02ae2d5b1c5928b7f46c71d8a0e2b5b5c862d39045971f8b0e3d159bf628b8aa616fc49cddc909b7d2015305d71c0aad8e1344dc228460156fb6d8ddad81c65a538c34670f4bae16955c2493045815716ad0114055ba52e38885c70fac0e10491c35a736284d13208a112055c2e30383924709ac0e10531c1ca2382a5071aac2e2f581c55b6b7d35e6f26b8dd8d49c5536b8a25e7134bae24971c412ab73a5270e49ae18931c2922b831266c40ba262154dfc16b8202508602ae011b1bed303812387008c0dfcd71beeb0380d626ff6dcdfad89b99aeb7e26e6fa4c4dcc945b442e95103d6f906adeed11bd91c0428156f346a108055bd629b7a35e6f24a4a9c17d3ec278418156ed6c0de0d11bad36376d606eb8c0dd2971ba012377d626ee6dcdd8d89b99aeb7526e6e74c4dcc975b402e9bc82d6e504adc6d11b89223702466e18a6dbed79b792f2a585f4fa09e104055b71ae36185d6db06a1020542000ab6ca5c6c20badb00941fc0ab6b02537803e53605db4eb6369c606cf4b0d9ad51b3dae366a406d4ac4da51b955631368a5d6d04a2544935b3924b66245379482a941b8ddc173644546c64a8d8a931b2a2f364b536c74bed8894db0d1fb612337398bce6914dc9e2939135371b4bee0694dbe127b78a4d67e492c24915b9121b6ea416da47edae8cdb54a736a93e5490bed9613db04268970454f307e6ec0bca681383e8156be4b8d775b5aee30b3ea5d6bf4aabc24d97849321105d6bd0aa22e0b598012b5c23d11605acbe095a1d222f01245e024cd64931aeeb6b5dc6d6ba694d72d19adda234324d6b6494d6a919ad122b59a445df26cbbe49938026b5884511405acba0959cd2a33a2446ad0bcd58149abe2cb574556ab4a8ce4919aa82ab2e0256924d8d22971a462f353c5266f2bcd511b9a413735324466e2dcd4a11596c12b47a6c68e498d44d79a39a933695e6a3ac4d1a9b9a852e33616e6a00bacb40959e92a342a4c67d8bad3d165a762ab4345168349ccf29195102eb4e05566604acf71b1a65ac34b3446998b8d2ad01a59ae34ac546846d8d288d1a49b6348b5c68f8c0d1d14199e3634d34f698696d2ed1da4da1b4823f68d46ed1813da2c23a6f03f41d06e4f409d37027a0d8476844d8d0e911a162a34236c6888dcd0d189a0d3733c25667848c9b6135a0822b3202527704ecfe9794f42fb3da6c67b8c0cf4d619f6b733e5626794dccf09799e12733b85d4150aacc40959d22c339b586758a4ce497d4ec2f93a02766f268cda5319b91fb362374d307e8200dc9bc13b2c0156676d8ccad7198daa333a606654b0cc6901511b73353624db6bccd2d69055ab3343526664dccc89799892b2ed12465f688cbc9219822fb2ec5365c6becb6d3d969a3b2ca526582bcbb44d9af22fb584536a96bed48d3da7da3b4da5f68a4bcd12949a0527b4024e67e494cec91d9c52333824266b2bcbb24d97649329d05f4d209e81c11c9b81b88882d66104ecae095951a8328d6d6518c2caad65879a8b12b49611682bf69257b920af093e5e125c81817594c2aae703d0e706a0f80541ec0ab0534c64d098c74d8191ca232523e5cc07a1c80d41e80ab1ca60646268c7098191c9c323134644680ca35b594636b203616376c0c48d65869ac308351650694c9ed25939a4326346608682bf49657b528b25a4a649490c90919914a32ef93e5df25c99e13590c22ae583d0e306a0f00553341fa040376238d0c1f181774a631135860e680c7c171902b0b10c5a60d8a4c7e9798792d31ea566084a4bb853176026a9802d63c04abf2d657b1a8b1d34a63968cc6c9758c92ab1c1465dd27c0ec0558dab031a25862f488c68d718813631946062e480c621718bd2631602462c488c5cd5183136316a4c62b048baa9b01d00a31bc515f8696bd6d0d8d527b19a4b63048ec5490d7709f26504f40508e6ea0fd8a417b1402707302ac4718188eb031036c6224b8c40d81896b73125626218c4c0f14987d3730f26260749abae13500816b0e82561b48c0e40541c40ab0d4526036a6c329794b42f9ba03f07002aa581758581fb0a8376178a4c291414a82fb0984c60f8c0c1f581839aa30626c60c6c0c1493182412308d6e610ac4c1b18981e2d305a6e6084c4c0e93575826a6102d60604a6e60fd8092e300a346026b0c02d201bc0ab01c5a6004bcbfe9597f9262e484d5fd04a0dc0557d5262fcc605f4498bf35817ddb62f92385f76c0be4d417d62f2fa4525f34bcbe49481b40aafdd6e5faac4bf11897d9372f8a4c5c809abe00941b00aaf424c5ec8c0bce9317b2b02f526c5e5478bd4d81795a82f445e5e78a4bcc979795290358155eeadcbdb5897ae312f4a6e5e4498b8e13578c128350155de4a0bbad81780a22ef2445dd8a2bb609576da92f0c5f5df8a6bb8d494a42fa6084f3fb08ebb4055756362e9c5c5d18a8baad8174dac2e8b405d88c4baf16975a292ea36e5306c4ba4d79009ad2e83564c26a4a501b93002f2e6b445cc490b9d17d72e29ae535e5c94a6b9092d71d21b2945f6428a6c82d798eda9b13b5262669cc38d2d861a5309346605686c08d097f129af7a4b5e2486bb24f97649729385f4bf09e7f411d73c1fae303d0d706a6ce0bc18c0aad73545804a8b22d616e52c2dc2595ad4aab888e570d1aabc9555c226aa8e4bd4e093adba485ac6a8b7c9b16fd36acf2695924cab7a9856d924ad5a455bc2daaae5955e0a2aa292f53624e0c40596e5a22daa54591488b6edb16462c2dab585b88b2b6d1556a9aaad525559e494b689195d0aaaa112d5b324aac453d54ca3ac04545af6b0b5f1b1601b62d72385ac4c0b551b96c1b6ac93655ad692b56d156a924ad496d5322caae45155809faa893706102c0c0059691ac2d33565a56a8b429256691a8dd15d56f2aab464d4d301702f01658a488b009516012a2cf92405d02cb231616652c2d0b4d58f68ab409756792d2cea5659c4aab36951669232c7a451b82baada5554f496acc12559704c0b6059621202c8c6c5916b8b0e90163a2a2c29205958b4b2916564e2c2c94565908a2b1ed395fda6ac7a39589462b088c06d8aeab595558d29aa54515630271a502e05902cb14931621a4ac3b4158647c3685355a8a2ac283e05702c3665755a0aa82b01605502cb009515f92c2c4b45584688b069b16092b2c0a5457f47c36257559caaabe92505402caf4d615ea362baa585736a8aeadb15cd282bdb6d5576caaf2d255e1a2abba6d5424d2a649955d930aba24957248aae0db15b9362b646056a460ad4d115a5362b425c56f47eada8ed5ad1bab3a33563488ac2db157d2a2aec585656acac8d50ae52eab12595604aa7209455791caae23534905c6900b81440a2ab46c5566b8a9ed715512e2a946054d4800a0051541aa2a7a5804f028a9ad515312a2ad45a5598b2ab116155e2b2aac512a64baaa69655452a9bfa5154e49aa7a9254a922aa5a4154a09c68c0b81380a2a42445464d8a8695150d2a29f25453c8b084517551e2caa2c554e08a2a889755092d2a0a565404aaa7e9514f52529da4652926ca524992f027297b58539690a6ed801340a25d84e04c028a631b14c526297c5852e4a80960514b230295c5840c8baa711654da2aa67c515356b4a68d654cdac2993565306a2a5ad294a9a329493e52925c9721394a01f1a202e04902896cd35705a5ae03495bb68eb74d15491a099624d5b2496b629256a123ad3a453bd482b448fd6591dac5a3757c4663605355c4a3ab314555b27ea924dd4e897a939274b807c6840b81200b27112f4d124e9c04bd33c93a90b5c51eadaa46d59489aa28f2614cd2baa405553a49aa73935519490a3cdb547936a8ea5551c4a8a36915469222731454dc25aa304954592227294551524aa26d71448aea7213550c68aa189153bca2a6c92d51024aa1c979400afa7b9474be0bca18d794311ca8595d4c42aa9da4d54262927f15f4f426ea0a91140db6280a544ff8b0a0ed59419aa266a5d5044b2a0495537128a802394fe46a9a64b93e1a227ca484f56889ec9113e5ae27c25c4f68a09ea9013f1ae27da5d4fa4a29ee8e53d11aa782484ee6889e0d713b92027925d4d94b29889553c528a77a394ed46a7f20d13aa2c27425c4e74889d71493a52fa732534e54769c88dd2f42f1fc8364d64b89c2911359ae26fb544dd4889b49113692226b45e4d58a49c51b93823126f26e4dc4c49b69353652526c2464d748a9a891134cb72609364c124c9781b8fe02b1fc0464cc6c098cd41341a42673544cc8d898c92132d22263a5e4c64a497417930dae261a4c4d18dc99f189335b72653624c9694990d25315a42623464c26829824f93049725c86e3f60ac7ec1193001f25da584ba47097c4a52f412a5e01f4b902ea4ad79491a928fa5f5174a6a2892d44523988a3d50f476a1a8e54291ba842353a44629fa57d3cca38af13d4ec26e9c64d534897a5f9274b80bc7ea118fd41b21112f40c24e8fed711b52825a13c4974c28fc9751b128a3d23d4b54729668d519118a2215d44027a9644d51f5b6257a484ab46892cd812bda624aa604aa46095a5312ad1e2549244a9468954d111a1362541244436d808c05125128a5823f4ae4769588dd29d19a5313f4a526e8404bd0289382281604402c8e6d711d12e22fb504604a0946d711c92ea2f2514a24729428d50dcaea5013504302c9275b124d28a3dc6c49a8a09255b527a2d24ec5949c8b09371591ea28a4926147949c8d69091712020415d4992aa8685344dca28210164786d88d4d81259a524ab4648c4ba91095521013020816493ad00800591992e24715c48cac0906091229a721994d13228a07e059222302410244864a090958120ca6241144497ac2929581249b6a3bb5e46f6b88d2d4924936a48a5e4904ba91e9712352aa3225248b49a91293121d22a1895d1312aa8364b521492a4082603c02c8fb1b11e13023fa3847d8c08f6d711e2b023f56247c6dc8f4d8918daea3ca6e4774c48c69450fcaea0213d47626a8e8d111cd1c01d81647046a0740591ca29a38b5e46f4a489257d0b0a781c81646a6c08dad111a1362355604688c08cc9711949223656246b6dc8d2d8918daea33a6e4644c48c69750f8aea0992d46224a8c0d1117d2222ea4645e8a68b8d7916d2f22315f42b29e070059165ae21815d45826a06e0580d80b22b25c42f2ba8aa4940d40b20912e0330288831b1129ae227a5c44d8c08909000c80a225b5444a4b0062051121aa223a544538b48a51651462c2284564408a28109751392ca2625541b4a2892934e692495fa45446482872539040970180144438d8887181105ae21ea4843b68887ad710ed202225624426dc880d890fd2ea1f25140447a8788e50e91aa09a314392dc81e4b90d5aa219a5c43248886f14d0d9af21a25f4314a686093d0bd21a14b4442a49084cd1109d2221535c4294b884f14109920216b5c42c4ba8569450a11ca12a354234a883e9b105d26210a4441f8c083d16105e2820e25c4186bc82ed49044af20a25c4144b8825161044a621156e420ac483a9b906d3120d25e4194ba82c9710552aa09a524102dc81e578fec9b1fd9263f80bc7f0139035ac203b6040b6907fcd000bc0a204c5802e02880f5810192e1ff25002d028806d7100d261fb85c3fc2980580500ac0a1ffa5e3fe4a47f84f8fdc270150143fc6a08195b902ab120436e4056c4808d79009aca00b524006a27fad40fec9f1fd92e3f60bc7ec1380a40a1fba503f904a7f007cfd80ba5b45e4b18a694914927da9a4c25f4804a68ea93d1b9269d92492fd48a8c290d16920a2ba3f45446688a57d0e0a7a1714d12e28a8484fd038979fd1273f509c7ea0f80a00b1f925c3efada7df184ec52e9f9a553862ba7e255445c969ab12526d06c4da098fb11e88b12d35424a7769109b0121360263e64987df5b4fbe369f734a3ed68c7d6d10ee9269f524a3e948c7d0914f9d221ca14d3e528a2284b4d4c9293583626b04c74e950ea1221f095e3e02a47c7164f8a2a9efa543a648c7bc554d44929e326c3c54b878b178f6e291a685e3dc8dc7889b8f69221ec94535024a6981b8f0d361e124c3d66bc784d48d2c2f1ebd623c14dc7aa970f50ae9a792534a0dc75c950ee5261d8c5d3d28b27a3154eea289dba4e3ad48c6ca574f40aa9ae1253af8d879ad60f29a21e6c5c3c9680794d70f262a1dc36c3c846878cdb0f15ae1e1c603c28a06bb1b0f39a79e634b3cb68e78ed0cf111f9e0a373c029e77e51ce489f9c093737124e72053cdfca39dc26c3bb488773150ee1b61de46e3ba8c476e9b8eb12b1d624636229a76c514d68929b71273b34bc73457cebd361d7c603ae6b07635b8ec2b11d6a6e3ac4bc758938eacae9af95535824a751160e9dac1d4c523a64be73057cdac939d1a443a14d86cc950e6d2a1ccc583868ba745164e822a9ca4513654ba73e968e792b1cea5539c4a8734928e61231c494e26706c4ce098e312e1caa4438c6b8726d50e45221b1a4438c8bc717148e5a371ca4623924dc720988d89269c7a4a38e48c71a914e29221c496e3782ac6f0518d243713303626604c70e950e0d361bda4c385488707180e0a2c1bdc503804b86f8d78deda91a385e3604b870d5b8e12b11c0a6e37f4c46fc978df52e9bd25c35f4aa6f2948de0af1bc14e3460dc6ee1789901b1320263726d86d28e0dc1ae1b7a3436c6a86da8d0dc9b01b4b503706b06ded20db5a81b634036a2bc6d2548d142f1bac623748b46e7148dc5371b725e36b4ac6d0930d10371b325435d6d86c6910d6dae1b025c3596a86bad80d6dac1acb403658dc6c9188d8a2f1b0c5a35f8ac6bd148d71371ad25e3584ac4c4090d55a41aa2443568be6a714cd49a91a8a5f35049e69e91cd0c2f13102634d268696530d222c1a394c3452786988fcd291b9a483f34606e68809cd0c0a9f845f3e48a67bad7cf61a79e9b473cf4be77c978ef5291daa4f3b449c764928ea9239d2a463a448472e57ce20a79bb14736726e2224b4d5c939a71253420bc4c20d89841319fb5033cada679184d01ac984b513106925f8d04b992496ca412aa2ba67c554a1c9e87393526d07c4da0b809c0b0130162f5698670530c95b019804433547c50c4f43909a8128163244c065e0d0cc9a0191a6033027065e4d0cf2b699e46d32b6c2644d80c3dac982b582fb6a2676d28ce9a499cb4833768c5e6d04b952c96c251336494668920ccd2315d94d33128a5084f438c9a99704626b07c4d60b808c0b15c93f2a626e61d1a0bea3013484c30d6b05f2d00ca4ae195d6130c8b45f1148ca92f184a5a3284ac5e6948a64a694992d32724a4d0130b91ac96bb51325694648d18c852e98ea5532308c4d20f80840b190d6031f4b0634910c7dae185a6c31d8c0632900c70ae18d24c31724862e910c65aa17ba6c31849862c490a593600f8143228a25c6d2cb59a199024f31e49663691cc552195b14f2a328e4fc4fcc509798992726807c03c058c3a3018756030b6d861a970c2db018856e30fac4619188bca2918526e3094c45e4934a60a694792d30824a60c9180740b00e0163058a45dcd4cc112f16115f27d27e036058b04ae98093f30026e605148bfe2815f95f2fe2985f5180beab017cb542f74d85eed80bd52617a1242fcadc5f7588be23117945a2f64dc5e6988bc92694b94d28b25a5e24949f09f976a5c2ec4685dad60bb1a400d0162ee8b45d6978ba92b174a4c28329a5d04940640b17024c2e48c05be930b92b017136c2dd4705c4d80b75a817045e2df8a45bc978b752900c0162e6adc5cb588b8e31170a6e2dc498504534b6c9280b8162d34985af180b492616bd602d54d85a08f0b55b01683502d38bc5a5148b452f16825201602c5b35b8b62b116b4622d44dc59e930a04a696712501502c588d60b31a416536000e02855e5380340a14a46c2c48b05869500300a160c602c08b0555174b2e2c964c552bb8a2590d68b1dac9633582c56ac526d44b09a515fb462ad29c5144f89bc9713383e26705c014050ae1b01593502bc690574d50ae2361592482b7488566978ac92915715e28c6b855e960ab91c15ec6e2bb8c4572db8ad9b115ab4a2b4692562d20ac1a3145b412ad2dc536558a6ca314493e26607c4cc0b8aadac152b602a969053cd000240a153c5800802854b580a912e14f250007028520d70a70ae13284c00602800a050a7d2f14f25229c29c4ca0f80100a14e2502aaadc551588a99b7151b622a26bc51ed64a85a915035129d6a0536578a6ca713203e26405c006050a59b614935c28e6a852cd80a512614935829049851cd00a312614cc622988b452f148a5537149a622914bc51e968a352b145a5228a2dc512578a19a4142a442878be50914ca0da994134b2816865009789edb61392382796b84f08d09d5aa13b23427b6c04e4d409e5ac13c3482766a04ead009c12f13995e2722a44e04f09fa3113ec5a27c8a44f49b89dd2f13a2562714984de5b89a928134b6026c2884d49109a6289318252656a04c69489b62f935c532686a44ce17c9982793204726202a67b17ccb62999635e3266a6624d48c45a7183b4b3036945fad18bc1a1977b422e74a65b492cb352195f15f2ac29e53451ca209f93f93d0d726a4dc4bc9841f13082e00202c1ee92097d1c12ea500b34604b35b496630903b5d25e6b24b8d5485da89103491fa6824b6964551288aea4912d48222e8f83d91d073a360b24640f84d809c1b0d22601504b01c89109611c03d1440250883f2d007e1a812b24011647843ed247dda083ca3602406c242d30945261282401a32c049a0d0688280d096024d0684b35b49663690f3591f66a2460d3495da492ab451da68235e984681300ae25914e4b025894495125129a4925249049e9184812088a23e0f44741c68d82c11904695624e28c0f04d810c2b12604602306c29a96092924057a302484c04835b0905a8917b4e1f5684203170902b6903c5d2498b248f1548c22892036122e69c3e8d089192d122a592444b0486958401288a5a4a13748c2208e435918856a3008c28c084118905340cfa601324a847e9203cd1c04495403f0a83e6d007c9a011ea5022d69c3e2d0821d2301e8462386b01888f0678b011a82419d0a03385808d41212046d22c8bc3e1148901b691f35e2176b4478d58769a90d726119b4c02929684c52b087a490f14901aa9048ed1d11d23923947046e8d830d1884315606e28c46c4d80f02b00c84623406c334980661280562302314901548c08bd2c114a381994c04509208b51c0ec45c2296bc450d48871a48ec3410a04bc44e578660a902f85e0c16984460d088c1a11946e2308c442b17875e2e91736e22c6c443ad6886dac9023561d76a2408d18859a28dd26e1964c44569288a92491324822548c1f29044391c86a2310a846013e5b8204ab11214605e0dc06e158888231092381954c043e9608451c0f7b442104703d8d508712c0ca26021a4b03269408611c0eab400bb4a03ab1502dd1c0ea34c2128bc423148841a70ea34209d4bc41e57864ca902e05e0bf47841609082c1211056e21eac443b17886e2e901c551d38a4432db885db110b3562036aa42ad3874da68dc26e1914c42b69644ad2888ca502144744268e48391c106a360be4621385b81b0a310613605b0dc02e1188281b0f4b401e868041096079da00f33501904c040c920639200eab4c1ff4a03aad307f92805dc5c1e24603fd1707fdae0f0b401e08a0178d302f1a60efa301ff69c3fcd247b9a10f5b411de6801369787f4af0c715205a0bc40f5b8816b1101c5e1d68ba408d78765ae90234e2036923dad087a9a08eeb401b64dc31a9888092f07e2592014a44009447f12804d16e0590dc3d11703c1240e72381f94803f1150631300fba580ef49039a8e07a22e0faa581484903988e07cd200f945418b4c028e9607c5240e5a381ef6b83dc9407b1ae0f5a501e949031494079d240c4a401e44903a49002f1a604ca4e1c346c3be538624a10e913a1c826c0b01387001b0f445e1e68a43cad3878da68da25e1884a43c49383f5248f0a421e04823bc9007451d0e3a360982bc3844d815c2f0df8361b34d830c940519240772380972d80ac1b061d300a2a580ed4903b68e0305240eac541d84b017e8e02f1200eac541d44903a45007462a0e745e1cd8a4398d7872da90e515e1862a438cd40721a00e34541c78a838ad802dd1e0e19401c28a837c090700a00dfc541be0483f55b87dab10fa46e1f08c43af17474e2d0f6c561ea8aa3bb150771b70ed3621d96bc3aed74759a70e9b4d1b14dc3029885692c8a1a5812a4a221a9243ad24069a411d047439e8e47251c0e22360b646212a5b81fcab0351461c126c0a81b80d42b00a8461bd06c376d506e52a0daa401b78b03688c06d5a40da3441b34d83649506e91f8dc23b1b646e3628cc565b4094b6010c6b01a4d405612c0942401ac6b8356d4049d20085a480d148035116069e280682301afac235d18455dad09335210a69419ed086b4af0aa15a1aa2ac2405486a4a708014a1a628c1865086881a0d11341956b2318d44691a48c3b411a348c3005745f0aa8d084619d04833a4906662f0c5c5219f6bc30ed486791b0b814d16928a3380d866a360ccb6019829032e510656b00ca36c1932703244d0629a80c4b40190ac0310d0063cae0c71501852683084d058c9a0c54501892803064d058d180c2c501846a0306d10632b00c5c601888a830ed806189c0c1134180ac02fc5605d8a20bf25c1562d82f4d405ea280bb94017c8c02f6d705e5a80ba9401632682eed005d8a60b99341634602e65105d52a09296c1742982e45105c2300b71481662682dc93040cb60b54501672802d51405b22c0b5c501696c02ca4c058c9a0b3b401622882cc4f058d180b11341654881905b0590ae0b09541a08a2336d44659a78c8b4b18d68e302d0c5fca78be94b17828e2e250c5bc9f8b693b16826e2c04cc565b0084b580ce6a01fa560566b00ab26c1582b82ac9804212405ba380c148019a8c0576b70ae56215b8b22b514455db108e352107694198d08554b70aa16215329c1f8528548a305f14211c27a2a0d24515a08a794614d8b0290d00530aa0a3c501456a02944d04cc9a0a445e1478a428cd78515a90a115e14426c2848c453a290a5b5f1496a6286d04504af09ca5d1364a22689704f91f89ea3b13c46e2768cc4e63009c4581344b82691404cda609b5601354b82649304fe2909d4501374be26294c4c126097a401296c020cd6032da808f15412868025358049d2a09296c1254c0246530488a209093c10549017e8e02f12008f3500bb4801948c04b6b709656212b8b2255144499b108e35a104694192d08490b709016211f29c1f2528474a305b14211c27a2344d8465a483f2440340881568f0459a2089a6c115488226d4445e2f88a4531124bc218d80425ac0833500fd2b021918040d3608594c1098a01fe970420a605b9241068a01f6950414a605f9241034c02024f03fd2c05ba480bc2781fb1402ec9e05fa500fb4801824f044237087c6210e8bc21b148429b1083b5a1046a416ad08408b70801620fe2bc1f85683e8ab07c9520b527a1eed603c1a0077b500ed6801ea5103cda7076b420f226c1ca4d03c22f077c520ee6bc1dad483a8af0761360ea4641ed17c3d229878b520eb6841d2578389b006e3500e54781c2d80399a40722480dc6901c51743862886e24c0df49e1bc92c3752386da430e78be1c714c381a906d3500d96901b0d00349b00673580cb6a017a550345a00694600d04881905b033a28066a440c22b81824902f092065c500ca4881745502ec920642600c62b818a5503109e0612580c149017e4f02f12005e3400bd6801769402e92005c16c0b72781ad1b83563106a45e0d38a419ed88331ad064b520b569418e5b830cb106015e0be2b41725582d8a905a93d0b36a80d28d029cb600a0340682480260902a9a6033a340b12880240d02bda48553410ae28c1564d02b1af0553520944bc14c5782a49b02985e0a76ba14c8f82ca2f8584530ad6bc150d3824d2f0322340a52bc0a417803c1a00702603206c142d502809c04a12009e4a813a4a02651804c23009b2801324c0261a204ba6c0964a81288f802c12051b450a248a13e8fc2711d84d2370954661264880c01b0050260914b81169442401f00482608e6b81104a022228045d600846b8114970225260439280856bc10894813c2f04135c0804b811f148235a984625f0864a61069342051f83fa3307e26009c17800c130349200776a00ecd801c9ac03db4807a4900f252019c9003b9480662600ea5701da2883293002d08c0e80b81ca29038a5e04b0bc0de9301b526035a4c0664a00d04d0199a0834b4f0676860ca9081282703e45f0788a60e6d481c1a503725306c4960d490c1909002485e02908c09a0981401b03035405f2700a64801752a02e1280584600ae8c0168a002c1300576880ac9b01552a029a3e04a2480a2d20140a282793d04d68a09892012d1d02501006268a0c29141791f82da3b05946e0a88cc1489102703604904c08e9701052882303e02f04c088d700f89401f450041ac0074d701012e01fa4c03d250076d780e92901885e0386b806c9700cda401914503127a05c9400ad1801745002b2800585380aca1017c5202d4a405490011629021b530424be07894c0e52681ba3f0354660684c00c02f014826014240044d40085b000eb5802669004a920090a40091200222900224c0080ae010c5101026000e11807c1700ec5201c4bc0181780692600c24c01649802294004c1a008b4101469e024d0c0412100594e00e68a01a9200311d0058100084a000a8c00222800294000629c00a50802629003a5200448004f17c08e2980f35201b69403294c05d2580aa4300f24001417800c2312d45f24b8a6484d7c8cda9910b4f2096963f6d1c6f1a18d825e1a54a62be948579270a8a4b14049425c91846d2188c24211147c1f08ec3a11d06ba360b44661488c8248af03e94606326c0901780a02300103691169f1ded0e35d27c5f2438a347f0c48ee0ed1bbe623376c29ee744fdb009bb2b12f5c524ea4c13d2dc1f9fa03734105e4c009c0040b80001f 19 6 11 12 7
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsF m_56 g_56 bds_56 (dagRefF 2326 (dagTraceF m_56 s_56 9 f_56) l_56 0) s_56 9 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_0 : treeBlockF 0 32 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_1 : treeBlockF 32 64 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_2 : treeBlockF 64 96 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_3 : treeBlockF 96 128 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_4 : treeBlockF 128 160 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_5 : treeBlockF 160 192 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_6 : treeBlockF 192 224 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_7 : treeBlockF 224 256 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_8 : treeBlockF 256 288 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_9 : treeBlockF 288 320 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_10 : treeBlockF 320 352 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_11 : treeBlockF 352 384 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_12 : treeBlockF 384 416 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_13 : treeBlockF 416 448 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_14 : treeBlockF 448 480 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_15 : treeBlockF 480 512 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_16 : treeBlockF 512 544 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_17 : treeBlockF 544 576 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_18 : treeBlockF 576 608 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_19 : treeBlockF 608 640 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_20 : treeBlockF 640 672 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_21 : treeBlockF 672 704 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_22 : treeBlockF 704 736 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_23 : treeBlockF 736 768 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_24 : treeBlockF 768 800 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_25 : treeBlockF 800 832 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_26 : treeBlockF 832 864 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_27 : treeBlockF 864 896 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_28 : treeBlockF 896 928 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_29 : treeBlockF 928 960 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_30 : treeBlockF 960 992 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_31 : treeBlockF 992 1024 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_32 : treeBlockF 1024 1056 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_33 : treeBlockF 1056 1088 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_34 : treeBlockF 1088 1120 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_35 : treeBlockF 1120 1152 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_36 : treeBlockF 1152 1184 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_37 : treeBlockF 1184 1216 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_38 : treeBlockF 1216 1248 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_39 : treeBlockF 1248 1280 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_40 : treeBlockF 1280 1312 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_41 : treeBlockF 1312 1344 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_42 : treeBlockF 1344 1376 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_43 : treeBlockF 1376 1408 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_44 : treeBlockF 1408 1440 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_45 : treeBlockF 1440 1472 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_46 : treeBlockF 1472 1504 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_47 : treeBlockF 1504 1536 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_48 : treeBlockF 1536 1568 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_49 : treeBlockF 1568 1600 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_50 : treeBlockF 1600 1632 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_51 : treeBlockF 1632 1664 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_52 : treeBlockF 1664 1696 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_53 : treeBlockF 1696 1728 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_54 : treeBlockF 1728 1760 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_55 : treeBlockF 1760 1792 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_56 : treeBlockF 1792 1824 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_57 : treeBlockF 1824 1856 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_58 : treeBlockF 1856 1888 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_59 : treeBlockF 1888 1920 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_60 : treeBlockF 1920 1952 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_61 : treeBlockF 1952 1984 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_62 : treeBlockF 1984 2016 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_63 : treeBlockF 2016 2048 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_64 : treeBlockF 2048 2080 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_65 : treeBlockF 2080 2112 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_66 : treeBlockF 2112 2144 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_67 : treeBlockF 2144 2176 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_68 : treeBlockF 2176 2208 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_69 : treeBlockF 2208 2240 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_70 : treeBlockF 2240 2272 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_71 : treeBlockF 2272 2304 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_72 : treeBlockF 2304 2326 (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) = true := by decide +kernel
theorem nj_56_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_56_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_56_1 h1 h2)
theorem nj_56_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_1 (fun _ h1 h2 => treeBlockF_at nb_56_2 h1 h2)
theorem nj_56_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_2 (fun _ h1 h2 => treeBlockF_at nb_56_3 h1 h2)
theorem nj_56_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_3 (fun _ h1 h2 => treeBlockF_at nb_56_4 h1 h2)
theorem nj_56_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_4 (fun _ h1 h2 => treeBlockF_at nb_56_5 h1 h2)
theorem nj_56_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_5 (fun _ h1 h2 => treeBlockF_at nb_56_6 h1 h2)
theorem nj_56_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_6 (fun _ h1 h2 => treeBlockF_at nb_56_7 h1 h2)
theorem nj_56_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_7 (fun _ h1 h2 => treeBlockF_at nb_56_8 h1 h2)
theorem nj_56_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_8 (fun _ h1 h2 => treeBlockF_at nb_56_9 h1 h2)
theorem nj_56_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_9 (fun _ h1 h2 => treeBlockF_at nb_56_10 h1 h2)
theorem nj_56_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_10 (fun _ h1 h2 => treeBlockF_at nb_56_11 h1 h2)
theorem nj_56_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_11 (fun _ h1 h2 => treeBlockF_at nb_56_12 h1 h2)
theorem nj_56_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_12 (fun _ h1 h2 => treeBlockF_at nb_56_13 h1 h2)
theorem nj_56_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_13 (fun _ h1 h2 => treeBlockF_at nb_56_14 h1 h2)
theorem nj_56_15 : ∀ i, 0 ≤ i → i < 512 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_14 (fun _ h1 h2 => treeBlockF_at nb_56_15 h1 h2)
theorem nj_56_16 : ∀ i, 0 ≤ i → i < 544 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_15 (fun _ h1 h2 => treeBlockF_at nb_56_16 h1 h2)
theorem nj_56_17 : ∀ i, 0 ≤ i → i < 576 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_16 (fun _ h1 h2 => treeBlockF_at nb_56_17 h1 h2)
theorem nj_56_18 : ∀ i, 0 ≤ i → i < 608 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_17 (fun _ h1 h2 => treeBlockF_at nb_56_18 h1 h2)
theorem nj_56_19 : ∀ i, 0 ≤ i → i < 640 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_18 (fun _ h1 h2 => treeBlockF_at nb_56_19 h1 h2)
theorem nj_56_20 : ∀ i, 0 ≤ i → i < 672 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_19 (fun _ h1 h2 => treeBlockF_at nb_56_20 h1 h2)
theorem nj_56_21 : ∀ i, 0 ≤ i → i < 704 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_20 (fun _ h1 h2 => treeBlockF_at nb_56_21 h1 h2)
theorem nj_56_22 : ∀ i, 0 ≤ i → i < 736 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_21 (fun _ h1 h2 => treeBlockF_at nb_56_22 h1 h2)
theorem nj_56_23 : ∀ i, 0 ≤ i → i < 768 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_22 (fun _ h1 h2 => treeBlockF_at nb_56_23 h1 h2)
theorem nj_56_24 : ∀ i, 0 ≤ i → i < 800 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_23 (fun _ h1 h2 => treeBlockF_at nb_56_24 h1 h2)
theorem nj_56_25 : ∀ i, 0 ≤ i → i < 832 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_24 (fun _ h1 h2 => treeBlockF_at nb_56_25 h1 h2)
theorem nj_56_26 : ∀ i, 0 ≤ i → i < 864 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_25 (fun _ h1 h2 => treeBlockF_at nb_56_26 h1 h2)
theorem nj_56_27 : ∀ i, 0 ≤ i → i < 896 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_26 (fun _ h1 h2 => treeBlockF_at nb_56_27 h1 h2)
theorem nj_56_28 : ∀ i, 0 ≤ i → i < 928 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_27 (fun _ h1 h2 => treeBlockF_at nb_56_28 h1 h2)
theorem nj_56_29 : ∀ i, 0 ≤ i → i < 960 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_28 (fun _ h1 h2 => treeBlockF_at nb_56_29 h1 h2)
theorem nj_56_30 : ∀ i, 0 ≤ i → i < 992 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_29 (fun _ h1 h2 => treeBlockF_at nb_56_30 h1 h2)
theorem nj_56_31 : ∀ i, 0 ≤ i → i < 1024 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_30 (fun _ h1 h2 => treeBlockF_at nb_56_31 h1 h2)
theorem nj_56_32 : ∀ i, 0 ≤ i → i < 1056 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_31 (fun _ h1 h2 => treeBlockF_at nb_56_32 h1 h2)
theorem nj_56_33 : ∀ i, 0 ≤ i → i < 1088 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_32 (fun _ h1 h2 => treeBlockF_at nb_56_33 h1 h2)
theorem nj_56_34 : ∀ i, 0 ≤ i → i < 1120 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_33 (fun _ h1 h2 => treeBlockF_at nb_56_34 h1 h2)
theorem nj_56_35 : ∀ i, 0 ≤ i → i < 1152 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_34 (fun _ h1 h2 => treeBlockF_at nb_56_35 h1 h2)
theorem nj_56_36 : ∀ i, 0 ≤ i → i < 1184 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_35 (fun _ h1 h2 => treeBlockF_at nb_56_36 h1 h2)
theorem nj_56_37 : ∀ i, 0 ≤ i → i < 1216 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_36 (fun _ h1 h2 => treeBlockF_at nb_56_37 h1 h2)
theorem nj_56_38 : ∀ i, 0 ≤ i → i < 1248 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_37 (fun _ h1 h2 => treeBlockF_at nb_56_38 h1 h2)
theorem nj_56_39 : ∀ i, 0 ≤ i → i < 1280 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_38 (fun _ h1 h2 => treeBlockF_at nb_56_39 h1 h2)
theorem nj_56_40 : ∀ i, 0 ≤ i → i < 1312 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_39 (fun _ h1 h2 => treeBlockF_at nb_56_40 h1 h2)
theorem nj_56_41 : ∀ i, 0 ≤ i → i < 1344 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_40 (fun _ h1 h2 => treeBlockF_at nb_56_41 h1 h2)
theorem nj_56_42 : ∀ i, 0 ≤ i → i < 1376 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_41 (fun _ h1 h2 => treeBlockF_at nb_56_42 h1 h2)
theorem nj_56_43 : ∀ i, 0 ≤ i → i < 1408 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_42 (fun _ h1 h2 => treeBlockF_at nb_56_43 h1 h2)
theorem nj_56_44 : ∀ i, 0 ≤ i → i < 1440 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_43 (fun _ h1 h2 => treeBlockF_at nb_56_44 h1 h2)
theorem nj_56_45 : ∀ i, 0 ≤ i → i < 1472 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_44 (fun _ h1 h2 => treeBlockF_at nb_56_45 h1 h2)
theorem nj_56_46 : ∀ i, 0 ≤ i → i < 1504 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_45 (fun _ h1 h2 => treeBlockF_at nb_56_46 h1 h2)
theorem nj_56_47 : ∀ i, 0 ≤ i → i < 1536 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_46 (fun _ h1 h2 => treeBlockF_at nb_56_47 h1 h2)
theorem nj_56_48 : ∀ i, 0 ≤ i → i < 1568 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_47 (fun _ h1 h2 => treeBlockF_at nb_56_48 h1 h2)
theorem nj_56_49 : ∀ i, 0 ≤ i → i < 1600 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_48 (fun _ h1 h2 => treeBlockF_at nb_56_49 h1 h2)
theorem nj_56_50 : ∀ i, 0 ≤ i → i < 1632 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_49 (fun _ h1 h2 => treeBlockF_at nb_56_50 h1 h2)
theorem nj_56_51 : ∀ i, 0 ≤ i → i < 1664 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_50 (fun _ h1 h2 => treeBlockF_at nb_56_51 h1 h2)
theorem nj_56_52 : ∀ i, 0 ≤ i → i < 1696 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_51 (fun _ h1 h2 => treeBlockF_at nb_56_52 h1 h2)
theorem nj_56_53 : ∀ i, 0 ≤ i → i < 1728 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_52 (fun _ h1 h2 => treeBlockF_at nb_56_53 h1 h2)
theorem nj_56_54 : ∀ i, 0 ≤ i → i < 1760 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_53 (fun _ h1 h2 => treeBlockF_at nb_56_54 h1 h2)
theorem nj_56_55 : ∀ i, 0 ≤ i → i < 1792 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_54 (fun _ h1 h2 => treeBlockF_at nb_56_55 h1 h2)
theorem nj_56_56 : ∀ i, 0 ≤ i → i < 1824 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_55 (fun _ h1 h2 => treeBlockF_at nb_56_56 h1 h2)
theorem nj_56_57 : ∀ i, 0 ≤ i → i < 1856 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_56 (fun _ h1 h2 => treeBlockF_at nb_56_57 h1 h2)
theorem nj_56_58 : ∀ i, 0 ≤ i → i < 1888 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_57 (fun _ h1 h2 => treeBlockF_at nb_56_58 h1 h2)
theorem nj_56_59 : ∀ i, 0 ≤ i → i < 1920 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_58 (fun _ h1 h2 => treeBlockF_at nb_56_59 h1 h2)
theorem nj_56_60 : ∀ i, 0 ≤ i → i < 1952 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_59 (fun _ h1 h2 => treeBlockF_at nb_56_60 h1 h2)
theorem nj_56_61 : ∀ i, 0 ≤ i → i < 1984 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_60 (fun _ h1 h2 => treeBlockF_at nb_56_61 h1 h2)
theorem nj_56_62 : ∀ i, 0 ≤ i → i < 2016 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_61 (fun _ h1 h2 => treeBlockF_at nb_56_62 h1 h2)
theorem nj_56_63 : ∀ i, 0 ≤ i → i < 2048 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_62 (fun _ h1 h2 => treeBlockF_at nb_56_63 h1 h2)
theorem nj_56_64 : ∀ i, 0 ≤ i → i < 2080 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_63 (fun _ h1 h2 => treeBlockF_at nb_56_64 h1 h2)
theorem nj_56_65 : ∀ i, 0 ≤ i → i < 2112 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_64 (fun _ h1 h2 => treeBlockF_at nb_56_65 h1 h2)
theorem nj_56_66 : ∀ i, 0 ≤ i → i < 2144 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_65 (fun _ h1 h2 => treeBlockF_at nb_56_66 h1 h2)
theorem nj_56_67 : ∀ i, 0 ≤ i → i < 2176 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_66 (fun _ h1 h2 => treeBlockF_at nb_56_67 h1 h2)
theorem nj_56_68 : ∀ i, 0 ≤ i → i < 2208 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_67 (fun _ h1 h2 => treeBlockF_at nb_56_68 h1 h2)
theorem nj_56_69 : ∀ i, 0 ≤ i → i < 2240 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_68 (fun _ h1 h2 => treeBlockF_at nb_56_69 h1 h2)
theorem nj_56_70 : ∀ i, 0 ≤ i → i < 2272 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_69 (fun _ h1 h2 => treeBlockF_at nb_56_70 h1 h2)
theorem nj_56_71 : ∀ i, 0 ≤ i → i < 2304 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_70 (fun _ h1 h2 => treeBlockF_at nb_56_71 h1 h2)
theorem nj_56_72 : ∀ i, 0 ≤ i → i < 2326 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := block_join nj_56_71 (fun _ h1 h2 => treeBlockF_at nb_56_72 h1 h2)
theorem nc_56 : ∀ i, 0 ≤ i → i < 2326 → (dagCheckNodeF m_56 g_56 bds_56 2326 (dagTraceF m_56 s_56 9 f_56) l_56) i = true := nj_56_72
theorem lb_56 : LowerBin m_56 s_56 g_56 10 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_56 sub_56 gl_56 rc_56 nc_56

def m_57 : Nat := 0xffffffff
def s_57 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_57 : Nat := 0x11573f7f
def bds_57 : List (Nat × List Nat × Nat × Nat) := [(m_34, s_34, 5, g_34), (m_39, s_39, 5, g_39), (m_42, s_42, 5, g_42), (m_45, s_45, 5, g_45), (m_7, s_7, 4, g_7), (m_13, s_13, 4, g_13)]
theorem kn_57 : KnownBin bds_57 := by
  intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_34
  · exact lb_39
  · exact lb_42
  · exact lb_45
  · exact lb_7
  · exact lb_13
theorem sub_57 : ∀ b ∈ bds_57, m_57 &&& b.1 = b.1 := by intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_57 : ∀ b ∈ bds_57, canon b.1 g_57 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_57 : Nat → Nat × Nat := unpackForestF 0x25239968c2503502d2e1b498694619528ad261950861740b47824e1fa4e7e9180a4b72d69e12872969ca56724a40a3b66969b150669599a3d664a40a33604f98015024ed593e564b5613056054093344d29124a44539114a4451919544605111420248cdb5d3c8e0f13836d44e15036d1408472cd68c1502cd58b139020fc545a2494091501515852421490051411a4c0505616500503e020dc124a0e8e0114e0a4f0114a0451811420207c001f 7 11
def l_57 : Nat → Nat → Option Nat := unpackLinksF 0x3a8750e83b9b68ed0d83b03516a0c3384300e00b6b6c2d85a1b4168294520a414468851096d2c2584388610c21842178cf01e03c0780f01e03c0744d19a0340680c899031156cac1582a154091920240480889089f23e07c0f09e03a2524a01402624c0909202403540e001 0x25a30911564355988e5ba31320f650358a5422c5c8ad24e0459117a4349769663a518c54a21508617488553611609387ad2a024e76929fa466e909e1287ad69a34276969d256688f54931724a531216c541a34a6e969aa56688f59929444856a42508c9893e4c4c9692d100b4201d6005561305a929713e444c9692d04075581548551181452d29424a4e539314a4a51911423e8e0f13838541035d32d648b553ad44db45180d8c15032d68bb562c4e41131141185036269409150161306846160f8693016500a45a2315882421e90021491c504605614138503e0e8e0293c10928314e0852819460450a4b4b84d1df24b708ed92335e4ed51334248cd0472a0fc48370207c001f 11 4 11 7 5
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsF m_57 g_57 bds_57 (dagRefF 77 (dagTraceF m_57 s_57 7 f_57) l_57 0) s_57 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_0 : treeBlockF 0 32 (dagCheckNodeF m_57 g_57 bds_57 77 (dagTraceF m_57 s_57 7 f_57) l_57) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_1 : treeBlockF 32 64 (dagCheckNodeF m_57 g_57 bds_57 77 (dagTraceF m_57 s_57 7 f_57) l_57) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_2 : treeBlockF 64 77 (dagCheckNodeF m_57 g_57 bds_57 77 (dagTraceF m_57 s_57 7 f_57) l_57) = true := by decide +kernel
theorem nj_57_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_57 g_57 bds_57 77 (dagTraceF m_57 s_57 7 f_57) l_57) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_57_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_57_1 h1 h2)
theorem nj_57_2 : ∀ i, 0 ≤ i → i < 77 → (dagCheckNodeF m_57 g_57 bds_57 77 (dagTraceF m_57 s_57 7 f_57) l_57) i = true := block_join nj_57_1 (fun _ h1 h2 => treeBlockF_at nb_57_2 h1 h2)
theorem nc_57 : ∀ i, 0 ≤ i → i < 77 → (dagCheckNodeF m_57 g_57 bds_57 77 (dagTraceF m_57 s_57 7 f_57) l_57) i = true := nj_57_2
theorem lb_57 : LowerBin m_57 s_57 g_57 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_57 sub_57 gl_57 rc_57 nc_57

def g_58 : Nat := 0x117175711573f7f
def bds_58 : List (Nat × List Nat × Nat × Nat) := [(m_56, s_56, 10, g_56), (m_53, s_53, 9, g_53), (m_52, s_52, 9, g_52), (m_50, s_50, 9, g_50), (m_54, s_54, 8, g_54), (m_47, s_47, 8, g_47), (m_57, s_57, 8, g_57), (m_55, s_55, 7, g_55), (m_51, s_51, 7, g_51), (m_49, s_49, 7, g_49), (m_48, s_48, 7, g_48), (m_46, s_46, 7, g_46), (m_23, s_23, 6, g_23), (m_29, s_29, 5, g_29), (m_17, s_17, 5, g_17), (m_16, s_16, 5, g_16), (m_27, s_27, 5, g_27), (m_28, s_28, 5, g_28), (m_18, s_18, 5, g_18), (m_13, s_13, 4, g_13), (m_3, s_3, 4, g_3), (m_1, s_1, 4, g_1)]
theorem kn_58 : KnownBin bds_58 := by
  intro b hb; simp only [bds_58, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_56
  · exact lb_53
  · exact lb_52
  · exact lb_50
  · exact lb_54
  · exact lb_47
  · exact lb_57
  · exact lb_55
  · exact lb_51
  · exact lb_49
  · exact lb_48
  · exact lb_46
  · exact lb_23
  · exact lb_29
  · exact lb_17
  · exact lb_16
  · exact lb_27
  · exact lb_28
  · exact lb_18
  · exact lb_13
  · exact lb_3
  · exact lb_1
theorem sub_58 : ∀ b ∈ bds_58, fullMask &&& b.1 = b.1 := by intro b hb; simp only [bds_58, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_58 : ∀ b ∈ bds_58, canon b.1 g_58 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_58, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_58 : Nat → Nat × Nat := unpackForestF 0x89b5789b558995b899578995500c5f8756d8745e873458714500c5b85b6d8596d00c5783b5f843558395f8346c7d5657d46e7d46d811537d3477d3457d14b7e35d7e9527e3457d1477d14500c5378c5b78c5978c5778c557895b7986c789577895500b5f76c6d76c617696d00b5775c646f56f7447c7417d6f5676f46f6f46e7217d6f4676f4627097e6f14b6f1476f14500b4f60d6e6d94560d6b6c1476c14560d6360d626a14f6a1476946c6914560c6b6746c67c606714560c6360b4e65e7a6095f64c6b6095d62256622546215662154616726117e6095300b4757c5b57c5957c5757c555d47d5d47157b5757b555bc6457b4f5856958568585615834e5815e5815257b470095f5695453c5f5596c53c575395e53956539460095b4dc6d4dc614db6d5147c4db4f4fd714fd704db474e23f4e2374d86c009574c95444c5f4b26c4b16c44c5749b4f49b474496e48b554495e47b4d44956449464534f4595c4534744814009533cd6f4337d3cd673cc6f3cc6e3cc673cc62404643cb6f3f47c3cb673e46c3cb573cb473cb450094f3356b335633a9643346f395703917c33467381543345f3736f3325e3634f3316e3557034b673315633d63331460094b24d6e24d6b3134524d6324d622f34f2f3472e46c2e34524c6b2cc6c2cb4524c632bd6824b6f2a5712a57024b6728e7a28e7224b5f2756b2756324b5d25e7225c6c24b4f2494e00947239641756f2297c17567219641746f1fd7c1fa7c1f97c174671e9541de721d96c174571ab6f1b4531b25f1b24f1a95c1725619365193471716e1715e17d6f1714600943161640ed6f151541456e141540ed6b1317c0ed6710a5610a5410956109540ed630e96e0e95e0e9560093b0dc680156f0c67d0c4580156b0b470015670a57c0967509458015630146e0146b0636e063660603401463014620145e0145b03d620145a014560145301d6e01452009370003f 9 11
def l_58 : Nat → Nat → Option Nat := unpackLinksF 0x3560d583560d583560cdc3322cc072e1cb071a9c607161c127040c103021bf0ef82be02f80bd86f22bc06f00bc02f00bb86e83b90ac50b102c40b102c40b102c40b086c20a9baa41a886a01a49e920a406900a4028c2a3028c0a3028a1a2828a0a206880a2026529902640980a5c2960a50493864e093824a29282443910244090863e28f063c08d8e3608c8a3208c823208c822a48a82243804a000800200080020008001fc27f01fc07d8df607d81f607d81f607d81e8774add207405d007385ce07381ce07115c407101c407101be36f81be06d91b606d81b22691da4067119a16681905640190063098c062858a06205880620188061858225d1d7215c816e25b816e05b816e05b816a25a816625981641590164051414214f893e04e893a04e813434d013024b852a24a812814a012614905240488510944010e143810a2420508042010424100fe33f80fe03e0cf803d08f403d00f023c00f003b08ec03b00e823a00e803908e403140c403008c002f84be02e88ba02e80ba02c90b202c04b002a8ca812a00a802a00a2327889e027809a226809a026048692180822208080120007c21f007a11e807a01e807a01c907201c80720191c640178c5c117005821600542150052114804c313004c013004c013004631180460118046011044401100440108426e00c8001 0x8856e81d6d88c6981c616e35d8bb578b3557534f3215d8a95b8a157899554394f231431593b0d137834640c9371493b2e1576935788d6d8845e68b5787b453b95b2d957871451393b0b9374314f7434f8246d82c518636d73b4f8596d4294f221431293b0a9378435584b5f8395f0a1378346c099377ea54811537e1452c9577e9527f35d7e3451213a673571193a81d6d82d658246e81c6d66b577134d80b47803453b15b2c1574094d7f94b7d9477d1451013b089377986c6e45d7c45b7bc597b4577ac55714510815d7a15b79157789553f94f3a14b2b1472114320941399592014277c6d774617696d3e94f3894b299471f14375c6474c7c7417d7217d7097e7556f73d677346f72c6e71c677146266356663465b16f5616b509674c1633795b251570494d7014b6f9476f1456596d6d94562d70639706246063160619615994d6c9476c1451e1536a94f6a14769c6c6496d6914567c606846c671455916f65e7a59d725897e64c6b4b96263a5663254629566215461e725827e6117e6e56e6d56b6bd636b56268c6b66c636635e6634e5796f5516b4f1674a9636515f6415d02955609533d94f1d1435dc7d5d4715bc6459356593465ad695a56859d615935e5934e5895e581523245d5fc5b5f4595ec575e45540c510835d5cb575c3555b34f57b47569545596c5645f554575495e54156539465147c4a17d4e87c505714fd704997d4e07c4ea3f4e23752c6d5246151b6d50b4f4f3474916d4d86c4a17e479644c95446014458144ba6c4997e4b16c4895c450144a34f49b4748b5547b4d4595c4634f453474c45f4ac574916e4815e47156469464481422c6423c7c4337d404643715a3f47c349453e46c43d6f42d674246f41c6e4146740c623fb6f3eb673db5704b4d3d3473cb453695a2495624946341452d1542e954339463725e3a96439d703917c349563617e381541b9443736f1a9443634f3557034b6733d633bd6b3b5633a46f38c6737c5f36a5e3596e34156331462936d28b6d313452635f2fb4f2f3472ec6c27b6d2e3452d46c2736d2cb452bd681c9422ad712a5702967a28e7227d6b275632667225c6c3256e31d6b30d63305622dc6b2c4632b36f29b672835f26b5d02b552534f2495e1815d2494e1a14223964179462297c1ca562196420d7c2027c1f97c1996c1e9541e6721917e1d96c1b95c1c4531ba5f1b24f1cb6f1a95c19b651934717d6f2356f225672146f1f4671d4571a2561896e1815e1714614e7e161641515414d6e141541317c1225611a54111561095415d6f13d6b12d67105630f96e0f15e0e9560cd790dc6801c500a5740ce7d0c45809d610b4700a57c09e7503c68094580736e06b660603403d6201d6e0d56f0bd6b0ad6708d630846e07c6b05c630546204c5e0445b0345a02c5602453014528945f86c5b854577cc537835f763576eb4f603475715f5315b4d157441533c14f3294b24147169430e13b009370003f 14 5 11 9 6
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsF fullMask g_58 bds_58 (dagRefF 280 (dagTraceF fullMask rootStock 11 f_58) l_58 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_0 : treeBlockF 0 32 (dagCheckNodeF fullMask g_58 bds_58 280 (dagTraceF fullMask rootStock 11 f_58) l_58) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_1 : treeBlockF 32 64 (dagCheckNodeF fullMask g_58 bds_58 280 (dagTraceF fullMask rootStock 11 f_58) l_58) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_2 : treeBlockF 64 96 (dagCheckNodeF fullMask g_58 bds_58 280 (dagTraceF fullMask rootStock 11 f_58) l_58) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_3 : treeBlockF 96 128 (dagCheckNodeF fullMask g_58 bds_58 280 (dagTraceF fullMask rootStock 11 f_58) l_58) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_4 : treeBlockF 128 160 (dagCheckNodeF fullMask g_58 bds_58 280 (dagTraceF fullMask rootStock 11 f_58) l_58) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_5 : treeBlockF 160 192 (dagCheckNodeF fullMask g_58 bds_58 280 (dagTraceF fullMask rootStock 11 f_58) l_58) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_6 : treeBlockF 192 224 (dagCheckNodeF fullMask g_58 bds_58 280 (dagTraceF fullMask rootStock 11 f_58) l_58) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_7 : treeBlockF 224 256 (dagCheckNodeF fullMask g_58 bds_58 280 (dagTraceF fullMask rootStock 11 f_58) l_58) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_8 : treeBlockF 256 280 (dagCheckNodeF fullMask g_58 bds_58 280 (dagTraceF fullMask rootStock 11 f_58) l_58) = true := by decide +kernel
theorem nj_58_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF fullMask g_58 bds_58 280 (dagTraceF fullMask rootStock 11 f_58) l_58) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_58_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_58_1 h1 h2)
theorem nj_58_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF fullMask g_58 bds_58 280 (dagTraceF fullMask rootStock 11 f_58) l_58) i = true := block_join nj_58_1 (fun _ h1 h2 => treeBlockF_at nb_58_2 h1 h2)
theorem nj_58_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF fullMask g_58 bds_58 280 (dagTraceF fullMask rootStock 11 f_58) l_58) i = true := block_join nj_58_2 (fun _ h1 h2 => treeBlockF_at nb_58_3 h1 h2)
theorem nj_58_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF fullMask g_58 bds_58 280 (dagTraceF fullMask rootStock 11 f_58) l_58) i = true := block_join nj_58_3 (fun _ h1 h2 => treeBlockF_at nb_58_4 h1 h2)
theorem nj_58_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF fullMask g_58 bds_58 280 (dagTraceF fullMask rootStock 11 f_58) l_58) i = true := block_join nj_58_4 (fun _ h1 h2 => treeBlockF_at nb_58_5 h1 h2)
theorem nj_58_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF fullMask g_58 bds_58 280 (dagTraceF fullMask rootStock 11 f_58) l_58) i = true := block_join nj_58_5 (fun _ h1 h2 => treeBlockF_at nb_58_6 h1 h2)
theorem nj_58_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF fullMask g_58 bds_58 280 (dagTraceF fullMask rootStock 11 f_58) l_58) i = true := block_join nj_58_6 (fun _ h1 h2 => treeBlockF_at nb_58_7 h1 h2)
theorem nj_58_8 : ∀ i, 0 ≤ i → i < 280 → (dagCheckNodeF fullMask g_58 bds_58 280 (dagTraceF fullMask rootStock 11 f_58) l_58) i = true := block_join nj_58_7 (fun _ h1 h2 => treeBlockF_at nb_58_8 h1 h2)
theorem nc_58 : ∀ i, 0 ≤ i → i < 280 → (dagCheckNodeF fullMask g_58 bds_58 280 (dagTraceF fullMask rootStock 11 f_58) l_58) i = true := nj_58_8
theorem lb_58 : LowerBin fullMask rootStock g_58 12 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_58 sub_58 gl_58 rc_58 nc_58

def wg : List Gate := [⟨GateOp.and, [5, 4]⟩, ⟨GateOp.or, [5, 4]⟩, ⟨GateOp.and, [4, 3]⟩, ⟨GateOp.or, [3, 0]⟩, ⟨GateOp.and, [7, 0]⟩, ⟨GateOp.and, [6, 2]⟩, ⟨GateOp.or, [11, 10]⟩, ⟨GateOp.and, [9, 2]⟩, ⟨GateOp.or, [8, 13]⟩, ⟨GateOp.and, [14, 12]⟩, ⟨GateOp.or, [14, 12]⟩, ⟨GateOp.and, [16, 1]⟩, ⟨GateOp.or, [15, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 4004036736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276676776 * 2 ^ 32 + 4004036736)) (13 - 1) := by
  rw [show canon fullMask (4276676776 * 2 ^ 32 + 4004036736) = g_58 by decide]
  exact lb_58

end PEqualNP.Outside.L_meta_47875

theorem PEqualNP.Outside.L_meta_47875 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676776 * 2 ^ 32 + 4004036736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 4004036736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_47875.table2_from_lowerBin (4276676776 * 2 ^ 32 + 4004036736) 13 PEqualNP.Outside.L_meta_47875.root_lb PEqualNP.Outside.L_meta_47875.wg 18 rfl PEqualNP.Outside.L_meta_47875.wfits PEqualNP.Outside.L_meta_47875.weval
