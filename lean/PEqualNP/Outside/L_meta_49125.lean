import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_49125

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

def m_0 : Nat := 0xf000f0000000000
def s_0 : List Nat := [0x500050000000000, 0x300030000000000, 0xf0000000000]
def g_0 : Nat := 0x100070000000000
def ep_0 : Nat := 0x600000000000000000000000000000000000000000001000200000000000100040000000000
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

def m_1 : Nat := 0x5500550000000000
def s_1 : List Nat := [0x1100110000000000, 0x500050000000000, 0x550000000000]
def g_1 : Nat := 0x100150000000000
def ep_1 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000000000000000000
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

def m_2 : Nat := 0x3300330000000000
def s_2 : List Nat := [0x1100110000000000, 0x300030000000000, 0x330000000000]
def g_2 : Nat := 0x100130000000000
def ep_2 : Nat := 0x1200000000000000000000000000010002000000000000000000000000000100100000000000
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

def m_4 : Nat := 0xff000000
def s_4 : List Nat := [0x55000000, 0x33000000, 0xf000000]
def g_4 : Nat := 0x17000000
def ep_4 : Nat := 0x600000000000000120000000000000014000000
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

def m_5 : Nat := 0x2222222200000000
def s_5 : List Nat := [0x202020200000000, 0x22002200000000, 0x222200000000]
def g_5 : Nat := 0x2022200000000
def ep_5 : Nat := 0x220000000000002002000000000000202000000000000000000000000000000000000000000
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

def m_6 : Nat := 0x4444444400000000
def s_6 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_6 : Nat := 0x4044400000000
def ep_6 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
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

def m_7 : Nat := 0x5050505000000000
def s_7 : List Nat := [0x1010101000000000, 0x50005000000000, 0x505000000000]
def g_7 : Nat := 0x10105000000000
def ep_7 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000000000000000000
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

def m_8 : Nat := 0x3030303000000000
def s_8 : List Nat := [0x1010101000000000, 0x30003000000000, 0x303000000000]
def g_8 : Nat := 0x10103000000000
def ep_8 : Nat := 0x1020000000000010002000000000000000000000000000000000000000000010100000000000
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

def m_9 : Nat := 0x5000500050005000
def s_9 : List Nat := [0x1000100010001000, 0x500000005000, 0x50005000]
def g_9 : Nat := 0x100010005000
def ep_9 : Nat := 0x1000400000001000000040000000000000000000000000000000000000001000100000000000000000000000
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

def m_10 : Nat := 0x3333000000000000
def s_10 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_10 : Nat := 0x113000000000000
def ep_10 : Nat := 0x12000000000000010200000000000000000000000000000110000000000000
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

def m_11 : Nat := 0x5555000000000000
def s_11 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_11 : Nat := 0x115000000000000
def ep_11 : Nat := 0x14000000000000010400000000000001100000000000000000000000000000
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

def m_12 : Nat := 0xc0c00000c0c0
def s_12 : List Nat := [0x404000004040, 0xc0000000c0, 0xc0c0]
def g_12 : Nat := 0x40000040c0
def ep_12 : Nat := 0x408000000000000000000000004000000080000000000000000000000000000000000000004000004000
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

def m_13 : Nat := 0x4040404040404040
def s_13 : List Nat := [0x40004000400040, 0x404000004040, 0x40404040]
def g_13 : Nat := 0x4000404040
def ep_13 : Nat := 0x40400000000040000040000000004000400000000000000000000000000000000000000000000000000000
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

def m_15 : Nat := 0xc000c000c000c0
def s_15 : List Nat := [0x40004000400040, 0xc0000000c0, 0xc000c0]
def g_15 : Nat := 0x40004000c0
def ep_15 : Nat := 0x40008000000040000000800000000000000000000000000000000000000000000000000000004000400000
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

def m_16 : Nat := 0xf0f000000000000
def s_16 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_16 : Nat := 0x107000000000000
def ep_16 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
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

def m_17 : Nat := 0x4400440044004400
def s_17 : List Nat := [0x400040004000400, 0x440000004400, 0x44004400]
def g_17 : Nat := 0x40004004400
def ep_17 : Nat := 0x400400000000400000040000000000000000000000004000400000000000000000000000000000000000000
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

def m_18 : Nat := 0x5500000055000000
def s_18 : List Nat := [0x1100000011000000, 0x500000005000000, 0x55000000]
def g_18 : Nat := 0x100000015000000
def ep_18 : Nat := 0x1400000000000000000000000000000000000000010000000400000001000000100000000000000000000000
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

def m_19 : Nat := 0x3300000033000000
def s_19 : List Nat := [0x1100000011000000, 0x300000003000000, 0x33000000]
def g_19 : Nat := 0x100000013000000
def ep_19 : Nat := 0x1200000000000000000000000000000000000000010000000200000000000000000000000100000010000000
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

def m_20 : Nat := 0xf0000000f000000
def s_20 : List Nat := [0x500000005000000, 0x300000003000000, 0xf000000]
def g_20 : Nat := 0x100000007000000
def ep_20 : Nat := 0x600000000000000000000000000000000000000000000000000000001000000020000000100000004000000
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

def m_21 : Nat := 0xf0f000000000
def s_21 : List Nat := [0x505000000000, 0x303000000000, 0xf000000000]
def g_21 : Nat := 0x107000000000
def ep_21 : Nat := 0x6000000000000000000000000000001020000000000000104000000000
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

def m_22 : Nat := 0xc0c0c0c0
def s_22 : List Nat := [0x40404040, 0xc000c0, 0xc0c0]
def g_22 : Nat := 0x4040c0
def ep_22 : Nat := 0x40800000000000400080000000000000000000000000000000000000000000404000
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

def m_23 : Nat := 0xff0000000000
def s_23 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_23 : Nat := 0x170000000000
def ep_23 : Nat := 0x6000000000000001200000000000000140000000000
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

def m_24 : Nat := 0x4444000044440000
def s_24 : List Nat := [0x404000004040000, 0x44000000440000, 0x44440000]
def g_24 : Nat := 0x4000004440000
def ep_24 : Nat := 0x440000000000000000000000004000000400000000400000400000000000000000000000000000000000000
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

def m_26 : Nat := 0xff00ff0000000000
def s_26 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_26 : Nat := 0x100170000000000
def ep_26 : Nat := 0x1600000000000000000000000000010006000000000001001200000000000100140000000000
theorem epk_26 : ep_26 = edgePack m_26 g_26 := by decide +kernel
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_23, s_23, 4, g_23), (m_1, s_1, 4, g_1), (m_2, s_2, 4, g_2)]
theorem kn_26 : KnownBin bds_26 := by
  intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_0
  · exact lb_23
  · exact lb_1
  · exact lb_2
theorem sub_26 : ∀ b ∈ bds_26, m_26 &&& b.1 = b.1 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_26 : ∀ b ∈ bds_26, canon b.1 g_26 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_26_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_26_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_26 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_26_1 (Nat.sub p 32)) (cc_26_0 p) (Nat.blt p 32)
def f_26 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV4 m_26 g_26 ep_26 43 bds_26 (dagTraceF m_26 s_26 6 f_26) (cur_26 0) s_26 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_26_0 : treeBlockF 0 32 (dagCheckNodeV4 m_26 g_26 ep_26 bds_26 43 (dagTraceF m_26 s_26 6 f_26) cur_26) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_26_1 : treeBlockF 32 43 (dagCheckNodeV4 m_26 g_26 ep_26 bds_26 43 (dagTraceF m_26 s_26 6 f_26) cur_26) = true := by decide +kernel
theorem nj_26_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_26 g_26 ep_26 bds_26 43 (dagTraceF m_26 s_26 6 f_26) cur_26) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_26_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_26_1 h1 h2)
theorem nc_26 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_26 g_26 ep_26 bds_26 43 (dagTraceF m_26 s_26 6 f_26) cur_26) i = true := nj_26_1
theorem lb_26 : LowerBin m_26 s_26 g_26 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_26 kn_26 sub_26 gl_26 rc_26 nc_26

def m_27 : Nat := 0xffff000000000000
def s_27 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_27 : Nat := 0x117000000000000
def ep_27 : Nat := 0x16000000000000010600000000000001120000000000000114000000000000
theorem epk_27 : ep_27 = edgePack m_27 g_27 := by decide +kernel
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16), (m_14, s_14, 4, g_14), (m_11, s_11, 4, g_11), (m_10, s_10, 4, g_10)]
theorem kn_27 : KnownBin bds_27 := by
  intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_16
  · exact lb_14
  · exact lb_11
  · exact lb_10
theorem sub_27 : ∀ b ∈ bds_27, m_27 &&& b.1 = b.1 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_27 : ∀ b ∈ bds_27, canon b.1 g_27 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_27_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_27_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_27 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_27_1 (Nat.sub p 32)) (cc_27_0 p) (Nat.blt p 32)
def f_27 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV4 m_27 g_27 ep_27 43 bds_27 (dagTraceF m_27 s_27 6 f_27) (cur_27 0) s_27 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_0 : treeBlockF 0 32 (dagCheckNodeV4 m_27 g_27 ep_27 bds_27 43 (dagTraceF m_27 s_27 6 f_27) cur_27) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_1 : treeBlockF 32 43 (dagCheckNodeV4 m_27 g_27 ep_27 bds_27 43 (dagTraceF m_27 s_27 6 f_27) cur_27) = true := by decide +kernel
theorem nj_27_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_27 g_27 ep_27 bds_27 43 (dagTraceF m_27 s_27 6 f_27) cur_27) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_27_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_27_1 h1 h2)
theorem nc_27 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_27 g_27 ep_27 bds_27 43 (dagTraceF m_27 s_27 6 f_27) cur_27) i = true := nj_27_1
theorem lb_27 : LowerBin m_27 s_27 g_27 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_27 kn_27 sub_27 gl_27 rc_27 nc_27

def m_28 : Nat := 0xf0f0f0f000000000
def s_28 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_28 : Nat := 0x10107000000000
def ep_28 : Nat := 0x1060000000000010006000000000000000000000000000101020000000000010104000000000
theorem epk_28 : ep_28 = edgePack m_28 g_28 := by decide +kernel
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3), (m_21, s_21, 4, g_21), (m_7, s_7, 4, g_7), (m_8, s_8, 4, g_8)]
theorem kn_28 : KnownBin bds_28 := by
  intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_3
  · exact lb_21
  · exact lb_7
  · exact lb_8
theorem sub_28 : ∀ b ∈ bds_28, m_28 &&& b.1 = b.1 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_28 : ∀ b ∈ bds_28, canon b.1 g_28 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_28_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_28_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_28 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_28_1 (Nat.sub p 32)) (cc_28_0 p) (Nat.blt p 32)
def f_28 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV4 m_28 g_28 ep_28 43 bds_28 (dagTraceF m_28 s_28 6 f_28) (cur_28 0) s_28 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28_0 : treeBlockF 0 32 (dagCheckNodeV4 m_28 g_28 ep_28 bds_28 43 (dagTraceF m_28 s_28 6 f_28) cur_28) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28_1 : treeBlockF 32 43 (dagCheckNodeV4 m_28 g_28 ep_28 bds_28 43 (dagTraceF m_28 s_28 6 f_28) cur_28) = true := by decide +kernel
theorem nj_28_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_28 g_28 ep_28 bds_28 43 (dagTraceF m_28 s_28 6 f_28) cur_28) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_28_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_28_1 h1 h2)
theorem nc_28 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_28 g_28 ep_28 bds_28 43 (dagTraceF m_28 s_28 6 f_28) cur_28) i = true := nj_28_1
theorem lb_28 : LowerBin m_28 s_28 g_28 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_28 kn_28 sub_28 gl_28 rc_28 nc_28

def m_29 : Nat := 0xcccccccc00000000
def s_29 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_29 : Nat := 0x4044400000000
def ep_29 : Nat := 0x440000000000004004000000000000404000000000000000000000000000004044400000000
theorem epk_29 : ep_29 = edgePack m_29 g_29 := by decide +kernel
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
theorem kn_29 : KnownBin bds_29 := by
  intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_6
theorem sub_29 : ∀ b ∈ bds_29, m_29 &&& b.1 = b.1 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_29 : ∀ b ∈ bds_29, canon b.1 g_29 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_29 : Nat → List (Nat × Nat) := fun _ => []
def f_29 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV4 m_29 g_29 ep_29 0 bds_29 (dagTraceF m_29 s_29 4 f_29) (cur_29 0) s_29 4 = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_29 g_29 ep_29 bds_29 0 (dagTraceF m_29 s_29 4 f_29) cur_29 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_29 : LowerBin m_29 s_29 g_29 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_29 kn_29 sub_29 gl_29 rc_29 nc_29

def m_30 : Nat := 0x3333333300000000
def s_30 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_30 : Nat := 0x113133300000000
def ep_30 : Nat := 0x1220000000000012002000000000010202000000000000000000000000000110100000000000
theorem epk_30 : ep_30 = edgePack m_30 g_30 := by decide +kernel
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2), (m_10, s_10, 4, g_10), (m_8, s_8, 4, g_8), (m_5, s_5, 4, g_5)]
theorem kn_30 : KnownBin bds_30 := by
  intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_2
  · exact lb_10
  · exact lb_8
  · exact lb_5
theorem sub_30 : ∀ b ∈ bds_30, m_30 &&& b.1 = b.1 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_30 : ∀ b ∈ bds_30, canon b.1 g_30 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_30_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8724381de0ee07323981c44b575a02d01642aa4550298940698435b9a80d406623301980c445a429214049844a123109c0064001 0x59003c6015407c9a07d3a36950b460fa10592a048cf1460a9f054b9d07a0c39201a830c4285a8825180a83d002c600c4040120310050280f4e07a6b69342c92a2450b20878f5a46ac94d2ca2874f5826a1c4e0626870f818720c320618830c018547826060d0805952980e400f180310100680c300c0a038c01a6015200b20078c02a8081340fa72cd29468c1f420b25269181c7c0e3d489e904d42a5a892506251e118287c0c3d0a17030a418440c21061003068202c624c0b2012d203e800d400e980310050680d300a90030c030480c300e980a0d0184015200c1207938d4945a460f21058f8a47442360b190e518626c0d2e06250811818741036060c878fc2c7742370b19874fe426e152f7093870fc1876b8370619850bc1856702706118306c102e000f 13 8191 5 31 10 1023 17 131071
def cc_30_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb817017bae0544a80580a014018811001 0x2e9c174d0f27059343c7c16390b19058c42c61514d84a2874f6626a152d8092d21341892a0450620870f5a06a142d4c12858c1f2493a4d0b24c29142c821e3d991a875383a7cf126942683124b08a0c410e1eb00d4702b104c0620078c1f2681520 11 2047 5 31 10 1023 17 131071
def cur_30 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_30_1 (Nat.sub p 32)) (cc_30_0 p) (Nat.blt p 32)
def f_30 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV4 m_30 g_30 ep_30 43 bds_30 (dagTraceF m_30 s_30 6 f_30) (cur_30 0) s_30 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_0 : treeBlockF 0 32 (dagCheckNodeV4 m_30 g_30 ep_30 bds_30 43 (dagTraceF m_30 s_30 6 f_30) cur_30) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_1 : treeBlockF 32 43 (dagCheckNodeV4 m_30 g_30 ep_30 bds_30 43 (dagTraceF m_30 s_30 6 f_30) cur_30) = true := by decide +kernel
theorem nj_30_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_30 g_30 ep_30 bds_30 43 (dagTraceF m_30 s_30 6 f_30) cur_30) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_30_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_30_1 h1 h2)
theorem nc_30 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_30 g_30 ep_30 bds_30 43 (dagTraceF m_30 s_30 6 f_30) cur_30) i = true := nj_30_1
theorem lb_30 : LowerBin m_30 s_30 g_30 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_30 kn_30 sub_30 gl_30 rc_30 nc_30

def m_31 : Nat := 0x5050505050505050
def s_31 : List Nat := [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050]
def g_31 : Nat := 0x10105010505050
def ep_31 : Nat := 0x1040400000001040000040000010004000400000000000000000000000101000100000000000000000000000
theorem epk_31 : ep_31 = edgePack m_31 g_31 := by decide +kernel
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7), (m_25, s_25, 4, g_25), (m_9, s_9, 4, g_9), (m_13, s_13, 4, g_13)]
theorem kn_31 : KnownBin bds_31 := by
  intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_7
  · exact lb_25
  · exact lb_9
  · exact lb_13
theorem sub_31 : ∀ b ∈ bds_31, m_31 &&& b.1 = b.1 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_31 : ∀ b ∈ bds_31, canon b.1 g_31 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_31_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_31_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
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

def m_32 : Nat := 0x5555555500000000
def s_32 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_32 : Nat := 0x115155500000000
def ep_32 : Nat := 0x1440000000000014004000000000010404000000000001101000000000000000000000000000
theorem epk_32 : ep_32 = edgePack m_32 g_32 := by decide +kernel
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1), (m_11, s_11, 4, g_11), (m_7, s_7, 4, g_7), (m_6, s_6, 4, g_6)]
theorem kn_32 : KnownBin bds_32 := by
  intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_1
  · exact lb_11
  · exact lb_7
  · exact lb_6
theorem sub_32 : ∀ b ∈ bds_32, m_32 &&& b.1 = b.1 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_32 : ∀ b ∈ bds_32, canon b.1 g_32 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_32_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8724381de0ee07323981c44b575a02d01642aa4550298940698435b9a80d406623301980c445a429214049844a123109c0064001 0x59003c6015407c9a07d3a36950b460fa10592a048cf1460a9f054b9d07a0c39201a830c4285a8825180a83d002c600c4040120310050280f4e07a6b69342c92a2450b20878f5a46ac94d2ca2874f5826a1c4e0626870f818720c320618830c018547826060d0805952980e400f180310100680c300c0a038c01a6015200b20078c02a8081340fa72cd29468c1f420b25269181c7c0e3d489e904d42a5a892506251e118287c0c3d0a17030a418440c21061003068202c624c0b2012d203e800d400e980310050680d300a90030c030480c300e980a0d0184015200c1207938d4945a460f21058f8a47442360b190e518626c0d2e06250811818741036060c878fc2c7742370b19874fe426e152f7093870fc1876b8370619850bc1856702706118306c102e000f 13 8191 5 31 10 1023 17 131071
def cc_32_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb817017bae0544a80580a014018811001 0x2e9c174d0f27059343c7c16390b19058c42c61514d84a2874f6626a152d8092d21341892a0450620870f5a06a142d4c12858c1f2493a4d0b24c29142c821e3d991a875383a7cf126942683124b08a0c410e1eb00d4702b104c0620078c1f2681520 11 2047 5 31 10 1023 17 131071
def cur_32 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_32_1 (Nat.sub p 32)) (cc_32_0 p) (Nat.blt p 32)
def f_32 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
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

def m_33 : Nat := 0xc0c0c0c0c0c0c0c0
def s_33 : List Nat := [0x4040404040404040, 0xc000c000c000c0, 0xc0c00000c0c0, 0xc0c0c0c0]
def g_33 : Nat := 0x40004040c0
def ep_33 : Nat := 0x40408000000040000040800000004000400080000000000000000000000000000000000000004000404000
theorem epk_33 : ep_33 = edgePack m_33 g_33 := by decide +kernel
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12), (m_22, s_22, 4, g_22), (m_13, s_13, 4, g_13), (m_15, s_15, 4, g_15)]
theorem kn_33 : KnownBin bds_33 := by
  intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_12
  · exact lb_22
  · exact lb_13
  · exact lb_15
theorem sub_33 : ∀ b ∈ bds_33, m_33 &&& b.1 = b.1 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_33 : ∀ b ∈ bds_33, canon b.1 g_33 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_33_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_33_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_33 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_33_1 (Nat.sub p 32)) (cc_33_0 p) (Nat.blt p 32)
def f_33 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
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

def m_34 : Nat := 0xcccc0000cccc
def s_34 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_34 : Nat := 0x444000044cc
def ep_34 : Nat := 0x408800000000000000000000004000000088000004000000000000000000000000000000044400004400
theorem epk_34 : ep_34 = edgePack m_34 g_34 := by decide +kernel
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
theorem kn_34 : KnownBin bds_34 := by
  intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_12
theorem sub_34 : ∀ b ∈ bds_34, m_34 &&& b.1 = b.1 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_34 : ∀ b ∈ bds_34, canon b.1 g_34 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_34 : Nat → List (Nat × Nat) := fun _ => []
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV4 m_34 g_34 ep_34 0 bds_34 (dagTraceF m_34 s_34 4 f_34) (cur_34 0) s_34 4 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_34 g_34 ep_34 bds_34 0 (dagTraceF m_34 s_34 4 f_34) cur_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_34 kn_34 sub_34 gl_34 rc_34 nc_34

def m_35 : Nat := 0x5555000055550000
def s_35 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_35 : Nat := 0x115000015550000
def ep_35 : Nat := 0x1440000000000000000000000014000000400000010400000400000001100000100000000000000000000000
theorem epk_35 : ep_35 = edgePack m_35 g_35 := by decide +kernel
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11), (m_18, s_18, 4, g_18), (m_25, s_25, 4, g_25), (m_24, s_24, 4, g_24)]
theorem kn_35 : KnownBin bds_35 := by
  intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_11
  · exact lb_18
  · exact lb_25
  · exact lb_24
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

def m_36 : Nat := 0x5500550055005500
def s_36 : List Nat := [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500]
def g_36 : Nat := 0x100150015005500
def ep_36 : Nat := 0x1400400000001400000040000000000000000000010004000400000001001000100000000000000000000000
theorem epk_36 : ep_36 = edgePack m_36 g_36 := by decide +kernel
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1), (m_18, s_18, 4, g_18), (m_9, s_9, 4, g_9), (m_17, s_17, 4, g_17)]
theorem kn_36 : KnownBin bds_36 := by
  intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_1
  · exact lb_18
  · exact lb_9
  · exact lb_17
theorem sub_36 : ∀ b ∈ bds_36, m_36 &&& b.1 = b.1 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_36 : ∀ b ∈ bds_36, canon b.1 g_36 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_36_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_36_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
def cur_36 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_36_1 (Nat.sub p 32)) (cc_36_0 p) (Nat.blt p 32)
def f_36 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV4 m_36 g_36 ep_36 43 bds_36 (dagTraceF m_36 s_36 6 f_36) (cur_36 0) s_36 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_0 : treeBlockF 0 32 (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 43 (dagTraceF m_36 s_36 6 f_36) cur_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_1 : treeBlockF 32 43 (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 43 (dagTraceF m_36 s_36 6 f_36) cur_36) = true := by decide +kernel
theorem nj_36_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 43 (dagTraceF m_36 s_36 6 f_36) cur_36) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_36_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_36_1 h1 h2)
theorem nc_36 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 43 (dagTraceF m_36 s_36 6 f_36) cur_36) i = true := nj_36_1
theorem lb_36 : LowerBin m_36 s_36 g_36 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_36 kn_36 sub_36 gl_36 rc_36 nc_36

def m_37 : Nat := 0xf0f00000f0f0
def s_37 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_37 : Nat := 0x1070000050f0
def ep_37 : Nat := 0x4080000000000000000000000060000000a0000000000000000000001020000000000000104000005000
theorem epk_37 : ep_37 = edgePack m_37 g_37 := by decide +kernel
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
theorem kn_37 : KnownBin bds_37 := by
  intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_12
theorem sub_37 : ∀ b ∈ bds_37, m_37 &&& b.1 = b.1 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_37 : ∀ b ∈ bds_37, canon b.1 g_37 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_37 : Nat → List (Nat × Nat) := fun _ => []
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV4 m_37 g_37 ep_37 0 bds_37 (dagTraceF m_37 s_37 4 f_37) (cur_37 0) s_37 4 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_37 g_37 ep_37 bds_37 0 (dagTraceF m_37 s_37 4 f_37) cur_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_37 kn_37 sub_37 gl_37 rc_37 nc_37

def m_38 : Nat := 0xcccc0000cccc0000
def s_38 : List Nat := [0x4444000044440000, 0xc0c00000c0c0000, 0xcc000000cc0000, 0xcccc0000]
def g_38 : Nat := 0x4000004440000
def ep_38 : Nat := 0x440000000000000000000000004000000400000000400000400000000000000000000000004000004440000
theorem epk_38 : ep_38 = edgePack m_38 g_38 := by decide +kernel
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_24, s_24, 4, g_24)]
theorem kn_38 : KnownBin bds_38 := by
  intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_24
theorem sub_38 : ∀ b ∈ bds_38, m_38 &&& b.1 = b.1 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_38 : ∀ b ∈ bds_38, canon b.1 g_38 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV4 m_38 g_38 ep_38 0 bds_38 (dagTraceF m_38 s_38 4 f_38) (cur_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_38 g_38 ep_38 bds_38 0 (dagTraceF m_38 s_38 4 f_38) cur_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_38 kn_38 sub_38 gl_38 rc_38 nc_38

def m_39 : Nat := 0x3300330033003300
def s_39 : List Nat := [0x1100110011001100, 0x300030003000300, 0x330000003300, 0x33003300]
def g_39 : Nat := 0x100130013001300
def ep_39 : Nat := 0x1200000000001200000000000000000000000000010002000200020000000000000000000100100010001000
theorem epk_39 : ep_39 = edgePack m_39 g_39 := by decide +kernel
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_39 : KnownBin bds_39 := by
  intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_39 : ∀ b ∈ bds_39, m_39 &&& b.1 = b.1 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_39 : ∀ b ∈ bds_39, canon b.1 g_39 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_39 : Nat → List (Nat × Nat) := fun _ => []
def f_39 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV4 m_39 g_39 ep_39 0 bds_39 (dagTraceF m_39 s_39 4 f_39) (cur_39 0) s_39 4 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_39 g_39 ep_39 bds_39 0 (dagTraceF m_39 s_39 4 f_39) cur_39 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_39 : LowerBin m_39 s_39 g_39 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_39 kn_39 sub_39 gl_39 rc_39 nc_39

def m_40 : Nat := 0xcc00cc00cc00cc00
def s_40 : List Nat := [0x4400440044004400, 0xc000c000c000c00, 0xcc000000cc00, 0xcc00cc00]
def g_40 : Nat := 0x40004004400
def ep_40 : Nat := 0x400400000000400000040000000000000000000000004000400000000000000000000000000040004004400
theorem epk_40 : ep_40 = edgePack m_40 g_40 := by decide +kernel
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 4, g_17)]
theorem kn_40 : KnownBin bds_40 := by
  intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_17
theorem sub_40 : ∀ b ∈ bds_40, m_40 &&& b.1 = b.1 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_40 : ∀ b ∈ bds_40, canon b.1 g_40 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_40 : Nat → List (Nat × Nat) := fun _ => []
def f_40 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV4 m_40 g_40 ep_40 0 bds_40 (dagTraceF m_40 s_40 4 f_40) (cur_40 0) s_40 4 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_40 g_40 ep_40 bds_40 0 (dagTraceF m_40 s_40 4 f_40) cur_40 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_40 : LowerBin m_40 s_40 g_40 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_40 kn_40 sub_40 gl_40 rc_40 nc_40

def m_41 : Nat := 0xf000f000f000f000
def s_41 : List Nat := [0x5000500050005000, 0x3000300030003000, 0xf0000000f000, 0xf000f000]
def g_41 : Nat := 0x100010005000
def ep_41 : Nat := 0x1000400000001000000040000000000000000000000000000000000000001000100000000000100010005000
theorem epk_41 : ep_41 = edgePack m_41 g_41 := by decide +kernel
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_41 : KnownBin bds_41 := by
  intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_41 : ∀ b ∈ bds_41, m_41 &&& b.1 = b.1 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_41 : ∀ b ∈ bds_41, canon b.1 g_41 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV4 m_41 g_41 ep_41 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_41 g_41 ep_41 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_41 kn_41 sub_41 gl_41 rc_41 nc_41

def m_42 : Nat := 0xcc00cc00cc00cc
def s_42 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_42 : Nat := 0x40044004400cc
def ep_42 : Nat := 0x40008800000040000000880000000000000000000400000000000000000000000000000004004400440000
theorem epk_42 : ep_42 = edgePack m_42 g_42 := by decide +kernel
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
theorem kn_42 : KnownBin bds_42 := by
  intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_15
theorem sub_42 : ∀ b ∈ bds_42, m_42 &&& b.1 = b.1 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_42 : ∀ b ∈ bds_42, canon b.1 g_42 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_42 : Nat → List (Nat × Nat) := fun _ => []
def f_42 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV4 m_42 g_42 ep_42 0 bds_42 (dagTraceF m_42 s_42 4 f_42) (cur_42 0) s_42 4 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_42 g_42 ep_42 bds_42 0 (dagTraceF m_42 s_42 4 f_42) cur_42 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_42 kn_42 sub_42 gl_42 rc_42 nc_42

def m_43 : Nat := 0xffff0000
def s_43 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_43 : Nat := 0x17570000
def ep_43 : Nat := 0x400000000000000602000000000000120200000000000014540000
theorem epk_43 : ep_43 = edgePack m_43 g_43 := by decide +kernel
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
theorem kn_43 : KnownBin bds_43 := by
  intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_4
theorem sub_43 : ∀ b ∈ bds_43, m_43 &&& b.1 = b.1 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_43 : ∀ b ∈ bds_43, canon b.1 g_43 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_43 : Nat → List (Nat × Nat) := fun _ => []
def f_43 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV4 m_43 g_43 ep_43 0 bds_43 (dagTraceF m_43 s_43 4 f_43) (cur_43 0) s_43 4 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_43 g_43 ep_43 bds_43 0 (dagTraceF m_43 s_43 4 f_43) cur_43 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_43 : LowerBin m_43 s_43 g_43 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_43 kn_43 sub_43 gl_43 rc_43 nc_43

def m_44 : Nat := 0xcccccccc
def s_44 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_44 : Nat := 0x44444cc
def ep_44 : Nat := 0x40880000000000400088000000000400000000000000000000000000000004444400
theorem epk_44 : ep_44 = edgePack m_44 g_44 := by decide +kernel
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_22, s_22, 4, g_22)]
theorem kn_44 : KnownBin bds_44 := by
  intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_22
theorem sub_44 : ∀ b ∈ bds_44, m_44 &&& b.1 = b.1 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_44 : ∀ b ∈ bds_44, canon b.1 g_44 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_44 : Nat → List (Nat × Nat) := fun _ => []
def f_44 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV4 m_44 g_44 ep_44 0 bds_44 (dagTraceF m_44 s_44 4 f_44) (cur_44 0) s_44 4 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_44 g_44 ep_44 bds_44 0 (dagTraceF m_44 s_44 4 f_44) cur_44 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_44 : LowerBin m_44 s_44 g_44 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_44 kn_44 sub_44 gl_44 rc_44 nc_44

def m_45 : Nat := 0xff000000ff000000
def s_45 : List Nat := [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000]
def g_45 : Nat := 0x100000017000000
def ep_45 : Nat := 0x1600000000000000000000000000000000000000010000000600000001000000120000000100000014000000
theorem epk_45 : ep_45 = edgePack m_45 g_45 := by decide +kernel
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_20, s_20, 4, g_20), (m_4, s_4, 4, g_4), (m_18, s_18, 4, g_18), (m_19, s_19, 4, g_19)]
theorem kn_45 : KnownBin bds_45 := by
  intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_20
  · exact lb_4
  · exact lb_18
  · exact lb_19
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

def m_46 : Nat := 0xff000000ff0000
def s_46 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_46 : Nat := 0x17000000570000
def ep_46 : Nat := 0x40000000000000000000000000000000000000000600000002000000120000000200000014000000540000
theorem epk_46 : ep_46 = edgePack m_46 g_46 := by decide +kernel
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
theorem kn_46 : KnownBin bds_46 := by
  intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_14
theorem sub_46 : ∀ b ∈ bds_46, m_46 &&& b.1 = b.1 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_46 : ∀ b ∈ bds_46, canon b.1 g_46 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_46 : Nat → List (Nat × Nat) := fun _ => []
def f_46 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV4 m_46 g_46 ep_46 0 bds_46 (dagTraceF m_46 s_46 4 f_46) (cur_46 0) s_46 4 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_46 g_46 ep_46 bds_46 0 (dagTraceF m_46 s_46 4 f_46) cur_46 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_46 : LowerBin m_46 s_46 g_46 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_46 kn_46 sub_46 gl_46 rc_46 nc_46

def m_47 : Nat := 0xf000f000f000f0
def s_47 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_47 : Nat := 0x100070005000f0
def ep_47 : Nat := 0x40008000000060000000a00000000000000000000000000000000000100020000000000010004000500000
theorem epk_47 : ep_47 = edgePack m_47 g_47 := by decide +kernel
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_47 : KnownBin bds_47 := by
  intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_47 : ∀ b ∈ bds_47, m_47 &&& b.1 = b.1 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_47 : ∀ b ∈ bds_47, canon b.1 g_47 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_47 : Nat → List (Nat × Nat) := fun _ => []
def f_47 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV4 m_47 g_47 ep_47 0 bds_47 (dagTraceF m_47 s_47 4 f_47) (cur_47 0) s_47 4 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_47 g_47 ep_47 bds_47 0 (dagTraceF m_47 s_47 4 f_47) cur_47 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_47 : LowerBin m_47 s_47 g_47 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_47 kn_47 sub_47 gl_47 rc_47 nc_47

def m_48 : Nat := 0xf0f00000f0f00000
def s_48 : List Nat := [0x5050000050500000, 0x3030000030300000, 0xf0000000f00000, 0xf0f00000]
def g_48 : Nat := 0x10000010500000
def ep_48 : Nat := 0x1040000000000000000000000010000000400000000000000000000000100000100000000010000010500000
theorem epk_48 : ep_48 = edgePack m_48 g_48 := by decide +kernel
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_25, s_25, 4, g_25)]
theorem kn_48 : KnownBin bds_48 := by
  intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_25
theorem sub_48 : ∀ b ∈ bds_48, m_48 &&& b.1 = b.1 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_48 : ∀ b ∈ bds_48, canon b.1 g_48 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_48 : Nat → List (Nat × Nat) := fun _ => []
def f_48 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV4 m_48 g_48 ep_48 0 bds_48 (dagTraceF m_48 s_48 4 f_48) (cur_48 0) s_48 4 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_48 g_48 ep_48 bds_48 0 (dagTraceF m_48 s_48 4 f_48) cur_48 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_48 : LowerBin m_48 s_48 g_48 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_48 kn_48 sub_48 gl_48 rc_48 nc_48

def m_49 : Nat := 0x4444444444444444
def s_49 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_49 : Nat := 0x4044404444444
def ep_49 : Nat := 0x440400000000440000040000004004000400000000404000400000000000000000000000000000000000000
theorem epk_49 : ep_49 = edgePack m_49 g_49 := by decide +kernel
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6), (m_24, s_24, 4, g_24), (m_17, s_17, 4, g_17), (m_13, s_13, 4, g_13)]
theorem kn_49 : KnownBin bds_49 := by
  intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_6
  · exact lb_24
  · exact lb_17
  · exact lb_13
theorem sub_49 : ∀ b ∈ bds_49, m_49 &&& b.1 = b.1 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_49 : ∀ b ∈ bds_49, canon b.1 g_49 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_49_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_49_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
def cur_49 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_49_1 (Nat.sub p 32)) (cc_49_0 p) (Nat.blt p 32)
def f_49 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV4 m_49 g_49 ep_49 43 bds_49 (dagTraceF m_49 s_49 6 f_49) (cur_49 0) s_49 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_0 : treeBlockF 0 32 (dagCheckNodeV4 m_49 g_49 ep_49 bds_49 43 (dagTraceF m_49 s_49 6 f_49) cur_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_1 : treeBlockF 32 43 (dagCheckNodeV4 m_49 g_49 ep_49 bds_49 43 (dagTraceF m_49 s_49 6 f_49) cur_49) = true := by decide +kernel
theorem nj_49_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_49 g_49 ep_49 bds_49 43 (dagTraceF m_49 s_49 6 f_49) cur_49) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_49_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_49_1 h1 h2)
theorem nc_49 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_49 g_49 ep_49 bds_49 43 (dagTraceF m_49 s_49 6 f_49) cur_49) i = true := nj_49_1
theorem lb_49 : LowerBin m_49 s_49 g_49 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_49 kn_49 sub_49 gl_49 rc_49 nc_49

def m_50 : Nat := 0x2222222222222222
def s_50 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_50 : Nat := 0x2022202020222
def ep_50 : Nat := 0x200000000000220000000200002002000000020000202000202020000000000000000000000000000000000
theorem epk_50 : ep_50 = edgePack m_50 g_50 := by decide +kernel
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
theorem kn_50 : KnownBin bds_50 := by
  intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_5
theorem sub_50 : ∀ b ∈ bds_50, m_50 &&& b.1 = b.1 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_50 : ∀ b ∈ bds_50, canon b.1 g_50 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_50 : Nat → List (Nat × Nat) := fun _ => []
def f_50 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV4 m_50 g_50 ep_50 0 bds_50 (dagTraceF m_50 s_50 4 f_50) (cur_50 0) s_50 4 = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_50 g_50 ep_50 bds_50 0 (dagTraceF m_50 s_50 4 f_50) cur_50 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_50 : LowerBin m_50 s_50 g_50 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_50 kn_50 sub_50 gl_50 rc_50 nc_50

def m_51 : Nat := 0xa0a0a0a0a0a0a0a
def s_51 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_51 : Nat := 0x202020202020a
def ep_51 : Nat := 0x200000800000200000000080002000000000008000000000000000000020202020202000000000000000000
theorem epk_51 : ep_51 = edgePack m_51 g_51 := by decide +kernel
def bds_51 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_51 : KnownBin bds_51 := by intro b hb; simp [bds_51] at hb
theorem sub_51 : ∀ b ∈ bds_51, m_51 &&& b.1 = b.1 := by intro b hb; simp [bds_51] at hb
theorem gl_51 : ∀ b ∈ bds_51, canon b.1 g_51 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_51] at hb
def cc_51_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0xe24c6d20345319280b83c581a2a0b14048912844921e0b0e04858202c9a124f08268303c141a040402249fa3ff91df28df4467993fc89dda4de8267292f8895c249df246f03f741db00dd3066802f34159809ca046381f100d8605c1026000f 11 2047 5 31 10 1023 17 131071
def cc_51_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0x3d299e140ec26741038251b924d8146a09314998240bc265c102c2795934a80c5205270513024900c4605202410234 8 255 3 7 10 1023 17 131071
def cur_51 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_51_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_51_0 p) (Nat.blt p 32)
def f_51 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV4 m_51 g_51 ep_51 64 bds_51 (dagTraceF m_51 s_51 5 f_51) (cur_51 0) s_51 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_0 : treeBlockF 0 32 (dagCheckNodeV4 m_51 g_51 ep_51 bds_51 64 (dagTraceF m_51 s_51 5 f_51) cur_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_1 : treeBlockF 32 64 (dagCheckNodeV4 m_51 g_51 ep_51 bds_51 64 (dagTraceF m_51 s_51 5 f_51) cur_51) = true := by decide +kernel
theorem nj_51_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_51 g_51 ep_51 bds_51 64 (dagTraceF m_51 s_51 5 f_51) cur_51) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_51_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_51_1 h1 h2)
theorem nc_51 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_51 g_51 ep_51 bds_51 64 (dagTraceF m_51 s_51 5 f_51) cur_51) i = true := nj_51_1
theorem lb_51 : LowerBin m_51 s_51 g_51 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_51 kn_51 sub_51 gl_51 rc_51 nc_51

def m_52 : Nat := 0xc0c0c0c0c0c0c0c
def s_52 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_52 : Nat := 0x404040404040c
def ep_52 : Nat := 0x400000800000400000000080004000000000008000000000000000000000000000000000004040404040400
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

def m_53 : Nat := 0x5555555555555555
def s_53 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_53 : Nat := 0x115155515555555
def ep_53 : Nat := 0x1440400000001440000040000014004000400000010404000400000001101000100000000000000000000000
theorem epk_53 : ep_53 = edgePack m_53 g_53 := by decide +kernel
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_32, s_32, 7, g_32), (m_35, s_35, 7, g_35), (m_31, s_31, 7, g_31), (m_36, s_36, 7, g_36)]
theorem kn_53 : KnownBin bds_53 := by
  intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_32
  · exact lb_35
  · exact lb_31
  · exact lb_36
theorem sub_53 : ∀ b ∈ bds_53, m_53 &&& b.1 = b.1 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_53 : ∀ b ∈ bds_53, canon b.1 g_53 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cur_53 : Nat → List (Nat × Nat) := unpackCursorV4 0xe001 0x174fba5dd1ee87e4ff25f91fc8763fb1dd8dec66d4f6a5b51da86d3f69db4dda66d2f695b49da4601f 10 1023 5 31 10 1023 13 8191
def f_53 : Nat → Nat × Nat := unpackForestF 0x1f 1 5
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV4 m_53 g_53 ep_53 1 bds_53 (dagTraceF m_53 s_53 8 f_53) (cur_53 0) s_53 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53 : treeBlockF 0 1 (dagCheckNodeV4 m_53 g_53 ep_53 bds_53 1 (dagTraceF m_53 s_53 8 f_53) cur_53) = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_53 g_53 ep_53 bds_53 1 (dagTraceF m_53 s_53 8 f_53) cur_53) i = true := fun _ h1 h2 => treeBlockF_at nb_53 h1 h2
theorem lb_53 : LowerBin m_53 s_53 g_53 9 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_53 kn_53 sub_53 gl_53 rc_53 nc_53

def m_54 : Nat := 0xcccccccccccccccc
def s_54 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_54 : Nat := 0x40444044444cc
def ep_54 : Nat := 0x440408800000440000040880004004000400088000404000400000000000000000000000004044404444400
theorem epk_54 : ep_54 = edgePack m_54 g_54 := by decide +kernel
def bds_54 : List (Nat × List Nat × Nat × Nat) := [(m_29, s_29, 5, g_29), (m_33, s_33, 7, g_33), (m_38, s_38, 5, g_38), (m_42, s_42, 5, g_42), (m_6, s_6, 4, g_6), (m_49, s_49, 7, g_49), (m_40, s_40, 5, g_40), (m_34, s_34, 5, g_34), (m_44, s_44, 5, g_44), (m_52, s_52, 6, g_52)]
theorem kn_54 : KnownBin bds_54 := by
  intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_29
  · exact lb_33
  · exact lb_38
  · exact lb_42
  · exact lb_6
  · exact lb_49
  · exact lb_40
  · exact lb_34
  · exact lb_44
  · exact lb_52
theorem sub_54 : ∀ b ∈ bds_54, m_54 &&& b.1 = b.1 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_54 : ∀ b ∈ bds_54, canon b.1 g_54 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_54 : Nat → List (Nat × Nat) := unpackCursorV4 0x187cbb125cf52a4d5afdd26ee032e91587e9d9d44d41a700af48383f14ce856a001540001 0x1c5f5c5e1c5b1c571c531c523b5f5b5b3b575b531b4f1b4b1b471b435a5f5a5e5a5b4a5a5a574a565a535a521a4f1a4e1a4b1a4a1a471a461a431a422a3f2a3e2a3d595f595e295b595729535952194f194b19471943293b393a29393937393629332931392739263925585f585b58575853184f184b18471843683f383b38376833682f682d682b682788256823281f781b781728131c5f5c5e1c5b1c571c531c523b5f3b5e3b5b3b573b535b521b4f1b4b1b471b432a5f2a5b2a572a531a4f1a4b1a471a432a3f3a3e2a3d2a372a352a332a32295f595e295b295a2957495629532952194f194e194b194a1947194619431942293739362935292f292e292d585f585b58575853184f184b18471843383f383b38373833282f282b28272823281f281d281b2817881528131c5f5c5e1c5b1c571c531c523b5f3b5e3b5b4b5a3b573b563b535b521b4f1b4e1b4b1b4a1b471b461b431b423a5f3a5b3a573a531a4f1a4b1a471a432a3f2a3e2a3d595f295b59572953194f194b19471943393f393e693d392f392e292b2929292339222921c120585f585b58575853184f184b18471843383f883d383b383738353833382f382b38273823281f781b781728131b4f5b4e1b4b1b471b431b423a4f3a4e3a4b3a473a435a421a3f1a3b1a371a33294f294b29472943193f193d193b193729351933292f392e292d584f584b58475843183f183b18371833382f382b38273823281f281b281728131c5f5c5e1c5b1c571c531c523b5f5b5e5b5b3b575b535b521b4f1b4b1b471b432a5f5a5e2a5b2a572a532a521a4f1a4b1a471a432a3f2a3d2a3b2a3a2a373a362a35c234295f595e295b295a2957495629532952194f194e194d194c194b194a194719462945994419431942293f693e293d292f292e292d585f585b58575853184f184b18471843683f383b38376833282f282b28272823281f281d281b2817881528131c5f5c5e1c5b1c571c531c523b5f4b5b3b575b531b4f1b4b1b471b435a5f5a5e4a5b4a5a4a574a565a535a521a4f1a4e1a4b1a4a1a471a461a431a42595f495b49575953194f194b19471943693f393b39376933692f692d692b29296927792569232921485f585e48575852184f1847383a38373836382738263825881f88171c5f4c5e1c5b1c571c531c523b5f3b5e3b5b3b573b534b521b4f1b4b1b471b434a5f4a5b4a574a531a4f1a4b1a471a433a3f3a3b3a373a33393e485e4856184e18463836282e78261c5f5c5e1c5b1c571c531c523b5f3b5e3b5b4b5a3b573b563b535b521b4f1b4e1b4b1b4a1b471b461b431b423a5f3a5b3a573a531a4f1a4b1a471a43595f495b49575953194f194b19471943393f793d393b29393937393539332931392f392b39273923485f4857184f1847383f383e683d382f382e38227020881f88171b4f4b4e1b4b1b471b431b423a4f3a4e3a4b3a473a434a421a3f1a3b1a371a33494f494b49474943193f193b19371933392f392b39273923382e1c5f4c5e1c5b1c571c531c523b5f4b5e4b5b3b574b534b521b4f1b4b1b471b434a5f4a5b4a574a531a4f1a4b1a471a436a3f3a3b3a376a33495e39367134485e4856184e184c18469844683e282e78261c5f5c5e1c5b1c571c531c525b5f4b5b4b575b531b4f1b4b1b471b432a5f2a5b2a572a531a4f1a4b1a471a432a3f2a3b2a372a33295f595e295b295a2957495629532952194f194e194b194a1947194619431942293f693e293b293a2937393629332932485f585e48575852184f1847883f8837282a282728262817281678151c5f4c5e1c5b1c571c531c524b5f4b5b4b574b531b4f1b4b1b471b434a5f4a5e2a5b4a572a534a521a4f1a4b1a471a437a3f2a3b7a372a33292e485e4856184e1846683e383678261c5f5c5e1c5b1c571c531c525b5f4b5b4b575b531b4f1b4b1b471b435a5f5a5e4a5b4a5a4a574a565a535a521a4f1a4e1a4b1a4a1a471a461a431a427a3f6a3e7a3b3a3a7a373a367a336a32595f295b49572953194f194b19471943793f293b79372933485f4857184f1847883f8837282f282e282d281f281e281220101b4f4b4e1b4b1b471b431b424a4f4a4b4a474a431a3f1a3b1a371a33494f494e494b494749434942193f193b19371933792f792b79277923781e1c5f4c5e1c5b1c571c531c524b5f4b5b4b574b531b4f1b4b1b471b432a5f4a5e2a5b2a572a532a521a4f1a4b1a471a432a3f2a3b2a372a33495e29262124485e4856184e184c18469844683e3836282e1b4f5b4e1b4b1b471b431b425a4f5a4b5a475a431a3f1a3b1a371a33594f594b59475943193f193b19371933f12fe12bd127b123584f584b58475843183f183b18371833a02f902b80276023501f401b30171013001f 17 131071 7 127 11 2047 16 65535
def f_54 : Nat → Nat × Nat := unpackForestF 0x14bc52b149f234148c42f10ac42774d0423107c41b105c924104c01f 4 10
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV4 m_54 g_54 ep_54 16 bds_54 (dagTraceF m_54 s_54 8 f_54) (cur_54 0) s_54 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54 : treeBlockF 0 16 (dagCheckNodeV4 m_54 g_54 ep_54 bds_54 16 (dagTraceF m_54 s_54 8 f_54) cur_54) = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 16 → (dagCheckNodeV4 m_54 g_54 ep_54 bds_54 16 (dagTraceF m_54 s_54 8 f_54) cur_54) i = true := fun _ h1 h2 => treeBlockF_at nb_54 h1 h2
theorem lb_54 : LowerBin m_54 s_54 g_54 9 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_54 kn_54 sub_54 gl_54 rc_54 nc_54

def g_55 : Nat := 0x1171777175757ff
def ep_55 : Nat := 0x1640408800001660000040a800160060004000a8010606000602020001121222120202000114144414545400
theorem epk_55 : ep_55 = edgePack fullMask g_55 := by decide +kernel
def bds_55 : List (Nat × List Nat × Nat × Nat) := [(m_30, s_30, 7, g_30), (m_45, s_45, 7, g_45), (m_28, s_28, 7, g_28), (m_53, s_53, 9, g_53), (m_51, s_51, 6, g_51), (m_34, s_34, 5, g_34), (m_54, s_54, 9, g_54), (m_27, s_27, 7, g_27), (m_31, s_31, 7, g_31), (m_35, s_35, 7, g_35), (m_26, s_26, 7, g_26), (m_50, s_50, 5, g_50), (m_47, s_47, 5, g_47), (m_16, s_16, 4, g_16), (m_36, s_36, 7, g_36), (m_52, s_52, 6, g_52), (m_33, s_33, 7, g_33), (m_23, s_23, 4, g_23), (m_43, s_43, 5, g_43), (m_32, s_32, 7, g_32), (m_20, s_20, 4, g_20), (m_49, s_49, 7, g_49), (m_37, s_37, 5, g_37), (m_41, s_41, 5, g_41), (m_39, s_39, 5, g_39), (m_48, s_48, 5, g_48), (m_46, s_46, 5, g_46)]
theorem kn_55 : KnownBin bds_55 := by
  intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_30
  · exact lb_45
  · exact lb_28
  · exact lb_53
  · exact lb_51
  · exact lb_34
  · exact lb_54
  · exact lb_27
  · exact lb_31
  · exact lb_35
  · exact lb_26
  · exact lb_50
  · exact lb_47
  · exact lb_16
  · exact lb_36
  · exact lb_52
  · exact lb_33
  · exact lb_23
  · exact lb_43
  · exact lb_32
  · exact lb_20
  · exact lb_49
  · exact lb_37
  · exact lb_41
  · exact lb_39
  · exact lb_48
  · exact lb_46
theorem sub_55 : ∀ b ∈ bds_55, fullMask &&& b.1 = b.1 := by intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_55 : ∀ b ∈ bds_55, canon b.1 g_55 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_55_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xda3f75b1bd366f3f1dca6af04cabd282cdceaa72299a096df61dfb7f505d84a667f5715153b15245540714e5b832ed0a84726a6c8d1b1fa747d821a4a453ab0bb281ea0002f00001 0x3e7b04e7304d7f11d7e03d7b03d7a03d7703d7604d732057204d6f06d6e06d6306d6202c7f02c7b02c7702c7302c6f02c6301c5f01c5e01c5d04b7f04b7e03b7b03b7a03b7703b7604b7304b7206b6f05b6e06b6305b620ab5f11b5e0ab5d1f35c04b5b04b5a0ab5904b5804b5704b560ab5504b540ab530ab520ab510ab5002b4f02b4e02b4b02b4a02b4702b4602b4302b4201a7f01a7b01a7701a7301a6f01a6301a5f01a5d01a5b01a5901a5701a5501a5301a5101a4f01a4d01a4b01a4701a4501a430197f0197b01977019730196f019630195f0295e0195d0194f0294e0194b019490194301942019410193f0193d0193b01939019370193501933019310192f0192b01927019230287f028770286a1b0660285f0285d02857028550284f028470183f0183e0183d0182f0182e018220181f0181702e7e02e7d02b7a02b7903b7602b7103b6602b650aa6d08a6908a650aa6101a5101a5006a410a96d01969089650196101951019500b86d0186908865018610a82d0502501e7e01e7d0bb6d02b6909b6502b610aa6d09a6909a650aa6101a5101a5006a410196d01969019650196101951019500187a01879038760187103866018650182d018250bc7e03c7a03c760bc7201b4e01b4d01a6101a6006a510aa4d0aa490aa450aa4101961019600194d0194901945019410193d019350284e0184d0283e0183901832018310182d018251d36f02b6b03b6702b630aa6f03a6b03a670aa6301a5101a5006a4102a3f0aa3b0aa3702a330a96f0196b039670196301951019500293f0193b0a937019331c06f0186b03867018630283f0183b1b037018330a82f0a82d0182b0a82704025018230181f0181b018170181303d6b06d632646f02c6b03c6702c6306c5f02c530ab6f2436e03b6b03b6a03b6703b660ab630ab6206b5f06b5e06b5306b5202b4f02b4e0ab4b0ab4a0ab472234602b4302b420aa6f01a6b03a6701a6306a5f01a5302a4f01a4b0aa4701a432116f0196b03967019630695f019530294f0194b1e147019430a93f0a93d0193b019390a9370913501933019310192f0192b01927019230a86f038670a85a1a0560284f028470183f0183e0183d0182f0182e018220181f0781702c6f02c6b02c6702c6301b6f01b6b01b6701b6301b4f01b4b01b4701b4301a6f01a6b01a6701a6301a4f01a4b01a4701a4301a3f01a3b01a3701a33019360e86e038660284e028460183e0182e0182603d6b04d6304c6f04c6e03c6b03c6a03c6703c6604c6304c6204c5f04c5e04c5306c5202b6f02b6b02b6702b6302b5f02b5301b4f01b4e01b4d01a6f01a6b01a6701a6301a5f01a5301a4f01a4d01a4b01a4901a4701a4501a4301a4101a3f01a3d01a3b01a3701a3501a330196f0196b01967019630195f019530194f0194d0194701945019430193f0193b019390193701933019310192f0192b01927019230286f028670284f0284d02847028450283f0283d02837028350182f018270181f0181703d6b06d6309c6f02c6b03c6702c6306c5f02c5301b6f01b6b01b6701b6301b5f01b5301b4f01b4b01b4701b4301a6f01a6b01a6701a6301a5f01a5301a4f01a4b01a4701a4301a3f01a3b01a3701a330196f0996e0196b0196a019670396601963019620195f0695e01953019520194f0294e0194b0194a019471714601943019420193f0193e0193b0193a019370193601933019320786f038670284f028470183f018370182a018270182601817018160781502c6f02c6b02c6702c630ab6f01b6b03b6701b6302b4f01b4b02b4701b4307a6f01a6b03a6701a6302a4f01a4b02a4701a4301a3f01a3b01a3701a330192e1386e038660284e028460183e0a8360782602e7f02e7e02e7d03d7b03d7306d6b05d6904d6305d6102c7b02c7a02c7902c7703c7602c7302c7102c6703c6602c6502c5f06c5e02c5302c5203b7f01b7b03b7701b7304b6f0db6d01b6b01b6908b6708b6501b6301b6106b5f01b5302b4f01b4b02b4701b4303a7f03a7e03a7b03a7a03a7703a7603a7303a7204a6f04a6e05a6d04a6c07a6b07a6a07a6907a6807a6708a6605a6508a6404a6304a6207a6104a6006a5f06a5e06a5306a5202a4f02a4e02a4b02a4a02a4702a4602a4302a4201a3f01a3e07a3b07a3a07a370b23601a3301a320397f0197b03977019730496f0596d0196b01969079670596501963019610695f019530294f0194b02947019430193f0193b01937019330287f028770286f0286d02867028650285a080560284f028470183f028370182f0182e0182d0181f0181e0181201e7f01e7e01e7d03d7b03d7306d6b05d6904d6305d6103c7f02c7b03c7702c7304c6f0dc6d02c6b02c6904c670dc6502c6302c6104c5f02c5301b7b01b7a01b7901b7703b7601b7301b7101b6703b6601b6501b5f01b5301b4f01b4b01b4701b4303a7f03a7e03a7b03a7a03a7703a7603a7303a7204a6f04a6e05a6d04a6c07a6b07a6a07a6907a6807a670ea6605a650ea6404a6304a6207a6104a6006a5f06a5e06a5306a5202a4f02a4e04a4b04a4a04a4704a4602a4302a4201a3f01a3e01a3b01a3a01a3701a3601a3301a320197f0197b01977019730196f0196d0196b01969019670196501963019610195f019530194f0194b01947019430193f0193b01937019330387f038770486f0786d07867078650785a070560284f028470183f018370182f0182e0182d0181f0181e0181202d7d02d7503c7e04c7d05c6e04c6202c5e01c5a01c5601c5201b7d01b7501b4d01b4901b4501b4103a7e03a7a03a7903a7803a7603a7204a7104a7006a6e06a6202a5e02a5a02a5602a5204a4e04a4d04a4c04a4a07a4907a4804a4605a4505a4404a4204a4104a4001a3e01a3a01a3601a320194d0194a0194901948049460194505944019410286a0b8660284d0284a0484602845128440182e0182d0181e0181203d6b04d6304c6f04c6e03c6b03c6a03c6703c6604c6304c6205c5f05c5e05c5305c5202b6f02b6b02b6702b6302b5f02b5301b4f01b4d02b4b02b4901b4701b4501b4301b4101a6f01a6b01a6701a6301a5f01a5301a4f01a4d01a4b01a4901a4701a4501a4301a4101a3f01a3b01a3701a330196f0196b01967019630195f019530194705946019450193f0193b01937019330192f0192b01927019230286f028670284705846028450183f028370182f018270181f0181703e7b04e7304d7f0dd7e03d7b03d7a03d7703d7604d731257204d6f05d6e06d6305d6202c7f02c7b02c7702c7302c6f02c6301c5f01c5e01c5d01b7f01b7b01b7701b7301b6f01b6301b5f02b5e01b5d01b4f02b4e01b4b01b4901b4301b4201b4104a7f04a7e03a7b03a7a03a7703a7604a7304a7206a6f06a6e06a6306a6207a5f0da5e05a5d1125c04a5b04a5a07a5904a5804a5704a5605a5504a5407a5307a5207a5107a5002a4f02a4e02a4b02a4a02a4702a4602a4302a4201a3f01a3e01a3b01a3a01a3701a3601a3301a320197f0197b01977019730196f019630195f0195d0195b01959019570195501953019510194f0194d0194b0194701945019430193f0193b01937019330287f028770286a060660285f0285d02857028550284f028470183f018370182f0182e0182d0181f0181e0181201d6f01d6d03d6b03d6901d6701d6501d6301d6105c6b05c6905c6305c6103c5b03c5304b6f04b6d02b6b02b6904b6704b6502b6302b6103b5f02b5b03b5702b5304b4f02b4301a6f04a6e01a6d01a5f03a5e01a5b01a5701a5301a5201a4f01a4301a3f01a3b01a3701a330196f0196d0196b01969019670196501963019610195f0195b01957019530194f019430193f0193b01937019330192f0192d0192b0192701925019230186f0186d07867078650185f038570283f028370182f0182d01827078250181f0181703d6f03d6e04d6d03c6b03c6304c5b06c5904c5304c5103b6f02b6b03b6702b6304b5f04b5d02b5b02b5904b5704b5502b5302b5104b4f02b4303a6f01a6b03a6701a6304a5f04a5d01a5b01a5904a570f25501a5301a5105a4f01a4302a3f01a3b04a3701a330396f0196b03967019630495704956079550594f019430293f0193b04937019330192f0192b01927019230386f038670485704856078550283f028370182f078270181f0381703d6b04d6302c6f02c6b02c6702c6302c5f02c5304b6f04b6e03b6b03b6a03b6703b6604b6304b6205b5f05b5e05b5305b5201b4f01b4e02b4b02b4a01b4701b4601b4301b4201a6f04a6e01a6b01a6701a6301a6201a5f05a5e01a5301a5201a4f01a4b01a4a01a4702a4601a4301a3704a3601a350196f0196b01967019630195f019530194f0194b01947019430193f0193d0193b01939019370193501933019310192f0192d0192b0192701925019230286f028670284f018470283f0283d01837018350182f0182d01827028250181f0181703d6b04d6304c6f04c6e03c6b03c6a03c6703c6604c6304c6204c5f04c5e04c5306c5202b6f02b6b02b6702b6302b5f02b5302b4f04b4e02b4d04a6f01a6b03a6701a6305a5f01a5304a4f0d24d01a4b01a4904a4704a4501a4301a4102a3f01a3b02a3701a330496f0196b03967019630595f019530294f0294e0294d0293f0193b02937019330192f0192b01927019230286f028670284f0484e0284d0283f028370182f028270181f0281702e7e02e7d05d6905d6102c7a02c7903c7602c7103c6602c6505c5e02c5203b7e03b7a03b7603b7204b6e05b6d04b6c08b6a08b6908b6808b6605b6505b6404b620cb6104b6006b5e06b5202b4e02b4a0cb4904b4802b4602b4202b4102b4001a6d01a6901a6501a6107a3e01a3d0196d0196901965019610a93e0193d0286d028650285a050560183e0183d03e7905e7102d7902d7103c7e05c7d04c7c03c7a03c7603c7503c7405c6e05c6202c5e04c5a04c5602c5201b7d01b7505b4e01b4d03a7e05a7d05a6e05a6202a5e0ca5a0ca5602a5203a4e03a4d03a4c01a3e01a3a01a3601a320197d019750594e0194d0192d0192901925019210787d038750586a058660184e0184d0182d0182503d6b05d630b46f02c6b03c6702c6305c5f02c5305b6f04b6e03b6b03b6a03b6703b660a36304b6205b5f06b5e05b5306b5202b4f02b4e0cb4b04b4a05b4704b4602b4302b4201a6f01a6b01a6701a6301a5f01a5301a4f01a4b01a4701a4301a3f07a3e01a3d0196f0196b01967019630195f019530194f0194b01947019430193f0a93e0193d0192f0192b01927019230786f038670785a040560284f028470183f0183e0183d0182f018270181f0181702e7e02e7d02b7a02b7903b7602b7103b6602b650ba6d01a6908a6501a610596d0796905965079610195101950069410792a051260586d018690586501861018510185001e7e01e7d0bb6d02b690db6502b6101a7a01a7903a7601a7103a6601a650596d0796905965079610195101950069410192a019260186d01869018650186101851018500bc7e03c7a03c760bc7201b4e01b4d02a4e01a4d02a3e01a3901a3201a310196101960069510594d0794905945079410192a0192601861018600184d0184901845018410183d0183501a5006a400536f02b6b03b6702b6305a6f03a6b03a6705a6301a5101a5005a4106a4002a3f05a3b05a3702a330196f0196b01967019630193f0193b01937019330192f0592e0192d0186f0186b01867018630183f0183b01837018330182f0582e0182d0181f0181b018130836f02b6b03b6702b630726f01a6b03a6701a6302a3f01a3b0623701a330596f0396b03967079630195101950069410293f0793b05937029330192f0792b0792a0592704126019230586f0186b038670186301851018500283f0183b05837018330182f0182b018270182303d6b06d631446f02c6b03c6702c6306c5f02c531336f01b6b03b6701b6306b5f01b5302b4f01b4b1034701b4307a6f0e26e03a6b03a6a03a6703a6607a6307a6206a5f06a5e06a5306a5202a4f02a4e07a4b07a4a07a470c24602a4302a4201a3f01a3e07a3b07a3a07a370923601a3301a320796f0196b03967019630695f019530294f0194b07947019430193f0193b01937019330786f038670785a030560284f028470183f078370182f0182e0182d0181f0181e0181202c6f02c6b02c6702c6301b6f01b6b01b6701b6301b4f01b4b01b4701b4301a6f01a6b01a6701a6301a4f01a4b01a4701a4301a3f01a3b01a3701a33019260986e038660284e028460183e018360182ed345f03c5b03c5706c53d235f03b5b03b57cd35306b4fc834bc734706b43c625f03a5b03a57c425306a4fc224bba24706a43b823fb623ba8237a7233a415f0395b03957a21530694fa014b94147069439113f8f13b7d1377c1337812f7412b671275e1235c05f0385b038575b0530684f5a04b3a047068433103f3003b2b0372a0332802f2702b19027180231601f1501b02017010130003f 18 262143 7 127 11 2047 20 1048575
def cc_55_1 : Nat → List (Nat × Nat) := unpackCursorV4 0x8ca358be0c8912d84f4282d227dc5178e4e73d516ef4e6ac436644861c4859a8255248532204e1514905144b453d17a389483692031b4e2d3482b3202367d1e5511a04514b551064508b7b04a410004a 0x13174162c84c55058a20edf80dbd01b79036f00edd80db901b71036e012d780dae84b5c036b406d640dac04b56036aa16d500da901b51036a00ad380da504b4603684069740d2d01a59034b0129580d2a8ca54034a2068f80d1e8195d032b4065640cac04956032aa165500ca88193e0327a064b80c9481922032421e480473c04e70098d80b18025be01b780b6e806dc065b601b600f240140d02e3784c6e078d60f1a81e3383c660b8c61318865b782b6b076ce0ad8c2da784b4d056960ad242da384b45056860ad040d3781a6b034ce0698c0d2385a460348a068fc0d1d81a3703466065bc0cb581967032c60651c2ca3019450327e064ec0c9b819330325e064ac0c9183e7a7cce4f51fc163d83c77058e6531b4163081b7f176fc06dec0dbd01b77076ec06dcc0db901b6d786d806d840db001b4f0569c06d2c0da501b471f68c06d0c0da101a7f034f6069dc0d3981a6d034c20693c0d2581a4703486068fc0d1f01a3d032fe065ec0cbb81973032da065840ca78194b0328e0650c0c9f8193e0327a064bc0c970192b032520648c0c91019210f240060d8201a018260302c0f5aabab15636f056d60ed9c15b1d335d056a3489bc1d3583a67154c7389740d2882a3f154772c8dc1519c916f072d60e59c3cb1c315d032a20a4fc3c9dbf137052662a4bc3c95bb1270f24668098180b03d6b0bac6171bc263703c6b078d40f19c1e3305c63098c41717c2e2f05c530b8a40adbc15b582b67056c60ad7c15a981b4f0369a0ad2c15a481b470368a06d0c0da081a6f034d60699c0d3181a5f034a60693c0d2681a4b034920691c0d2281a4303482068fc0d1d81a3703466065bc2cb70196b032ce0658c0cb10195f032a60651c2ca3019450327e064ec0c9d019370526c064cc0c978192b032540649c0c9301923050de0a19c0c278184d0508e0a1140c1f828370305e0609c0c0f8181707ad61b58c463784c6e078d60f1a81e3383c66118c613188362f86c5e0d8a61b14815b782b6b056ce0ad8c15af82b530369e06d3415a381b4505686229bc0d3583a67034c61a97c0d2982a4f0549c0a934151f82a3e034760a8dc0d1982a32112de065ac1cb3819630d2be0654c6ca7b914d032960652464a3b51450328606504149f8193b0526e064cc0c978a92d032560649da09281923050de0a19c14278284d0508e0a114141f828370305e0a0b41413828250303e0a05c1eb585d63058de0b1ac163382c63058be0b14c45b784b6e076d60eda81db383b66116c612d882daf85b5e0b6a616d4815a782b4e0369606d280da381b460368606d080d3788a6e034d60699c0d3181a62034be0694c0d2781a4b034940691c152301a430346e168d80d1a8196f032d60659c0cb18195f032a60653c0ca58194703286064fc0c9e8193b03272064dc0c9a8193303262064bc0c968192b0324e064940c918286f050ce0613c14238183f0307a0a0dc141a8182f0304e0607c0c0b83d6b0bac6171bc263703c6b078d40f19c1e3308c63098c41717c362f05c530d8a40adbc15b582b67056c60ad7c15a981b4f0369a0ad1c0da282b43114de069ac1d3381a630b4be0694c8d27b724d03496069242d23b52450348606904151f81a3b0546e068cc2cb78196b072ce0658c2caf819530529e0a53814a68293f0527c064ec149b8193305264064bc0c958792a0324ecc4980c918286f050ce0a13c1426828470508a0a0fc141b8182f0504e0607c140e828170502a0f5ac2eb185c6f098dc0f1ac1e3503c67078cc1718c263105c5f0b8bc1714c2e2902b6f056d60ad9c15b182b5f056a606d3c0da681b470368a06d0c0d3781a6b034ce0698c0d2f81a530349e169380d2681a3f03476068dc0d198196f032d60659c0cb18195f032a60653c2ca70194d0327e064ec0c9b819330325e064ac0c9381923050de0a19c0c278184d0508e0a1140c1f828370305e0609c0c0f8181707ad61b58c463783c6b078ce2318c362f86c53056de0adac15b382b63056be0ad4c0da781b4703686069bc0d3581a67034c60697c0d2981a4f0549c0692c0d2481a4703486069080d2081a400347e0a8f80d1d81a3703466068c80cb78196b032ce0658c0caf819530329e325380ca5819490328e0650c0ca10194103280064fc0c9d8193703266064bc0c970192d050de0a19c0c27828470307e0a0dc0c178182d0304e0a0940c0f8181707ad61758c2e3783c6b078ce1718c2e2f85c53056de0adac15b382b63056be0ad4c0da781b4703686069bc0d3581a67034c60697c0d2981a4f0549c0692c0d2481a4703486069080d2081a400347e0a8f80d1d81a3703466068c80cb78196b032ce0658c0caf819530329e165380ca5819490328e0650c0ca10194103280064fc0c9d8193703266064bc0c970192d050de0a19c0c27828470307e0a0dc0c178182d0304e0a0940c0f8181707cf61b9cc16bf82d7b05aee0b5cc16b782d63058fe231f8163d82c7a058ee0f1d8163982c72058de171b8163182c62036fe12df80dbd81b7a036ee0edd80db981b72036de1adb80db181b62036be0ad780dad81b5a036ae0ad580da981b520369e0ad380da682b4c0369606d280da481b480368e0ad180da2b53440368606d080da081b40034fe069ec0d3b81a73034de0698c0d2f81a5b034ae0694c0d2781a4d03496069280d2481a480348e0a9180d22b424403486069040d1f81a3e0347a065fc0cbd81977032e6065bc0cb18195f032b60655c0ca98194f0329a0652c0ca501949032900651c14a301945662880650c0ca08193f0327c064f40c978192e03256064a40c9181922032421e480143f82877050b40a15c142b028470508c0a1140c1f8183d0306e0a0d40c17818270303e0605c1eb586d63058de0b1ac163382c63058be0b14c15b788b6e056d60ada815b383b66056c60ad8815af86b5e056a60ad48453783a6b074ce2298c352f86a530549e0a92c152382a430547e0a8f4151d81a390546ee08d4151981a31112de0e5ac1cb3879630d2be1a54c14a78294b0528e0a50c149f8293d05276064e4149bb613505266064c454978792b6424e1e48c143782867050940a11c1423028370506c0a0d41417828270503e0a05c163782c6b058ce0b18c25b783b6b076ce12d8c15a782b4b0568e0ad0c253783a6b074ce1298c152782a4b0548e0a90c3d1f87a3b0f46e1e8cc14a71386e070cc0a1180c1f0a8360305c1e09816b782d6e03ad6075a816b381d6605ac60b5881e3583c630d8b617164362985c51056de0adac15b382b63056be0ad7415ad81b59056ae0ad540da981b510569e0ad0c1d3783a6e034d60a99c0d3183a62094be12978252e86a4f034860a8fc0d1d82a3a0546e0a8d80d198396f032d60e59c0cb18c95f0b2ba0656c0cac8c9570b2aa0654c0ca88694f032860a4fc0c9d8293703266064bc0c9581927032460a1bc14338285f050ba0a15c142a8283f0506e060bc1416828270504a0607c140b82d6f05adc075ac0eb502d6703acc0b58c16b103c6b078c61716c2e2c85c530b8a20adbc15b582b67056c60ad7c15ae82b5b036b20ad5c15aa81b53036a20ad3c15a183a6f034d60e99c0d3185a5f194ba0696c0d2c85a570b4aa0694c0d2885a4f034860a8fc0d1d82a37034660e5bc1cb70196b052ce0658c1cb10495f092bc125742ca7819430527e064ec149d029370526c064cc0c978192b0324e0648c143782867050be0a174142b828550507e0a0dc0c17828270303e0a074140b8281505ade0b5b816b683c6b078c61316c362c84c53098a20adbc15b582b67056c60ad5c25ab02b550569e0ad0c1d3783a6b074ce0e98c252f84a5d094b606964252baf255094a606944352786a430547e0a8ec151b82a33072de0e5ac1cb383963092be1257424ad81959092aeb855424a9819510d29e1a50c149f8293b0526e0a4cc54978792b2924e1e48c143782867050ae12158142a8283f0506e0a0bc14138281f0502e0f9ec273982d7f29afc0b5ec16bd02d7707aec0b5cc16b902d6f0badc0b58c16b102c7f058f60b1dc163982c6f058c606dfc25bf01b7b036f406ddc1dbb01b73036e406dbc35b701b63036c406d7c15af01b5d056b806d6c0dad01b59036b006d5c15ab01b55096a806d4c0da901b51036a006d3c15a701b4b0369406d1c15a301b4303684069fc0d3d81a77034e6069bc0d3181a5f034ba0696c0d2c81a57034aa0694c0d2881a4f034960691c0d2181a3f0347c068f40cbf8197b032ee065cc0cb781963032be065740cad81959032ae065540ca9819510329e0652c0ca3819430327e064f80c9e8192f0325c064ac0c948192303244064843c900287f050ee0a17c142f0285d0509e0a13814210183f0307a060dc141a8182f0304e0607c0c0b83d6b09ac60b1bd6a3702c6b058d40b19c1e3302c63058c40b17c362f02c53058a40adbc15b582b67056c60ad7c15a984a6f074d60e99c253186a5f0d4a60a93c152682a4b034920a91d112282a43034820a8fc151d82a3705466125bc1cb583967092c61a57c34a98294f0529a0a52c0ca4829471828a0a50c0ca08293f052760a4dc14998a92f0f256b049c3c918286f050ce0a13c14270284d0507e0a0f814190282f0504e0a07c140b82c6f058d60b19c163188b6f076d60ed9c45b182b4f056960ad1c15a187a6f074d60e99c3d3182a4f054960a91c152187a3f0f4761e8dc3d1982946110dc0e19814270183e1506c060b83c1303d6b09ac6131bc263703c6b078d40f19c1e3304c63098c41317c262f04c530d8a40adbc15b582b67056c60ad7c15a981b4f0369c06d340d3781a6b034ce0698c0d2f81a530349e069340d2381a4503486068fc0d1d81a390346e068cc0d188196f032d60659c0cb18195f032a60653c0ca68194b032920651c0ca28194303282064fc0c9e8193b0326e064d40c998192f032560649c0c918286f050ce0a13c1426828470508a0a0fc141e828370506a060bc0c138181f0302e0f5ac36b18ec6f058d60f19c163186c5f058a606dbc0db581b67036c606d7c0da981b4f0369606d1c0da181a6f1d4dc069ac0d3501a67074cc0698c0d3101a5f0d4bc0694c0d2901a4f0549c0692c0d2501a475248c0690c0d210196f032d60659c0cb18195f032a60653c0ca58194703286064fc0c9d8193703266064bc0c968192b032520649c0c9281923032422a1bc1c338284f0508e060e80c1b818360304e0609854128181f0302e0b1bc163582c67058c62adbc0db583b67036c60ad3c0da582b47036861e9bc0d3583a67034c60a93c0d2582a4703486068fc0d1d81a3703466064f89c37038660509c0a118541b0182e0f04c0b9fc173f02e7d07af60f5cc36b586d6909ac61b584163d82c7a058f20b1dc1e3b02c73058e20b19c1e3302c65058be1b178162982c52076fe0edf81dbd83b7a076ee0edd81db983b72096de12db855b684b6c116d622da845b488b68116ce22d9845b288b64096c612d8855b084b600d6be1ad7835a986b520569e0ad3815a582b4a0568e0ad1815a182b42074fe069ec1d3b81a73094de2a9b40d3581a69114ce229940d3181a610d4be0694c152781a4b0548e0690c1cbf8197b072ee065cc24b79196d032d6065a444b388965032c60658434af819530529e0652c14a3819431527e2a4f40c9d819391526e2c4d40c99819310325e064ac0c9381923050fe0a1dc14378286d050ce0a194142d1d0560509e0a11c0c1f8183e0307a060bc0c17018220303e0a05c1eb783d6e03ad6075a80eb381d6603ac6075881e3583c630b8b6171642e2985c51076de0adac1db382b63096be12d7415ad82b59096ae12d5415a982b510969e0ad0c0d3781a6b034ce0698c0d2f81a5d034b6069640d2b81a55034a6069440d2781a430347e068ec0d1b81a33032de0e5b80cb581967032c6065880caf8495e032ba0653c0ca18193f03276064dc0c998192f03256064a80c938192603246061bc1c338185f030ba1615c2c2a8283f0506e060bc0c138181f0303a0605c2c0a83d6f07adc135b41e3583c63098b61b164262984c51076de0adac1db382b63096be12d7415ad82b59096ae12d5415a982b510969e0ad0c1d3781a6b074ce0698c252b84a56154aa1a93c0d2182a3f03476128dc0d198396f032d60e59c0cb18495f092ba0656c0cac849574a2aa0654c0ca88694f032860a4fc0c9d8493703266064bc0c9581927032460e1bc1c3384857090ac2a154141f828370305e0e09c0c0f8781707ad61358c263784c6e078d60f1a81e3383c66098c6131882e2f85c5e0b8a61714815b782b6b056ce0ad8c15af82b530569e0ad340da581b490368e06d140da181b41034de069ac0d3381a63034be0694c0d2781a4d03496069240d2381a4503486069040d1f81a3b0346e068cc0cb78496e032d60659c0cb181962032be165780ca9819520328e125180ca28193f03276064e80c9b8293603266064bc0c958192a0324e064980c918286f050ce0a13c1426818470308a0a0fc0c1b8182f0304e0607c0c0e818170502a0f5ac26b184c6f098dc0f1ac1e3503c67078cc1318c263104c5f098bc1314c362902b6f056d60ad9c15b182b5f056a60ad3c25a702b4d094de069ac1d3381a630d4be0694c152782a4e0549a0a8fc0d1d82a3703466125bc0cb583967032c61a57c0ca98494f4629a0652c0ca4849470928a0650c0ca08293f032760a4dc0c998192f032560649c0c918286f050ce0a13c24270284d0507e0a0dc0c17828270303e0a05c0f3f81e7e03cfa0f5ec1eb986d6b0dad21358c36b083c7f058f60f1dc163984c6f238da0b1ac163484c67138ca0b18c163084c5f058a60edfc1dbf03b7b076f40eddc1dbb03b73076e412dbc25b70ab6d096d826dac4db509b69136d026d9c4db309b65136c812d8c25b10ab61096c01ad7c2daf06b530b6a40ad3c15a704b4b0969412d1c25a302b4305684069fc0d3d81a77034e6069bc0d3681a6b034d20699c0d3281a63034c20697c0d2981a4f034960691c0d218197b032f4065e40cbb83976032e6065c40cb383966032ca0657c0ca98194f032960651c0ca18193f0327a064ec0c9c819370326a064cc0c988192f032560649c0c918387f070ee121bc3c36878670f0ca1e168e02b0284f0508e060fc0c1f0183d0305e060b80c110181f0302e0b5f416ba83c7e098fa1b1b8263102c5e038b4071580e2903b7e076f40ede41dbc03b76076e412dc425b805b6e0b6c40ad7815ad02b56056a412d3825a684b4c096942ad2455a404b461568a32d1025a104b4109680069340d2501a4903490129180d228ca4403482065f40cba8194d03292065140ca08193d03272064d40c988286a170cc0a1341425048460508a4a1100c1f0183d0305c060881eb584d63058de0b1ac163382c63058be0b14c25b784b6e076d60eda81db383b66096c612d8835af85b5e0d6a616d4815a782b4e0369606d280da381b460368606d080d3781a6b034ce0698c0d2f81a530349e0692c0d2381a430346e328d80d1a8196f032d60659c0cb18195f032a60653c0ca58194703286064fc0c9e8193b03272064dc0c9a8193303262064bc0c9581927032460a1bc14338184f0508e0a0dc641b028350305e0609c0c0f81817 20 1048575 8 255 11 2047 19 524287
def cc_55_2 : Nat → List (Nat × Nat) := unpackCursorV4 0xc479ad4faac322a0a0a3e8a76b2976ca45b0895060e2e7dcb9de326f705a8aa652a17dae592c94eac4f2911c4141ca8e6c1346a8bcaa296b88db01e6a060b212ab032b0082900041 0x9d6f07ad60f59c36b189c6f078d60f19c4e3186c5fcc8b79515c362981b6f036d606d9c0db181b5f036b606d5c0da981b4f0369606d1c0da181a6f034d60699c0d3181a5f034b60695c0d2981a4f034960691c0d2181a3f0347a068ec0d1d01a370346c068d7111a0196f132dc065ac0cb501967072cc0658c0cb10195f0d2bc0656c0cab81953032a40653c14a70194dc22980652c0ca501947c028c06516f8a20194303284064fc0c9f0193d0325e064b80c968786f070d60e19c3c318685f0f0b61e15c34298784f0f0961e11c3c218183f03076060dc0c198182f030560609c0c118181f0303a0606c0c0b87815030260f5ec1eb986d6b0bad21358c2eb083c7f058f60f1dc163984c6f298da0b1ac163484c67278ca0b18c163084c5f058a606dfc1dbf01b7b036f406ddc1dbb01b73036e406dbc25b701b6d096d806dac0db501b69036d006d9c9db301b65276c806d8c0db101b61036c006d7c35af01b53036a406d3c15a701b4b0369406d1c25a301b4303684069fc0d3d81a77034e6069bc0d3681a6b034d20699c0d3281a63034c20697c0d2981a4f034960691c0d2181a3f0347c068f40cbf8197b032ee065cc0cb78196d032d6065a40cb381965032c6065840caf819530329e0652c0ca3819430327e064f80c9e8192f0325c064ac0c948192303244064843c900387a070ee0e1d81c3383866070ca0a13c14238183f0307a060dc3c1a8182f0304e0607c0c0b83c6b078c61b16c362c84c530d8a20edbc15b583b67056c612d7d69ae82b5b056b212d5c9daa82b53056a212d3c15a183a6f074d60e99c1d3184a5f484ba2a96c0d2c93a57274aa1294c0d2886a4f0d4860a8fc251d84a37054660e5bc1cb583967072c61257c70ae8795b032b24e55c9caa84953032a21a53c34a18293f09276124dc14998a92f0f2577449c3c918386a070ce0e1981c2b83856070aa0a0fc141b8a82f1504e1e07c3c0b82c6f058d60b19c163183b6f076d60ed9c1db182b4f056960ad1c15a183a6f074d60e99c1d3182a4f054960a91c152187a3f0f4761e8dc3d1983966070dc0a13814230183e1506c060b83c1302c6f058d60b19c16318ab6f076d60ed9c55b182b4f056960ad1c15a187a6f074d60e99c3d3182a4f054960a91c152187a3f0f4761e8dc3d198a9360f24c4e1b81c330284e0508c060f8541b0182e0f04c071ac0e3503b6f056d60ed9c15b184b4f0969a0ad2c15a484b470968a0ad0c15a083a6f074dc069ac0d3183a620949e12938252682a3f03476128e8251b84a36034660e5bc0cb583967032c63253c2ca68194b032923251c2ca281943032820a4fc0c9d8493703266064bc54968192b0324e324940c9181c6b038d40edbc15b583b67056c612d3c25a682b4b0569212d1c25a282b43056820e9bc0d3583a67034c61693c652681a4b034921691c2d2281a43034820a8fc0d1d84a37034660e5bc1cb70196b032c60e58824a78494e0929a0a4fc0c9d8493a0926e124d80c998192f032561e4a80c9385926032460edbc15b583b67056c612d3c25a682b4b0569212d1c25a282b43056820e9bc1d3583a67074c61293c252684a4b034921291ec92284a43034820a8fc251d84a37054660e5bc1cb583967072c61253c24a68494b032921251ec0a284943032820a4fc249d84937052662a4bc3c95be1270f2460b9fc173f02e7d07af40f5c846b508d6809ac41358015bd82b7a056f20addc1dbb02b73056e20ad9c1db302b65056ba12d7015a882b50074fe0e9ec1d3b83a73094de2e9b4453581a69114ce22994253181a61a24ba06944151f82a3b0546e0a8cc1cbf8397b072ee0e5cc24b78b96d0f2d6065a444b388965092c60658640ae819510527e0a4ec149b829331525e1e4ade893879233a04c20058263784c6e078d60f1a81e3383c66098c61318815b782b6b056ce0ad8c0da181b41094de069ac1d3381a630949e12938252681a3b054740a8dc151b01a33092de065ac1cb3819631929e165340ca5819491928e165140ca1819410527e064ec149b819330325e064ac0c9381923098de131b81e3583c6a078ce0f198263184c62056de0adac15b382b630368606d04253781a6b074ce0698c2d278ca4d03496069242d2385a450348606904151f81a3b0546e068cc24b78196b072ce0658c24a78494e0929a064ec149d029370526c064cc0c978192b0324e0648c263784c6e078d60f1a81e3383c66098c61318815b784b6e056d60ad9c15b182b62094de0e9ac1d3384a630949e12934252581a490948f54914252181a410547e0a8ec151b82a33092de0e5ac1cb3849630929e1253424a5819490928f5051424a1819410527e0a4ec149b829331525e1e4aca4938792303cfe079f80f3e83d7a07ae42f5a876b404d6209ac00edfc15bd83b77056e612dbc5db682b6b056d212d9c75b282b63056c212d7415a881a7b074f4069e41d3b83a76034e6069c41d3383a66074ca2a976812e01a51034a00a8fc0d1d84a37034660e5fc0cbd83977032e6125bc5cb68196b032d22e59c74b281963032c31c5740ca88293f03276124dc0c998192f032560649c0c918a8260e02c0b9f8173e83c7e078f40f1d81e3904c6e178da131b0463508c69118d023198463288c64098c42f184263002b7a056f20edd815b883b66056ca0ad3415a482b45056820e9f81d390aa6d034d2229940d308b96d032d2225940cb08c94d032925a5140ca081d6f03adc075b41db78bb6d076d60eda81db383b66076ca0ed6c1dad03a6f054d60e99c153184a5f054b61295c152984a3f05476128dc15198396f032d60e59c0cb18495f032b62e55c0ca98c93f03276324dc0c998292f032561249c0c9185c6f098dc0f1ac1e3503c67078cc1718c263116b6f056d60ed9c15b185b4f0969a0ad2c15a485b470968a0ad0c15a081a6f034d60699c0d3181a4303482068fc0d1d81a3703466065bc0cb581967032c60653c2ca70194d0327e064ec0c9b8193303256064a80c938192603246631bc263703c6b078d40f19c1e330cc63098c544dbc15b583b67056c632d3c25a682b4b0569232d1c25a282b43056822a9be813701a6b074ce0698c553102a3f034762a8dc0d19ca16f032d60e59c0cb18c94f7829a0652c0ca4989479e28a0650c0ca08293f03277044dc0c998192f032560649c0c9182c6f058d60b19c163184b6f096dc0edac1db503b67076cc12d8c25b101b4b03694129bc0d3583a67034c60a93c0d2581a430547e0a8f424b78196b072ce0658c14a78194b0528e0650cbc9f8593d03276064e4bc9b8593503266064c40c978192b0324e0648c541303e7a09ce4131f81e3d03c76098e4171b46e3605c610b8c00adb415b081b4d0369206d140da081a6d034c2069340d2481a4503482125f80cb90196d0b2d8065840cb0049460328a064e8149b0192a0324c060980c0b03e7a09ce4131fc5e3f03c7b078f40f1dc1e3b04c73178e4131b426360fc619a8c00adfc15bd82b77056e60adb415b081b4f0369c06d34253f81a7b074ee069cc553681a610549e0a938152682a3f0547c068ec0d1c81a3305464068c424bf8197b072ee065ce28b6819611b29f305340ca5819490928e3e5140ca1819410527e0a4f40c9d829371f26a064cc0c978192b0324e0648c54130601603cfc079f41e3f03c7a078ec0f1c826370bc6d098d8271a84e3489c68138cc271944e3204c62178c2131805db682b69136ca0ad8425a682b490968a0ad041d3f01a72034da069a40d3281a61032f4065e41cbb01971072cc065940ca6819490328a065040f3f81e7e03cfa0f5e81eb909d6a13ad01358826b003b7f056f60eddc15b984b6f176da0adac15b484b67136ca0ad8c15b084b5d056a20e9fc0d3d83a77034e6129bc5d3681a6b034d22699c4d3281a63034c3289740d2882a3f03476128dc0d198197b072f4065e41cbb83976032e6065c41cb383966072ca1657620ae01951032a00a4fc0c9d8493703266064bc0c958192703246700982c0b02e7e05cfa0f1f81e3d03c76078e4131b85e3684c6c118d4171a42e3408c66118ca23190263105c61098c00ade815bc83b76056e20ed9815b282b4d056920ad1415a08ba6d034d2229940d308ca4d03492329140d208397e072e4165b40cb485965032c2079f80f3e83c7e078f40f1d81e3904c6e178da131b05e3505c690b8d02f19876328ec64098c41718426300bb6d056d236d9415b084b4d0569212d1415a081a7a034f20e9d80d3883a66034ca069340d2481a45034820e5f80cb90196d032d2065940cb08cd6f09adc0f5ac1eb503d6707acc3358c26b10cb6f056d60ed9c15b18cb5f096ba0ad6c15ac8cb57096aa0ad4c15a881a6f034d60699c0d3181a5f0b4bc069740d1f81a3b0346e068cc0cb78196b032ce0658c0ca9819510327e064ec0c9b819330325e064b40c938192503246135f81ebd03d7609ae42f1f81e3d03c76178e417178262e84c5c238b437164962c0dc56098aa131502e290dc510b8a00ad7415ac82b55056a206d380da681a5d034b2069540d2882a4e0349a0a8f80d1c81a3203462125f80cb90d94e0329a165300ca48194503284065040ca00193d0326a075bc0eb701d6d076de16db41db583b6a076ce0ed981db283b5b076b40e9bc153583a67054c61297c152d84a57054a6128fc151d84a37054660e5bc0cb583967032c61257c0cad85957032a6164fc0c9d85937032660a4bc0c9584927032464b1bc263703c6b078d40f19c1e3305c63098c520dbc15b583b67056c616d3c25a682b4b056924ad1c25a282b43056831c9bc0d3583a67034c61693de12681a4b034924691e312281a43034820a8fc0d1dc523703466165be20b70196b072ce0658c3cb10293f03276164dc0c998192f032560649c0c9182c6f058d60b19c163184b6f096dc0edac1db503b67076cc12d8c25b101b4b03694129bc0d3583a67034c60a93c0d2582a4703486668fc651e81a3b03472668dc651a81a3303462125bc0cb583967032c60a53c0ca5819430527e0a4f40c978192b0324e0648c2c0b04d7e07af40f5d826b90bc7e078f40f1d85e390cc5e098ba13170662d0fc59318b033158262a84c54198a433144662802b5d056b20ad5415a881b4e0369a129f80d390ca4e0349a329300d2481a4503484069040d2001a3d0346a065740cac81955032a20a5380ca68293e03272064c80c9883e7a09ce40b1b4163084b7e076f40edd825b911b6d236d832d8465b001b4e0369406d180da104a7e034e4069b4653601a61034c006928152304a360346a065b40cb08193d03272064d40c988192d0324a060980c0b03e7a09ce4131fc5e3f03c7b078f40f1dc1e3b04c73178e4131b426360fc61848c00adfc15bd82b77056e60adb415b081b4f0369c06d34253f81a7b074ee069ce093681a611f49f009340d2581a490948e3e9140d2181a410547e0a8f40d1d82a371f46a068cc24bf8197b072ee065cc2cb6819610529e0a53814a68293f0527c064ec0c9c8193305264064c40c978192b0324e0648cd81305816 18 262143 7 127 11 2047 19 524287
def cc_55_3 : Nat → List (Nat × Nat) := unpackCursorV4 0xa024f99f6393e619013d8c43d85d677fc617bf3d7823d71b676ba6167c3e5e3995855e522634bf6341ea13e03e3a23e3564c2fd592ad50254591f2621b04216e4214d2112c210ef3d0b33c03c770003c 0x3d6b04d6304c6f04c6e03c6b03c6a03c6703c6604c6304c6206c5f06c5e06c5306c5202b6f02b6b02b6702b6302b5f02b5301b4f01b4d02b4701b4502b4304a6f01a6b03a6701a6306a5f01a5311a4f1f24d01a4b01a490da477f24501a4301a4102a3f01a3b02a3701a330496f0196b03967019630695f019530294f0294d0294702945019430293f0193b02937019330192f0192b01927019230286f0486e02867028620284704846028450283f0283a02837028360182f028270181f0281a028170781604d6f03d6b03d6704d6304c6f8c46e03c6b03c6a03c6703c6604c638946204c5f06c5e0fc5b04c5706c5306c5204b6f02b6b03b6702b6304b5f02b5b04b5702b5301b4f01b4e01b4d04a6f01a6b03a6701a6306a5f01a5b8725701a538624f8424d01a4b01a4904a476824501a4301a4102a3f8323d01a3b04a378223501a330496f0196b03967019630695f0195b81157019530294f0294e0294d0293f0293e0193b019390193302932019310192f0192b01927019230486f0286b03867028630685f0285b3f057028538004f7e04d0284b048470c045028430283f0283b02837028330182f0282b1e027018230181f0281b078170181308d6f03d6b03d6706d6302c6f02c6b02c6702c6302c5f02c5b02c5702c5301b6f01b6b01b6701b6301b5f01b5b01b5701b5301b4f01b4b01b4701b4301a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4d01a4b01a4a01a4702a4601a4501a3f01a3b01a3701a330196f0896e0196b0196a019670396601963019620195f0695e0195b0195701953019520194f0294e0194d0193f0193e0193b0193a019370193601933019320192f0192e0192d0286f0286b02867028630285f0285b02857028530284f0284b02847028430183f0183b01837018330182f0182b01827018230181f0181d0181b01817028150181302d7f02d7b02d7702d7302d6d08c7e03c7602c5e01b7f01b7b01b7701b7301b5f01b5b01b5701b5301b4901b4501a7f04a7e01a7b01a7a01a7703a7601a7301a7201a5f02a5e01a5b01a5a01a5702a5601a5301a5201a4901a4801a450fa4401a3f01a3e01a3d0197f0197b01977019730195f0195b019570195301949019450193b0193a019390193701936019330193101927019260192503e7a0ee7204c7f02c7b03c7702c7305c6d02c5101b7f01b7b01b7701b7301b6d01b6101b4f01b4b01b4701b4301a7f04a7e01a7b01a7a01a7703a7601a7301a7201a6d10a6c01a6101a6001a4f02a4e01a4b01a4a01a4704a4601a4301a4201a3f01a3e01a3d0197f0197b01977019730196d019610194f0194b01947019430193b0193a019390193701936019330193101927019260192504d6f03d6b03d6704d6304c6f04c6e03c6b03c6a03c6703c6604c6304c6204c5f04c5e04c5b04c5704c5306c5204b6f02b6b03b6702b6304b5f02b5b04b5702b5301b4f01b4e01b4d01a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4d01a4b01a4901a4701a4501a4301a4101a3f01a3b01a3901a3701a3301a310196f0196b01967019630195f0195b01957019530194f0194d0194b01949019470194501943019410193f0193d0193b0193701935019330192f0192b01927019230486f0286b03867028630685f0285b0a857028530484f0a84d0284b0484704845028430283f0283b02837028330182f0182b01827018230181f0181b01817018130ed6f03d6b03d6706d630ec6f03c6b03c670ec6306c5f7b45b7a45706c5301b6f01b6b01b6701b6301b5f01b5b01b5701b5301b4f01b4b01b4701b4301a6f0ea6e01a6b01a6a01a6703a6601a6301a6201a5f06a5e01a5b01a5701a5301a5201a4f02a4e01a4b01a4a01a477924601a4301a4201a3f01a3e01a3d0196f0196b01967019630195f0195b01957019530194f0194b01947019430193b0193a01939019370193601933019310192701926019250a86f0386b03867078630685f0785b0a857068530a84f0784b0a847078430183f0183b01837018330182f0182d0182b018270a825018230181f0181b018170181302d7f02d7b02d7702d7302d6d08c7e03c7602c5e01b7f01b7b01b7701b7301b5f01b5b01b5701b5301b4901b4501a7f01a7b01a7701a7301a5f01a5b01a5701a5301a4901a4501a3f01a3e01a3d01a3701a3501a3301a320197f0497e0197b0197a019770397601973019720195f0295e0195b0195a019570295601953019520194901948019450f9440193701936019350192f0192e0192d03e7a09e7204c7f02c7b03c7702c7306c6d02c5101b7f01b7b01b7701b7301b6d01b6101b4f01b4b01b4701b4301a7f01a7b01a7701a7301a6d01a6101a4f01a4b01a4701a4301a3f01a3e01a3d01a3701a3501a3301a320197f0497e0197b0197a019770397601973019720196d1096c01961019600194f0294e0194b0194a019470494601943019420193701936019350192f0192e0192d04d6f03d6b03d6704d6304c6f04c6e03c6b03c6a03c6703c6604c6304c6204c5f04c5e04c5b04c5704c5306c5204b6f02b6b03b6702b6304b5f02b5b04b5702b5301b4f01b4e01b4d01a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4d01a4b01a4901a4701a4501a4301a4101a3f01a3d01a3b01a3701a3501a330196f0196b01967019630195f0195b01957019530194f0194d0194b01949019470194501943019410193f0193b019390193701933019310192f0192b01927019230486f0286b03867028630685f0285b07857028530484f0784d0284b0484704845028430283f0283b02837028330182f0182b01827018230181f0181b018170181309d6f03d6b03d6706d6309c6f03c6b03c6709c6306c5f7745b7645706c5301b6f01b6b01b6701b6301b5f01b5b01b5701b5301b4f01b4b01b4701b4301a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3e01a3d01a3701a3501a3301a320196f0996e0196b0196a019670396601963019620195f0695e0195b0195701953019520194f0294e0194b0194a019477514601943019420193701936019350192f0192e0192d0786f0386b03867078630685f0785b07857068530784f0784b07847078430183f0183b01837018330182f0182b01827018230181f0181d0181b01817078150181303e7e03d7a03c7f03c7b03c7703c7302c6914c6501b7f03b7e01b7b01b7a01b7703b7601b7301b7201b6901b6801b6515b6401b4f02b4e01b4b01b4a01b4704b4601b4301b4201a7f01a7b01a7701a7301a6901a6501a4f01a4b01a4701a4301a3f01a3e01a3d0197f0197b019770197301969019650194f0194b01947019430193f0193e0193d0192f0192e0192b019290192301922019210992002e7f02e7e02e7d03d7f03d7b03d7703d7304d6f06d6b05d6908d6704d6305d6102c7b03c7a02c7903c7703c7602c7302c7103c6703c6603c6504c5f06c5e02c5b04c5702c5306c5201b7f03b7e01b7b01b7a01b7703b7601b7301b7201b6f04b6e01b6d04b6c01b6b01b6a01b6901b6801b6708b6601b6508b6401b6301b6201b6101b6001b5f06b5e01b5b01b5701b5301b5201b4f02b4e01b4b01b4a01b4704b4601b4301b4201a7f01a7b01a7701a7301a6f01a6d01a6b01a6901a6701a6501a6301a6101a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3e01a3d0197f0197b01977019730196f0196d0196b01969019670196501963019610195f0195b01957019530194f0194b01947019430193f0193e0193d0192f0192e0192b01929019230192201921099200387f0287b03877028730486f1486d0286b0886708865028630685f0285b3d057028530284f0284b02847028430183f0183d0183b018370b035018330182f0182b01827018230181f0181b018170181303d6f03d6b03d6703d6302c6f02c6b02c6701c6302c5f02c5b02c5702c5303b6f03b6e01b6b01b6a01b6701b6601b6301b6205b5f05b5e05b5b05b5705b5305b5202b4f02b4e01b4b01b4a01b4701b4601b4301b4201a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f05a3e01a3d0196f0196b01967019630195f0195b01957019530194f0194b01947019430193f0593e0193d0192f0192b01927019230286f0286b02867028630285f0285b02857028530284f0284b02847028430283f0283d0283b0283702835028330182f0182b01827018230181f0181b018170181303d6f03d6b03d6703d6302c6f02c6b02c6701c6302c5f02c5b02c5702c5303b6f01b6b01b6701b6306b5f0cb5b0cb5706b5302b4f01b4b01b4701b4301a6f03a6e01a6b01a6701a6301a6201a5f01a5b01a5701a5301a4f02a4e01a4b01a4701a4301a4201a3f02a3e01a3b01a3901a3701a3301a3201a3101a300196f0196b01967019630195f0195b01957019530194f0194b01947019430193f0c93e0193b0193901937019330193201931019300192f0192e0192d0286f0286b02867028630285f0285b02857028530284f0284b02847028430283f0283b02837028330182f0182d0182b0182702825018230181f0181b018170181303d6f03d6b03d6703d6302c6f02c6b02c6701c6302c5f02c5b02c5702c5303b6f01b6b01b6701b6305b5f05b5b05b5705b5302b4f01b4b01b4701b4301a6f03a6e01a6b01a6701a6301a6201a5f01a5b01a5701a5301a4f02a4e01a4b01a4701a4301a4201a3f02a3e01a3b01a3901a3701a3301a3201a3101a300196f0196b01967019630195f0195b01957019530194f0194b01947019430193f0593e0193b0193901937019330193201931019300192f0192e0192d0286f0286b02867028630285f0285b02857028530284f0284b02847028430283f0283b02837028330182f0182d0182b0182702825018230181f0181b018170181303e7f03e7b03e7703e7302d7f02d7d02d7b02d7a02d7703d7602d7502d6f06d6e02d6b02d6702d6302d6202c7f03c7e02c7d02c6f05c6e02c6b02c6702c6302c6202c5f02c5e02c5d01b7f03b7e01b7b01b7a01b7703b7601b7301b7201b6f06b6e01b6b01b6701b6301b6201b5f02b5e01b5b01b5a01b5702b5601b5301b5201b4f02b4e01b4d02b4c01b4b01b4a01b4901b4801b4702b4601b457134401b4301b4201b4101b4001a7f01a7b01a7701a7301a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4d01a4b01a4a01a4901a4801a4702a4601a457024401a4301a4101a3f01a3e01a3d0197f0197b01977019730196f0196b01967019630195f0195b01957019530194f0194d0194b0194a01949019480194702946019456f14401943019410193f0193e0193d0192f0192e0192b01929019230192201921099200287f0287b02877028730286f0286b02867028630285f0285b02857028530284f0284d0284b0284702845028430183f0183d0183b0183702835018330182f0182b01827018230181f0181b018170181302d7f02d7b02d7702d7302d6d08c7e03c7602c5e01b7f04b7e01b7b01b7a01b7703b7601b7301b7201b5f02b5e01b5b01b5a01b5702b5601b5301b5201b4901b4801b450fb4401a7f01a7b01a7701a7301a5f01a5b01a5701a5301a4901a4501a3f01a3e01a3d0197f0197b01977019730195f0195b019570195301949019450193f0193e0193d0192f0192e0192b019290192301922019216412003e7a10e7204c7f02c7b03c7702c7305c6d02c5101b7f04b7e01b7b01b7a01b7703b7601b7301b7201b6d10b6c01b6101b6001b4f02b4e01b4b01b4a01b4704b4601b4301b4201a7f01a7b01a7701a7301a6d01a6101a4f01a4b01a4701a4301a3f01a3e01a3d0197f0197b01977019730196d019610194f0194b01947019430193f0193e0193d0192f0192e0192b019290192301922019216312001d6f01d6e01d6701d6301d6203c6b03c6305c5b05c5905c5305c5103b6f02b6b03b6702b6304b5f04b5d02b5b02b5904b5704b5502b5302b5104b4f02b4301a6f01a6b01a6701a6301a5f01a5d01a5b01a5701a5501a4f01a4301a3f01a3b01a3701a330196f0196b01967019630195f0195d0195b01957019550194f019430193f0193b01937019330192f0192b01927019230386f0386e01867038620485f0485e0485d0283f028370182f0182a01827018260181f0181a018170181601d6f01d6e01d6d03c6f03c6b03c6703c6304c5f04c5b06c5904c5704c5304c5103b6f03b6b03b6703b6304b5f04b5d04b5b02b5904b5704b5504b5302b5104b4f04b4b04b4704b4301a6f01a6b01a6701a6301a5704a5601a5501a4f01a4b01a4701a4301a3f01a3b01a3701a330196f0196b01967019630195704956019550194f0194b01947019430193f0193b01937019330192f0192b01927019230386f0386b03867038630485f0485d0485b048576b055048530584f0784b0b847058430483f0483b04837048330182f0182b01827018230181f0181b018170181303d6b04d6304c6f04c6e03c6b03c6a03c6703c6604c6304c6205c5f05c5e05c5305c5202b6f02b6b02b6702b6302b5f02b5301b4f01b4d01b4701b4501b4301a6f01a6b01a6701a6301a5f01a5301a4f01a4d01a4701a4501a4301a3f01a3b01a3701a330196f0196b01967019630195f019530194f0194d0194701945019430193f0193b01937019330192f0192b01927019230286f0486e02867028620585e028520284704846028450183f0283a02837028360182f0182a01827018260181f0181a018170181604d6f03d6b03d6704d6304c6f04c6e03c6b03c6a03c6703c6604c6304c6204c5f04c5e04c5b04c5704c5306c5204b6f02b6b03b6702b6304b5f02b5b04b5702b5301b4f01b4e01b4d01a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f04a4e01a4d01a3f01a3b01a3701a330196f0196b01967019630195f0195b01957019530194f0494e0194d0193f0193b01937019330192f0192b01927019230486f0286b03867028630585f0285b0f857028530484f6904d0284b0484704845028430283f0283b02837028330182f0182b01827018230181f0181b01817018137356f03d6b03d6706d637246f03c6b03c676e46306c5f6d45b6c45706c5301b6f6a36e01b6b01b6a01b6703b6601b6301b6201b5f06b5e01b5b01b5701b5301b5201b4f02b4e01b4b01b4a01b476834601b4301b4201a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3e01a3d0196f0196b01967019630195f0195b01957019530194f0194b01947019430193f0193e0193d0192f0192e0192b01929019230192201921621205d06f0386b03867078630685f0785b3b057068533204f0784b2c047078430183f0183d0183b0183709035018330182f0182b01827018230181f0181b018170181302d7f02d7b02d7702d7302d6d08c7e03c7602c5e01b7f01b7b01b7701b7301b5f01b5b01b5701b5301b4901b4501a7f01a7b01a7701a7301a5f01a5b01a5701a5301a4901a4501a3f01a3d01a3b01a3a01a3701a3601a35642340197f0497e0197b0197a019770397601973019720195f0295e0195d0295c0195b0195a0195702956019550f95401953019520194901948019450f9440193f0193e0193d0192f0192e0192d03e7a09e7204c7f02c7b03c7702c7306c6d02c5101b7f01b7b01b7701b7301b6d01b6101b4f01b4b01b4701b4301a7f01a7b01a7701a7301a6d01a6101a4f01a4b01a4701a4301a3f01a3d01a3b01a3a01a3701a3601a35632340197f0497e0197b0197a019770397601973019720196d1096c01961019600194f0294e0194d0294c0194b0194a0194704946019450494401943019420193f0193e0193d0192f0192e0192d02c6f02c6b02c6702c6302c5d08b6e03b6602b4e01a6f01a6b01a6701a6301a4f01a4b01a4701a4301a3901a350196f0196b01967019630194f0194d0194b01947019450194301939019350192f0192e0192d03d6a09d6204b6f02b6b03b6702b6305b5d02b4101a6f01a6b01a6701a6301a5d01a5101a3f01a3b01a3701a330196f0196b01967019630195d019510193f0193d0193b0193701935019330192f0192e0192d09c5f03c5b03c5706c5309b5f03b5b03b5709b5306b4f6434b6334706b4301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3b01a3701a330195f0195b01957019530194f0194b01947019430193f0193d0193b0193701935019330192f0192e0192d0785f0385b03857078530684f0784b07847068430783f0783b07837078330182f0182b01827018230181f0181b018170181308c5f03c5b03c5706c5302b5f02b5b02b5702b5302b4f02b4b02b4702b4301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3b01a3701a330195f0195b01957019530194f0194b01947019430193f0193b01937019330192f0192b01927019230285f0285b02857028530284f0284b02847028430283f0283b02837028330182f0182b01827018230181f0181b018170181304d6f03d6b03d6704d6304c6f04c6e03c6b03c6a03c6703c6604c6304c6204c5f04c5e04c5b04c5704c5306c5204b6f04b6e02b6b03b6a03b6703b6602b6304b6204b5f04b5e02b5b0fb5a04b5704b5602b5306b5201b4f01b4e01b4d01a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4d01a4b01a4901a4701a4501a4301a4101a3f01a3d01a3b01a3901a3701a3501a3301a310196f0196b01967019630195f0195b01957019530194f0194d0194b01949019470194501943019410193f0193d0193b01939019370193501933019310192f0192b01927019230486f0286b03867028630685f0285b07857028530484f0784d0284b0484704845028430283f0783d0283b04839028370483502833078310182f0182b01827018230181f0181b018170181304c5f03c5b03c5704c5304b5f03b5b03b5704b5304b4f0fb4b04b4706b4301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3b01a3701a330195f0195b01957019530194f0194b01947019430193f0193b01937019330192f0192b01927019230485f0385b03857048530684f0784b07847068430783f0483b04837078330182f0182b01827018230181f0181b0181701813 20 1048575 8 255 11 2047 20 1048575
def cc_55_4 : Nat → List (Nat × Nat) := unpackCursorV4 0x987329483f918308e4348a53f8792c84f2a81b347ee2d7af3f78f2073a556d16966e6360b635aa61541694f54c49c59433693e15237a6734d2d30e3f26f9f2214e1b869163551045f0bd470477600047 0x3b6f03b6b03b6703b6304b4f04b4d04b4b02b4904b4704b4504b4302b4103a6f01a6b03a6701a6304a4f04a4d01a4b01a4904a479f24501a4301a4104a3f01a3b04a3701a330396f0496d0196b0396703965019630494f0494d0194b01949039470394501943019410493f0193b04937019330192f0192b019270192302e7f02e7e02e7d03d7a03d7208d6a08d6804d6204d6002b7b03b7a02b7903b7703b7602b7302b7103b6703b6603b6504b5d04b5c02b5102b5003a7f01a7b03a7701a7304a6f0ba6d01a6b01a6908a6708a6501a6301a619925d01a5102a3f01a3b04a3701a330397f0197b03977019730496f0596d0196b01969089670596501963019610695d019410293f0193b04937019330192f0192b019270192304c6f04c6e03c6b03c6a03c6703c6604c6304c6204b6f02b6b03b6702b6301b4301b4101a6f01a6b01a6701a6301a4f04a4e01a4d01a3b01a3a01a3704a3601a330196f0196b01967019630194f0194d0194b01949019470194501943019410193f0193d0193b0193701935019330192f0192b019270192304c6f04c6e03c6b03c6a03c6703c6604c6304c6204b6f04b6e02b6b03b6702b6304b6204a6f01a6b03a6701a6304a4f04a4d01a4b01a4904a479c24501a4301a4102a3f01a3b04a3701a330496f0196b03967019630494f0494d0194b01949049470694501943019410293f1093d0193b0493704935019330192f0192b019270192301e7f01e7e01e7d03d7a03d720bd6a0ed6804d6204d6003b7f03b7b03b7703b7304b6f0bb6d04b6b02b6904b670eb6504b6302b6104b5d02b5101a7b01a7a01a7901a7703a7601a7301a7101a6703a6601a6501a5d9825c01a5101a5001a3f01a3b01a3701a330197f0197b01977019730196f0196d0196b01969019670196501963019610195d019410193f0193b01937019330192f0192b019270192302e7e02e7d03c7e03c7a03c7603c7204c6e0bc6d04c6c08c6a08c6908c6808c6608c6508c6404c620bc6104c6003b7a02b7903b7602b7103b6603b6504b4d02b4904b4502b4103a7e01a7201a6d01a6901a6501a610196d0196901965019610194d0194901945019410192d0192501d6f01d6e01d6d03b6f0bb6d03b6b03b6a03b6703b6603b6503b5b03b5a03a6f03a6b03a6703a6304a5f04a5b04a5704a5304a3f08a3b04a3708a330196f0196b01967019630195f0195d0195b0195701955019530193f0193b01937019330192f0192b019270192311c6f04c6e03c6b03c6a03c6703c660cc6304c629936f03b6b03b670cb630cb4f04b4d0cb4b02b490cb4704b450cb4302b4101a6f9826e01a6b01a6701a6301a6201a3f01a3b01a3701a330196f0196b01967019630194f0194d0194b01949019470194501943019410193f0193b01937019330192f0192d0192b01927019250192304c6f02c6b03c6702c6304b6f04b6e03b6b03b6a03b6703b6604b6304b6201b4b01b4a01a6f01a6b01a6701a6301a4f01a4b01a4301a3f01a3d0196f0196b01967019630194f0194d0194b0194701945019430193f0193d0193b01939019370193501933019310192f0192b019270192303e7a04e7204c7f0bc7e03c7b03c7a03c7703c7604c730bc7204c6d04c6c0fc619646004b7f02b7b03b7702b7304b6d02b6101b4f01b4e01b4d01a7f01a7b01a7701a7301a6d01a6101a4f02a4e01a4d01a3f02a3e01a3b01a3901a3301a3201a310197f0197b01977019730196d019510194f0194d0194b01949019470194501943019410193f0193d0193b0193701935019330192f0192b019270192303d6a9e5629d36f03b6b03b6710b639b35d02b519a26f01a6b03a6701a639725d01a5110a3f01a3b9523701a330996f0196b03967019630695d019411093f0193b81137019330192f0192b019270192304d6f03d6b03d6704d6304c6f03c6b03c6704c6304c5f0fc5b04c5706c5302b6f02b6b02b6702b6302b5f02b5b02b5702b5301b4f01b4e01b4d01a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f02a4e01a4d01a3f01a3b01a3901a3701a3301a310196f0196b01967019630195f0195b01957019530194f0194b019490194701943019410193702936019350192f0192b01927019230286f0286b02867028630285f0285b02857028530284f0284b02847028430283f0283b02837028330182f0182b01827018230181f0181b018170181308d6f03d6b03d6706d6308c6f04c6e03c6b03c6a03c6703c6608c6304c6206c5f06c5e10c5b0cc5706c5306c5202b6f02b6b02b6702b6302b5f02b5b02b5702b5301b4f01b4d01b4b01b4901b4701b4501b4301b4101a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f02a4e01a4d01a3f02a3e01a3b01a3701a3301a320196f0196b01967019630195f0195b01957019530194f0194d0194b01949019470194501943019410193f0193b01937019330192f0192d0192b0192701925019230286f0286b02867028630285f0285b02857028530284f0284d0284b0284702845028430283f0283b02837028330182f0182d0182b0182702825018230181f0181b018170181308d6f03d6b03d6706d6302c6f02c6b02c6702c6302c5f02c5b02c5702c5302b6f08b6e02b6b02b6a02b6703b6602b6302b6202b5f06b5e02b5b02b5702b5302b5201b4f01b4e01b4d08a6f01a6b03a6701a6306a5f01a5b10a5701a5302a4f02a4d01a4b02a479324501a4302a3f02a3d01a3b01a3902a379223501a3301a310896f0196b03967019630695f0195b10957019530194b0294a01949029470294601943019410293702936901350192f0192b01927019230286f0286b02867028630285f0285b02857028530284f0284b02847028430283f0283d0283b0283702835028330182f0282b02827018230181f0281b028170181304d6f03d6b03d6704d6304c6f04c6e03c6b03c6a03c6703c6604c6304c6204c5f04c5e04c5b04c5704c5306c5202b6f02b6b02b6702b6302b5f02b5b02b5702b5301b4f01b4e01b4d01a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4d01a4b01a4901a4701a4501a4301a4101a3f01a3d01a3b01a3701a3501a330196f0196b01967019630195f0195b01957019530194f0294e0194d0193f0293e0193b019390193301932019310192f0192b01927019230286f0286b02867028630285f0285b02857028530284f0284d0284b0284702845028430283f0283b02837028330182f0182b01827018230181f0181b018170181304d6f03d6b03d6704d6304c6f02c6b03c6702c6304c5f02c5b04c5702c5301b6f01b6b01b6701b6301b5f01b5b01b5701b5301b4f01b4b01b4701b4301a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f02a4e01a4d01a4701a4501a4301a4201a3f01a3b01a3701a330196f0996e0196b0196a019670396601963019620195f0695e0195b0195701953019520194790146019450193f0193e0193b0193a019370193601933019320192f0192e0192d0486f0286b03867028630685f0285b07857028530284f0284b02847028430183f0183b01837018330182f0182b01827018230181f0181d0181b01817078150181303d6f03d6e01d6b01d6a01d6701d6601d6301d6203c6f03c6b03c6703c630bc5f05c5b05c590bc5705c5305c5101b6f02b6b03b6702b6301b5f01b5d01b5b01b5904b5704b5501b5301b5104b4f02b4b04b4702b4301a6f03a6e01a6b01a6701a6301a6201a5f04a5e01a5d01a4f01a4b01a4701a4301a3f01a3b01a3a01a3704a3601a330196f0196b01967019630195f0195d0195b01959019570195501953019510194f0194b01947019430193f0193b01937019330192f0192d0192b0192701925019230386f0286b03867028630c85f1185d0285b0c8570c855028530584f0284b0b847028430283f0283b02837028330182f0182b01827018230181f0181b018170181303d6f03d6e02d6702d6302d6203c6b03c6305c5b05c5905c5305c5102b6f02b6b02b6702b6302b5f02b5d02b5b02b5702b5502b4f02b4303a6f01a6b03a6701a630da5f0ca5d01a5b01a590da570ca5501a5301a5105a4f01a4302a3f01a3b02a3701a330296f0196b03967019630295f0295d0195b05957059550594f019430293f0193b02937019330192f0192b01927019230286f0386e02867028620285f0485e0285d0283f0283a02837028360182f028270181f0281a028170581603d6f03d6e04d6d03c6f03c6b03c6703c6304c5f04c5b06c5904c5704c5304c5103b6f02b6b03b6702b6304b5704b5604b5504b4f02b4b04b4702b4303a6f01a6b03a6701a6304a5f04a5d01a5b01a5904a578e25501a5301a5105a4f01a4b0ba4701a4302a3f01a3b04a3701a330396f0196b03967019630495704956089550594f0194b05947019430293f0193b03937019330192f0192b01927019230386f0286b03867028630485f0485d0285b048578d055028530584f0284b0b847028430283f0283b02837028330182f0282b11827018230181f0281b058170181303d6f03d6b03d6703d6303c6f02c6b03c6701c6304c5f02c5b04c5702c5303b6f03b6e01b6b01b6a01b6701b6601b6301b6206b5f05b5e0bb5b0bb5706b5305b5202b4f02b4e01b4b01b4a01b4701b4601b4301b4201a6f03a6e01a6b01a6701a6301a6201a5f01a5b01a5a01a570ba5601a5301a4f01a4b01a4701a4301a3f04a3e01a3d0196f0196b01967019630195f0195b01957019530194f0194b01947019430193f0193d0193b01939019370193501933019310192f0192b01927019230386f0286b03867028630685f0285b0b857028530284f0284b02847028430c83f1283d0283b0c8370c835028330182f0182d0182b018270c825018230181f0181b018170181303d6b03d6302c6f02c6b02c6702c6302c5f02c5303b6f03b6e02b6702b6302b6206b5f05b5e06b5305b5202b4f02b4e02b4b02b4a02b4702b4602b4302b4203a6f01a6b03a6701a6306a5f01a5302a4f01a4b02a4701a4312a3f0ca3d01a3b01a3912a370ca3501a3301a310396f0196b03967019630695f019530294f0194b02947019430293f0293d0193b01939029370293501933019310192f0192b01927019230286f0386e02867028620285a0b8560284f028470283f0483e0283d0182f0282a02827128260181f0281703d6f03d6b03d6703d6303c6f04c6d02c6b03c6703c6502c6304c5f02c5b04c5702c5303b6f03b6e04b6d04b5f06b5e04b5b04b5704b5304b5202b4f02b4e01b4b01b4a03b4701b4602b4302b4203a6f01a6b03a6701a6306a5f01a5b0ba5701a5302a4f01a4b04a4701a4304a3f04a3d01a3b01a3904a378b23501a3301a310396f0496d0196b0396703965019630695f0195b09957019530294f0194b03947019430293f0293d0193b01939039370293501933019310192f0192b01927019230386f0286b03867028630685f0285b0b857028530284f0284b02847028430483f0483d0283b048378a035028330182f0282b20027018230181f0281b078170181304c6f02c6b03c6702c6304b6f04b6e03b6b03b6a03b6703b6604b6304b6201b4b01b4a01a6f01a6b01a6701a6301a4f01a4d01a4b01a4701a4501a4301a3f01a3d01a3b01a3901a3701a3501a3301a310196f0196b01967019630194f0194b019430193f0193d0192f0192b019270192303e7a04e7204c7f0bc7e03c7b03c7a03c7703c7604c730bc7204c6d04c6c0fc618846004b7f02b7b03b7702b7304b6d02b6101b4f01b4e01b4d01a7f01a7b01a7701a7301a6d01a5101a4f01a4d01a4b01a4901a4701a4501a4301a4101a3f01a3d01a3b01a3701a3501a330197f0197b01977019730196d019610194f0294e0194d0193f0293e0193b019390193301932019310192f0192b019270192304e7f03e7b03e7704e7304d7f04d7e03d7b03d7a03d7703d7604d7304d7204d6f04d6e04d6b0fd6a04d6704d6604d6306d6204c7f02c7b03c7702c7304c6f02c6b04c6702c6301c5f01c5e01c5d04b7f04b7e03b7b03b7a03b7703b7604b7304b7205b6f05b6e0cb6b0fb6705b6305b6201b5f01b5e01b5d01b5c01b4f01b4e01b4b01b4a01b4901b4801b4701b4601b4301b4201b4101b4001a7f04a7e01a7b01a7701a7301a7201a6f01a6b01a6701a6301a5b01a5a01a5901a5801a5704a5601a5504a5401a5301a5101a4f01a4d01a4b01a4a01a4704a4601a4504a4401a4301a3704a3601a350197f0197b01977019730196f0196b01967019630195f0295e0195d0194f0294e0194b019490194301942019410193f0193d0193b01939019370193501933019310192f0192d0192b0192701925019230487f0287b03877028730586f0286b0f867028630485f1185d0285b02859048570485502853028510284f0284b02847028430c83f1183d0283b1183711835028330182f0182b01827018230181f0181b018170181303d6b04d6302c6f02c6b02c6702c6302c5f02c5304b6f04b6e03b6b03b6a03b6703b6604b6304b6206b5f05b5e06b5305b5201b4f01b4e02b4b02b4a01b4701b4601b4301b4201a6f01a6b01a6701a6301a5f01a5301a4f01a4b01a4701a4301a3f01a3d01a3b01a3701a350196f0196b01967019630195f019530194f0194b01947019430193f0193d0193b01939019370193501933019310192f0192b01927019230286f028670284f018470283f0c83e0283d0182f0182a01827018260181f0181704d6f03d6b03d6704d6304c6f02c6b03c6702c6304c5f02c5b04c5702c5304b6f04b6e03b6b03b6a03b6703b6604b6304b6206b5f06b5e0cb5b11b5706b5306b5201b4f01b4e01b4b01b4a01b4701b4601b4301b4201a6f04a6e01a6b01a6701a6301a6201a5f01a5b01a5701a5301a4f01a4b01a4a01a4704a4601a4301a3704a3601a350196f0196b01967019630195f0195b01957019530194f0194b01947019430193f0193d0193b01939019370193501933019310192f0192d0192b0192701925019230486f0286b03867028630685f0285b40057028530284f0284b02847028430c83f1f03d0283b1183785035028330182f0182b01827018230181f0181b018170181304d6f03d6b03d6704d6304c6f03c6b03c6704c6304c5f0fc5b04c5706c5302b6f02b6b02b6702b6302b5f02b5b02b5702b5301b4f01b4e01b4d01a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4b01a4901a4701a4301a4101a3702a3601a350196f0196b01967019630195f0195b01957019530194f0294e0194d0193f0193b019390193701933019310192f0192b01927019230286f0286b02867028630285f0285b02857028530284f0284b02847028430283f0283b02837028330182f0182b01827018230181f0181b018170181304d6f03d6b03d6704d6304c6f03c6b03c6704c6304c5f04c5b04c5704c5304b6f03b6b03b6704b6304b5f04b5b04b5704b5301b4f01b4e01b4b01b4901b4701b4301b4201b4101b4001a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f02a4e01a4d01a3f04a3e01a3b01a3901a3701a3301a3201a310196f0196b01967019630195f0195b01957019530194f0494e0194b01949019470194301942019410193f0293e0193d0192f0192b01927019230486f0286b03867028630685f0285b0f857028530484f0284b04847028430483f0283b04837028330182f0182b01827018230181f0181b018170181303e7a04e7204c7f05c7e03c7b03c7a03c7703c7604c7309c7204c6d04c6c02c6102c6005c5106c5004b7f02b7b03b7702b7304b6d04b6c02b6102b6001b4f01b4e01b4d01a7f01a7b01a7701a7301a6d01a6101a4f01a4d01a4b01a4901a4701a4501a4301a4101a3f01a3d01a3b01a3701a3501a330197f0197b0197a0197703976019730196d019510194f0294e0194d0193f0293e0193b019390193301932019310192f0192b0192a01927019260192303e7b04e7304d7f04d7e03d7b03d7a03d7703d7604d7304d7204d6f04d6e04d6306d6204c7f04c7e03c7b03c7a03c7703c7604c7304c7205c6f05c6e05c6305c6202b7f02b7b02b7702b7302b6f02b6301b5f01b5e01b5d01b4f01b4d02b4701b4502b4302b4104a7f01a7b03a7701a7305a6f01a6304a5f11a5d01a5b01a5904a5704a5501a5301a510da4f11a4d01a4b01a490da470da4501a4301a4102a3f02a3d01a3b02a3704a3501a330497f0197b03977019730596f019630295f0295e0295d0294f0294d029470294501943019410293f0293e0193b019390193302932019310192f0192b01927019230287f0487e02877028720285a02858028570485602855048540284704846028450283f0283a02837028360182f028270181f0281a028170581603d6b04d6304c6f04c6e03c6b03c6a03c6703c6604c6304c6206c5f05c5e06c5305c5202b6f02b6b02b6702b6302b5f02b5301b4f01b4d01b4701b4501b4301a6f01a6b01a6701a6301a5f01a5301a4f0ca4e01a4d01a3f01a3b01a3701a330196f0196b01967019630195f019530194f0194d0194701945019430193f0193b01937019330192f0192b01927019230286f028670184f0184d02847028450183f028370182f0182d01827028250181f01817 20 1048575 8 255 11 2047 20 1048575
def cc_55_5 : Nat → List (Nat × Nat) := unpackCursorV4 0x9ff309cb3499f2c96b3494b208e26987f6381c637bb61752697064c6ad59644695f25258b67544474a59f4574e3ee6937876331472e24f27f6321e611f42a1b53f154610e76d08661050360302000030 0x4c6f04c6e03c6b03c6a03c6703c6604c6304c6204b6f02b6b03b6702b6301b4301b4101a6f01a6b01a6701a6301a4f01a4d01a4b01a4901a4701a4501a4301a4101a3f01a3d01a3b01a3701a3501a330196f0196b01967019630194f0494e0194d0193b0193a0193704936019330192f0192b019270192304c6f04c6e03c6b03c6a03c6703c6604c6304c6204b6f04b6e02b6b03b6702b6304b6204a6f01a6b03a6701a6304a4f04a4d01a4b01a4904a4706a4501a4301a4102a3f10a3d01a3b04a3704a3501a330496f0196b03967019630494f0494d0194b0194904947be14501943019410293f0193b04937019330192f0192b019270192302e7e02e7d03d7e03d7a03d7603d7204d6e0bd6d04d6c08d6a05d6905d6808d6608d6508d6404d6205d6104d6003b7a02b7903b7602b7103b6603b6504b5d02b5904b5502b5101a6d01a6901a6501a6101a5d01a5901a5501a510397e019720196d0196901965019610192a019261ad6f04d6e03d6b03d6a03d6703d6605d6304d62bc36f03b6b03b6710b6305b5f04b5d10b5b02b5916b5704b5505b5302b5101a6f01a6b01a6701a6301a5f01a5d01a5b01a5901a5701a5501a5301a5101a3f01a3b01a3701a330196fa616e0196b0196701963019620193f0193b01937019330192f0192b0192a01927019260192303d6ac0562bf36f03b6b03b6710b63bd35d02b510ea6f01a6b03a6701a6306a5d01a4110a3f01a3baf23701a33a516f0196b0396701963bb15d019511093f0193b87137019330192f0192b019270192308d6f03d6b03d6705d6302c6f02c6b02c6702c6302c5f02c5b02c5702c5305b6f04b6e03b6b03b6a03b6703b6608b6304b6205b5f06b5e05b5b05b5705b5306b5201b4f01b4e01b4b01b4a01b4701b4601b4301b4201a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3d01a3b01a3901a3701a3501a3301a310196f0196b01967019630195f0195b01957019530194f0294e0194b0194701943019420193f0293e0193d0192f0192b0192a0192701926019230286f0286b02867028630285f0285b02857028530284f0284b02847028430283f0283d0283b0283702835028330182f0182b01827018230181f0181d0181b01817028150181308d6f03d6b03d6706d6302c6f02c6b02c6702c6302c5f02c5b02c5702c5302b6f08b6e02b6b02b6a02b6703b6602b6302b6202b5f06b5e02b5b02b5702b5302b5201b4f01b4e01b4d08a6f01a6b03a6701a6306a5f01a5b10a5701a5301a4b02a4a01a4902a4702a4601a4301a4102a3702a36b72350896f0196b03967019630695f0195b10957019530294f0294d0194b0294783145019430293f0293d0193b0193902937b913501933019310192f0192b01927019230286f0286b02867028630285f0285b02857028530284f0284b02847028430283f0283d0283b0283702835028330182f0282b02827018230181f0281b028170181304d6f03d6b03d6704d6304c6f04c6e03c6b03c6a03c6703c6604c6304c6204c5f04c5e04c5b04c5704c5306c5202b6f02b6b02b6702b6302b5f02b5b02b5702b5301b4f01b4e01b4d01a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f02a4e01a4d01a3f02a3e01a3b01a3901a3301a3201a310196f0196b01967019630195f0195b01957019530194f0194d0194b01949019470194501943019410193f0193d0193b0193701935019330192f0192b01927019230286f0286b02867028630285f0285b02857028530284f0284d0284b0284702845028430283f0283b02837028330182f0182b01827018230181f0181b018170181304d6f03d6b03d6704d6304c6f02c6b03c6702c6304c5f02c5b04c5702c5301b6f01b6b01b6701b6301b5f01b5b01b5701b5301b4f02b4e01b4d01b4701b4501b4301b4201a6f0ea6e01a6b01a6a01a6703a6601a6301a6201a5f06a5e01a5b01a5701a5301a5201a47b724601a4501a3f01a3e01a3d0196f0196b01967019630195f0195b01957019530194f0194b01947019430193f0193b01937019330192f0192d0192b01929019270192501923019210486f0286b03867028630685f0285b0a857028530284f0284b02847028430183f0183b01837018330182f0182d0182b018270a825018230181f0181b018170181303d6f03d6e01d6b01d6a01d6701d6601d6301d6203c6f03c6b03c6703c6305c5f05c5b05c5905c5705c5305c5101b6f02b6b03b6702b6301b5f01b5d01b5b01b5904b5704b5501b5301b5104b4f02b4b04b4702b4301a6f01a6b01a6701a6301a5f01a5d01a5b01a5901a5701a5501a5301a5101a4f01a4b01a4701a4301a3f01a3b01a3701a330196f0396e0196b0196701963019620195f0495e0195d0194f0194b01947019430193f0193b0193a0193704936019330192f0192b0192a0192701926019230386f0286b03867028630585f0d85d0285b0585705855028530584f0284b05847028430283f0283b02837028330182f0182b01827018230181f0181b018170181303d6f03d6e02d6702d6302d6203c6b03c6306c5b05c5906c5305c5102b6f02b6b02b6702b6302b5f02b5d02b5b02b5702b5502b4f02b4302a6f01a6b03a6701a6302a5f02a5d01a5b08a5708a5506a4f01a4302a3f01a3b02a3701a330396f0196b03967019630d95f0595d0195b019590d9570595501953019510694f019430293f0193b02937019330192f0192b01927019230286f0386e02867028620285f0485e0285d0283f0283a02837028360182f0282a028270a8260181f0281703d6f03d6e04d6d03c6f03c6b03c6703c6304c5f04c5b06c5904c5704c5304c5103b6f02b6b03b6702b6304b5704b5604b5504b4f02b4b04b4702b4303a6f01a6b03a6701a6304a5704a5608a5506a4f01a4b0ba4701a4302a3f01a3b03a3701a330396f0196b03967019630495f0495d0195b0195904957b515501953019510694f0194b0b947019430293f0193b04937019330192f0192b01927019230386f0286b03867028630485f0485d0285b04857b4055028530684f0284b0b847028430283f0283b02837028330182f0282b0a827018230181f0281b0d8170181303d6f03d6b03d6703d6303c6f02c6b03c6701c6304c5f02c5b04c5702c5303b6f03b6e01b6b01b6a01b6701b6601b6301b6205b5f05b5e05b5b05b5705b5305b5202b4f02b4e01b4b01b4a01b4701b4601b4301b4201a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3d01a3b01a3901a3701a3501a3301a310196f0396e0196b0196701963019620195f0195b0195a0195705956019530194f0194b01947019430193f0493e0193d0192f0192b01927019230386f0286b03867028630585f0285b05857028530284f0284b02847028430583f1183d0283b0583705835028330182f0182b01827018230181f0181d0181b01817058150181303d6b03d6302c6f02c6b02c6702c6302c5f02c5303b6f03b6e02b6702b6302b6206b5f05b5e06b5305b5202b4f02b4e02b4b02b4a02b4702b4602b4302b4203a6f01a6b03a6701a6306a5f01a5302a4f01a4b02a4701a4302a3f02a3d01a3b01a3902a3702a3501a3301a310396f0196b03967019630695f019530294f0194b02947019431293f0593d0193b01939129370593501933019310192f0192b01927019230286f0386e02867028620285a0b8560284f028470283f0483e0283d0182f028270181f0281a028171281603d6f03d6b03d6703d6303c6f04c6d02c6b03c6703c6502c6304c5f02c5b04c5702c5303b6f03b6e04b6d04b5f06b5e04b5b04b5704b5304b5202b4f02b4e01b4b01b4a03b4701b4602b4302b4203a6f04a6d01a6b03a6703a6501a6306a5f01a5b0ba5701a5302a4f01a4b03a4701a4302a3f02a3d01a3b01a3903a3702a3501a3301a310396f0196b03967019630695f0195b0b957019530294f0194b04947019430493f0493d0193b0193904937b213501933019310192f0192b01927019230386f0286b03867028630685f0285b0b857028530284f0284b02847028430483f0483d0283b04837b1035028330182f0282b0a827018230181f0281b120170181303e7a04e7204c7f0bc7e03c7b03c7a03c7703c7604c730bc7204c6d04c6c02c6102c6006c5106c5004b7f02b7b03b7702b7304b6d04b6c02b6102b6001b4f01b4e01b4d01a7f01a7b01a7a01a7703a7601a7301a6d01a5101a4f02a4e01a4d01a3f02a3e01a3b01a3901a3301a3201a310197f0197b01977019730196d019610194f0194d0194b01949019470194501943019410193f0193d0193b0193701935019330192f0192d0192b01927019250192304e7f03e7b03e7704e7304d7f04d7e03d7b03d7a03d7703d7604d7304d7204d6f04d6e04d6b0fd6a04d6704d6604d6305d6204c7f04c7e03c7b03c7a03c7703c7604c7304c7206c6f06c6e0dc6b0dc6706c6306c6201c5f01c5e01c5d01c5c04b7f02b7b03b7702b7304b6f02b6b04b6702b6301b5f01b5e01b5d01b4f01b4e01b4d01b4c01b4b01b4901b4701b4501b4301b4201b4101b4001a7f01a7b01a7701a7301a6f01a6b01a6701a6301a5f02a5e01a5d01a4f01a4d01a4b01a4901a4701a4501a4301a4101a3f02a3e01a3b01a3901a3301a3201a310197f0497e0197b0197701973019720196f0196b01967019630195b0195a01959019580195704956019550495401953019510194704946019450193f0193d0193b0193a01937049360193504934019330192f0192b0192a0192701926019230487f0287b03877028730686f0286b0d867028630485f0d85d0285b02859048570485502853028510d84f0d84d0284b0d8470d845028430283f0283b02837028330182f0182b01827018230181f0181b018170181303d6b04d6304c6f04c6e03c6b03c6a03c6703c6604c6304c6205c5f05c5e05c5305c5202b6f02b6b02b6702b6302b5f02b5302b4f02b4d01b4b01b4901b4701b4501b4301b4101a6f01a6b01a6701a6301a5f01a5301a4f01a4d01a4b01a4901a4701a4501a4301a4101a3f01a3b01a3701a330196f0196b01967019630195f019530194f0194d0194b01947019450193f0193b01937019330192f0192b01927019230286f028670284f0584e0284d0283f018370182f018270181f0181a018170181604d6f03d6b03d6704d6304c6f04c6e03c6b03c6a03c6703c6604c6304c6205c5f06c5e05c5b05c5705c5306c5204b6f02b6b03b6702b6304b5f02b5b04b5702b5301b4f01b4d01b4b01b4901b4701b4501b4301b4101a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4d01a4b01a4901a4701a4501a4301a4101a3f01a3b01a3701a330196f0496e0196b0196701963019620195f0195b01957019530194704946019450193f0193b0193a0193704936019330192f0192b0192a0192701926019230486f0286b03867028630585f0285b4c057028530584f1104d0284b0d847ad045028430283f0283b02837028330182f0182b01827018230181f0181b018170181303e7b04e7304d7f04d7e03d7b03d7a03d7703d7604d7304d7204d6f04d6e04d6306d6204c7f04c7e03c7b03c7a03c7703c7604c7304c7206c6f06c6e06c6306c6202b7f02b7b02b7702b7302b6f02b6301b5f01b5e01b5d01b4f01b4d02b4701b4502b4302b4104a7f01a7b03a7701a7306a6f01a6302a5f02a5e02a5d02a4f02a4d02a4702a4501a4301a4102a3f02a3e01a3b01a3901a3302a3201a310497f0197b03977019730696f019630495f0d95d0195b01959049570495501953019510d94f0d94d0194b019490d9470d94501943019410293f0293d0193b0293704935019330192f0192b01927019230287f0487e02877028720285a02858028570485602855048540284704846028450283f0283a02837028360182f0282a028270a8260181f0281703d6b04d6304c6f04c6e03c6b03c6a03c6703c6604c6304c6205c5f05c5e05c5305c5202b6f02b6b02b6702b6302b5f02b5301b4f01b4d01b4701b4501b4301a6f01a6b01a6701a6301a5f01a5301a4f01a4d01a4701a4501a4301a3f01a3b01a3701a330196f0196b01967019630195f019530194f0594e0194d0193f0193b01937019330192f0192b01927019230286f028670184f0184d02847028450183f028370182f018270181f0181d018170281503d6b04d6304c6f04c6e03c6b03c6a03c6703c6604c6304c6206c5f06c5e06c5306c5202b6f02b6b02b6702b6302b5f02b5301b4f01b4d02b4701b4502b4304a6f01a6b03a6701a6306a5f01a5302a4f02a4d02a4702a4501a4302a3f01a3b02a3701a330496f0196b03967019630695f019530d94f1114d0194b019490d947aa14501943019410293f0193b02937019330192f0192b01927019230286f0486e02867028620284704846028450283f0283a02837028360182f0282a028270a8260181f0281704d6f03d6b03d6704d6304c6fb346e03c6b03c6a03c6703c6604c63b046204c5f06c5e0fc5b04c5706c5306c5204b6f02b6b03b6702b6304b5f02b5b04b5702b5301b4f01b4e01b4d04a6f01a6b03a6701a6306a5f01a5baf25701a5302a4f02a4e02a4d02a3f02a3e01a3b01a3901a3302a3201a310496f0196b03967019630695f0195b9515701953ae14fac14d0194b01949049476814501943019410293f9313d0193b0493782135019330192f0192b01927019230486f0286b03867028630685f0285b4b05702853ab04fa904d0284b0484722045028430283f0283b02837028330182f0282b0a827018230181f0281b100170181308d6f03d6b03d6706d6302c6f02c6b02c6702c6302c5f02c5b02c5702c5301b6f01b6b01b6701b6301b5f01b5b01b5701b5301b4f01b4d01b4b01b4a01b4702b4601b4501a6f08a6e01a6b01a6a01a6703a6601a6301a6201a5f06a5e01a5b01a5701a5301a5201a4f02a4e01a4d01a3f01a3e01a3d0196f0196b01967019630195f0195b01957019530194f0194b01947019430193f0193b01937019330192f0192d0192b01929019270192501923019210286f0286b02867028630285f0285b02857028530284f0284b02847028430183f0183b01837018330182f0182d0182b0182702825018230181f0181b018170181301d6f01d6e01d6d03c6f05c6d03c6b03c6a03c6703c6603c6503c5b03c5a03a6f03a6b03a6703a6304a5f04a5b04a5704a5304a4f05a4b04a4705a430196f0196b01967019630195f0195d0195b0195701955019530194f0194b01947019430192f0192b019270192301e7f01e7e01e7d03d7a03d7209d6a09d6804d6204d6003b7f03b7b03b7703b7304b6f0bb6d04b6b02b6904b6709b6504b6302b6104b5d02b5101a7f01a7b01a7701a7301a6f01a6d01a6b01a6901a6701a6501a6301a6101a5d01a4101a3f01a3b01a3701a330197b0197a01979019770397601973019710196703966019650195da615c01951019500193f0193b01937019330192f0192b019270192301d6f01d6e01d6d03c6f03c6b03c6703c6304c5f06c5b06c5909c5704c5306c5103b6f03b6b03b6703b6304b5f8c35d04b5b02b5904b5709b5504b5302b5104b4f08b4b04b4706b4303a6f01a6b03a6701a6304a5f6a25d01a5b01a5909a5709a5501a5301a5106a4f01a4ba524701a4308a3f01a3b04a3701a330196b0396a01969039670396601963019610395703956039550694f0194b09947019430893f0193b04937019330192f0192b01927019230386f0386b03867038630485f0e05d0785b0985709855048530684f0784b49047068430883f0483b04837078330182f0782b21027018230181f0781b078170181303d6f03d6b03d6703d6303c6f03c6e02c6b02c6a03c6702c6603c6303c6204c5f04c5e04c5b04c5704c5306c5203b6f03b6e02b6b03b6702b6303b6204b5f02b5b08b5a04b5704b5602b5301b4f01b4e01b4d01a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4d01a4b01a4901a4701a4501a4301a4101a3f01a3d01a3b01a3701a3501a330196f0196b01967019630195f0195b01957019530194f0194d0194b01949019470194501943019410193f0193b019390193701933019310192f0192b01927019230386f0286b03867028630685f0285b07857028530484f0784d0284b0484704845028430283f0783d0283b0283704835028330182f0182b01827018230181f0181b018170181303d6f03d6b03d6703d6303c6f03c6b03c6703c6304c5f08c5b04c5706c5301b6f01b6b01b6701b6301b5f01b5b01b5701b5301b4f01b4b01b4701b4301a6f01a6d01a6b01a6a01a6703a6601a6501a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3b01a3701a330196f0396e0196d0195f0695e0195b0195701953019520194f0294e0194b0194a01947a314601943019420193f0193e0193b0193a019370193601933019320192f0192e0192d0386f0386b03867038630685f0785b07857068530784f0484b04847078430183f0183b01837018330182f0182b01827018230181f0181d0181b01817078150181304c6f04c6e03c6b03c6a03c6703c6604c6304c6204b6f04b6e02b6b03b6702b6304b6201a6f01a6b01a6701a6301a4f01a4d01a4b01a4901a4701a4501a4301a4101a3f01a3d01a3b01a3701a3501a330196f0196b01967019630194f0194d0194b01949019470194501943019410193f0193b019390193701933019310192f0192b019270192309c6f03c6b03c6709c6301b6f01b6b01b6701b6301b4f01b4b01b4701b4301a6f01a6b01a6701a6301a5d01a4f01a4b01a4701a4301a3f01a3b01a3701a330996e039660294ea11460193e019360192e01c6b01c6a03b6f03b6b03b6703b6304b4f04b4d04b4b02b4904b4704b4504b4302b4101a6f03a6e01a6b01a6301a6201a4f04a4e01a4d01a3f01a3b01a3a01a3704a3601a330196f0196b01967019630194f0194d0194b01949019470194501943019410193f0193b01937019330192f0192b0192701923 20 1048575 8 255 11 2047 20 1048575
def cc_55_6 : Nat → List (Nat × Nat) := unpackCursorV4 0x2c820a5b8e64658b7b5fb65713b593635f0b96332530b9333248c81132038b84ac6d1ef8460b61428038b007ec8003f 0x3d6e03c6a03b6f03b6b03b6703b6302b5915b5503a6f03a6b03a6703a6301a5915a5508a3f04a3b04a3708a330396f0396b039670396301959159550893f0493b04937089330e92f0992b731270992302d6f02d6e02d6d03c6f03c6b03c6703c6304c5f06c5b06c5908c5704c5306c5102b6b03b6a02b6903b6703b6602b6302b6103b5703b5603b5504b4f06b4e02b4b04b4702b4306b4203a6f03a6b03a6703a6304a5fb325d08a5b01a5908a5708a5504a5301a5106a4f0ea4bbf24706a4302a3f04a3b04a3702a330396f0396b03967039630495f8c15d0895b01959089570895504953019510694f0994b9d147069430293f0493b04937029330e92f0992b72127099230386f0286b03867028630485f2d05d0285b0885708855028530684f0284b56047028430283f0283b02837028330e82f0282b26027028230981f0281b140170281303d6f03d6b03d6703d6302c6f02c6b02c6701c6302c5f02c5b02c5702c5303b6f03b6e01b6b01b6a01b6701b6601b6301b6205b5f05b5e05b5b05b5705b5305b5202b4f02b4e01b4b01b4a01b4701b4601b4301b4201a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3f01a3d01a3b01a3901a3701a3501a3301a310196f0196b01967019630195f0195b01957019530194f0194b01947019430193705936019350192f0192b0192a0192701926019230286f0286b02867028630285f0285b02857028530284f0284b02847028430283f0283d0283b0283702835028330182f0182b01827018230181f0181b018170181303d6f03d6b03d6703d6302c6f02c6b02c6702c6302c5f02c5b02c5702c5303b6f03b6e01b6b01b6a03b6701b6603b6303b6206b5f06b5e10b5b0cb5706b5306b5202b4f02b4e01b4b01b4a02b4701b4602b4302b4203a6f03a6e01a6b03a6701a6303a6206a5f01a5b0ea5a0ca5710a5601a5302a4f02a4e01a4b02a4701a4302a4202a3f02a3e02a3d0396f0196b03967019630695f0195b10957019530294f0194b02947019431793fd113d0193b019390c9377113501933019310192f0e92d0192b0192770125019230286f0286b02867028630285f0285b02857028530284f0284b02847028430283f0283d0283b0283702835028330182f0282d0282b0282702825018230181f0281b028170181303d6f03d6b03d6703d6302c6f02c6b02c6701c6302c5f02c5b02c5702c5303b6f03b6e01b6b01b6a01b6701b6601b6301b6205b5f05b5e0cb5b0cb5705b5305b5202b4f02b4e01b4b01b4a01b4701b4601b4301b4201a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4b01a4701a4301a3705a3601a350196f0196b01967019630195f0195b01957019530194f0194b01947019430193f0193d0193b01939019370193501933019310192f0192d0192b0192701925019230286f0286b02867028630285f0285b02857028530284f0284b02847028430283f0283d0283b0283702835028330182f0182b01827018230181f0181b018170181303d6f03d6b03d6703d6302c6f02c6b02c6702c6302c5f02c5b02c5702c5303b6f03b6e01b6b01b6a03b6701b6603b6303b6205b5f06b5e05b5b05b5705b5306b5202b4f02b4e01b4b01b4a02b4701b4602b4302b4203a6f01a6b03a6701a6305a5f01a5b10a5701a5302a4f01a4b02a4701a4311a3fcf23d01a3b01a3905a377123501a3301a310396f0396e0196b0396701963039620595f0195b0995a0595710956019530294f0294e0194b0294701943029420293f0293e0293d0192f0192b0992a019276f126019230286f0286b02867028630285f0285b02857028530284f0284b02847028430283f0283d0283b0283702835028330182f0282b02827018230181f0281d0281b02817028150181303d6f03d6b03d6703d6302c6f02c6d02c6b02c6a02c6703c6602c6502c5f06c5e02c5b02c5702c5302c5202b6f03b6e02b6d02b5f06b5e02b5b02b5702b5302b5202b4f02b4e02b4d03a6f03a6b03a6703a6306a5f0ea5b10a5706a5302a4f02a4b02a4702a4302a3f02a3d02a3b01a3902a37d023502a3301a310396f0396b03967039630695f0995b10957069530294f0294b02947029430293f0293d0293b0193902937ce13502933019310e92f0992b6e127099230286f0286b02867028630285f0285b02857028530284f0284b02847028430283f0283d0283b0283702835028330282f0282b02827028230281f0281b028170281302c6f02c6b02c6702c6305b6f04b6e03b6b03b6a03b6703b6605b6304b6202b4f02b4e01b4b01b4a01b4701b4601b4301b4201a6f01a6b01a6701a6301a4f01a4b01a4701a4301a3b01a390196f0196b01967019630194f0194b01947019430193705936019350192b0192a01927019260192302c6f02c6b02c6702c6308b6f04b6e03b6b03b6a03b6703b6608b6304b6202b4f02b4e01b4b01b4a02b4701b4602b4302b4208a6f01a6b03a6701a6302a4f02a4e01a4b02a4701a4302a420896f0196b03967019630294f0194b02947019430f93fcc13d0193b019390c9370f93501933019310192f0192b019270192302c6f02c6b02c6702c6308b6f04b6e03b6b03b6a03b6703b6608b6304b6202b4f02b4e01b4b01b4a01b4701b4601b4301b4201a6f01a6b01a6701a6301a4f01a4b01a4701a4301a3705a3601a350196f0196b01967019630194f0194b01947019430193b019390192f0192d01927019250192302c6f02c6b02c6702c6305b6f04b6e03b6b03b6a03b6703b6608b6304b6202b4f02b4e01b4b01b4a02b4701b4602b4302b4208a6f01a6b03a6701a6302a4f01a4b02a4701a430fa3fca23d01a3b01a3905a370fa3501a3301a310596f0196b03967019630294f0294e0194b0294701943029420192f0192b019270192302c6f02c6b02c6702c6302c5d08b6e03b6602b4e08a6f03a6b03a6708a6302a4f02a4b02a4702a4301a39cb2350896f0396b03967089630294f0294b029470294301939c91357b12f7712b6d1276612303d6a10d6204b6f02b6b03b6702b6306b5d02b4104a6f03a6b03a6704a6310a5d01a5102a3f04a3b04a3702a330496f0396b03967049631095d019510293f0493b04937029337a12f7612b6c1276512301d6f01d6e01d6d03c6f03c6b03c6703c6304c5f06c5b06c590ec5704c5306c5103b6f03b6b03b6703b6304b5fb335d04b5b02b5904b570eb5504b5302b5104b4f08b4b04b4706b4301a6b03a6a01a6903a6703a6601a6301a6103a5703a5603a5506a4f01a4b0ea4701a4308a3f01a3b04a3701a330396f0196b03967019630495f6a15d0195b019590e9570e95501953019510694f0194b9a147019430893f0193b04937019330192f0192b01927019230386f0386b03867038630485f2405d0a85b0e8570e855048530684f0a84b52047068430883f0483b04837088330182f0a82b0a827018230181f0a81b130170181303d6f03d6b03d6703d6303c6f03c6e02c6b02c6a03c6702c6603c6303c6204c5f04c5e04c5b04c5704c5306c5203b6f03b6e02b6b03b6702b6303b6204b5f02b5b08b5a04b5704b5602b5301b4f01b4e01b4d01a6f01a6b01a6701a6301a5f01a5b01a5701a5301a4f01a4d01a4b01a4901a4701a4501a4301a4101a3f01a3b01a3901a3701a3301a310196f0196b01967019630195f0195b01957019530194f0194d0194b01949019470194501943019410193f0193d0193b0193701935019330192f0192b01927019230386f0286b03867028630685f0285b0a857028530484f0a84d0284b0484704845028430283f0883d0283b0283704835028330182f0182b01827018230181f0181b018170181303d6f03d6b03d6703d6303c6f03c6b03c6703c6304c5f08c5b04c5706c5301b6f01b6d01b6b01b6a01b6703b6601b6501b5f01b5b01b5701b5301b4f01b4b01b4701b4301a6f03a6e01a6d01a5f06a5e01a5b01a5701a5301a5201a4f02a4e01a4b01a4a01a47c524601a4301a4201a3f01a3e01a3d0196f0196b01967019630195f0195b01957019530194f0194b01947019430193f0193b01937019330192f0192d0192b01929019270192501923019210386f0386b03867038630685f0a85b0a857068530884f0484b04847088430183f0183b01837018330182f0182d0182b018270a825018230181f0181b018170181304c6f04c6e03c6b03c6a03c6703c6604c6304c6204b6f04b6e02b6b03b6702b6304b6201a6f01a6b01a6701a6301a4f01a4d01a4b01a4901a4701a4501a4301a4101a3f01a3b01a3901a3701a3301a310196f0196b01967019630194f0194d0194b01949019470194501943019410193f0193d0193b0193701935019330192f0192b01927019230ec6f03c6b03c670ec6301b6f01b6b01b6701b6301b5d01b4f01b4b01b4701b430ea6e03a6602a4ec324601a3e0196f0196b01967019630194f0194b01947019430193f0193b0193701933019290192501c6b01c6a03b6f03b6b03b6703b6304b4f04b4d04b4b02b4904b4704b4504b4302b4101a6f01a6b01a6701a6301a4f01a4d01a4b01a4901a4701a4501a4301a4101a3f01a3b01a3701a330196f0396e0196b01963019620194f0494e0194d0193f0193b0193a0193704936019330192f0192b019270192303b6f03b6b03b6703b6304b4f04b4d04b4b02b4904b4704b4504b4302b4103a6f04a6d01a6b03a6703a6501a6304a4f04a4d01a4b01a4903a4703a4501a4301a4104a3f01a3b04a3701a330396f0196b03967019630494f0494d0194b0194904947c114501943019410493f0193b04937019330192f0192b019270192302e7f02e7e02e7d03d7a03d7208d6a08d6804d6204d6002b7b03b7a02b7903b7703b7602b7302b7103b6703b6603b6504b5d04b5c02b5102b5003a7f01a7b03a7701a7304a6f0ba6d01a6b01a6908a6708a6501a6301a6106a5d01a4102a3f01a3b04a3701a330397f0197b03977019730496f0b96d0196b0196908967089650196301961bc15d019510293f0193b04937019330192f0192b0192701923 18 262143 7 127 11 2047 20 1048575
def cur_55 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (cc_55_6 (Nat.sub p 192)) (cc_55_5 (Nat.sub p 160)) (Nat.blt p 192)) (Bool.rec (cc_55_4 (Nat.sub p 128)) (cc_55_3 (Nat.sub p 96)) (Nat.blt p 128)) (Nat.blt p 160)) (Bool.rec (Bool.rec (cc_55_2 (Nat.sub p 64)) (cc_55_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_55_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def f_55 : Nat → Nat × Nat := unpackForestF 0x18be02d7f449ee7235cf47b9c4d405a9e613dc946b948f7249a80b4b0168e0297f152300a53c348c0292f04a2ddd62bb6df7c516edaede36fbb2ba0291ee49a80a3fb748c028eed0aada055a98dd624d6c41ad4c62a94af5253eb422d494da909f54516a42680a37014674c57295238095fa328c0254e84a30094b9f48b2b58a55b7ce245956bb2a9be61b7cc26e954bb2d182551b809479248b248d4049fc8146012771a956342abf46e8a46b140d5fa31444607e4aefc93e141abf24d7e47afc8d5f8abbf04f7f48afc134049b80933798b6f315de5230092f758b6eb15dd4a30092b68aded11bdbda237a446f288d118da22db44576b0aad0db9a426b43460124ebf16d7e2bb1b4b6368ebe8d17ca62f9465f2880248d74938085f010a60212d6122ac1453bac476dbd5122aa1453b6ba769bd3db7a7a6e4f28a7697532302614d3b46e94974ecb7a236f444de88915111ba216e3b2ba811810136a024d3b26e799c8f23f9e36c3b24e0211ce4a6992353749a644d4cda219a44332886449c041f8083b2e4aa5c554b237161270106e020cca5230082f01056351bc94aa8d36e2329a34d1868b78fd721f6b83451c6db78d86f1b06e341580413808231728c0207c040d81c6f036de235c8452e01b470f4aa069b8352681a460a8de14d8c0d1b0236f044de088dc15b782126030ac0205c04098003f 8 11
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV4 fullMask g_55 ep_55 212 bds_55 (dagTraceF fullMask rootStock 11 f_55) (cur_55 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_0 : treeBlockF 0 32 (dagCheckNodeV4 fullMask g_55 ep_55 bds_55 212 (dagTraceF fullMask rootStock 11 f_55) cur_55) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_1 : treeBlockF 32 64 (dagCheckNodeV4 fullMask g_55 ep_55 bds_55 212 (dagTraceF fullMask rootStock 11 f_55) cur_55) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_2 : treeBlockF 64 96 (dagCheckNodeV4 fullMask g_55 ep_55 bds_55 212 (dagTraceF fullMask rootStock 11 f_55) cur_55) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_3 : treeBlockF 96 128 (dagCheckNodeV4 fullMask g_55 ep_55 bds_55 212 (dagTraceF fullMask rootStock 11 f_55) cur_55) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_4 : treeBlockF 128 160 (dagCheckNodeV4 fullMask g_55 ep_55 bds_55 212 (dagTraceF fullMask rootStock 11 f_55) cur_55) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_5 : treeBlockF 160 192 (dagCheckNodeV4 fullMask g_55 ep_55 bds_55 212 (dagTraceF fullMask rootStock 11 f_55) cur_55) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_6 : treeBlockF 192 212 (dagCheckNodeV4 fullMask g_55 ep_55 bds_55 212 (dagTraceF fullMask rootStock 11 f_55) cur_55) = true := by decide +kernel
theorem nj_55_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 fullMask g_55 ep_55 bds_55 212 (dagTraceF fullMask rootStock 11 f_55) cur_55) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_55_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_55_1 h1 h2)
theorem nj_55_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeV4 fullMask g_55 ep_55 bds_55 212 (dagTraceF fullMask rootStock 11 f_55) cur_55) i = true := block_join nj_55_1 (fun _ h1 h2 => treeBlockF_at nb_55_2 h1 h2)
theorem nj_55_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeV4 fullMask g_55 ep_55 bds_55 212 (dagTraceF fullMask rootStock 11 f_55) cur_55) i = true := block_join nj_55_2 (fun _ h1 h2 => treeBlockF_at nb_55_3 h1 h2)
theorem nj_55_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeV4 fullMask g_55 ep_55 bds_55 212 (dagTraceF fullMask rootStock 11 f_55) cur_55) i = true := block_join nj_55_3 (fun _ h1 h2 => treeBlockF_at nb_55_4 h1 h2)
theorem nj_55_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeV4 fullMask g_55 ep_55 bds_55 212 (dagTraceF fullMask rootStock 11 f_55) cur_55) i = true := block_join nj_55_4 (fun _ h1 h2 => treeBlockF_at nb_55_5 h1 h2)
theorem nj_55_6 : ∀ i, 0 ≤ i → i < 212 → (dagCheckNodeV4 fullMask g_55 ep_55 bds_55 212 (dagTraceF fullMask rootStock 11 f_55) cur_55) i = true := block_join nj_55_5 (fun _ h1 h2 => treeBlockF_at nb_55_6 h1 h2)
theorem nc_55 : ∀ i, 0 ≤ i → i < 212 → (dagCheckNodeV4 fullMask g_55 ep_55 bds_55 212 (dagTraceF fullMask rootStock 11 f_55) cur_55) i = true := nj_55_6
theorem lb_55 : LowerBin fullMask rootStock g_55 12 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_55 kn_55 sub_55 gl_55 rc_55 nc_55

def wg : List Gate := [⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.or, [1, 8]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [5, 11]⟩, ⟨GateOp.and, [7, 12]⟩, ⟨GateOp.and, [10, 13]⟩, ⟨GateOp.or, [10, 13]⟩, ⟨GateOp.or, [14, 15]⟩, ⟨GateOp.and, [16, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276676744 * 2 ^ 32 + 3903367168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276676744 * 2 ^ 32 + 3903367168)) (13 - 1) := by
  rw [show canon fullMask (4276676744 * 2 ^ 32 + 3903367168) = g_55 by decide]
  exact lb_55

end PEqualNP.Outside.L_meta_49125

theorem PEqualNP.Outside.L_meta_49125 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676744 * 2 ^ 32 + 3903367168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676744 * 2 ^ 32 + 3903367168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_49125.table2_from_lowerBin (4276676744 * 2 ^ 32 + 3903367168) 13 PEqualNP.Outside.L_meta_49125.root_lb PEqualNP.Outside.L_meta_49125.wg 18 rfl PEqualNP.Outside.L_meta_49125.wfits PEqualNP.Outside.L_meta_49125.weval
