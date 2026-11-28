import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_49345

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

def m_1 : Nat := 0x3030303000000000
def s_1 : List Nat := [0x1010101000000000, 0x30003000000000, 0x303000000000]
def g_1 : Nat := 0x10103000000000
def ep_1 : Nat := 0x1020000000000010002000000000000000000000000000000000000000000010100000000000
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

def m_2 : Nat := 0x5050505000000000
def s_2 : List Nat := [0x1010101000000000, 0x50005000000000, 0x505000000000]
def g_2 : Nat := 0x10105000000000
def ep_2 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000000000000000000
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

def m_3 : Nat := 0x5500550000000000
def s_3 : List Nat := [0x1100110000000000, 0x500050000000000, 0x550000000000]
def g_3 : Nat := 0x100150000000000
def ep_3 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000000000000000000
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

def m_4 : Nat := 0x3300330000000000
def s_4 : List Nat := [0x1100110000000000, 0x300030000000000, 0x330000000000]
def g_4 : Nat := 0x100130000000000
def ep_4 : Nat := 0x1200000000000000000000000000010002000000000000000000000000000100100000000000
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

def m_5 : Nat := 0xf000f0000000000
def s_5 : List Nat := [0x500050000000000, 0x300030000000000, 0xf0000000000]
def g_5 : Nat := 0x100070000000000
def ep_5 : Nat := 0x600000000000000000000000000000000000000000001000200000000000100040000000000
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

def m_7 : Nat := 0x2222222200000000
def s_7 : List Nat := [0x202020200000000, 0x22002200000000, 0x222200000000]
def g_7 : Nat := 0x2022200000000
def ep_7 : Nat := 0x220000000000002002000000000000202000000000000000000000000000000000000000000
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

def m_8 : Nat := 0xf000f000000000
def s_8 : List Nat := [0x50005000000000, 0x30003000000000, 0xf000000000]
def g_8 : Nat := 0x10007000000000
def ep_8 : Nat := 0x60000000000000000000000000000000000000000000100020000000000010004000000000
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

def m_9 : Nat := 0xcccc0000
def s_9 : List Nat := [0x44440000, 0xc0c0000, 0xcc0000]
def g_9 : Nat := 0x44c0000
def ep_9 : Nat := 0x480000000000000408000000000000000000000000000004400000
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

def m_12 : Nat := 0x4040404040404040
def s_12 : List Nat := [0x40004000400040, 0x404000004040, 0x40404040]
def g_12 : Nat := 0x4000404040
def ep_12 : Nat := 0x40400000000040000040000000004000400000000000000000000000000000000000000000000000000000
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

def m_13 : Nat := 0xff000000000000
def s_13 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_13 : Nat := 0x17000000000000
def ep_13 : Nat := 0x600000000000000120000000000000014000000000000
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

def m_14 : Nat := 0xf0f000000000000
def s_14 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_14 : Nat := 0x107000000000000
def ep_14 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
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

def m_15 : Nat := 0x4400440044004400
def s_15 : List Nat := [0x400040004000400, 0x440000004400, 0x44004400]
def g_15 : Nat := 0x40004004400
def ep_15 : Nat := 0x400400000000400000040000000000000000000000004000400000000000000000000000000000000000000
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

def m_16 : Nat := 0xf0000000f000000
def s_16 : List Nat := [0x500000005000000, 0x300000003000000, 0xf000000]
def g_16 : Nat := 0x100000007000000
def ep_16 : Nat := 0x600000000000000000000000000000000000000000000000000000001000000020000000100000004000000
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

def m_17 : Nat := 0xf0f000000000
def s_17 : List Nat := [0x505000000000, 0x303000000000, 0xf000000000]
def g_17 : Nat := 0x107000000000
def ep_17 : Nat := 0x6000000000000000000000000000001020000000000000104000000000
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

def m_18 : Nat := 0x30303030
def s_18 : List Nat := [0x10101010, 0x300030, 0x3030]
def g_18 : Nat := 0x101030
def ep_18 : Nat := 0x10200000000000100020000000000000000000000000000000000000000000101000
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

def m_19 : Nat := 0xcc000000cc0000
def s_19 : List Nat := [0x44000000440000, 0xc0000000c0000, 0xcc0000]
def g_19 : Nat := 0x40000004c0000
def ep_19 : Nat := 0x48000000000000000000000000000000000000000400000008000000000000000000000004000000400000
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

def m_20 : Nat := 0xff0000000000
def s_20 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_20 : Nat := 0x170000000000
def ep_20 : Nat := 0x6000000000000001200000000000000140000000000
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

def m_21 : Nat := 0x4444000044440000
def s_21 : List Nat := [0x404000004040000, 0x44000000440000, 0x44440000]
def g_21 : Nat := 0x4000004440000
def ep_21 : Nat := 0x440000000000000000000000004000000400000000400000400000000000000000000000000000000000000
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

def m_22 : Nat := 0xa0a00000a0a0000
def s_22 : List Nat := [0x202000002020000, 0xa0000000a0000, 0xa0a0000]
def g_22 : Nat := 0x20000020a0000
def ep_22 : Nat := 0x208000000000000000000000002000000080000000000000000000000020000020000000000000000000000
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

def m_23 : Nat := 0xc0c00000c0c0000
def s_23 : List Nat := [0x404000004040000, 0xc0000000c0000, 0xc0c0000]
def g_23 : Nat := 0x40000040c0000
def ep_23 : Nat := 0x408000000000000000000000004000000080000000000000000000000000000000000000004000004000000
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

def m_24 : Nat := 0xff00ff0000000000
def s_24 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_24 : Nat := 0x100170000000000
def ep_24 : Nat := 0x1600000000000000000000000000010006000000000001001200000000000100140000000000
theorem epk_24 : ep_24 = edgePack m_24 g_24 := by decide +kernel
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5), (m_20, s_20, 4, g_20), (m_3, s_3, 4, g_3), (m_4, s_4, 4, g_4)]
theorem kn_24 : KnownBin bds_24 := by
  intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_5
  · exact lb_20
  · exact lb_3
  · exact lb_4
theorem sub_24 : ∀ b ∈ bds_24, m_24 &&& b.1 = b.1 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_24 : ∀ b ∈ bds_24, canon b.1 g_24 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_24_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_24_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_24 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_24_1 (Nat.sub p 32)) (cc_24_0 p) (Nat.blt p 32)
def f_24 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV4 m_24 g_24 ep_24 43 bds_24 (dagTraceF m_24 s_24 6 f_24) (cur_24 0) s_24 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_24_0 : treeBlockF 0 32 (dagCheckNodeV4 m_24 g_24 ep_24 bds_24 43 (dagTraceF m_24 s_24 6 f_24) cur_24) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_24_1 : treeBlockF 32 43 (dagCheckNodeV4 m_24 g_24 ep_24 bds_24 43 (dagTraceF m_24 s_24 6 f_24) cur_24) = true := by decide +kernel
theorem nj_24_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_24 g_24 ep_24 bds_24 43 (dagTraceF m_24 s_24 6 f_24) cur_24) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_24_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_24_1 h1 h2)
theorem nc_24 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_24 g_24 ep_24 bds_24 43 (dagTraceF m_24 s_24 6 f_24) cur_24) i = true := nj_24_1
theorem lb_24 : LowerBin m_24 s_24 g_24 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_24 kn_24 sub_24 gl_24 rc_24 nc_24

def m_25 : Nat := 0xffff000000000000
def s_25 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_25 : Nat := 0x117000000000000
def ep_25 : Nat := 0x16000000000000010600000000000001120000000000000114000000000000
theorem epk_25 : ep_25 = edgePack m_25 g_25 := by decide +kernel
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14), (m_13, s_13, 4, g_13), (m_11, s_11, 4, g_11), (m_10, s_10, 4, g_10)]
theorem kn_25 : KnownBin bds_25 := by
  intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_14
  · exact lb_13
  · exact lb_11
  · exact lb_10
theorem sub_25 : ∀ b ∈ bds_25, m_25 &&& b.1 = b.1 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_25 : ∀ b ∈ bds_25, canon b.1 g_25 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_25_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_25_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_25 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_25_1 (Nat.sub p 32)) (cc_25_0 p) (Nat.blt p 32)
def f_25 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV4 m_25 g_25 ep_25 43 bds_25 (dagTraceF m_25 s_25 6 f_25) (cur_25 0) s_25 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_0 : treeBlockF 0 32 (dagCheckNodeV4 m_25 g_25 ep_25 bds_25 43 (dagTraceF m_25 s_25 6 f_25) cur_25) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_1 : treeBlockF 32 43 (dagCheckNodeV4 m_25 g_25 ep_25 bds_25 43 (dagTraceF m_25 s_25 6 f_25) cur_25) = true := by decide +kernel
theorem nj_25_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_25 g_25 ep_25 bds_25 43 (dagTraceF m_25 s_25 6 f_25) cur_25) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_25_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_25_1 h1 h2)
theorem nc_25 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_25 g_25 ep_25 bds_25 43 (dagTraceF m_25 s_25 6 f_25) cur_25) i = true := nj_25_1
theorem lb_25 : LowerBin m_25 s_25 g_25 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_25 kn_25 sub_25 gl_25 rc_25 nc_25

def m_26 : Nat := 0xffff00000000
def s_26 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_26 : Nat := 0x177700000000
def ep_26 : Nat := 0x6000000000000006000000000000001222000000000000144400000000
theorem epk_26 : ep_26 = edgePack m_26 g_26 := by decide +kernel
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 4, g_17)]
theorem kn_26 : KnownBin bds_26 := by
  intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_17
theorem sub_26 : ∀ b ∈ bds_26, m_26 &&& b.1 = b.1 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_26 : ∀ b ∈ bds_26, canon b.1 g_26 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_26 : Nat → List (Nat × Nat) := fun _ => []
def f_26 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV4 m_26 g_26 ep_26 0 bds_26 (dagTraceF m_26 s_26 4 f_26) (cur_26 0) s_26 4 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_26 g_26 ep_26 bds_26 0 (dagTraceF m_26 s_26 4 f_26) cur_26 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_26 : LowerBin m_26 s_26 g_26 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_26 kn_26 sub_26 gl_26 rc_26 nc_26

def m_27 : Nat := 0xf0f0f0f000000000
def s_27 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_27 : Nat := 0x10107000000000
def ep_27 : Nat := 0x1060000000000010006000000000000000000000000000101020000000000010104000000000
theorem epk_27 : ep_27 = edgePack m_27 g_27 := by decide +kernel
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8), (m_17, s_17, 4, g_17), (m_2, s_2, 4, g_2), (m_1, s_1, 4, g_1)]
theorem kn_27 : KnownBin bds_27 := by
  intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_8
  · exact lb_17
  · exact lb_2
  · exact lb_1
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

def m_28 : Nat := 0xcccccccc00000000
def s_28 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_28 : Nat := 0x4044400000000
def ep_28 : Nat := 0x440000000000004004000000000000404000000000000000000000000000004044400000000
theorem epk_28 : ep_28 = edgePack m_28 g_28 := by decide +kernel
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
theorem kn_28 : KnownBin bds_28 := by
  intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_6
theorem sub_28 : ∀ b ∈ bds_28, m_28 &&& b.1 = b.1 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_28 : ∀ b ∈ bds_28, canon b.1 g_28 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_28 : Nat → List (Nat × Nat) := fun _ => []
def f_28 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV4 m_28 g_28 ep_28 0 bds_28 (dagTraceF m_28 s_28 4 f_28) (cur_28 0) s_28 4 = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_28 g_28 ep_28 bds_28 0 (dagTraceF m_28 s_28 4 f_28) cur_28 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_28 : LowerBin m_28 s_28 g_28 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_28 kn_28 sub_28 gl_28 rc_28 nc_28

def m_29 : Nat := 0x3333333300000000
def s_29 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_29 : Nat := 0x113133300000000
def ep_29 : Nat := 0x1220000000000012002000000000010202000000000000000000000000000110100000000000
theorem epk_29 : ep_29 = edgePack m_29 g_29 := by decide +kernel
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4), (m_10, s_10, 4, g_10), (m_1, s_1, 4, g_1), (m_7, s_7, 4, g_7)]
theorem kn_29 : KnownBin bds_29 := by
  intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_4
  · exact lb_10
  · exact lb_1
  · exact lb_7
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

def m_30 : Nat := 0xaa00aa00aa00aa
def s_30 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_30 : Nat := 0x20022000a002a
def ep_30 : Nat := 0x800080000002000000020000000000000000000020000000a000800020022000000200000000000000000
theorem epk_30 : ep_30 = edgePack m_30 g_30 := by decide +kernel
def bds_30 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_30 : KnownBin bds_30 := by intro b hb; simp [bds_30] at hb
theorem sub_30 : ∀ b ∈ bds_30, m_30 &&& b.1 = b.1 := by intro b hb; simp [bds_30] at hb
theorem gl_30 : ∀ b ∈ bds_30, canon b.1 g_30 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_30] at hb
def cur_30 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0xf 2 3 1 1 4 15 5 31
def f_30 : Nat → Nat × Nat := unpackForestF 0xf 1 4
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV4 m_30 g_30 ep_30 1 bds_30 (dagTraceF m_30 s_30 3 f_30) (cur_30 0) s_30 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30 : treeBlockF 0 1 (dagCheckNodeV4 m_30 g_30 ep_30 bds_30 1 (dagTraceF m_30 s_30 3 f_30) cur_30) = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_30 g_30 ep_30 bds_30 1 (dagTraceF m_30 s_30 3 f_30) cur_30) i = true := fun _ h1 h2 => treeBlockF_at nb_30 h1 h2
theorem lb_30 : LowerBin m_30 s_30 g_30 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_30 kn_30 sub_30 gl_30 rc_30 nc_30

def m_31 : Nat := 0xaaaaaaaa00000000
def s_31 : List Nat := [0x2222222200000000, 0xa0a0a0a00000000, 0xaa00aa00000000, 0xaaaa00000000]
def g_31 : Nat := 0x2022200000000
def ep_31 : Nat := 0x220000000000002002000000000000202000000000000020222000000000000000000000000
theorem epk_31 : ep_31 = edgePack m_31 g_31 := by decide +kernel
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
theorem kn_31 : KnownBin bds_31 := by
  intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_7
theorem sub_31 : ∀ b ∈ bds_31, m_31 &&& b.1 = b.1 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_31 : ∀ b ∈ bds_31, canon b.1 g_31 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_31 : Nat → List (Nat × Nat) := fun _ => []
def f_31 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV4 m_31 g_31 ep_31 0 bds_31 (dagTraceF m_31 s_31 4 f_31) (cur_31 0) s_31 4 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_31 g_31 ep_31 bds_31 0 (dagTraceF m_31 s_31 4 f_31) cur_31 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_31 kn_31 sub_31 gl_31 rc_31 nc_31

def m_32 : Nat := 0x5555555500000000
def s_32 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_32 : Nat := 0x115155500000000
def ep_32 : Nat := 0x1440000000000014004000000000010404000000000001101000000000000000000000000000
theorem epk_32 : ep_32 = edgePack m_32 g_32 := by decide +kernel
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3), (m_11, s_11, 4, g_11), (m_2, s_2, 4, g_2), (m_6, s_6, 4, g_6)]
theorem kn_32 : KnownBin bds_32 := by
  intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_3
  · exact lb_11
  · exact lb_2
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
def g_33 : Nat := 0x4000404040
def ep_33 : Nat := 0x40400000000040000040000000004000400000000000000000000000000000000000000000004000404040
theorem epk_33 : ep_33 = edgePack m_33 g_33 := by decide +kernel
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
theorem kn_33 : KnownBin bds_33 := by
  intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_12
theorem sub_33 : ∀ b ∈ bds_33, m_33 &&& b.1 = b.1 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_33 : ∀ b ∈ bds_33, canon b.1 g_33 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_33 : Nat → List (Nat × Nat) := fun _ => []
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV4 m_33 g_33 ep_33 0 bds_33 (dagTraceF m_33 s_33 4 f_33) (cur_33 0) s_33 4 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_33 g_33 ep_33 bds_33 0 (dagTraceF m_33 s_33 4 f_33) cur_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_33 kn_33 sub_33 gl_33 rc_33 nc_33

def m_34 : Nat := 0xcccc0000cccc
def s_34 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_34 : Nat := 0x4440000444c
def ep_34 : Nat := 0x400800000000000000000000004000000008000004000000000800000000000000000000044400004440
theorem epk_34 : ep_34 = edgePack m_34 g_34 := by decide +kernel
def bds_34 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_34 : KnownBin bds_34 := by intro b hb; simp [bds_34] at hb
theorem sub_34 : ∀ b ∈ bds_34, m_34 &&& b.1 = b.1 := by intro b hb; simp [bds_34] at hb
theorem gl_34 : ∀ b ∈ bds_34, canon b.1 g_34 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_34] at hb
def cc_34_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0xe24c6d20345319280b83c581a2a0b14048912844921e0b0e04858202c9a124f08268303c141a040402249fa3ff91df28df4467993fc89dda4de8267292f8895c249df246f03f741db00dd3066802f34159809ca046381f100d8605c1026000f 11 2047 5 31 10 1023 17 131071
def cc_34_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0x3d299e140ec26741038251b924d8146a09314998240bc265c102c2795934a80c5205270513024900c4605202410234 8 255 3 7 10 1023 17 131071
def cur_34 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_34_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_34_0 p) (Nat.blt p 32)
def f_34 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV4 m_34 g_34 ep_34 64 bds_34 (dagTraceF m_34 s_34 5 f_34) (cur_34 0) s_34 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_0 : treeBlockF 0 32 (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 64 (dagTraceF m_34 s_34 5 f_34) cur_34) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_1 : treeBlockF 32 64 (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 64 (dagTraceF m_34 s_34 5 f_34) cur_34) = true := by decide +kernel
theorem nj_34_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 64 (dagTraceF m_34 s_34 5 f_34) cur_34) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_34_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_34_1 h1 h2)
theorem nc_34 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_34 g_34 ep_34 bds_34 64 (dagTraceF m_34 s_34 5 f_34) cur_34) i = true := nj_34_1
theorem lb_34 : LowerBin m_34 s_34 g_34 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_34 kn_34 sub_34 gl_34 rc_34 nc_34

def m_35 : Nat := 0xaaaa0000aaaa0000
def s_35 : List Nat := [0x2222000022220000, 0xa0a00000a0a0000, 0xaa000000aa0000, 0xaaaa0000]
def g_35 : Nat := 0x20000020a0000
def ep_35 : Nat := 0x20800000000000000000000000200000008000000020000020a000000020000020000000000000000000000
theorem epk_35 : ep_35 = edgePack m_35 g_35 := by decide +kernel
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_22, s_22, 4, g_22)]
theorem kn_35 : KnownBin bds_35 := by
  intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_22
theorem sub_35 : ∀ b ∈ bds_35, m_35 &&& b.1 = b.1 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_35 : ∀ b ∈ bds_35, canon b.1 g_35 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_35 : Nat → List (Nat × Nat) := fun _ => []
def f_35 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV4 m_35 g_35 ep_35 0 bds_35 (dagTraceF m_35 s_35 4 f_35) (cur_35 0) s_35 4 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_35 g_35 ep_35 bds_35 0 (dagTraceF m_35 s_35 4 f_35) cur_35 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_35 : LowerBin m_35 s_35 g_35 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_35 kn_35 sub_35 gl_35 rc_35 nc_35

def m_36 : Nat := 0x5555000055550000
def s_36 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_36 : Nat := 0x115000005550000
def ep_36 : Nat := 0x440000000000000000000000014000000500000010400000500000001100000000000000000000000000000
theorem epk_36 : ep_36 = edgePack m_36 g_36 := by decide +kernel
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
theorem kn_36 : KnownBin bds_36 := by
  intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_11
theorem sub_36 : ∀ b ∈ bds_36, m_36 &&& b.1 = b.1 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_36 : ∀ b ∈ bds_36, canon b.1 g_36 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_36 : Nat → List (Nat × Nat) := fun _ => []
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV4 m_36 g_36 ep_36 0 bds_36 (dagTraceF m_36 s_36 4 f_36) (cur_36 0) s_36 4 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_36 g_36 ep_36 bds_36 0 (dagTraceF m_36 s_36 4 f_36) cur_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_36 kn_36 sub_36 gl_36 rc_36 nc_36

def m_37 : Nat := 0x5500550055005500
def s_37 : List Nat := [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500]
def g_37 : Nat := 0x100150005005500
def ep_37 : Nat := 0x400400000001400000050000000000000000000010004000500000001001000000000000000000000000000
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

def m_38 : Nat := 0xff000000ff00
def s_38 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_38 : Nat := 0x170000005700
def ep_38 : Nat := 0x400000000000000000000000000000000000000006000000020000001200000002000000140000005400
theorem epk_38 : ep_38 = edgePack m_38 g_38 := by decide +kernel
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_20, s_20, 4, g_20)]
theorem kn_38 : KnownBin bds_38 := by
  intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_20
theorem sub_38 : ∀ b ∈ bds_38, m_38 &&& b.1 = b.1 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_38 : ∀ b ∈ bds_38, canon b.1 g_38 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV4 m_38 g_38 ep_38 0 bds_38 (dagTraceF m_38 s_38 4 f_38) (cur_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_38 g_38 ep_38 bds_38 0 (dagTraceF m_38 s_38 4 f_38) cur_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_38 kn_38 sub_38 gl_38 rc_38 nc_38

def m_39 : Nat := 0xf0f00000f0f0
def s_39 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_39 : Nat := 0x107000005070
def ep_39 : Nat := 0x400000000000000000000000006000000020000000000000000000001020000000200000104000005040
theorem epk_39 : ep_39 = edgePack m_39 g_39 := by decide +kernel
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 4, g_17)]
theorem kn_39 : KnownBin bds_39 := by
  intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_17
theorem sub_39 : ∀ b ∈ bds_39, m_39 &&& b.1 = b.1 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_39 : ∀ b ∈ bds_39, canon b.1 g_39 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_39 : Nat → List (Nat × Nat) := fun _ => []
def f_39 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV4 m_39 g_39 ep_39 0 bds_39 (dagTraceF m_39 s_39 4 f_39) (cur_39 0) s_39 4 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_39 g_39 ep_39 bds_39 0 (dagTraceF m_39 s_39 4 f_39) cur_39 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_39 : LowerBin m_39 s_39 g_39 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_39 kn_39 sub_39 gl_39 rc_39 nc_39

def m_40 : Nat := 0xcccc0000cccc0000
def s_40 : List Nat := [0x4444000044440000, 0xc0c00000c0c0000, 0xcc000000cc0000, 0xcccc0000]
def g_40 : Nat := 0x40000044c0000
def ep_40 : Nat := 0x448000000000000000000000004000000480000000400000408000000000000000000000004000004400000
theorem epk_40 : ep_40 = edgePack m_40 g_40 := by decide +kernel
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_19, s_19, 4, g_19), (m_9, s_9, 4, g_9), (m_21, s_21, 4, g_21), (m_23, s_23, 4, g_23)]
theorem kn_40 : KnownBin bds_40 := by
  intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_19
  · exact lb_9
  · exact lb_21
  · exact lb_23
theorem sub_40 : ∀ b ∈ bds_40, m_40 &&& b.1 = b.1 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_40 : ∀ b ∈ bds_40, canon b.1 g_40 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_40_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_40_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_40 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_40_1 (Nat.sub p 32)) (cc_40_0 p) (Nat.blt p 32)
def f_40 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV4 m_40 g_40 ep_40 43 bds_40 (dagTraceF m_40 s_40 6 f_40) (cur_40 0) s_40 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_0 : treeBlockF 0 32 (dagCheckNodeV4 m_40 g_40 ep_40 bds_40 43 (dagTraceF m_40 s_40 6 f_40) cur_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_1 : treeBlockF 32 43 (dagCheckNodeV4 m_40 g_40 ep_40 bds_40 43 (dagTraceF m_40 s_40 6 f_40) cur_40) = true := by decide +kernel
theorem nj_40_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_40 g_40 ep_40 bds_40 43 (dagTraceF m_40 s_40 6 f_40) cur_40) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_40_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_40_1 h1 h2)
theorem nc_40 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_40 g_40 ep_40 bds_40 43 (dagTraceF m_40 s_40 6 f_40) cur_40) i = true := nj_40_1
theorem lb_40 : LowerBin m_40 s_40 g_40 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_40 kn_40 sub_40 gl_40 rc_40 nc_40

def m_41 : Nat := 0xaaaa0000aaaa
def s_41 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_41 : Nat := 0x2220000022a
def ep_41 : Nat := 0x800000000000000000000002000000028000002000000020800000222000002200000000000000000
theorem epk_41 : ep_41 = edgePack m_41 g_41 := by decide +kernel
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_41 : KnownBin bds_41 := by
  intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_41 : ∀ b ∈ bds_41, m_41 &&& b.1 = b.1 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_41 : ∀ b ∈ bds_41, canon b.1 g_41 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV4 m_41 g_41 ep_41 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_41 g_41 ep_41 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_41 kn_41 sub_41 gl_41 rc_41 nc_41

def m_42 : Nat := 0x3300330033003300
def s_42 : List Nat := [0x1100110011001100, 0x300030003000300, 0x330000003300, 0x33003300]
def g_42 : Nat := 0x100130003001300
def ep_42 : Nat := 0x200000000001200000010000000000000000000010002000300020000000000000000000100100000001000
theorem epk_42 : ep_42 = edgePack m_42 g_42 := by decide +kernel
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
theorem kn_42 : KnownBin bds_42 := by
  intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_4
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
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
theorem kn_43 : KnownBin bds_43 := by
  intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_15
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
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
theorem kn_44 : KnownBin bds_44 := by
  intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_5
theorem sub_44 : ∀ b ∈ bds_44, m_44 &&& b.1 = b.1 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_44 : ∀ b ∈ bds_44, canon b.1 g_44 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_44 : Nat → List (Nat × Nat) := fun _ => []
def f_44 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV4 m_44 g_44 ep_44 0 bds_44 (dagTraceF m_44 s_44 4 f_44) (cur_44 0) s_44 4 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_44 g_44 ep_44 bds_44 0 (dagTraceF m_44 s_44 4 f_44) cur_44 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_44 : LowerBin m_44 s_44 g_44 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_44 kn_44 sub_44 gl_44 rc_44 nc_44

def m_45 : Nat := 0x33333333
def s_45 : List Nat := [0x11111111, 0x3030303, 0x330033, 0x3333]
def g_45 : Nat := 0x3131333
def ep_45 : Nat := 0x10200000000000100020000000000302020000000000000000000000000000101000
theorem epk_45 : ep_45 = edgePack m_45 g_45 := by decide +kernel
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 4, g_18)]
theorem kn_45 : KnownBin bds_45 := by
  intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_18
theorem sub_45 : ∀ b ∈ bds_45, m_45 &&& b.1 = b.1 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_45 : ∀ b ∈ bds_45, canon b.1 g_45 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_45 : Nat → List (Nat × Nat) := fun _ => []
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV4 m_45 g_45 ep_45 0 bds_45 (dagTraceF m_45 s_45 4 f_45) (cur_45 0) s_45 4 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_45 g_45 ep_45 bds_45 0 (dagTraceF m_45 s_45 4 f_45) cur_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin m_45 s_45 g_45 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_45 kn_45 sub_45 gl_45 rc_45 nc_45

def m_46 : Nat := 0xcc00cc00cc00cc
def s_46 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_46 : Nat := 0x40044004c004c
def ep_46 : Nat := 0x48000800000040000000000000000000000000000400000008000800000000000000000004004400400040
theorem epk_46 : ep_46 = edgePack m_46 g_46 := by decide +kernel
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_19, s_19, 4, g_19)]
theorem kn_46 : KnownBin bds_46 := by
  intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_19
theorem sub_46 : ∀ b ∈ bds_46, m_46 &&& b.1 = b.1 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_46 : ∀ b ∈ bds_46, canon b.1 g_46 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_46 : Nat → List (Nat × Nat) := fun _ => []
def f_46 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV4 m_46 g_46 ep_46 0 bds_46 (dagTraceF m_46 s_46 4 f_46) (cur_46 0) s_46 4 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_46 g_46 ep_46 bds_46 0 (dagTraceF m_46 s_46 4 f_46) cur_46 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_46 : LowerBin m_46 s_46 g_46 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_46 kn_46 sub_46 gl_46 rc_46 nc_46

def m_47 : Nat := 0xffff0000
def s_47 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_47 : Nat := 0x75f0000
def ep_47 : Nat := 0x58000000000000070a000000000000020000000000000004500000
theorem epk_47 : ep_47 = edgePack m_47 g_47 := by decide +kernel
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_47 : KnownBin bds_47 := by
  intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_47 : ∀ b ∈ bds_47, m_47 &&& b.1 = b.1 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_47 : ∀ b ∈ bds_47, canon b.1 g_47 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_47 : Nat → List (Nat × Nat) := fun _ => []
def f_47 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV4 m_47 g_47 ep_47 0 bds_47 (dagTraceF m_47 s_47 4 f_47) (cur_47 0) s_47 4 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_47 g_47 ep_47 bds_47 0 (dagTraceF m_47 s_47 4 f_47) cur_47 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_47 : LowerBin m_47 s_47 g_47 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_47 kn_47 sub_47 gl_47 rc_47 nc_47

def m_48 : Nat := 0xffff
def s_48 : List Nat := [0x5555, 0x3333, 0xf0f, 0xff]
def g_48 : Nat := 0x577f
def ep_48 : Nat := 0x28000000000000020800000000000002200000000000005440
theorem epk_48 : ep_48 = edgePack m_48 g_48 := by decide +kernel
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_48 : KnownBin bds_48 := by
  intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_48 : ∀ b ∈ bds_48, m_48 &&& b.1 = b.1 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_48 : ∀ b ∈ bds_48, canon b.1 g_48 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_48 : Nat → List (Nat × Nat) := fun _ => []
def f_48 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV4 m_48 g_48 ep_48 0 bds_48 (dagTraceF m_48 s_48 4 f_48) (cur_48 0) s_48 4 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_48 g_48 ep_48 bds_48 0 (dagTraceF m_48 s_48 4 f_48) cur_48 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_48 : LowerBin m_48 s_48 g_48 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_48 kn_48 sub_48 gl_48 rc_48 nc_48

def m_49 : Nat := 0xff00ff00
def s_49 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_49 : Nat := 0x7005700
def ep_49 : Nat := 0x50000000000000000000000000000700020000000000020002000000000004005400
theorem epk_49 : ep_49 = edgePack m_49 g_49 := by decide +kernel
def bds_49 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_49 : KnownBin bds_49 := by intro b hb; simp [bds_49] at hb
theorem sub_49 : ∀ b ∈ bds_49, m_49 &&& b.1 = b.1 := by intro b hb; simp [bds_49] at hb
theorem gl_49 : ∀ b ∈ bds_49, canon b.1 g_49 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_49] at hb
def cur_49 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0xf 2 3 1 1 4 15 5 31
def f_49 : Nat → Nat × Nat := unpackForestF 0xf 1 4
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV4 m_49 g_49 ep_49 1 bds_49 (dagTraceF m_49 s_49 3 f_49) (cur_49 0) s_49 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49 : treeBlockF 0 1 (dagCheckNodeV4 m_49 g_49 ep_49 bds_49 1 (dagTraceF m_49 s_49 3 f_49) cur_49) = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_49 g_49 ep_49 bds_49 1 (dagTraceF m_49 s_49 3 f_49) cur_49) i = true := fun _ h1 h2 => treeBlockF_at nb_49 h1 h2
theorem lb_49 : LowerBin m_49 s_49 g_49 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_49 kn_49 sub_49 gl_49 rc_49 nc_49

def m_50 : Nat := 0xf0f0f0f0
def s_50 : List Nat := [0x50505050, 0x30303030, 0xf000f0, 0xf0f0]
def g_50 : Nat := 0x505070
def ep_50 : Nat := 0x50200000000000500020000000000000000000000000000000200000000000505040
theorem epk_50 : ep_50 = edgePack m_50 g_50 := by decide +kernel
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 4, g_18)]
theorem kn_50 : KnownBin bds_50 := by
  intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_18
theorem sub_50 : ∀ b ∈ bds_50, m_50 &&& b.1 = b.1 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_50 : ∀ b ∈ bds_50, canon b.1 g_50 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_50 : Nat → List (Nat × Nat) := fun _ => []
def f_50 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV4 m_50 g_50 ep_50 0 bds_50 (dagTraceF m_50 s_50 4 f_50) (cur_50 0) s_50 4 = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_50 g_50 ep_50 bds_50 0 (dagTraceF m_50 s_50 4 f_50) cur_50 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_50 : LowerBin m_50 s_50 g_50 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_50 kn_50 sub_50 gl_50 rc_50 nc_50

def m_51 : Nat := 0xcccccccc
def s_51 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_51 : Nat := 0x44c444c
def ep_51 : Nat := 0x40000000000000480008000000000408000800000000000000000000000004404440
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

def m_52 : Nat := 0xaaaaaaaa
def s_52 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_52 : Nat := 0x20a022a
def ep_52 : Nat := 0x20000000000008002800000000020a020800000000020002200000000000000000
theorem epk_52 : ep_52 = edgePack m_52 g_52 := by decide +kernel
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_52 : KnownBin bds_52 := by
  intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_52 : ∀ b ∈ bds_52, m_52 &&& b.1 = b.1 := by intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_52 : ∀ b ∈ bds_52, canon b.1 g_52 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_52 : Nat → List (Nat × Nat) := fun _ => []
def f_52 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV4 m_52 g_52 ep_52 0 bds_52 (dagTraceF m_52 s_52 4 f_52) (cur_52 0) s_52 4 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_52 g_52 ep_52 bds_52 0 (dagTraceF m_52 s_52 4 f_52) cur_52 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_52 : LowerBin m_52 s_52 g_52 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_52 kn_52 sub_52 gl_52 rc_52 nc_52

def m_53 : Nat := 0xff000000ff000000
def s_53 : List Nat := [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000]
def g_53 : Nat := 0x100000007000000
def ep_53 : Nat := 0x600000000000000000000000000000000000000010000000700000001000000020000000100000004000000
theorem epk_53 : ep_53 = edgePack m_53 g_53 := by decide +kernel
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16)]
theorem kn_53 : KnownBin bds_53 := by
  intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_16
theorem sub_53 : ∀ b ∈ bds_53, m_53 &&& b.1 = b.1 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_53 : ∀ b ∈ bds_53, canon b.1 g_53 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_53 : Nat → List (Nat × Nat) := fun _ => []
def f_53 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV4 m_53 g_53 ep_53 0 bds_53 (dagTraceF m_53 s_53 4 f_53) (cur_53 0) s_53 4 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_53 g_53 ep_53 bds_53 0 (dagTraceF m_53 s_53 4 f_53) cur_53 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_53 : LowerBin m_53 s_53 g_53 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_53 kn_53 sub_53 gl_53 rc_53 nc_53

def m_54 : Nat := 0xff000000ff0000
def s_54 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_54 : Nat := 0x170000005f0000
def ep_54 : Nat := 0x4800000000000000000000000000000000000000060000000a000000120000000000000014000000500000
theorem epk_54 : ep_54 = edgePack m_54 g_54 := by decide +kernel
def bds_54 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
theorem kn_54 : KnownBin bds_54 := by
  intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_13
theorem sub_54 : ∀ b ∈ bds_54, m_54 &&& b.1 = b.1 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_54 : ∀ b ∈ bds_54, canon b.1 g_54 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_54 : Nat → List (Nat × Nat) := fun _ => []
def f_54 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV4 m_54 g_54 ep_54 0 bds_54 (dagTraceF m_54 s_54 4 f_54) (cur_54 0) s_54 4 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_54 g_54 ep_54 bds_54 0 (dagTraceF m_54 s_54 4 f_54) cur_54 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_54 : LowerBin m_54 s_54 g_54 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_54 kn_54 sub_54 gl_54 rc_54 nc_54

def m_55 : Nat := 0xf000f000f000f0
def s_55 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_55 : Nat := 0x10007000500070
def ep_55 : Nat := 0x40000000000060000000200000000000000000000000000000000000100020000000200010004000500040
theorem epk_55 : ep_55 = edgePack m_55 g_55 := by decide +kernel
def bds_55 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
theorem kn_55 : KnownBin bds_55 := by
  intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_8
theorem sub_55 : ∀ b ∈ bds_55, m_55 &&& b.1 = b.1 := by intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_55 : ∀ b ∈ bds_55, canon b.1 g_55 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_55 : Nat → List (Nat × Nat) := fun _ => []
def f_55 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV4 m_55 g_55 ep_55 0 bds_55 (dagTraceF m_55 s_55 4 f_55) (cur_55 0) s_55 4 = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_55 g_55 ep_55 bds_55 0 (dagTraceF m_55 s_55 4 f_55) cur_55 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_55 : LowerBin m_55 s_55 g_55 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_55 kn_55 sub_55 gl_55 rc_55 nc_55

def m_56 : Nat := 0xf0f00000f0f0000
def s_56 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_56 : Nat := 0x1070000070f0000
def ep_56 : Nat := 0x608000000000000000000000006000000080000000000000000000001020000020000000104000004000000
theorem epk_56 : ep_56 = edgePack m_56 g_56 := by decide +kernel
def bds_56 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14), (m_16, s_16, 4, g_16), (m_23, s_23, 4, g_23), (m_22, s_22, 4, g_22)]
theorem kn_56 : KnownBin bds_56 := by
  intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_14
  · exact lb_16
  · exact lb_23
  · exact lb_22
theorem sub_56 : ∀ b ∈ bds_56, m_56 &&& b.1 = b.1 := by intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_56 : ∀ b ∈ bds_56, canon b.1 g_56 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_56_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_56_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
def cur_56 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_56_1 (Nat.sub p 32)) (cc_56_0 p) (Nat.blt p 32)
def f_56 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV4 m_56 g_56 ep_56 43 bds_56 (dagTraceF m_56 s_56 6 f_56) (cur_56 0) s_56 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_0 : treeBlockF 0 32 (dagCheckNodeV4 m_56 g_56 ep_56 bds_56 43 (dagTraceF m_56 s_56 6 f_56) cur_56) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56_1 : treeBlockF 32 43 (dagCheckNodeV4 m_56 g_56 ep_56 bds_56 43 (dagTraceF m_56 s_56 6 f_56) cur_56) = true := by decide +kernel
theorem nj_56_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_56 g_56 ep_56 bds_56 43 (dagTraceF m_56 s_56 6 f_56) cur_56) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_56_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_56_1 h1 h2)
theorem nc_56 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_56 g_56 ep_56 bds_56 43 (dagTraceF m_56 s_56 6 f_56) cur_56) i = true := nj_56_1
theorem lb_56 : LowerBin m_56 s_56 g_56 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_56 kn_56 sub_56 gl_56 rc_56 nc_56

def m_57 : Nat := 0x4444444444444444
def s_57 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_57 : Nat := 0x4044404444444
def ep_57 : Nat := 0x440400000000440000040000004004000400000000404000400000000000000000000000000000000000000
theorem epk_57 : ep_57 = edgePack m_57 g_57 := by decide +kernel
def bds_57 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6), (m_21, s_21, 4, g_21), (m_15, s_15, 4, g_15), (m_12, s_12, 4, g_12)]
theorem kn_57 : KnownBin bds_57 := by
  intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_6
  · exact lb_21
  · exact lb_15
  · exact lb_12
theorem sub_57 : ∀ b ∈ bds_57, m_57 &&& b.1 = b.1 := by intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_57 : ∀ b ∈ bds_57, canon b.1 g_57 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_57_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_57_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
def cur_57 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_57_1 (Nat.sub p 32)) (cc_57_0 p) (Nat.blt p 32)
def f_57 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV4 m_57 g_57 ep_57 43 bds_57 (dagTraceF m_57 s_57 6 f_57) (cur_57 0) s_57 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_0 : treeBlockF 0 32 (dagCheckNodeV4 m_57 g_57 ep_57 bds_57 43 (dagTraceF m_57 s_57 6 f_57) cur_57) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_1 : treeBlockF 32 43 (dagCheckNodeV4 m_57 g_57 ep_57 bds_57 43 (dagTraceF m_57 s_57 6 f_57) cur_57) = true := by decide +kernel
theorem nj_57_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_57 g_57 ep_57 bds_57 43 (dagTraceF m_57 s_57 6 f_57) cur_57) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_57_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_57_1 h1 h2)
theorem nc_57 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_57 g_57 ep_57 bds_57 43 (dagTraceF m_57 s_57 6 f_57) cur_57) i = true := nj_57_1
theorem lb_57 : LowerBin m_57 s_57 g_57 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_57 kn_57 sub_57 gl_57 rc_57 nc_57

def m_58 : Nat := 0x5a5a00005a5a
def s_58 : List Nat := [0xa0a00000a0a, 0x121200001212, 0x5a0000005a, 0x5a5a]
def g_58 : Nat := 0x12520000525a
def ep_58 : Nat := 0x400800000000000000000000004000000008000000000000000000001202000002000000000000000000
theorem epk_58 : ep_58 = edgePack m_58 g_58 := by decide +kernel
def bds_58 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_58 : KnownBin bds_58 := by intro b hb; simp [bds_58] at hb
theorem sub_58 : ∀ b ∈ bds_58, m_58 &&& b.1 = b.1 := by intro b hb; simp [bds_58] at hb
theorem gl_58 : ∀ b ∈ bds_58, canon b.1 g_58 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_58] at hb
def cur_58 : Nat → List (Nat × Nat) := unpackCursorV4 0x16ac58b12a44890e8701 0x31343068c4a08121928204928ea11b393a526c80e841b000f 7 127 3 7 10 1023 15 32767
def f_58 : Nat → Nat × Nat := unpackForestF 0xc7463629d64a0a6c43a494209086c00f 3 10
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV4 m_58 g_58 ep_58 10 bds_58 (dagTraceF m_58 s_58 4 f_58) (cur_58 0) s_58 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58 : treeBlockF 0 10 (dagCheckNodeV4 m_58 g_58 ep_58 bds_58 10 (dagTraceF m_58 s_58 4 f_58) cur_58) = true := by decide +kernel
theorem nc_58 : ∀ i, 0 ≤ i → i < 10 → (dagCheckNodeV4 m_58 g_58 ep_58 bds_58 10 (dagTraceF m_58 s_58 4 f_58) cur_58) i = true := fun _ h1 h2 => treeBlockF_at nb_58 h1 h2
theorem lb_58 : LowerBin m_58 s_58 g_58 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_58 kn_58 sub_58 gl_58 rc_58 nc_58

def m_59 : Nat := 0xc0c0c0c0c0c0c0c
def s_59 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_59 : Nat := 0x40404040c040c
def ep_59 : Nat := 0x408000800000400000000000004000000080008000000000000000000000000000000000004040404000400
theorem epk_59 : ep_59 = edgePack m_59 g_59 := by decide +kernel
def bds_59 : List (Nat × List Nat × Nat × Nat) := [(m_23, s_23, 4, g_23)]
theorem kn_59 : KnownBin bds_59 := by
  intro b hb; simp only [bds_59, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_23
theorem sub_59 : ∀ b ∈ bds_59, m_59 &&& b.1 = b.1 := by intro b hb; simp only [bds_59, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_59 : ∀ b ∈ bds_59, canon b.1 g_59 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_59, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_59 : Nat → List (Nat × Nat) := fun _ => []
def f_59 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_59 : dagCheckRootsV4 m_59 g_59 ep_59 0 bds_59 (dagTraceF m_59 s_59 4 f_59) (cur_59 0) s_59 4 = true := by decide +kernel
theorem nc_59 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_59 g_59 ep_59 bds_59 0 (dagTraceF m_59 s_59 4 f_59) cur_59 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_59 : LowerBin m_59 s_59 g_59 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_59 kn_59 sub_59 gl_59 rc_59 nc_59

def m_60 : Nat := 0xaaaaaaaaaaaaaaaa
def s_60 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_60 : Nat := 0x20222020a022a
def ep_60 : Nat := 0x20800080000022000000020000200200008002800020200020a020800020222020002200000000000000000
theorem epk_60 : ep_60 = edgePack m_60 g_60 := by decide +kernel
def bds_60 : List (Nat × List Nat × Nat × Nat) := [(m_22, s_22, 4, g_22), (m_7, s_7, 4, g_7), (m_31, s_31, 5, g_31), (m_41, s_41, 5, g_41), (m_52, s_52, 5, g_52), (m_30, s_30, 4, g_30), (m_0, s_0, 4, g_0)]
theorem kn_60 : KnownBin bds_60 := by
  intro b hb; simp only [bds_60, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_22
  · exact lb_7
  · exact lb_31
  · exact lb_41
  · exact lb_52
  · exact lb_30
  · exact lb_0
theorem sub_60 : ∀ b ∈ bds_60, m_60 &&& b.1 = b.1 := by intro b hb; simp only [bds_60, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_60 : ∀ b ∈ bds_60, canon b.1 g_60 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_60, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_60 : Nat → List (Nat × Nat) := unpackCursorV4 0x6e03321961b3c588abc55c190f470a38102d7f13f81fc0fc17d0bd0de80d506a03501a0495e3d69e80f407622d70ec0078001 0xe2d06d3434b392519120968f7a4725a35691886578308218400c1e860e4306a18311c9a07178b8bbb3492da08696834b21a562d2886918348a5a3e89190657832a4394d1ca286134309218450c20940f8306418290c10c0d4030a0483c0c18064b038b394512dae86d6836ac1b55a1a73cd0834bc5a5dc12734908347c1a3d0caf06548725a3925182706108307218310c16860a830521828b81306094904818210c2412112a6bc1b5a0dab16d48b69a5a5ea1291690542bc483d0c1c920d4306303500d2241140729839240c141209248a5135e79a916d35c4bc1a5a0d2b34948b49a815e60930e490905a1829241286084729891440d258690c74763a330ca78652c328e19431c9f8e4ec726e39335097a048c309e184b0c238610c307e183b0c1b860cc305e682e0c1186088303e181b0c0b8604c349e1a4b0d238690c329c184f0c258611c3086182f0c158609c3046493c209a1293c34961a472521868f4a29e194b0ca38c50c925e492b24939248cd09c1b420d278692c348e1a430ca70613c309618470c21860f4305e182b0c138608c302a1b4be1a1e893c34961a47b121cc8fd6466394f38a70651cc284392f1c938613c309618470c21920fc407c18330819120bc305648270c118606c702e001f 13 8191 5 31 11 2047 17 131071
def f_60 : Nat → Nat × Nat := unpackForestF 0xea390b43db490a4fbc51ba4eb8260a43a35ea2520a3f6452635e84506352625e625261260a33412f49444123094e0942194f21341943083e0832001f 5 11
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsV4 m_60 g_60 ep_60 30 bds_60 (dagTraceF m_60 s_60 7 f_60) (cur_60 0) s_60 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60 : treeBlockF 0 30 (dagCheckNodeV4 m_60 g_60 ep_60 bds_60 30 (dagTraceF m_60 s_60 7 f_60) cur_60) = true := by decide +kernel
theorem nc_60 : ∀ i, 0 ≤ i → i < 30 → (dagCheckNodeV4 m_60 g_60 ep_60 bds_60 30 (dagTraceF m_60 s_60 7 f_60) cur_60) i = true := fun _ h1 h2 => treeBlockF_at nb_60 h1 h2
theorem lb_60 : LowerBin m_60 s_60 g_60 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_60 kn_60 sub_60 gl_60 rc_60 nc_60

def m_61 : Nat := 0x5555555555555555
def s_61 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_61 : Nat := 0x115155505555555
def ep_61 : Nat := 0x440400000001440000050000014004000500000010404000500000001101000000000000000000000000000
theorem epk_61 : ep_61 = edgePack m_61 g_61 := by decide +kernel
def bds_61 : List (Nat × List Nat × Nat × Nat) := [(m_32, s_32, 7, g_32)]
theorem kn_61 : KnownBin bds_61 := by
  intro b hb; simp only [bds_61, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_32
theorem sub_61 : ∀ b ∈ bds_61, m_61 &&& b.1 = b.1 := by intro b hb; simp only [bds_61, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_61 : ∀ b ∈ bds_61, canon b.1 g_61 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_61, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_61 : Nat → List (Nat × Nat) := fun _ => []
def f_61 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_61 : dagCheckRootsV4 m_61 g_61 ep_61 0 bds_61 (dagTraceF m_61 s_61 7 f_61) (cur_61 0) s_61 7 = true := by decide +kernel
theorem nc_61 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_61 g_61 ep_61 bds_61 0 (dagTraceF m_61 s_61 7 f_61) cur_61 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_61 : LowerBin m_61 s_61 g_61 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_61 kn_61 sub_61 gl_61 rc_61 nc_61

def m_62 : Nat := 0x3333333333333333
def s_62 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_62 : Nat := 0x113133303131333
def ep_62 : Nat := 0x200000000001220000010200012002000100020010202000302020000000000000000000110100000101000
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

def m_63 : Nat := 0xcccccccccccccccc
def s_63 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_63 : Nat := 0x40444044c444c
def ep_63 : Nat := 0x448400800000440000040000004004000480008000404000408000800000000000000000004044404404440
theorem epk_63 : ep_63 = edgePack m_63 g_63 := by decide +kernel
def bds_63 : List (Nat × List Nat × Nat × Nat) := [(m_40, s_40, 7, g_40), (m_28, s_28, 5, g_28), (m_43, s_43, 5, g_43), (m_59, s_59, 5, g_59), (m_12, s_12, 4, g_12), (m_15, s_15, 4, g_15), (m_57, s_57, 7, g_57), (m_46, s_46, 5, g_46), (m_51, s_51, 5, g_51), (m_34, s_34, 6, g_34)]
theorem kn_63 : KnownBin bds_63 := by
  intro b hb; simp only [bds_63, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_40
  · exact lb_28
  · exact lb_43
  · exact lb_59
  · exact lb_12
  · exact lb_15
  · exact lb_57
  · exact lb_46
  · exact lb_51
  · exact lb_34
theorem sub_63 : ∀ b ∈ bds_63, m_63 &&& b.1 = b.1 := by intro b hb; simp only [bds_63, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_63 : ∀ b ∈ bds_63, canon b.1 g_63 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_63, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_63 : Nat → List (Nat × Nat) := unpackCursorV4 0xacf49ff493338c5b7e39713464345773509b4279357428741bb314db06b900590001 0x3c5f4c5b3c574c534b5f4b5e4b5b4b5a4b574b564b534b522b4f2b4e2b4d4a5f4a5e2a5b4a572a534a522a4b3a4a2a493a473a462a432a413a373a363a35495e485f485b48574853484f384b38474843483f483d483b18394837883548331831282f782b782728233c5f3c5e3c5b3c573c535c522b5f2b5b2b572b532b4f3b4e2b4d2b472b452b432b422a5f5a5e2a5b2a5a2a574a562a532a522a473a462a452a3f2a3e2a3d595e585f485b48575853384f384b38473843283f283b28372833282f282d282b182928278825282318213c5f3c5e3c5b4c5a3c573c563c536c523b5f3b5b3b573b532b4f2b4e2b4d5a5f2a5b4a572a533a4f3a4e4a4d3a3f3a3e2a3b2a392a333a322a31c230695e685f485b48576853384f884d384b18493847384538431841383f383b38373833282f782b782728233b4f3b4e3b4b3b473b434b422a4f2a4b2a472a432a3f3a3e2a3d494e2926484f484b48474843383f383b38373833282f282b282728233c5f4c5e4c5b3c574c534c522b5f4b5e2b5b2b572b532b522b4f2b4d2b4b2b4a2b473b462b45c3442a5f4a5e2a5b2a5a2a574a562a532a522a4f4a4e2a4d2a3f2a3e2a3d495e29269924485f485b48574853484f384b38474843283f283b28372833282f282d282b182928278825282318213c5f4c5b3c574c534b5f4b5e4b5b4b5a4b574b564b534b521b4f1b4e1b4d4a5f4a5b4a574a534a4f3a4b3a474a434a3f4a3d4a3b2a394a377a354a332a31495e485f485e185b485718534852184b384a18493847384618431841383738363835882f182b882718233c5f3c5e3c5b3c573c536c526b5f4b5b4b576b533b4f3b4b3b473b436a5e195f195b19571953194f394e194d1947194519431942193f193b19371933185f685e185b185a1857485618531852184738461845183f283e183b183a1837783618331832181f181e181d3c5f3c5e3c5b4c5a3c573c563c536c523b5f3b5b3b573b531b4f1b4e1b4d6a5f4a5b4a576a533a4f7a4d3a4b2a493a473a453a432a413a3f3a3b3a373a33695e685f185b48571853384f384e484d383f383e183b18391833383218317030882f182b882718233b4f3b4e3b4b3b473b434b424a4f4a4b4a474a433a3f3a3b3a373a33494e184f184b18471843183f383e183d182f182b1827182318153c5f4c5e4c5b3c574c534c524b5f4b5b4b574b534b4f3b4b3b474b434a5e195f495e195b195719531952194f194d194b194a1947394619457144193f193b19371933185f485e185b185a1857485618531852184f484e184d183f283e183b183a183778361833183218259824181f181e181d5c5f5c5b5c575c532b5f2b5b2b572b532b4f2b4b2b472b432a5f5a5e2a5b2a5a2a574a562a532a522a4f4a4e2a4b2a4a2a473a462a432a421a3f1a3e1a3d595e585f585e185b585718535852884f184b88471843183b283a183928372836183318312827282678256c5f5c5b5c576c535b5f6b5e2b5b5b572b536b527b4f2b4b7b472b436a5e195f195b19571953194f194b19471943193f293e193d1937193519331932185f685e185b185a1857485618531852184f484e184b184a1847384618431842183778361835181f181e181d6c5f5c5b5c576c536b5f6b5e5b5b4b5a5b574b566b536b527b4f4b4e7b4b3b4a7b473b467b434b425a5f2a5b5a572a537a4f2a4b7a472a431a3f1a3e1a3d695e685f185b58571853884f184b88471843283f283e283d282f282e182b182918232822182120205b4f5b4b5b475b435a4f5a4e5a4b5a475a435a427a3f7a3b7a377a33594e184f184b18471843183f183b18371833182f782e182d18155c5f5c5b5c575c532b5f5b5e2b5b2b572b532b522b4f2b4b2b472b435a5e195f595e195b195719531952194f194b19471943193f193d193b193a1937293619352134185f585e185b185a1857485618531852184f484e184b184a1847384618431842183f283e183d18259824181f181e181d6b4f6b4b6b476b436a4f6a4b6a476a43f23fe23bd237b233694e684f684b68476843a03f903b80376033502f402b30271023001f 16 65535 6 63 11 2047 16 65535
def f_63 : Nat → Nat × Nat := unpackForestF 0x18fc63b18df34418cc43f10ec437751043310bc42b109c934108c01f 4 10
set_option maxHeartbeats 0 in
theorem rc_63 : dagCheckRootsV4 m_63 g_63 ep_63 16 bds_63 (dagTraceF m_63 s_63 8 f_63) (cur_63 0) s_63 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63 : treeBlockF 0 16 (dagCheckNodeV4 m_63 g_63 ep_63 bds_63 16 (dagTraceF m_63 s_63 8 f_63) cur_63) = true := by decide +kernel
theorem nc_63 : ∀ i, 0 ≤ i → i < 16 → (dagCheckNodeV4 m_63 g_63 ep_63 bds_63 16 (dagTraceF m_63 s_63 8 f_63) cur_63) i = true := fun _ h1 h2 => treeBlockF_at nb_63 h1 h2
theorem lb_63 : LowerBin m_63 s_63 g_63 9 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_63 kn_63 sub_63 gl_63 rc_63 nc_63

def m_64 : Nat := 0xffffffff
def s_64 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_64 : Nat := 0x75f577f
def ep_64 : Nat := 0x5020000000000058002800000000070a020800000000020002200000000004505440
theorem epk_64 : ep_64 = edgePack m_64 g_64 := by decide +kernel
def bds_64 : List (Nat × List Nat × Nat × Nat) := [(m_50, s_50, 5, g_50), (m_52, s_52, 5, g_52), (m_48, s_48, 5, g_48), (m_47, s_47, 5, g_47), (m_45, s_45, 5, g_45), (m_51, s_51, 5, g_51), (m_49, s_49, 4, g_49), (m_0, s_0, 4, g_0), (m_18, s_18, 4, g_18), (m_9, s_9, 4, g_9)]
theorem kn_64 : KnownBin bds_64 := by
  intro b hb; simp only [bds_64, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_50
  · exact lb_52
  · exact lb_48
  · exact lb_47
  · exact lb_45
  · exact lb_51
  · exact lb_49
  · exact lb_0
  · exact lb_18
  · exact lb_9
theorem sub_64 : ∀ b ∈ bds_64, m_64 &&& b.1 = b.1 := by intro b hb; simp only [bds_64, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_64 : ∀ b ∈ bds_64, canon b.1 g_64 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_64, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_64 : Nat → List (Nat × Nat) := unpackCursorV4 0x11a85eb2bd406eb0db0982d2fc25e84bc0539027004e009a090ca218042048208fc21f413d067a00f401e4130326000c00178221b625780320001 0x6d1c368c4b450d278691cb47e5a370ca78652c328e19432c9f964ecb26e59339895b849c309e184b0c238610c507e383b141b8e0cc7056982a14139e098503e381b140b8e04c369e4b4e0da69293c948e1a3f0d1e868dd146a494f24a59251c9286193f0c9d864dc3266892b44938a13c909c384b14238e10c9084183f0c1d860dc3066382b44150a09cf04c281f1c0d8a05c70264b5d2dac92d54b6a21b4d0da506d18968a8b440d2f0693b62ba695960aa9a544329b614550928a17470b228551c288a094f0484b482da00716838ac1a5e0d2e9a95434a46a3a491b06558d2aa594e24a512518b284693ac89b064b8325a503a3c1b0a0b4504a281d1c0c8a0547022284c1c2020490f048285c362f0717496ba5b5925aa96d4436941b46b92eb0954349b62450caf06574329c69490ca106506425471263c2f0a17450b83859142ad414870a2385018151e098503a2815142e0e14268b48c56352d4895894944a46351a86578d2b511560ca916538929449462ca11a4d4503a3819140a8e045e6905b4025241690096b85b50142e0e14094988b440d28205110288e45a462b06d79a6b4c3560da916d3896948b4925a412d18b684b3412da028958d47c915a38ab12528928c6929141e8e0e4506a3831202e0e140369e5b4b4da512d1d168c1b430ca79452c628e19432c9f924ec926e59330c278e12c708e18431c1f8e0ec706e383314128e07c703638171c0986d3cb6967b4a25a39ed1836861a4f15258a91c34862a3f151d8a8e4546e2a3315189e518525c184f3c259e11c3086583f241d920dcb066282f14158a09c50461b4f2da5f4d28968fc3460da18693f448e5a3f251b8653f029741470ca1964fc927649372c99c04acc24e184f1c258a11c3086283f1c1d8a0dc7066382b10150a09c204c281f1c0d8a05c7026001f 15 32767 6 63 11 2047 17 131071
def f_64 : Nat → Nat × Nat := unpackForestF 0xb4a0b46d95d0a47c936094baa5daa45a85209478c5a8a568956092b7b483c5a3b5a3b563b413a56395a414439560927194b205c1947082a0826001f 5 11
set_option maxHeartbeats 0 in
theorem rc_64 : dagCheckRootsV4 m_64 g_64 ep_64 30 bds_64 (dagTraceF m_64 s_64 7 f_64) (cur_64 0) s_64 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64 : treeBlockF 0 30 (dagCheckNodeV4 m_64 g_64 ep_64 bds_64 30 (dagTraceF m_64 s_64 7 f_64) cur_64) = true := by decide +kernel
theorem nc_64 : ∀ i, 0 ≤ i → i < 30 → (dagCheckNodeV4 m_64 g_64 ep_64 bds_64 30 (dagTraceF m_64 s_64 7 f_64) cur_64) i = true := fun _ h1 h2 => treeBlockF_at nb_64 h1 h2
theorem lb_64 : LowerBin m_64 s_64 g_64 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_64 kn_64 sub_64 gl_64 rc_64 nc_64

def m_65 : Nat := 0xffff0000ffff
def s_65 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_65 : Nat := 0x17770000577f
def ep_65 : Nat := 0x400800000000000000000000006000000028000006000000020800001222000002200000144400005440
theorem epk_65 : ep_65 = edgePack m_65 g_65 := by decide +kernel
def bds_65 : List (Nat × List Nat × Nat × Nat) := [(m_34, s_34, 6, g_34), (m_38, s_38, 5, g_38), (m_26, s_26, 5, g_26), (m_39, s_39, 5, g_39), (m_48, s_48, 5, g_48), (m_41, s_41, 5, g_41), (m_58, s_58, 5, g_58), (m_20, s_20, 4, g_20), (m_0, s_0, 4, g_0)]
theorem kn_65 : KnownBin bds_65 := by
  intro b hb; simp only [bds_65, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_34
  · exact lb_38
  · exact lb_26
  · exact lb_39
  · exact lb_48
  · exact lb_41
  · exact lb_58
  · exact lb_20
  · exact lb_0
theorem sub_65 : ∀ b ∈ bds_65, m_65 &&& b.1 = b.1 := by intro b hb; simp only [bds_65, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_65 : ∀ b ∈ bds_65, canon b.1 g_65 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_65, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_65 : Nat → List (Nat × Nat) := unpackCursorV4 0xd00a18a007187006a3643339038001 0x3c5e3c5d5a5e3a5d5a4e3a493a423a41815d195969551951392d3125685e485d485c28594855685228512850382d48251c5e1c5d625d3a596a553a51595e195d594e194919421941192a2126885e485d485c28594855785228512850181d48151a50195028503a50395028505b5e435a6b565b523a5a32561a3e1a3d195a2156393e193d392e1929192219211920483d28394835283128292821281918115a4f3a4b72473a43594f194b51471943392f192b11271923484f284b48472843382f282b48272823181f281b48171813001f 12 4095 5 31 11 2047 16 65535
def f_65 : Nat → Nat × Nat := unpackForestF 0x215d191da5d151cb5a2958956149c01f 4 10
set_option maxHeartbeats 0 in
theorem rc_65 : dagCheckRootsV4 m_65 g_65 ep_65 9 bds_65 (dagTraceF m_65 s_65 7 f_65) (cur_65 0) s_65 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65 : treeBlockF 0 9 (dagCheckNodeV4 m_65 g_65 ep_65 bds_65 9 (dagTraceF m_65 s_65 7 f_65) cur_65) = true := by decide +kernel
theorem nc_65 : ∀ i, 0 ≤ i → i < 9 → (dagCheckNodeV4 m_65 g_65 ep_65 bds_65 9 (dagTraceF m_65 s_65 7 f_65) cur_65) i = true := fun _ h1 h2 => treeBlockF_at nb_65 h1 h2
theorem lb_65 : LowerBin m_65 s_65 g_65 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_65 kn_65 sub_65 gl_65 rc_65 nc_65

def g_66 : Nat := 0x1171777075f577f
def ep_66 : Nat := 0x64840080000166000005020001600600058002801060600070a020801121222020002200114144404505440
theorem epk_66 : ep_66 = edgePack fullMask g_66 := by decide +kernel
def bds_66 : List (Nat × List Nat × Nat × Nat) := [(m_27, s_27, 7, g_27), (m_65, s_65, 8, g_65), (m_24, s_24, 7, g_24), (m_62, s_62, 8, g_62), (m_61, s_61, 8, g_61), (m_56, s_56, 7, g_56), (m_63, s_63, 9, g_63), (m_60, s_60, 8, g_60), (m_64, s_64, 8, g_64), (m_55, s_55, 5, g_55), (m_25, s_25, 7, g_25), (m_32, s_32, 7, g_32), (m_29, s_29, 7, g_29), (m_57, s_57, 7, g_57), (m_40, s_40, 7, g_40), (m_0, s_0, 4, g_0), (m_54, s_54, 5, g_54), (m_38, s_38, 5, g_38), (m_46, s_46, 5, g_46), (m_42, s_42, 5, g_42), (m_53, s_53, 5, g_53), (m_36, s_36, 5, g_36), (m_28, s_28, 5, g_28), (m_44, s_44, 5, g_44), (m_43, s_43, 5, g_43), (m_19, s_19, 4, g_19), (m_34, s_34, 6, g_34), (m_37, s_37, 5, g_37)]
theorem kn_66 : KnownBin bds_66 := by
  intro b hb; simp only [bds_66, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_27
  · exact lb_65
  · exact lb_24
  · exact lb_62
  · exact lb_61
  · exact lb_56
  · exact lb_63
  · exact lb_60
  · exact lb_64
  · exact lb_55
  · exact lb_25
  · exact lb_32
  · exact lb_29
  · exact lb_57
  · exact lb_40
  · exact lb_0
  · exact lb_54
  · exact lb_38
  · exact lb_46
  · exact lb_42
  · exact lb_53
  · exact lb_36
  · exact lb_28
  · exact lb_44
  · exact lb_43
  · exact lb_19
  · exact lb_34
  · exact lb_37
theorem sub_66 : ∀ b ∈ bds_66, fullMask &&& b.1 = b.1 := by intro b hb; simp only [bds_66, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_66 : ∀ b ∈ bds_66, canon b.1 g_66 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_66, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_66_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xfa4abc6c5ed68ba5a0e1cf77720dac635e99d3293372bc2572e2cda95ee8fab9739a38c88a085f9dd6edf589e35932954a04b934f0fb32340a3ca24c8454fd0bb301ea0002f00001 0x66b781b5ac17ace06d6304e378271ac138ce09c630362f82716c138ae06c5300d378069ac034ce01a6300d2f80696c034ae01a5300d25806924032de0196b00cb380658c032be0195b00cab80654c0329e0194e00ca5806524032860594200ca08064bc0325c0192d0442b0060b819cfe06e7b05f3b81b9cc0f8fc04c760363700f198036fe01b7e00dbd812de8036ee01b7600db981edc8036de01b6e00db580eda8036ce01b6600db181ad88036921f34800da2806d10054fe02a7b0153b80a9cc054de02a6b0153380a98c0549202a48015228789100347e01a3e0151e8065fc032f60197700cb98065bc032d60196700cb18065240b2900194500ca20064fc0327c0193d00c978064b8032560192900c9180a488032420887e044330060f8110780cd6f036b582f59c0dac607b6e025b301ad78076ac2526f0153582e99c054c606a5f0152d83295c054a602a391191a8805bc0b2d60b96702cb181a57c0b2b60c95702ca98164e40326a0292f02c9587449c052460886e0442b02f5bc0dad60bd67036b180adbc056d602b67015b180ad7c056b602b57015a98169bc0b4d605a6702d3181697c0b4b605a5702d2980a8fc0547602a370151981e1b8090cc0685e01c2b00a0f80506c0582e00c1300b9fc05cfc02e7d03ebf8135ec09aee06d7303eb780f5b40dad606d6903eb380f5940dac606d6102e3f0131d80b8dc05c6c02e330171900b8bc03c560153d80a9e8054f202a770253b00a9cc054e202a670253300a994054be02a5b0152b80a94c0549202a4502cbf8125ec092ee0597302cb78065b40b2d60596902cb38065940b2c60596102caf81656c0b2ae0595302ca48065140525e0292b0149380a48c19ade06d6b05eb381b58c0b8dc04c6602e2f00f158344de02a6b05d3380a98c0d4be02a5b0652b80a94c0549205a4502cb78165ac0b2ce0596302caf81656c0b2ae0595302ca48065140525e0592b02c9380a48c178be06c5b05e2b81b14c054be02a5b0152b80a94c0549e02a4b0152380a90c0b2be0595b02cab81654c0b29e0594b02ca381650c0525e0292b0149380a48c178be06c5b05e2b81b14c054be02a5b0152b80a94c0549e02a4b0152380a90c032be0195b00cab80654c0329e0194b00ca380650c0325e0192b00c9380648c1908c0bd6f036b582f59c0dac602b6f015b580ad9c056c602b5f015ad80ad5c056a60aa6f02d3582a99c0b4c606a5f02d2d82a95c0b4a602a3f0151d80a8dc054660b96e064ab01e1b8090cc0685e01c2b00a0f80506c0582e0c0160060982e04802d6b016b501f1bc098d604c670363183317c078ba06c5b0362c83315c078aa06c530362880a9bc054d602a630152f80a9740549e02a4b0152380a90c0b2de0496b024b381658c0b2be0195d02cad8165640b2ae0195502ca98165440b29e0594b02ca381650c0525e0292b0149380a48c0fafe04d7b026bb81b5cc0bade03d6d02eb581b5a40bace03d6502eb1817584098ec04c66015bf80adec056ee02b73015b780adb4056d602b69015b380ad94056c602b61015af80ad6c056ae02b530153f81e9f8054f602a7a0153b8129d8054e602a72015378169b8054da05a6c0153580a9a8054d202a6801533816998054ca152640153180a988054c202a600152f81a978054b602a5a0152b80e958054a602a5202cbf8125ec092ee0597302cb78065b40b2d60596902cb38065940b2c60596102caf81656c0b2ae059530149f80a4ec0526e02933014978064b405256059290149380649405246029210141b00a09805ade02d6d02eb58175a405ace02d65016b180b584198de03c6d0363581b1a4198ce03c650363181b1840f8be04c5b0262b81b14c0b6de05b6d02db3816d940b6be04b5702da7816d1c034de01a6d00d33806994034c602a5f0152d80a95c054a602a4f0152580a91c0548602a3b0151b8065bc032da0196b00cb480659c032ca0196300cb080657c032b60195700ca980653c032960194700ca18064ec0326e0192f00c9580649c032460186f00c3680a19c050ca0285f0142b80a13c0508e0182f0141380607c0302e01e7f02f3f0079f40fafe04d7b026bb81b5cc03ade01d6d00eb581b5a403ace03d6500eb18075840b8fe04c7700e378071b4038ce05c6502e2f81715c056fe02b7b015bb80adcc036de01b6d00db580ada4036ce02b6500db1806d84056be02b5b015ab80ad4c0569602b470153f81e9f8054f602a7a0153b8129d8054e602a7200d378069b8034da01a6c00d358069a8054d202a6800d33806998054ca1326400d31806988034c201a600152f81a978054b602a5a0152b80e958054a602a520152580a9280548e05a4600cbd8125e8032f20197700cbb0065cc032e20196700cb3006594032be0195e00cad80655c032a60695200ca580651c0327e0193b00c9b8064cc0325e0192d00c958064a40324e0192500c91806484050fe0287700c378061b4030ce028650142f80a15c05074028370141b00a09c0504c0282500c0f80605c19ade06d6b05eb381b58c1f6de07b6e05db5812da8176ce04b6607db181ed880d6be06b5e065ad80ed68196ae03b56035a981ad48054de02a6b0153380a98c054be02a5b0152b80a94c0346e01a3500cb78065ac032ce0196300caf80656c032ae0195300c9d8064e40325e0192700c918339fc0dcf60be77037398075fc03afc01d7b026bd0075dc03aec01d7303eb90075bc03adc01d6b01eb500759c03acc01d63036b1007178056fe02b7b015bb80adcc056de02b6b015b380ad8c036be02b5d00dad806d64036ae01b5500da980ad44054fe07a7e0153d80a9e8054ee04a760153980a9c8054de06a6e0153580a9a8054ce03a660153180a988034be01a5e0152e844970034b601a5a00d2c806960034ae01a5600d2a806950034a601a520152880a9400548a05a4400cbf8065ec032ee0197300cb78065ac032ce0196300ca48064fc032760293a00c9b8064d8032660192f00c968064ac052540192902c9400649c0324c0192500c9200648c032420185e0442e00a0d80504c0cd6f036b582f59c0dac61446f05e3381b17c198ae02b6f015b580ad9c056c602b5f015ad80ad5c056a602b4b015a380a9bc0f4dc02a6b0153500a99c094cc02a630153100a97c0d4bc02a5b0152d00a95c074ac02a530152900a92c0549402a4702d230485bc152d60b967054b181a57c152b60c957034a982a52c2028e0293f0149d80a4dc052660292f00c9680a4ac0b2520292700c9280a48c052420286f0143380a17c050ae0283a0141b80a0d80504e028260141280a07c0502e0bd6f036b582f59c0dac602b6f015b580ad9c056c602b5f015ad80ad5c056a60aa6f0553582a99c154c606a5f0552d82a95c0d4a602a3f0151d80a8dc054660c9560149f01e1b8090cc0685e01c2b00a0d80b05c0182603ebf8135ec09aee06d7302eb780f5b40bad606d6902eb380f5940bac605d610263b013198056fe07b7e015bd80ade8056ee04b76015b980adc8056de05b6e015b6816db0056d602b6a015b480ada0056ce05b66015b2822d90056c602b62015b080ad80056be06b5e015ad80ad68056ae03b56015a980ad48054fe02a7b0153b80a9cc054de02a6d0153580a9a4054ce02a650153180a984054be02a5b0152b80a94c0b2fe0497b024bb8165cc0b2de0196d02cb58165a40b2ce0196502cb18165840b2be0595b02cab81654c0527e0193d0149d8164e40526e019350149980a4c40525e0292b0149380a48c110ac0283e014170079fc0bcfc01e7d03ebf8135ec09aee06d7300eb78075b403ad606d6900eb380f59403ac601d6102e3f8131dc038de01c6d00e338171940b8be05c57015bf81edf8056f602b7a015bb812dd8056e602b7200db7806db8036da01b6c00db5806da8056d202b6800db3806d98056ca08b6400db1806d88036c201b60015af81ad78056b602b5a015ab80ed58056a602b52015a580ad280568e05b460153f80a9ec054ee02a7300d378069b4034d602a6900d3380a994034c601a610152f80a96c054ae02a530152580a91c032f60497a00cbc8065dc032ec0197300cb880659c032cc0196500caf806578032b60195700ca981a548032960194700c9f8064f4032760193900c9b8064d4032660193100c978064ac0324e019230143f80a1dc030de0186d00c3380a194050be0285a0142b8221580507e0283e0141e80a0bc0505c0282200c0f80605c19cfe06e7b05f3b81b9cc03afe01d7e00ebd8135e803aee01d7600eb981f5c803ade01d6e00eb580f5a803ace01d6600eb181b588038bc02b7f03dbf00adec056f402b77025bb00adcc056e402b6f035b700adac056d402b6701db300ad8c056c401b5f00daf00ad74116b801b5b00dad006d64036b001b5700dab006d54036a801b5300da900ad44056a002a7f0153d80a9dc054e602a6f0153580a99c054c601a5f0152e80696c034b201a5700d2a80694c054a20197f00cbd8065dc032e60196f00cb580659c032c60194900c9f8064f4032760293a00c9c8164e00326e0193600c9a8064d0032660193100c978064ac052540192700c9300648c110cc0283e014170335bc0dad60bd67036b18351bc178ce06c5f0662b80adbc0f6dc02b6b015b500ad9c096cc02b63015b100ad7c0d6bc02b5b015ad00ad5c076ac02b53015a900ad2c0569402b4702da300a9bc054d602a670153180a97c054b602a570152980a92c0548e0c16f054b582e59c152c60695f054ad83255c0d2a60a94b058a380a4fc0327a0293b02c9c80a4dc0326a029330149880a4bc05256029270149180a1bc050ce0285f0142d00a15c110ac0283f0141f00a0f40505e0282e0141100a07c0502e0bd6f036b582f59c0dac602b6f015b580ad9c056c602b5f015ad80ad5c056a60aa6f0553582a99c154c606a5f0552d82a95c0d4a602a3f0151d80a8dc054660293603c370121980d0bc038560141f0160b80304c02d6f016b70135ac09ad402d67016b300b58c05ac407c6f0263581319c0d8c60cc5f01e2e81b16c0d8b20cc5701e2a81b14c0d8a205b6f025b3816d7c0b6ba05b5702daa816d3c0b68e02a6f0153580a99c054c602a5f0152e80a96c054b202a570152a80a94c054a202a4f0152580a91c0548602a3b0151b8065bc092d60196702cb180657c032ba0195700caa80a54c0329e0594b00ca381650c0b2760193700c9780a4ac0324e029230143780a19c050be0185d00c2b8061540509e028470141780a09c0503e018170173f80b9f805cfa07d7f026bd8135dc0dae607d6f01eb681b5ac0dad207d6701eb281b58c0dac205c7f0263b8171bc0b8da05c6702e3281717c0b8ae02b7b015bd00ade4056ee04b76015b980adc4056ce04b66015b280ad7c056b602b57015a980ad2c0568e01a7f0253d8069dc0b4e601a6f00d368169ac0b4d201a6700d3281698c0b4c201a5f02d2d80695c0b4a605a4b02d2500691c0b48c01a3f0151d8068dc054660597f03cbf0125ec092f404977024bb0165cc0b2e40596f03cb70165b40f2d80596b02cb50165a40b2d00596703cb3016594102c80596302cb10165840b2c00595f034af01656c072b40595701cab01654c0b2a40594b02ca501651c0b28c0293f0149f00a4ec05274029370149b00a4cc052640287f0143b80a1bc050da028670143280a17c050ae0283f0141b8060a80304e0182600c0b8060580302a0cd6f036b582f59c0dac605c6f02e3381717c0b8ae09b6f03db702edac096d409b67025b3052d8c0f6c406b5f035af032d6c076b409b5701dab01ad4c0d6a405b4b02da5016d1c0b68c02a6f0153580a99c054c602a5f0152d80a95c054a602a4b0152500a91c0b48c02a3f02d1f00a8f4032de0596b00cb381658c032be0595b00cab81654c0b2960594a00ca38165180327e0193d00c9b8064d4052660192f014958164a40324e029230149080a1bc050ce0285f0142b80a0fc0307a0183700c1a80a0bc0505a028270141280a07c0302e0cd6f036b582f59c0dac605c6f02e3381717c0b8ae0736f015b582ed9c056c606b5f015ad832d5c056a602b4b02da38069bc0b4d601a6702d3180697c0b4b601a5702d2981692c0b49401a4702d230068fc0b47601a37015198165bc0f2dc0596b024b501659c092cc0596302cb101657c0d2bc0595b01cad01655c072ac0595302ca901652c0b2940594702ca300a4fc0527c0593b02c9d0164dc0c26c02933014990221bc110ce0685f0442b80a0fc0506e0182a00c138060980302e0181600c0a82f5bc0dad60bd67036b180adbc056d602b67015b180ad7c056b602b57015a98069bc034d601a6700d3180697c034b601a5700d298068fc0347601a3700d198325580325c0786e0243301a178070ac0283e0141b00609805cfe02e7e0173e81f5fc09af604d77036b981f5bc07ada06d6b036b481f59c07aca06d63036b08171fc098ee05c6f02e3681719c0b8ca05c5f02e2b80adec056f402b79015bb812dd8056e602b71015b3812d98056ca02b5f015ad80ad5c056a602b4b015a38069fc034fc01a7b0253d0069dc034ec01a7303d390069bc034dc01a6d00d360069ac0f4d401a690553400699c034cc01a6500d3200698c0f4c401a6103d3000697c034bc01a5b01d2d00695c034ac01a530352900692c0b49401a4700d230068fc0347c01a3b0151d0068dc0346c01a33015190065fc032f60197700cb98065bc032da0196b00cb480659c032ca0196300cb080657c032b60195700ca980652c152940194700ca30064fc032760193700c9980a1fc050ee0286f0143680a19c050ca0285f0142d00a15c110ac0283f0141b8060bc0305c0282d00c0f806078030240cd6f036b582f59c0dac605c6f02e3381717c0b8ae0336f015b582ed9c056c606b5f015ad832d5c056a602b4b02da38069bc034dc01a6b0253500699c034cc01a6303d3100697c034bc01a5b01d2d00695c034ac01a530352900692c0b49401a4700d230068fc0347c01a3b0551d0068dc0346c01a33015190065bc032d60196700cb180657c032b60195700ca980652c152940194700ca30064fc032760193700c998221bc110ce0685f0542d02215c110ac0283f0141b8060bc0305c0582d00c0f806078030240bd6f036b582f59c0dac602b6f015b580ad9c056c602b5f015ad80ad5c056a601a6f02d3580699c0b4c601a5f02d2d80695c0b4a601a3f0151d8068dc054660192603c370121980d0bc038560141f00a0d80b05d1c45f0362dc6115c0d8a71635f8a1adc40d5e1c6a606b4f861a5c28d1c0d6870425f8192dc0895df84a606a4f7b125bbc91c0d486e623f7091db648dd9a466c015f5f0adad855d682a60694f580a5aa851c0d286a113f4b89d9e84dcdc2666312f3009594049c9e2464a05f2482d8fc15c7a0a60684f1e02589c11c0d0861c03f0d81d8640dc2c0660f02f0701582809c120460501f0200d80805c020260003f 18 262143 7 127 11 2047 21 2097151
def cc_66_1 : Nat → List (Nat × Nat) := unpackCursorV4 0x8461982422801237d62b7a82e73f696f04f6628e639295ee4b5a04e5742c50d674be4f47d41445383b5903882d3592f325342bb6a265561dd8818b5215e2d11f3f0fd220ca3309d2d06c3102b410002b 0x3c5f0f16c3c570f14c2a5f0a96c2a570a94c2a4f0a92c2a470a90c795f1256c49571e54c394f0e52c39470e50c292f0a4ac29270a48c48561f5bc4d6b1359c6d630adbc2b6b0ad9c2b630ad7c2b5b0ad5c2b531e9bc4a6b1299c7a631a97caa5b2a95c6a530a8fc2a3b0a8dc2a3312598786e1a178685c0e15be0540a0f82836160b818260f5bc3d6b0f59c3d630adbc2b6b0ad9c2b630ad7c2b5b0ad5c2b532a9bcaa6b2a99caa630e97c3a5b0e95c3a530a8fc2a3b0a8dc2a332e598395e0a4d8a9261e1b848660e158283e0a0d8582e060983d6f0f59c3d630f19c3c660f17c3c5e1e9bc2a6b1299c2a630e97c2a5b0e95c2a533e93c9a4d0a92c2a493e91c9a450a90c2a41165bc496b1259c59630e57c395b0e55c39531653c194d1652c59491651c19451650c59410a4bc592b1649c29230b9e83d7e135e83d761f5c83d6e0f5b43d6c275a83d69275a03d660f5943d644b5883d615b5804c7a0f1d83c6d0f1a43c650f1847a7e0a9c85a6e0a9b42a5d0a9642a550a944196d165a4196516584195d0e56419551654448762219888640e178384e0a09858160f5fc3d7e0f5ec4d7a0f5dc3d760f5cc7d720f5bc3d6e0f5b43d6c0f5ac5d6a0f5a7b5680f59c3d660f5943d640f58c5d620f5845d600f1fc3c7b131e83c770f1d83c730f1bc3c6d0f1ac5c6a0f1a46c680f19c3c660f1943c640f18c3c6112dd84b660ed785b5c1e9fc2a7b129dc2a73169bc5a6d0a9ac2a691699fa2650a98c2a610e97f625d0a96c2a590e95c3a550a94c2a510e93c2a4b0e91c2a43165fc497b125dc5973165bc196d165ac59691659c19651658c59610e57c195d0e56c39590e55c19550e54c59510e53c394b0e51c39430a4bc592b1649c2923121d8586622190385e0e1388826160583d6f0b5ac3d670f58c2c6f0b1b82c6b0b1a83c670f1982c630b1883c5f0f1782c570b14c2c521edbc4b670ed7c3b573ed3c5b4d3ed1c5b450a9bc2a6b0a99c2a630a97c2a5b0a95c2a530a93c2a4d0a92c2a490a91c2a450a90c2a410a8ec2a371e5bc496b1259c79630e57c395b0e55c39533e53c194d2a52c59493e51c19452a50c59412a4ecf9370a4bc292b0a49c29230a1bc28670a17c28570a13c284d0a11c28450a0bc282a0a09c28260a07c28170b9fc2e7e0b9f43d7f0f5f83d7b135e83d770f5d83d731f5c83d6f0f5b83d6d0f5b03d6b1f5a83d69e15a03d670f5983d650f5903d631f5883d611f5803c7f0f1ec4c7a0f1dc3c760f1cc3c6f0f1b43c6b1b1a83c691b1a03c670f1983c650f1903c630f1847b7f12ddc7b6f16db47b6716d943b5f16d743b570ed543b4f0ed1c2a7b0a9e82a790a9dc4a760a9cc2a710a99c4a660a9942a5f0e9782a5dd49702a5b0a9642a570a9542a530a9482a510a9402a4f0a92c2a470a90c2a3b0a8dc797f125ec49771e5cc796f065b4796b165a4796706594796316584395f06574395b0e564395706554395316544394f0e52c39470e50ca93b3e4dc292f0a4ac29270a48c287f0a1e82877121d8286f0a1b4286a0a19c78660a19488640a17c385e0a174284f0e1382842220f828320a0bc282a0a09c28260a07c281a0a05c88160f5b43d690f5943d611f1f84c7a131d87c72171b85c6d171b05c6a271a49c68171989c654f1905c62171845c600b1784b7612d987a7e0a9c82a6d0a9a42a650a9842a5a0e9583a460a914196d165a4196516584194d165241945165042d6f0b5b82d6d0f1bc3c6b0f19c3c630f17c3c5d0f16c6c5a0f15c3c560f1543c531edbc7b6d12dac4b6a12d9c4b6626d943b630ed7c3b5d12d6c4b5a0ed5c3b560ed543b540ed4c2b4f0ad1c2b431e9bc4a671e97c7a570e93c3a47268fc9a371e5bc496b1259c79631e57c795b1e55c79530e53c394b0e51c3943264fc993b264dc9933264ac99270a1bc28670a17c285d0a16828571e15828550a13c28470a0fc28370a07c28170f5bc3d6b0f59c3d634f1bc7c6e271ac4c6a2f19c4c662718c7c620b17c2c5e0b15c2c530b14b636f2ed9c3b5f0ed5c9b4f16d349b4716d142a6fd49b82a6b0a99c2a630a9882a5f0a96c2a5a0a95c3a560a94c2a470e9182a450a8ec2a37bc5bca96b2e59ca9630e57c395b0e55c39532653c194d2a52c59494251c19452650c59412a4eec1370a4bc292b0a49c29230a1bc28670a17c28570a13c284d0a11c28450a0bc282d0a09c28250a07c28170f5bc3d6b0f59c3d635adbc7b6e2edac4b6a2ed9c4b665ad8c7b620ed7c3b5e0a9bc2a6b0a99c2a630a97c2a5b0a95c2a3b0a8e4596f165ac59671658c395f0e56c39570e54c593f064f4593b164e45937064d45933164c4292f0a4ac29270a48c28260f9fc3e7e0f9ec4e7a0f9dc3e760f9cc7e720f5fc3d7b1b5e83d770f5d83d73171fc5c7e171ec4c7a171dc4c76171cc7c720f1bc3c6e171b45c6c0f1ac3c6a0f1a43c680f19c3c660f1943c640f18c3c621718734600f17c3c5e0f16c3c5a0f1643c580f15c3c560f14c3c52171446c500ad382a7f0a9ec2a770a9cc2a6f0a9b42a6b0a9a42a670a9942a630a9842a5f0a96c2a570a94c2a39165fc597b165dc59730e5bc196d0e5ac39690e59c19650e58c59610e57c395b0e55c39531653c194d1652c59491651c19451650c59410a4bc292b0a49c2923221d8386e0e178584e221302826160583d6f0f5ac3d670f58c3c6f0f1b83c6b0f1a83c670f1985c63171881c5f071781c570714c1c5216dbc4b670ed7c3b5716d3c5b4d16d1c5b451e9bc2a6b1299c2a630e97c2a5b0e95c2a533e93c9a4d0a92c2a493e91c9a450a90c2a410a8ec5a37065bc196b0659c19630657c195b0655c19530653c194d0652c19490651c19450650c1941064ec1937064bc192b0649c19231e1bc48670e17c18571a13c684d0611c18450a0bc28270607c181a0605c18160b9f45e790b9d42e710f5f83d7d0f5f09d7a0f5e49d780f5d83d750f5d11d720f5c51d700f5b84d6a0f5987d620f1f43c790f1d43c71131a83c6616df45b7516d743b55069f81a7d1e9b82a620a9742a590a9542a51065f41979065d41971065741959065541951064b419250a1f4287a221d82875221d0286a12198385e0a174384e0a108883e0a0c8282a0a098181a060585e7e079f41d6d0f5a43d65075847c7e131e84c761f1c81c6e071b41c6c071a89c69271a01c66431953c64071881c61071802c5e0b1481b6d16d945b4d16d147a7e0a9c81a6d0a9a42a65069842a5a0e9583a460a914497a065e41976065c4196606594195e0e548194d06524194506504186d0a194284d0a114282d0a0941e7f179f81e7d0f5fc3d7e0f5ec4d7a0f5dc3d760f5cc7d72075bc1d6e075b41d6c075ac1d6a0f5a715680759c1d660f5943d640758c1d62075841d600f1fc3c7b131e83c770f1d83c73071bc1c6d071ac1c6a0f1a46c680719c1c660f1943c640718c1c6116dfc4b7706dbc1b6d06d9c5b650ed7c5b5d0ed5c3b550ed3c3b471e9fc2a7b129dc2a73069bc1a6d069ac2a690699f02650698c1a610e97ef25d0a96c2a590e95c3a550a94c2a510e93c2a4b0e91c2a430a8ec5a37065ec497a065e41977065d81973065c419670659819650657c195e06574195c0656c19590655c19550654c39520654459500653c194e0652c19470650c3942064ec1937064bc192b0649c19231e1fc487a121dc4876061bc186d061a8186706198886522190385f0e178685d0e13c384e0e108883e2a0c8282f2a0a8282722098181f060681817060583d6f0f5ac3d670f58cfb6f1edb8bb6b12da8bb6712d98fb631ed881b5f06d78fa6f0a9acba670a98c3a5f0a96c3a570a94cfa3f268f42a3b0a8e4fa37268d42a330a8c4196f065ac19670658c195f0656c1957064ec1939064bc192b0649c19230605818141f5f84d7a135d87d720b5b81c7e131e81c761f1c81c6e0f1a81c660f1881c5e071741c5c271681c594f1601c56071541c54271481c51271401b4e269f82a720a9a83a660e9582a55069382a4d269301a49069141a420a9042a40065741959065541951064e4292a064983e7e139e83e761f9c86d7a0f5d87b7e12de84b761edc83b6e46db51b6c0eda83b690eda03b660ed943b640ed889b6126d803b5e0ed683b560ed48fa7e0a9c83a6e0a9b49a6c0a9a42a650a9882a610a9801a36068d4196d065a41965065841939064b41925221d8386e0e178883e220f02826060583e7f0f9f83e7b139e83e770f9d83e731f9c83d7f0f5ec6d7a0f5dc3d760f5cc1c7f071f81c7b131e81c77071d81c731f1c81c6f071b81c6d071b01c6b0f1a81c690f1a01c67071981c65071901c630f1881c61b51801c5f071781c5b0f1681c590f1601c57071581c530f1481c511b1401b4e3e9fc2a7b2e9dc2a730e9bec26d0a9ac2a690e99c3a650a98c2a610e97c2a5b0e95c2a530693eb24d0692c1a490691c1a450690c2a41065fc197b065dc1973065bc196d065ac19690659c19650658c19610657c195b0655c1953064e4192f064ac592a0649c19260648c88760e1b8385e06138884c220981816060503d6f0f5ac3d670f58c5c6f1719c3c5f0f15c2b6f0adac2b670ad8c2b5f0ad6c2b570ad4c2b4b0ad1cfa6f1e9b8ba6b129a8ba6712998fa631e9881a5f069781a570694c1a521692c5a4a1691c5a460a8fc2a3e0a8ec2a3a0a8dc2a360a8cc2a32065bc196b0659c19630657c195b0655c19530652c1947064fc193b064dc1933064bc192d064ac19290649c19250648c19210a1bc28670a17c18572213828420a0fc283a0a0dc28360a0bc282d060a8182706098182506090181f060681817060583e7f0f9f83e7b139e83e770f9d83e731f9c83d7f0f5ec6d7a0f5dc3d760f5cc5c7f171dc3c6f171b43c670f1943c5f0f15c1b7f06df81b7b12de81b7706dd81b731edc81b6f06db81b6d06db01b6b0eda81b690eda01b6706d981b6506d901b630ed881b61a4d801b5f06d781b5b0ed681b5706d581b530ed481b4b16d281b4706d182a7f0a9ec2a770a9cc2a6f0a9b42a6b0a9a42a670a9942a630a9842a5f0a96c2a570a94c2a4b0a91c1a3f068f82a3d065fc197b065dc1973065bc196d065ac19690659c19650658c19610657c195b0655c19530652ca94a0651c1946064fc193e064f4192f064b8192b064a419230a48819210a1fc287a0a1dc88760a1bc386e0a1b4285f0e1782852221382842060fc283d060e81837060d81835060d0282f0a0a828270a098181f060681817060583d6f0f5b83d6b135a83d670f5983d631f5883c6f0f1ac6c6a0f19c3c660f18f936f2ed9c3b5f16d743b570ed543b4f0ed1f726f0a9acba670a98c3a5fd09742a5b0a9643a570e9542a530a9443a4f0a92c3a470a90c2a3bc88dee16f2a5acb9672a58c395f06574395b0e564395706554395316544394f0e52c39470e50ca93ba84dc292f2a4ae81270a48c886f321a8886722198385f0e178685d0e13c384e0e108883e320c8282f320a8282722098881f320688817220582d6b0b5a49c6f0f1b46c6b1b1a49c670f1946c631b1847c5f1316c4c571b14c2a670a9942a5b0a95c2a530a93c2a4b0a91c2a43265bc196d165ac59692659c19651658c59611e57c495b1255c59531a53c594b3251c59430a4bc292b0a49c29231e17888460b9fc2e7e0b9f47d7f135ec4d771b5cc7d6f0f5b46d6b1b5a47d670f5946d631b5847b7e12dd87b6e1edb07b6698d906b5e0ed582a7b0a9e82a790a9dc4a760a9cc2a710a99c4a660a9942a5f0a96c2a570a94c2a390a8d4797f125ec4977165cc796f065b4596b165a4796706594596316584695f1656cc9571654c5939064d4292f0a4ac29270a48c787e221587d7e1f5f47d7c135e84d76275d49d741b5b8cd6a275986d621edf87b7d1adb83b6a0ed986b6212d784b5d12d702a7d0a9d42a393e5745959265545951064f45939064d459310a4b4992522198cd6f1b5acbd671b58c9c6f1f1b8bc6b131a89c671319a44631f1886c5f1b178cc5b0f1689c570f1586c531b1482a6f0a9ac2a670a98c2a5f0a96c2a570a94e116f165acb9671658c695f1656cc9571654d094f06534594b16524994706514594316504292f0a4b4292b0a49de1250a48c8856175ac5d69331bc3c6d1b1ac6c693319c3c651b18c6c611f17c4c5b1315c6c533e9bc9a6d0a9ac2a693e99c9a650a98c2a611e97c2a5b1295c2a531a93c2a4b3291c2a430659c19650656c19570654c194f0652c19470650c192f064ac19270648c785e221185e7e079f41d6d1b5a43d65075847c7e131e84c761f1c81c6e071b41c6c071a90c69571a01c66271949c64071881c61071806c5e0f1683c561b1481a6d0a9a42a6506984497a065e41976065c4196606594195e16548194e06534194c06524194516508194116500192d064948856079fc5e7e079f47d7f135ec4d771b5cc1d6f075b41d6b1b5a41d670f5941d63075847b7e12dd81b6e06db01b6688d906b5e0ed587a7f0a9ec4a770a9cc1a6f069b41a6b0a9a41a67269941a63069846a5f0a96cca570a94c2a39848d4197b125e81979065dc1976065cc19710659c196606594195f06578195b0655c1953165481939064d4192f064ac19270648c787e22158cd6f1b5acbd671b58c2b6f0adac2b670ad8c2b5f0ad6c2b570ad4c9a6f1e9b89a6b129a89a67129989a631e9886a5f1a9789a5b0e9689a570e9586a531a9482a3b0a8e8196f065ac19670658c195f0656c19570654c193f064ec1933064bc192d 20 1048575 8 255 11 2047 18 262143
def cc_66_2 : Nat → List (Nat × Nat) := unpackCursorV4 0x9f16f9539e9282b8e5438ba2b88b2f8464581b2b7d843738a0691a75eca55aa4256b3f508634a7614495e420293c0603437d2f94a2d8212885025b2d1fe5d1d12d1a1301732e1145f0c74d04a7d0004a 0x7ade0f5ac0eb383d63098de131ac263384c63078be0f16c1e2b83c53096de0adac25b382b63076be0ad6c1dab82b532569e0ad2c2da382b43034de069b8253584a6a034ce069980d3181a62034be069781d2d83a5a034ae069580d2981a522949e1692c2d2505a470b48c5290c151f82a3e0b476168e81d1b83a36054660a8c80cb78196b032ce0658c0caf8195b032ae0654c0ca78194b1d2940651c0ca3019430327e064f80c9d81937032660a4c80c978192e0325a064ac0c94819270324a0648c1c910192107240121bc143584867050c60e17c142d83857050a62e13c142585847050860a0fc141d82837050662e0bc44168282b1704e2209414118181f030360605c0c0983e7f07cfc139f41ebf83d7e07afa0f5bc1eb703d6b07ad20f58c26b103d61078fe171f41e3d83c77078ea0f1cc263784c6b098ce1318c1e2f83c5b078ae0f14c0dbf81b7e036fa06df00dbd83b7a036f20ede00dbb81b76036ea06dd00db983b72036e378dc00db781b6e036d612da80db381b66036c612d880daf81b5e036b60ed680dab81b56036a60ed480da781b4b0b69406d1c0da301b43074fe269f4153d82a79074ee0e9d4153982a71094de0a9ac253382a63074be0a96c1d2b82a532549e0a92c2d2382a430347e068f82d1e8197f032fc065f40cbe0197b032f2065dc0cba81973072e4065c42cb80196f032d60659c0cb18195f032b60655c0ca98194f032963a5280ca38194603286064fc0c9f0193d0325e064b80c9581929032460a4880c908387f110fa0a1ec1c3b83875050e6121bc143584867050c60e17c342e8285b070ae0e15414298b84f050961611c14218183f1107a060ec0c1b81835030660a0bc141582827050460607c0c0d8181703026135bc26b584d6709ac612dbc15b584b67056c61ad7c15ad89b57056a6069bc0d3704a6b094d40699c0d3301a63034c41a97c352f09a5b074b42695c1d2b06a530d4a4168ec2d1d0196f032d60659c0cb18195f032b60655c0ca98193f03276064cc0c978192d09cfe139ec273b84e7309afc131d8363703c66036fe06df80dbd84b7a036f212de00dbb81b76036e612dc80db887b70036de06db80db583b6a036ce06d980db186b620369370d200da281b44094fe0a9ec253b82a730d4de0a9ac4d3382a6305492269140d1f81a3e0b47a065fc0cbd81977032e6065bc0cb581967032c6065242ca40194503288064fc0c9f0193d0325e064b80c9581929032460a4880c9087d6f09ad61359c36b187b6f056d612d9c15b186b5f056b626d5c15a981a6f034dc069ac0d3501a67034cc1698c2d3106a5f0d4bc2696c1d2d09a57074ac1a94c352905a3b0b474065bc0cb581967032c60657c0cad81957032a6064fc0c9d819330325e064b43eb784d6b09ace1b58c2db782b6b096ce16d8c35af89b5b136ae1ad4c0d3781a6e034d6069a40d3381a630f4c4069843d3001a5f034b60e9680d2b81a56034a6068ec0d1c8196f032d60659c0cb18195f032b60655c0ca98193f0327c064ec0c9c819330b264064c40c978192e0325a1f9fc273d84e770dce6135d82e3f06c6e078cc06dfc0dbf01b7b096f406de425bc01b77036ec06dcc3db901b710f6e006dbc0db701b6b076d406d9c0db301b630d6c406d26d1a401b45036881e9fc153d84a77054e61a9bc153589a67054c60a924152409a45b2488068fc0d1f05a3d032fe065ec0cbb81973032de065ac0cb38196303292165200ca2819440327e064f80c9e8192f0325c064ac0c948192305244064841eb783d6b07ace0f58c4db782b6b136ce0ad8c1daf82b5b076ae0ad4c4d3787a6e134d6129a84d3384a66134c61e9880d2f81a5e074b60e9680d2b81a56034a6069482d1d85a3a032de065ac0cb381963032be0656c0cab819530327e064ec0c998192f0325a0f9fc1f3d83e7707ce60f5b83e3f04c76078cc06dfc0dbf01b7b096f406ddc0dbb01b730f6e406dbc0db701b6b076d406da41db401b67036cc06d8c1db101b610d6c006d26b9a401b4503688269fc153d89a77054e60e9bc153583a67054c60a9244d2281a3f0347c168f40cbf8197b032ee065cc0cb78196b032ce0658c0ca4859480328a065100c9f8193e0327a064bc0c970192b032520648c14910192105cfe0b9f8173e87d7f09af6135dc36b987d6f07ada1b5ac36b487d6707aca1b58c36b085c7f098f6131dc3e3985c6f0b8da1f1ac2e3385c650f8c61717c4e2d85c570d8a606dfc0dbf01b7b096f406de425bc01b77036ec06dcc3db901b710f6e006dbc0db701b6d036d806dac25b501b69096d006d9c0db301b65036c806d8c2db101b610b6c006d7c0daf01b5b076b406d5c0dab01b530d6a406d3c0da585b4a0368e06d180da182a7b054f40a9e4153b84a76054e60a9c4153384a66054ca0a97c152d82a57054a60a93c152582a4705486068fc0d1f02a3d032fe065ec0cbb81973032de065b40cb58796a032d2165a00cb381966032ca065900cb181961032be0656c0cab819530329e0652c4ca5019470328c0650c0c9f8193e0327a064bc0c970192b032520648c149101921050fe0a1ec143b82873050de0a1b4143582867050ca0a18c142f8285b050ae0a14c14278284b0508e0a10c0c1f8283d03076060dc0c1a818330505e0a0ac1413828230303e0606c0c0b8181305cfe0b9f8173e84d7f07afa135ec26bc84d7707aea135cc36b884d6f09ad61359c26b184c7f0b8fa131ec263b84c75098e6131bc263584c67098c61717c4e2d85c570d8a606dfc0dbf01b7d036f806dec25bd01b79096f006ddc0dbb01b75036e806dcc25b901b710b6e006dbc0db701b6b096d406da425b401b67036cc06d8c25b101b610f6c006d7c0daf01b5b076b406d5c0dab01b530d6a406d3c0da585b4a0368e06d180da182a7f094fc0a9f4153784a6e054d60a9a4153182a62054c20a97c152d82a5a054ae26958152982a4f054960a928152385a4605486068fc0d1f02a3d032fe065f80cbe8197c032f6065e40cbb81975032e6125c80cb885970032de065ac0cb381963032be0656c0cab819530329e0652c4ca5019470328c0650c0c9f8193e0327a064bc0c970192b032520648c149101921052400a1fc143e8287b050ee0a1d414398286f050d60a19c14318285f050b60a15c14298284f050960a11c14218183f0507a060ec0c1b81835030660a0bc14168282b0504e0a09414118181f030360605c0c0983e7f07cfc0f9ec273d03e7707cec0f9cc3f3903d7f07af60f5dc1eb982d6f05adc0b5b42e3f89c7b0b8ee271cc1e3785c6d078d60f19c1e3283c63078be0f16c1e2b83c53036fe06df80dbd84b7a036ee06dd80db987b72036de06db80db681b6c036d60eda80db483b68036ce06d980db281b64036c60ed880db085b60036be06d780dad83b5a036b20ed600dab81b56036a60ed480da886b500369e06d2c2da501b470368c06d0c153f82a7b054f40a9dc4d3b02a73054de0e9b8153682a5f074bc0a96c152c82a53054a40a944152782a4b054940a91c2d2302a430347e068f8151e8197f032f6065dc0cb98196f032dc065b40cb60196b032d20659c0cb281963072c4065842cb00195f032b60655c0ca98194f03296265280ca38194603286064fc0c9f0193d0325e064b80c9581929032460a4880c9082920050fe0a1ec143b82873050de0a1b4143582867050ca0a18c142f8285b050ae0a14c14278284b0508e0a10c0c1f8283d03076060dc0c1a818330505e0a0ac1413828230303e0606c0c0b8181325cfe1b9ec973b86e730f8fc131d8363703c66036fe06df80dbd84b7a036ee06dd80db987b72036de06db80db583b6a036ce06d980db186b62036b216d600da485b480368a06d10153f82a7b054ee0a9cc153782a6b054ce0a98c152c82a450347e068f8151e8197f032f6065dc0cb98196f032d60659c0cb1819490b290065140ca20193f0327c064f40c978192e03256064a40c9182922032420a48076b786d6b1dace1b58c2e3785c670b8be1715c0db781b6b036ce06d8c0daf81b5b036ae06d4c0da581b47134de0a9ac4d3382a630d4be0a96c4d2b82a53054961691c0d1f81a3e0b47a165bc2cb5859670b2c61657c2cad859570b2a60651c0ca3019450327e064f82c9e8292f0525c164ac2c9382923052442a1bc54338685f150ae060fc441e818370306a0a0bc14138581f0b02f7d5bc36b5dd5670dac6171beda3585c67b08c61717eb22d85c570d8a606dbc0db701b6b096d406d9c0db301b630f6c406d7c0daf01b5b076b406d5c0dab01b530d6a406d3c0da585b4a0368e06d180da1d526f054d75099c153186a5f054b74c95c1529d224f054961691c152181a3f0347c168f40cb78196b032ce0658c0caf8195b032ae0654c0ca78194ba22940651c0ca3019430327e064f80c9e8192f0325c064ac0c9481923052440648658378286b800ce0a18c342f8285b500ae0a14ce8278284b0b08e0a10c0c1f8883d03076060dc0c1a818330505e0a0ac1413828230303e0606c0c0b818131dade1b5ac76b386d630b8de171ac2e3385c630b8be1716c2e2b85c53056de0adac15b382b63056be0ad6c15ab82b530569e0ad2c15a382b43034de169ac0d3385a63034be1696c0d2b85a530349e1692c0d2385a430347e068f4151d82a3a0346e0a8d80d1a8296f0f2dc0a5ac14b502967092cc0a58c14b10295f0d2bc0a56c14ad02957072ac0a54c14a90294f052960a52814a38594605286064fc0c9f0193d0525e164b814968286f050d60a19c14318285f050b60a15c14298284f050960a11c14218283f050760a0dc14198282f030560609c14118281f0503a0a06c140b82815050261f5fc26bd84d770dae61f5bc1eb686d6b0dad21f59c1eb286d630dac2171fc2e3f04c7b098f4131dc263b05c730f8e4171bc2e3705c6d0b8d8171ac3e3505c69178d01719c2e3305c650b8c81718c3e3105c610f8c01717c2e2f05c5b078b41715c1e2b05c530d8a40ad38153f82a7b054ee0a9cc153782a6d054d60a9a4153382a65054c60a984152f82a5b054ae0a94c151c8597f092f6125dc2cb98596f032da165ac2cb485967032ca1658c2cb08595f0b2b61655c2ca98594f0329a1652c2ca4859470328a1650c2ca08292f052560a49c149184876090cc16138442603d6d0dad20f59436b087b7e096f412dd83db907b6e0f6da1edb03db509b69136d01ed985db28bb640f6c41ed843db006b5e076b40ed5835a907a7e054e40a9b4153482a65054c2068d80d1a8196d032d2065940cb0819390325a06494243b048660fafe135ec26bb86d730fade0f5b436b586d690face0f59436b186d61038fe071f80e3d84c7a038ee071d80e3987c72038de071b80e3681c6c038d61f1a80e348bc68038ce071980e3281c64038c61f1880e3087c60038be071780e2d83c5a038ae071580e2986c520369c1e9fc153d84a77054e61e9bc3d3682a6b054d21e99c5d3282a63054c21a97c152d8ca57054a60693e692681a4b034920691c0d2281a4305482065fc0cbd81977032e6065bc0cb68196b032d20659c0cb281963032c20657c0cad81957032a6064e40c978192b0b2540649c0c9301923090ec121980c270884c0fafe135ec26bb86d730fade0f5b436b586d690face0f59436b186d610b8fe131dc2e3785c6d0b8ce171942e2f85c57036fe06df80dbd84b7a036ee06dd80db987b72036de06db80db681b6c036d61eda80db48bb68036ce06d980db281b64036c61ed880db087b60036be06d780dad83b5a036ae06d580da986b520369616d280da381b46054fe0a9ec153b82a73054de0a9b4153582a69054ce0a994153182a61054be0a96c152b82a53054960a91c0d1f81a3e0547a065fc0cbd81977032e6065bc0cb68196b032d20659c0cb281963032c20657c0cad81957032a60652c54a5019470328c064fc0c9f0193d0325e064b80c9581929032460a4880c908287a050ee121d8143384866050ca0a17c142b8884e05084060fc141e818370306a0a0bc14138181f0302e1f1bc263584c670d8c61f17c1e2e86c5b0d8b21f15c1e2a86c530d8a21edbc25b387b5f0b6ba1ed5c2daa86b4f1968e1e9bc153584a67054c61e97c3d2e82a5b054b21e95c5d2a82a53054a21a93c15258ca47054860a8ee711b8796f092d61259c3cb18795f032ba1e56c2cac87957032aa1e54c2ca88694f152963251c34a18a93b9826e0a4bc5495cb12705246121a8243384866090ae12158242a8684f1108e220f85c190282f0504e2207c440b84d6f09ad61359c26b182b6f056d60ad9c15b182b5f056b60ad5c15a984a6f094d61299c253186a5f154b62a95c352982a3f054760a8dc15198496e192ac12198342f038560507c0a0d82c170182605ade0b5b816b382d6305ac4131bc263584c67098c62717c1e2e86c5b0d8b23315c1e2a86c530d8a212dbc25b389b5f0b6ba26d5c2daa86b4f1968e0a9bc153582a6a054ce12998153182a57094ac0a954152786a4e054960a91c152182a42054760a8dc24b78496b092ce1258c4caf8195d152b61656484ab81955132a61654434a78a94b1928e1a50c549dc41370525e0a4ac149382923050de0a19c142f8285d050ae0a15414278284a0508e2211814178282d0504e0a094140f8281709ade135ac26b384d63096de12db835af86b5e196b60ed6865ab83b560d6a61ad48153782a6b054ce0a97c152d82a57054a60a8ec151c8496f092d61259c24b18595f0b2b61655c2ca98593f0327a164ec2c9c859370326a164cc2c988292f052560a49c14918486e110ac135fc1ebe84d7b09af2135dc1eba84d730dae2135bc26b584d6709ac6131fc263f05c7d0b8f8131ec263d04c79098f0131dc263b04c75098e8131cc263905c718e8e0131bc263704c6b098d41319c263304c63098c41717c2e2f05c5b078b41715c1e2b05c530d8a40ad38153f82a7d054f60a9e4153b82a75054e60a9c4153782a6b054ce0a98c152f82a5b054ae0a94c151c8497f032fa125ec24bc84977032ea125cc2cb88496f092d61259c24b18595f0b2b61655c2ca98594f0329a1652c2ca4859470328a1650c2ca08292f052560a49c14918487e090dc2215826b784d6b09ace1358c0db781b6e0d6be1ad7865ad83b5a196ae0ed5835a986b52094de0a9ac253382a630d4be0a96c652b82a531f47e268f4151d82a391f46e268d4151982a31032de065ac0cb38195f032b60655c0ca98193b03272064bc0c958192703246121b8442b02e7e07ada1b5a41eb286d61038fc131e80e3b04c72038dc071b40e3609c6a038d26f1a00e3301c65038c8271880e3089c60038bc0f1680e2b06c520369c0a9e8253b04a66054ca1a978152901a4e0549a269300d2481a45034840a90415200196d032d2065940cb0819390525406498442b03d7d09af20f5d436b884b7e236fa46df025bd04b79096f012dd825ba84b74096e426dc44db804b6e096d412d9825b106b5e076b40ed5835a904a7e054fa269f0153c82a75054e40a9c4153804a6e054c4068d80d1a8197d032f2065d40cb8819390325a06494243f0486e110ac135fc1ebe84d7b09af2135dc1eba84d730dae2135bc26b584d6709ac6071fc0e3f01c7d038f8071ec263d01c79098f0071dc0e3b01c75038e8071cc263901c718a8e0071bc0e3701c6b098d40719c0e3301c63098c40717c0e2f01c5b078b40715c0e2b01c530d8a406d38253fc427d054f60a9e4253b84a75054e60a9c4253782a6b094ce0a98c352f82a5b194ae0a94c0d27c324d03496069240d2381a45034860a9040cbf8197d032f6065e40cbb81975032e6065c40cb78196b032ce0658c0caf8195b032ae0654c0c9c8192f03256164a80c938192603246121f824370885609ade135ac26b384d63098de1319c2e2f85c57056de0adac15b382b63056be0ad6c15ab82b53056960ad1c0d3781a6e034ce0698c0d3106a5f0d4bc3296c1d2d0ca57074ac1a94c352905a4b0b4941691c2d2302a3f0547c0a8ec151d02a370546c0a8cc15190196f032d60659c0cb18195f032b60655c0ca98194b0328e064fc0c9d8193703266064bc0c968192b032520649c0c9281923032420a1bc0c338285f050ae0a0fc141b8282f0505a0609c0c128181f0302e135fc1ebe84d7b09af2135dc1eba84d730dae2135bc26b584d6709ac6131fc2e3e84c77098ea131bc263385c5f0b8ae06dfc0dbf01b7d036f806dec25bd01b79096f006ddc0dbb01b75036e806dcc25b901b71826e006dbc0db701b6b096d406d9c0db301b63096c406d7c0daf01b5b076b406d5c0dab01b530d6a406d2c2da501b470368c0a9fc153e82a7b054f20a9dc153a82a73054e20a9bc153582a67054c60a97c152d82a57054a60a92c152381a3f0347c0a8f40cbf8197d032f6065e40cbb81975032e6065c40cb78196b032ce0658c0caf8195b032ae0654c0ca58a94a0328e065180c9f8193e0327a064bc0c970192b032520648c149101921050fe121f8143e8286f090dc0a188142f8285a050ae221580c1f8283d0306e060d41417828270303e0605c263783c6d098d6131a4263383c65098c61b184262f84c5b098ae1314c25b785b6d096ce12d9425af84b570d69e32d1c2537c826d054d60a9a4253384a65054c60a984252f82a5b094ae0a94c352782a4b1948e0a90c151dc6237092de065b424b584969092ce0659424b185961092be1256c24ab849530d29e2a52c64a38694315277084dc14978a92b8024e0a48c24378486e0f0da1217c242f048520d09e2e1284423888460505e0a09c440f88817 20 1048575 8 255 11 2047 19 524287
def cc_66_3 : Nat → List (Nat × Nat) := unpackCursorV4 0x929408e2478a1418534e8074c7da2d79d3d7722b7333f7082b6c5436972e65a3d62f2b6012e5cb365ab20515964a66f40a9c3dd2d3a03d3752b3482d3093f2dc2d29f3d23e6119ca20fba10986300098 0x3e7e04e7d03d7e03d7d03d6e03d6904d6203d6105c7d03c7503b7e11b7d11b7c03b7a03b7903b7803b7603b7503b7403b7209b7109b7004b6e04b6a04b6604b6203b5e03b5a03b5603b5205b4a05b4603a7e09a7d09a7c02a7903a7503a7202a7102a7004a6e04a6205a4a05a4601a3601a350197e0197d0197c019790197503972019710597001939019310192d019250887d038750685d038550883d0883502d6f02d6e02d6d07c6f04c6b04c6706c6307c5f06c5b07c5706c5305b6f04b6705b5f05b5d05b5705b5505b4f05b4707a6f07a6d04a6b04a6a04a6704a6609a6501a6301a5f01a5d04a5b04a5a01a5701a5601a5501a5401a5306a4f09a4b09a4706a4305a3b05a370196f0196b01967019630195f0195d0195b0195701955019530194f0194b01947019430193b019370192b01927019230786f048670785f078570684f0f8470982f098270181f0181707d6f04d6b04d6706d6305c6f04c6705c5f05c5701b6f04b6b04b6a09b6904b6704b6607b6307b6106b5f09b5b11b5706b5305b4b02b4702a6f07a6e02a6d02a5f02a5b02a5702a5302a4b02a4a02a4705a4602a3711a3602a350196f0196b01967019630195f0195b01957019530194b019470193b01937019330192f0192d0192b0192701925019230286f028670285f028570283f028370282f028270181f018177f56f06d6b7e56706d6305c6f05c6705c5f05c5711b6f07b6e09b6b04b6a11b6704b6609b6307b6206b5f06b5e09b5b03b5a11b5703b5606b5306b5205b4b05b4a05b4705b4609a6f7d26e02a6b09a6702a637c26206a5f02a5b09a5702a5302a4b05a4a05a4705a4601a3701a3601a350196f0196b01967019630195f0195b01957019530194b019470193b019390193701933019310192f0192d0192b0192701925019234d06f430670685f2b0570983f0883d11837088350282f028270181f018179656f06d6b8c56706d6301c6f01c6e01c6b04c6a01c6701c6601c6307c6201c5f01c5e01c5b03c5a01c5701c5601c5306c5205b6f05b6705b5f05b5701b4f01b4e05b4d8a26f8826b862678426306a5f8225b8025706a5301a4f7b24d01a4b01a4901a4701a4501a4302a4105a3b05a370196f0196b01967019630195f0195b01957019530193b01939019310192f0192b0592a0192701926019234c06f420670685f2a0570184f0884d01847018451002f0b0270181f0581d018170181502d6f02d6e07c6f04c6b04c6706c6309c5f03c5d06c5b06c5909c5703c5506c5306c5102a6b04a6a04a6704a6602a6304a5704a5506a4f02a4b09a4702a430196f0496b01967059630195f0195d0595b05959019570195505953059510194f0594b01947059430192f0592b019270292302e7f02e7e02e7d07d7f04d7b04d7706d7307d6f03d6d06d6b06d6907d6703d6506d6306d6102b7b04b7a02b7904b7704b7602b7302b7104b6704b6604b6506b5f02b5b09b5702b5301a7f04a7b01a7705a7301a6f01a6d05a6b05a6901a6701a6505a6305a6101a5f05a5b01a5705a5301a4501a3f05a3b01a3702a330797e049760796e0796c07966791640695e039560293e099360592e04d6f04d6b04d6704d6302b6f02b6702b6302b5f02b5b02b5702b5304a6704a6606a5f06a5e0da5b03a5a0da5703a5606a5306a5202a3f02a3e0196f0496b01967049630195f0595b01957059530193f0293b01937029330192f0192d0592b059290192701925029230292104e7f04e7b04e7704e7302c7f04c7e02c7d02c7702c7502c7302c7202c6f02c6b02c6702c6302b7704b7602b7502b6f06b6e02b6b02b6a02b6703b6602b6302b6202b4f02b4e02b4d01a7f04a7b01a7704a7301a6f05a6b01a6705a6301a5501a4f02a4b01a4702a4301a3f01a3d02a3b05a3901a3701a3502a3302a310497e049760696e039660294e0294c02946711440293e0293c02936771340592e02d6f02d6d09c6f03c6d06c6b06c6909c6703c6506c6306c6104c5f04c5b04c5704c5307a6f07a6d04a5f02a5b02a5306a4f02a4b09a4702a430196f0196d0496b04969019670196505963059610195f0495b01957049530194f0594b01947059430192f0592b019270292302e7f02e7e02e7d04d7f03d7d04d7b04d7904d7703d7504d7306d7104d6f04d6b04d6704d6304b7f04b7e07b7d04b6f04b6e02b6b02b6902b6304b6202b6106b5f02b5b09b5702b5301a7f04a7e01a7d01a7c04a7b04a7901a7701a7504a7304a7205a7105a7001a6f04a6b01a6704a6301a5f05a5b01a5705a5301a4501a3f05a3b01a3702a330497e7517c04976049740496e049660695e039560293e0293c09936701340592e07d6f04d6b04d6706d6302b6f02b6b02b6a02b6704b6602b5f02b5b02b5702b5307a6f07a6e06a5f06a5e0ea5b03a5a0ea5703a5606a5306a5202a3f02a3e0196f0496b01967059630195f0595b0195705953019450193f0293b01937029330192f0192d0592b059290192701925029230292107e7f04e7b04e7706e7302c7f02c7d02c7b02c7a02c7704c7602c7502c6f02c6b02c6702c6302b7f07b7e02b7d02b6f06b6e02b6b02b6a02b6703b6602b6302b6202b4f02b4e02b4d01a7f04a7b01a7705a7301a6f05a6b01a6705a6301a5501a4f02a4b01a4702a4301a3f01a3d02a3b05a3901a3701a3502a3302a310797e049760696e039660294e029460293e0293c02936731340592e04d6f04d6b04d6704d6304b6f04b6e04b6704b6304b6206b5f0db5b09b5706b5302a6704a6602a6502a5f02a5b02a5a02a5703a5602a5302a3f14a3e02a3d0196f0496b01967049630195f0595b01957059530193f0593b01937029330192f0292b0592901927029230292102d6f02d6e02d6d04c6f03c6d04c6b04c6703c6504c6304c5f04c5b04c5704c5304a6f04a6e04a5f04a5e04a5b04a5904a5304a5209a5106a4f09a4b09a4706a430196f0496e0496b04969019670496304962059610195f0495b01957049530194f0594b01947059430192f0592b01927059230ed6f06d6b0ed6706d6309b6f07b6e14b6b04b6a09b6704b6614b6307b6206b5f06b5e0eb5b03b5a09b5703b5606b5306b5209a6f02a6b7126a09a677026602a6306a5f02a5b0ea5a09a570ea5602a530196f0596b01967059630195f0595b01957059530193f0193d0593b05939019370193505933059310192f0592b059290192702923059210ed6f06d6b0ed6706d637836f7636b743677236306b5f0eb5b0eb5706b5301a6f05a6b01a6705a6301a5f05a5b01a5705a5301a4501a3f05a3b01a3705a330796e049660695e039560293e6f1360592e03e7f06e7e03e7d03d7b04d7a03d7903d7703d7603d7303d7103d6703d6603d6505c7f04c7b04c7707c7303c6f03c6d03c6b03c6705c6503c6303c5f03c5b03c5703c5302b7f02b7b02b7702b7302b6f02b6d02b6b02b6902b6702b6502b6302b6102b5f02b5b02b5702b5302b4f02b4b02b4702b4301a7f07a7e01a7b01a7a01a7704a7601a7301a7201a6f03a6e01a6d03a6c01a6b01a6a01a6901a6801a6703a6601a650da6401a6301a6201a6101a6001a5f03a5e01a5b01a5a01a5703a5601a5301a5201a4f01a4b01a4a01a4705a4601a4301a3f02a3e01a3d0197f0197b01977019730196f0196d0196b01969019670196501963019610195f0195b01957019530194f0194b01947019430193b0293a01939019370193601933019310192701926019250287f0287b02877028730286f0286d0286b0286702865028630285f0285b02857028530284f0284b02847028430283f0283b02837028330182f0182d0182b0182702825018230181f0181b018170181304d6f04d6d01d6b01d6901d6701d6501d6301d6103c6f03c6d01c6b01c6901c6701c6501c6301c6103c5f03c5b01c5703c5305b6f05b6d10b6b05b6705b6510b6304b5f04b5b04b5704b5303b4f03b4b03b4703b4302a6f02a6d02a6b02a6902a6702a6502a6302a6102a5f02a5b02a5702a5302a4f02a4b02a4702a4302a3f02a3b02a3702a330196f0196e0196d0196b019690196701965019630396201961039600195f0195b01957019530194f0194b01947019430193f0193b01937019330192f0192b0292a0192701926019230286f0286d0286b0286702865028630285f0285b02857028530284f0284d0284b0284702845028430283f0283b02837028330282f0282b02827028230181f0181b018170181303e7f03e7e04e7d03d7f03d7e03d7d03d6f03d6e03d6b03d6903d6304d6203d6103c7f05c7d03c7b03c7703c7503c7304c6f04c6b04c6704c6303c5f03c5b03c5703c5302b7f02b7d02b7b02b7902b7702b7502b7302b7102b6f02b6b02b6702b6302b5f02b5b02b5702b5302b4f02b4b02b4702b4301a7f03a7e01a7d6c27c01a7b01a7a01a7901a7801a7703a7601a7503a7401a7301a7201a7101a7001a6f04a6e01a6b01a6a01a6704a6601a6301a6201a5f03a5e01a5b01a5a01a5703a5601a5301a5201a4f01a4b01a4a01a4705a4601a4301a3f02a3e01a3d0197f0197e0197d0197c0197b019790197701975019730397201971059700196f0196b01967019630195f0195b01957019530194f0194b01947019430193b0293a01939019370193601933019310192701926019250287f0287d0287b0287702875028730286f0286b02867028630285f0285d0285b0285702855028530284f0284b02847028430283f0283b02837028330182f0182d0182b0182702825018230181f0181b018170181304d6f04d6b04d6704d6301b6f01b6e01b6b01b6a04b6704b6601b6301b6206b5f06b5e0db5b03b5a0db5703b5606b5306b5202a6f02a6b02a6702a6302a5f02a5b02a5702a5302a3b02a390196f0196b01967019630195f0195b019570195301937019350192b0292a01927019260192304e7f04e7b04e7704e7304d7e04c7606c6e03c6602b7f02b7b02b7702b7302b6f02b6b02b6702b6302b4902b4501a7f04a7e01a7b01a7a01a7704a7601a7301a7201a6f06a6e01a6b01a6a01a6703a6601a6301a6201a4901a4801a456a24401a3f02a3e01a3d0197f0197b01977019730196f0196b019670196301949019450193b0293a019390193701936019330193101927019260192507d6f04d6b04d6706d6305b6f02b6b02b6702b6306b5f10b5b09b5706b5301a6f07a6e01a6b01a6701a6301a6201a5f01a5b01a5a01a5703a5601a5301a3f10a3e01a3d0196f0196b01967019630195f0195b01957019530193b0193901937019330193101927019260192507d6f04d6b04d6706d6305b6f05b6e01b6b01b6a01b6701b6601b6301b6206b5f06b5e0fb5b03b5a0fb5703b5606b5306b5202a6f02a6b02a6702a6302a5f02a5b02a5702a5302a3b02a390196f0196b01967019630195f0195b019570195301937019350192b0292a01927019260192307e7f04e7b04e7706e7304d7605c7e06c6e03c6602b7f02b7b02b7702b7302b6f02b6b02b6702b6302b4902b4802b456834401a7f07a7e01a7b01a7a01a7704a7601a7301a7201a6f06a6e01a6b01a6a01a6703a6601a6301a6201a4901a4801a456724401a3f02a3e01a3d0197f0197b01977019730196f0196b019670196301949019450193b0293a019390193701936019330193101927019260192503d6f03d6b03d6703d6310b6f07b6e0db6b04b6a0db6704b6610b6307b6201b5f01b5e01b5b01b5a03b5703b5601b5301b5202a6f02a6b02a6702a6302a5f02a5b02a5702a5302a3b02a390196f0196b01967019630195f0195b019570195301937019350192b0292a01927019260192303e7f03e7b03e7703e7303d6e07c7e04c7603c6602b7f02b7b02b7702b7302b6f02b6b02b6702b6302b4902b4501a7f07a7e01a7b01a7a01a7704a7601a7301a7201a6f03a6e01a6b01a6a01a6703a6601a6301a6201a4901a4801a456524401a3f02a3e01a3d0197f0197b01977019730196f0196b019670196301949019450193b0293a01939019370193601933019310192701926019256d56f06d6b6b56706d6305c6f6946b05c676646305c5f6445b05c5706c5302b6f02b6b02b6702b6302b5f02b5b02b5702b5302b4f02b4b02b4702b4301a6f07a6e01a6b01a6a01a6704a6601a6301a6201a5f06a5e01a5b01a5a01a5703a5601a5301a5201a4f01a4b01a4a01a4705a4601a4301a3f02a3e01a3d0196f0196b01967019630195f0195b01957019530194f0194b01947019430193b0293a01939019370193601933019310192701926019250286f0286b02867028630285f0285b02857028530284f0284b02847028430283f0283b02837028330182f0182d0182b0182702825018230181f0181b018170181302e7f02e7e02e7d07d7f04d7b04d7706d7307d6f03d6d06d6b06d6907d6703d6506d6306d6105c7f04c7b04c7705c7305c6f05c6d05c6b05c6705c6505c6305c5f05c5b05c5705c5302b7b02b7a02b7902b7704b7602b7302b7102b6704b6602b6502b5f02b5b02b5702b5302b4f05b4e02b4b02b4702b4302b4201a7f04a7b01a7705a7301a6f01a6d05a6b05a6a05a6905a6801a6707a6601a6501a6405a6305a6101a5f05a5b01a5705a5301a4f05a4b05a4a01a4705a4605a4301a3f02a3e01a3d01a3701a3502a3302a320597f0797e0597d0797c0497b0497a0497704976059750497405973059720196f0196e0196d0196c0496b0496a049690496805967049660196501964059630596205961059600595f0695e0595b0395a059570395605953059520594f0594b0594a0594705946059430193701936019350292f0292e0292d0287f0287b02877028730286f0286d0286b0286702865028630285f0285b02857028530284f0284b02847028430283f0283b02837028330282f0182b01827028230281f0281d0281b02817028150281302e7f02e7e02e7d04d7f03d7d04d7b04d7904d7703d7504d7306d7104d6f04d6b04d6704d6304c7f05c7d04c7b04c7704c7504c7304c6f04c6b04c6704c6305c5f05c5b05c5705c5302b7f04b7e02b7d02b6f04b6e02b6b02b6902b6302b6202b6102b6002b5f02b5b02b5702b5302b4f02b4b02b4702b4301a7f04a7e01a7d01a7c04a7b04a7901a7701a7504a7304a7205a7105a7001a6f04a6b01a6704a6301a5f05a5b01a5705a5301a4f05a4b05a4a01a4705a4605a4301a3f02a3e01a3d01a3701a3502a3302a320497f0497e0197d0197c0497b0497a049790497801977019760197501974049730497205971059700496f0496e0596d0796c0496b0496a0496704966049650496404963049620595f0695e0595b0395a059570395605953059520594f0594b0594a0594705946059430193701936019350292f0292e0292d0287f0287d0287b0287702875028730286f0286b02867028630285f0285b02857028530284f0284b02847028430283f0283b02837028330282f0182b01827028230281f0281d0281b0281702815028130ed6f06d6b0ed6706d6305c6f05c6b05c6705c6305c5f05c5b05c5705c536236f02b6b6136702b6306b5f02b5b0eb5702b5305b4f02b4b05b4702b4301a6f05a6b01a6705a6301a5f05a5b01a5705a5301a4f05a4b05a4a01a4705a4605a4301a3f02a3e01a3d01a3701a3502a3302a320596f0796e0596b0496a059670496605963059620595f0695e0595b0395a059570395605953059520594f0594b0594a0594705946059430193701936019350292f0292e0292d0a86f0286b0a867028630685f0285b0a857028530584f0284b05847028430283f0283b02837028330582f0182b01827028230581f0581d0281b05817088150281303e7f06e7e03e7d03d7b04d7a03d7903d7703d7603d7303d7103d6703d6603d6505c7f04c7b04c7707c7303c6f03c6d03c6b03c6705c6503c6303c5f03c5b03c5703c5301b7f01b7e01b7b04b7a01b7701b7601b7307b7201b6f01b6e01b6d01b6c01b6b03b6a01b690db6801b6701b6601b6501b6401b6303b6201b6103b6001b5f01b5e01b5b03b5a01b5701b5601b5303b5201b4f01b4b05b4a01b4701b4601b4307a7f02a7b04a7702a7303a6f03a6d02a6b02a6903a6709a6502a6302a6103a5f02a5b03a5702a5312a4f02a4b05a4702a4301a3f01a3e05a3d0197f0197b01977019730196f0196d0196b01969019670196501963019610195f0195b01957019530194f0194b0e94a0194701946019430193f0193e0193d0192f0192e0192b019290192302922019210787f0287b04877028730386f0386d0286b0386708865028630385f0285b03857028530c84f0284b05847028430183f0883d0183b0183701835018330282f0282b02827028230181f0181b0181701813 20 1048575 8 255 11 2047 20 1048575
def cc_66_4 : Nat → List (Nat × Nat) := unpackCursorV4 0x9a34d922818d1518547d80351782817364c6ea4c66981664056630165d066510c65100650016450b5ee575ae4052b834da514598140a4f38585330552b37d2644f1d88c1894f104850b3510367d00036 0x4d6f04d6b04d6704d6304c6f04c6705c5f05c5702b6f02b6b02b6702b6302b5f02b5b02b5702b5302b4b02b4704a6f04a6e04a6b04a6a04a6704a6604a6304a6206a5f06a5e0da5b03a5a0da5703a5606a5306a5202a4b01a4a01a4701a4602a3f02a3e02a3b02a3a02a3702a3602a3302a320196f0496b01967049630195f0595b01957059530294b019470193f0293b01937029330192f0192d0192701925029230286f028670285f028570283f028370282f0282d02827028250281f0181704e7f04e7b04e7704e7304d7f04d7705d6f05d6702c7f04c7e02c7d02c7702c7502c7302c7202c6f02c6b02c6702c6302c5b02c5702b7704b7602b7502b6f06b6e02b6b02b6a02b6703b6602b6302b6202b5b02b5a02b5705b5602b4f02b4e02b4d01a7f04a7b01a7704a7301a6f05a6b01a6705a6301a5d01a5701a5501a4f02a4b02a4a01a4702a4602a4301a3f01a3d02a3b02a3a05a3905a3801a3702a3601a3501a3402a3302a310497f0497e0497b0497a049770497604973049720596f0696e0596b0396a059670396605963059620195701956019550294f0294e0294b0294a029470294602943029420293f0293e0293d0293c0293b0293a05939059380293702936059359e134029330293202931029300287f028770286f028670284f028470283f0283d02837028350282f0282d01827028250281f0281d028170281502d6f02d6d04d6b04d6904d6702d6504d6304d610dc6f03c6d06c6b06c690dc6703c6506c6306c6104c5f04c5b04c5704c5301b6f01b6d04b6701b6504b5f04b5705b4f05b4707a6f07a6d02a6b02a6905a6705a6502a6302a6104a5f02a5b04a5702a5306a4f02a4b09a4702a4302a3b05a370196f0196d0496b01967019650195f0495b01957049530194f0594b01947059430493b019370192f0592b0592a0192709926029230a86f0886d0a867088650485f048570684f0a8470282f028270581f0581d018170a81502e7f02e7e02e7d04d7f03d7d04d7b04d7904d7703d7504d7306d7104d6f04d6b04d6704d6304c7f05c7d04c7704c7504c6f04c6705c5f05c5704b7f04b7e07b7d04b6f04b6e02b6b02b6902b6304b6202b6106b5f02b5b09b5702b5302b4b05b4701a7f01a7d04a7b04a7901a7701a7504a7305a7101a6f04a6b01a6704a6301a5f05a5b01a5705a5301a4d01a4701a4501a3f05a3b05a3a01a3709a3602a330497f0497e0597d9c17c0497b0497a049790497804977049760497504974049730497205971059700496f0496e0496b0496a049670496604963049620595f0695e0595b0395a059570395605953059520194701946019450293f0293e0593b0593a059370993602933029320487f0887d04877048750486f048670685f0a8570283f028370582f0582d018270a8250581f0581d058170881507d6f04d6b04d6706d6305c6f04c6705c5f05c5702b6f02b6b02b6702b6302b5f02b5b02b5702b5302b4b02b4707a6f07a6e04a6b04a6a04a6704a6605a6305a6206a5f06a5e0ea5b03a5a0ea5703a5606a5306a5202a4b01a4a01a4701a4602a3f02a3e02a3b02a3a02a3702a3602a3302a320196f0496b01967059630195f0595b01957059530194d0294b01947019450193f0293b01937029330192f0192d0192701925029230286f028670285f028570283f028370282f0282d02827028250281f0281d018170281507e7f04e7b04e7706e7305d7f04d7705d6f05d6702c7f02c7d02c7b02c7a02c7704c7602c7502c6f02c6b02c6702c6302c5b02c5702b7f07b7e02b7d02b6f06b6e02b6b02b6a02b6703b6602b6302b6202b5b02b5a02b5705b5602b4f02b4e02b4d01a7f04a7b01a7705a7301a6f05a6b01a6705a6301a5d01a5701a5501a4f02a4b02a4a01a4702a4602a4301a3f01a3d02a3b02a3a05a3905a3801a3702a3601a3501a3402a3302a310597f0797e0497b0497a049770497605973059720596f0696e0596b0396a059670396605963059620195701956019550294f0294e0294b0294a029470294602943029420293f0293e0293d0293c0293b0293a05939059380293702936059359a134029330293202931029300287f028770286f028670284f028470283f0283d02837028350282f0282d01827028250281f0281d02817028150ed6f06d6b0ed6706d6305c6f05c6705c5f05c5709b6f07b6e14b6b04b6a09b6704b6614b6307b6206b5f06b5e0eb5b03b5a09b5703b5606b5306b5205b4b01b4a01b4701b4609a6f02a6b09a6702a6306a5f02a5b09a5702a5302a4b05a4a05a4705a4605a3f05a3e05a3d0196f0596b01967059630195f0595b01957059530594b019470193f0193d0193701935059330192f0592b059290192702923059210a86f0a8670685f0a8570a83f0883d09837088350282f028270581f018170ed6f06d6b0ed6706d6305c6f05c6705c5f05c579f36f9d36b9b3679936306b5f0eb5b0eb5706b5305b4b05b4701a6f05a6b01a6705a6301a5f05a5b01a5705a5301a4d01a4701a4501a3f05a3b05a3a01a375123605a330596f0796e0596b0496a059670496605963059620595f0695e0595b0395a059570395605953059520194701946019450593f0293e0593b0593a059379813605933029320a86f0a8670685f0a8570a83f0a8370582f0582d018270a8250581f0581d058170881503e7f06e7e03e7d03d7b04d7a03d7903d7703d7603d7303d7103d6703d6603d6501c7f01c7e01c7b04c7a01c7701c7601c7307c7201c6f01c6e01c6d01c6c01c6b03c6a01c690dc6801c6701c6601c6501c6401c6303c6201c6103c6001c5f01c5e01c5b03c5a01c5903c5801c5701c5601c5303c5201c5106c5005b7f04b7703b6f03b6d03b6705b6503b5f03b5701b4f01b4e05b4d07a7f04a7b04a7707a7303a6f03a6d03a6b02a6903a670da6503a6302a6103a5f03a5b03a5703a5301a4f7f24d01a4b01a4901a4701a4501a4302a4105a3b05a370197f0197b01977019730196f0196d0196b01969019670196501963019610195f0195b01957019530193b01939019310192f0192b0592a0192701926019230787f048770386f0386d03867088650385f038570184f0884d01847018450c82f0c8270181f0581d018170181502b4c9424809a440394005930912349434c02b4009a4403940039280192404c7801c7003c6801c6005c5802b4c09a3c902300194c03940039300f84c9123c02b489034407a7c04a7406a6c03a6405a5409a4c03940059280f82403d6f03d6e03d6b01d6703d6304d6204c6f04c6703c5f03c5701b6f01b6e04b6b04b6a01b6701b6601b6301b6201b5f01b5e03b5b03b5a01b5701b5601b5301b5205b4b05b4a03b4703b4604a6f04a6b04a6704a6303a5f03a5b03a5703a5305a4b05a479523f09a3d9323b02a399223709a358f23302a310196f0196b01967019630195f0195b01957019530194b019470193b0193901937019330393201931039300192f0192b0592a0192701926019230486f048670385f0685d03857038550b83f0883d0b837088350b82f0b8270181f0581d018170181504e7d02e7904e7502e7103d7d02d7903d7502d7101c7e01c7d01c7c09c7a01c7913c7801c7601c7501c7409c7201c7109c7001c6e04c6a01c6604c6201c5e03c5a01c5603c5205b7d05b7501b4e05b4d03a7603a7504a6a04a6603a5a03a5601a4e09a4d09a4c01a4901a4501a4202a4102a400197e0197d0197c019790197505972019710597001939019310592a019260887d088750884d018450581d0181503e7f03e7e04e7d03d7f03d7e03d7d03d6f03d6e03d6b03d6903d6304d6203d6101c7f01c7e01c7d01c7c01c7b03c7a01c7903c7801c7701c7601c7501c7401c7303c7201c718e47001c6f01c6e01c6b04c6a01c6701c6601c6304c6201c5f01c5e01c5b03c5a01c5701c5601c5303c5203b7f05b7d03b7703b7504b6f04b6703b5f03b5701b4f01b4e05b4d03a7f8d27d03a7b02a7903a7703a7503a7302a7104a6f04a6b04a6704a6303a5f03a5b03a5703a5301a4f7e24d01a4b01a4901a4701a4501a4302a4105a3b05a370197f0197e0197d0197c0197b019790197701975019730397201971059700196f0196b01967019630195f0195b01957019530193b01939019310192f0192b0592a0192701926019230387f0887d03877038750486f048670385f0685d03857038550184f0884d01847018450b82f0b8270181f0581d018170181507d6f04d6b04d6706d6305c6f04c6705c5f05c5701b6f01b6e01b6b01b6a01b6701b6602b6302b6206b5f06b5e0fb5b03b5a0fb5703b5606b5306b5205b4b05b4a05b4705b4601a6f02a6b02a6904a6702a6302a6106a5f02a5b09a5702a5302a4b05a4704a3f04a3d01a3b01a3901a3701a3501a3301a310196f0196b01967019630195f0195b01957019530194b019470193b019390193701933019310192f0192b0592a0192701926019230786f048670685f0f8570f83f0883d0f837088350282f028270181f0181702e7f02e7e02e7d07d7f04d7b04d7706d7307d6f03d6d06d6b06d6907d6703d6506d6306d6101c7f01c7e01c7b04c7a01c7701c7601c7307c7201c6f01c6e01c6d01c6c01c6b07c6a01c698b46801c6701c6601c6501c6401c6307c6201c6107c6001c5f01c5e01c5b03c5a01c5701c5601c5306c5205b7f04b7705b6f05b6d05b6705b6505b5f05b5701b4f01b4e05b4d02a7b04a7a02a7904a7704a7602a7302a7104a6704a6604a6506a5f02a5b09a5702a5301a4f01a4e09a4d7d24c01a4b01a4901a4701a4501a4301a4202a4102a4002a3b05a370197f0197b01977019730196f0196d0196b01969019670196501963019610195f0195b01957019530193b01939019310192f0192b0592a0192701926019230787f048770786f0786d07867088650685f0f8570184f0884d01847018450282f028270181f0581d018170181504d6f04d6b04d6704d6304c6f04c6705c5f05c5701b6f01b6e04b6b04b6a01b6701b6601b6301b6206b5f06b5e0db5b03b5a0db5703b5606b5306b5205b4b05b4a02b4702b4602a6f04a6e01a6b02a6702a6302a6202a5f02a5b02a5702a5302a4b02a4701a3f01a3d01a3b01a3901a3701a3502a3302a310196f0196b01967019630195f0195b01957019530194b019470193b019390193701933019310192f0192b01927019230286f028670285f028570283f0283d02837028350282f028270181f0181704e7f04e7b04e7704e7301d7f01d7e01d7b04d7a01d7904d7801d7701d7601d7304d7201d7107d7001d6f01d6e01d6b03d6a01d6701d6601d6306d6204c7f04c7705c6f05c6701c5f01c5e05c5d02b7f04b7e02b7d02b7702b7502b7302b7202b6f02b6b02b6702b6301b5f02b5d01b5b01b5901b5701b5501b5302b5102b4b02b4702a7704a7602a7502a6f06a6e02a6b02a6a02a6703a6602a6302a6201a5f01a5e02a5d8925c01a5b01a5a01a5901a5801a5701a5601a5501a5401a5301a5202a5102a5002a4b02a4a02a4705a4602a3f02a3e02a3d0197f0197b01977019730196f0196b01967019630194b01949019410193f0193b0293a0193701936019330192f0192d0192b0292a01929059280192701926019250192401923019210287f028770286f028670185f0285d01857018550283f028370282f0282d02827028250181f0281d018170181504d6f04d6b04d6704d6304c6f04c6705c5f05c5701b6f01b6e02b6b02b6a01b6701b6601b6301b6206b5f06b5e0db5b03b5a0db5703b5606b5306b5205b4b05b4a04b4704b4604a6f04a6e02a6b02a6901a6702a6304a6202a6106a5f02a5b09a5702a5302a4b05a4707a3f07a3d01a3b01a3901a3701a3501a3301a310196f0196b01967019630195f0195b01957019530194b019470193b019390193701933019310192f0192b0592a0192701926019230486f048670685f0b8570b83f0883d0b837088350282f028270181f0581d018170181502e7f02e7e02e7d04d7f03d7d04d7b04d7904d7703d7504d7306d7104d6f04d6b04d6704d6301c7f01c7e01c7d01c7c01c7b04c7a01c7904c7801c7701c7601c7501c7401c7304c7201c718747001c6f01c6e01c6b04c6a01c6701c6601c6304c6201c5f01c5e01c5b03c5a01c5701c5601c5306c5204b7f05b7d04b7704b7504b6f04b6705b5f05b5701b4f01b4e05b4d04a7f04a7e07a7d04a6f04a6e02a6b02a6902a6304a6202a6106a5f02a5b09a5702a5301a4f09a4d01a4b01a4901a4701a4501a4302a4102a3b05a370197f0197d0197b01979019770197501973019710196f0196b01967019630195f0195b01957019530193b01939019310192f0192b0592a0192701926019230487f0887d04877048750486f048670685f0b8570184f0884d01847018450282f028270181f0581d018170181507d6f04d6b04d6706d6305c6f04c6705c5f05c5701b6f01b6e01b6b01b6a01b6701b6607b6307b6206b5f06b5e0fb5b03b5a0fb5703b5606b5306b5205b4b05b4a02b4702b4602a6f02a6b02a6701a6302a5f02a5b02a5702a5302a4b02a4701a3f01a3d01a3b01a3901a3701a3502a3302a310196f0196b01967019630195f0195b01957019530194b019470193b019390193701933019310192f0192b01927019230286f028670285f028570283f0283d02837028350282f028270181f0281d018170181507e7f04e7b04e7706e7301d7f01d7e01d7b04d7a01d7904d7801d7701d7601d7307d7201d7107d7001d6f01d6e01d6b03d6a01d6701d6601d6306d6205c7f04c7705c6f05c6701c5f01c5e05c5d02b7f02b7d02b7b02b7a02b7704b7602b7502b6f02b6b02b6702b6301b5f01b5e02b5d7c35c01b5b01b5901b5701b5501b5301b5202b5102b5002b4b02b4702a7f07a7e02a7d02a6f06a6e02a6b02a6a02a6703a6602a6302a6201a5f01a5e02a5d8525c01a5b01a5a01a5901a5801a5701a5601a5501a5401a5301a5202a5102a5002a4d02a4b02a4a02a4705a4602a4505a4402a3f02a3e02a3d0197f0197b01977019730196f0196b01967019630194b01949019410193f0193b0293a0193701936019330192f0192d0192b0292a01929059280192701926019250192401923019210287f028770286f028670185f0285d01857018550283f028370282f0282d02827028250181f0281d018170181503d6f03d6b03d6703d6305c6f05c6703c5f03c5711b6f07b6e0db6b04b6a0db6704b6611b6307b6201b5f01b5e03b5b03b5a01b5701b5601b5301b5205b4b05b4a02b4702b4602a6f02a6b02a6702a6302a5f01a5b02a5702a5302a4b02a4701a3f01a3d01a3b01a3901a3701a3502a3302a310196f0196b01967019630195f0195b01957019530194b019470193b019390193701933019310192f0192b01927019230286f028670285f028570283f0283d02837028350282f028270181f0281d018170181503e7f03e7b03e7703e7301d7f01d7e01d7b04d7a01d7701d7601d7307d7201d6f01d6e01d6b03d6a01d6903d6801d6701d6601d6303d6201d6106d6005c7f05c7703c6f03c6701c5f01c5e05c5d02b7f02b7b02b7702b7302b6f03b6e02b6d02b6702b6502b6302b6201b5f02b5d01b5b01b5901b5701b5501b5302b5102b4b02b4702a7f07a7e02a7b02a7a02a7704a7602a7302a7202a6703a6602a6501a5f01a5e02a5d8325c01a5b01a5a01a5901a5801a5701a5601a5501a5401a5301a5202a5102a5002a4b02a4a02a4705a4602a3f02a3e02a3d0197f0197b01977019730196f0196b01967019630194b01949019410193f0193b0293a0193701936019330192f0192d0192b0292a01929059280192701926019250192401923019210287f028770286f028670185f0285d01857018550283f028370282f0282d02827028250181f0281d018170181503d6f03d6b03d6703d6305c6f05c6703c5f03c5718b6f07b6e0db6b04b6a0db6704b6618b6307b6201b5f01b5e02b5b02b5a01b5701b5601b5301b5205b4b05b4a03b4703b4609a6f02a6b09a6702a6303a5f02a5b02a5901a5702a5302a5102a4b05a4706a3f06a3d01a3b01a3901a3701a3501a3301a310196f0196b01967019630195f0195b01957019530194b019470193b019390193701933019310192f0192b0592a0192701926019230c86f0c8670385f038570c83f0883d0c837088350282f028270181f0181703e7f03e7e03e7b04e7a03e7703e7603e7307e7203d7f03d7b03d7703d7302d6f02d6e02d6d01c7f01c7e01c7b04c7a01c7701c7601c7307c7201c6f01c6e01c6d01c6c01c6b03c6a01c6903c6801c6701c6601c6501c6401c6303c6201c618146001c5f01c5e01c5b03c5a01c5701c5601c5303c5205b7f05b7703b6f05b6d03b6703b6503b5f03b5701b4f01b4e05b4d09a7f02a7b09a7702a7303a6f03a6e06a6d03a5f03a5e02a5b02a5902a5303a5202a5101a4f09a4d01a4b01a4901a4701a4501a4302a4102a3b05a370197f0197b01977019730196f0196d0196b01969019670196501963019610195f0195b01957019530193b01939019310192f0192b0592a0192701926019230c87f0c8770386f0886d03867038650385f038570184f0884d01847018450282f028270181f0581d018170181506e7e03e7d04d7a03d7903d7603d7103d6603d6503c6d05c6507b7e04b7a04b7607b7203b6e03b6d03b6c03b6a09b6909b6803b660db650db6403b6203b6103b6003b5e03b5a03b5603b5205b4a05b4607a7e07a7203a6d02a6909a6502a6105a4a05a4601a3601a350196d01969019650196101939019310192d019250386d088650883d08835 20 1048575 8 255 11 2047 20 1048575
def cc_66_5 : Nat → List (Nat × Nat) := unpackCursorV4 0x9d66196d699422b9261c8e5418ca1b89c2e859437f86178b6d72863692965f89a59167530614ef41459963bb9e37e3d33f3f2de612a13d260412233d1e63d1a5411663f1293d0ec3d0cc2007d4f0007d 0x4d6f04d6b04d6704d6304c6f04c6b04c6704c6305c5f05c5b05c5705c5304b6f04b6b04b6704b6306b5f0db5b0db5706b5305b4f05b4b05b4705b4301a6f04a6e01a6d01a6701a6504a6304a6201a5f05a5b01a5705a5301a4f05a4b01a4705a4301a3f05a3b01a3705a330196701966019650495f0695e0495b0395a049570395604953049520494f0494b0494a0494705946049430493f0293e0493b0493a04937bf13604933029320492f0592e0492d0486f0486b04867048630685f0a85b0a857068530584f0584b05847058430a83f0a83b0a8370a8330582f0182b01827058230481f0481d0481b04817088150481302d6f02d6e04d6b04d6a04d6704d6604d6302d6204c6f04c6b04c6704c6309c5f03c5d06c5b06c590dc5703c5506c5306c5104b6f04b6b04b6704b6305b5f05b5d09b5b05b5705b5509b5305b4f09b4b05b4706b4304a6f02a6b04a6a04a6704a6602a6301a5701a5601a5506a4f02a4b09a4702a4309a3fbb23e02a3b05a3702a33b92320196f0196b01967019630195f0195d0195b01959019570195501953019510194f0194b01947019430193f0193b01937019330192f0192d0192b0192701925019230486f0286b04867028630985f0885d0285b0b85708855028530684f0284b0b847028430983f0283b05837028330282f0282b02827028230181f0181b018170181304d6b04d6a04c6f04c6b04c6704c630dc5f03c5d06c5b06c590dc5703c5506c5306c5104a6f02a6b04a6702a6305a5f05a5d01a5b01a5901a5701a5501a5301a5106a4f02a4b0da4702a430196f0196b019630195f0195d0194f0194b01947019430192f0192b019270192302d6f04d6b04d6704d6304c6f04c6b04c6704c6309c5f06c5b09c5706c5305b5604a6601a5601a540196f0196b019630195f0195b01957019530194f0194b01947019430192501e7f01e7e04e7d01d7f03d7d01d7b01d7901d7701d7501d7306d7104d6f04d6b04d6704d6301b7ebc37c01b7601b7404b6e04b6606b5e03b5601a7f01a7e09a7dbb27c01a7b01a7901a7701a7501a7301a7202a7102a7004a6f02a6b04a6702a6306a5f02a5b0da5702a5302a4905a350197f0197e0197d0196f0196e0196b019690196304962019610195f0195b019570195301939019350192f0192b019270192302d6f04d6b02d6702d6304c6f04c6b04c6704c6309c5f06c5b09c5706c5304a6609a560196f0196b019630195f0195b01957019530194f0194b0194701943019250192404d6b04d6a04c6f04c6b04c6704c630dc5f03c5d06c5b06c590dc5703c5506c5306c5102a6f02a6b02a6702a6301a5f01a5d01a5b01a5901a5701a5502a5302a5102a4f02a4b02a4702a430196f0196e0196b01963049620195f0195e0195d0194f0194b01947019430192f0192b019270192301e7f01e7e04e7d01d7f03d7d01d7b01d7901d7701d7501d7306d7104d6f04d6b04d6704d6301b7f01b7e02b7db937c01b7b01b7901b7701b7501b7301b7202b7102b7002b6f02b6b02b6702b6302b5f02b5b02b5702b5302b4501a7eb827c01a7601a7404a6e04a6606a5e03a5602a3e0197f0197e0197d0196f0196e0196b019690196304962019610195f0195b01957019530193f0193b01937019330192905928019250192401d6f01d6e04d6d01c6f03c6d01c6b01c6901c6701c6501c6306c6104c5f04c5b04c5704c5301b6f05b6d01b6b01b6701b6501b6304b5f04b5b04b5704b5305b4f0db4b05b4706b4301a6fbd26d01a6b01a6901a6701a6501a6302a6104a5f04a5b04a5704a5306a4f0da4b0da4706a43ba23f05a3b05a37b72330196f0196e0196d0195f0195e0195b019590195304952019510194f0194b01947019430193f0193b01937019330192f0192b01927019230186f0886d0186b0186701865018630485f0485b04857048530684f0a84b0b847068430b83f0583b058370a8330b82f0a82b0b8270a8230181f0181b018170181307d6f04d6b04d6706d6305c6f04c6b04c6705c6305c5f05c5b05c5705c5301b6f01b6e02b6b02b6a04b6702b6607b6301b6206b5f06b5e0eb5b03b5a09b5703b5606b5306b5205b4f05b4b05b4a05b4705b4605b4307a6f07a6e02a6b04a6702a6307a6206a5f02a5b0ea5a09a570ea5602a5305a4f02a4b05a4a05a4705a4602a4305a3f05a3e05a3d0196f0496b01967059630195f0595b01957059530194f0594b01947059430193f0193d0493b04939019370193505933049310192f0592b059290192702923059210786f0286b04867028630685f0285b0a857028530584f0284b05847028430a83f0883d0283b0983708835028330282f0a82d0282b028270a825028230581f0181b018170281307d6f04d6b04d6706d6305c6f04c6b04c6705c6305c5f05c5b05c5705c5307b6f04b6b04b6707b6306b5f0eb5b0eb5706b5305b4f05b4b05b4705b4301a6f01a6d04a6b04a6a01a6704a6601a6501a5f06a5e05a5b01a5705a5305a5201a4f05a4b01a4705a4301a3f05a3b01a3705a330196f0196e0196d0595f0695e0595b0395a059570395605953059520594f0594b0594a0594705946059430593f0293e0593b0593a05937b513605933029320492f0492e0492d0786f0486b04867078630685f0a85b0a857068530584f0584b05847058430a83f0a83b0a8370a8330582f0182b01827058230581f0581d0581b05817088150581302e7f02e7e02e7d03d7f03d7b03d7703d7303d6f03d6d03d6b03d6903d6703d6503d6303d6105c7f04c7b04c7705c7305c6f05c6d05c6b05c6705c6505c6303c5f03c5b03c5703c5302b7b04b7a02b7904b7704b7602b7302b7104b6704b6604b6503b5f02b5b03b5702b5305b4f02b4b05b4702b4301a7f04a7b01a7705a7301a6f01a6d05a6b05a6901a6701a6505a6305a6101a5f03a5e01a5d01a5701a5503a5303a5201a4f05a4b01a4705a4301a3f05a3b01a3702a330397f0797e0397b0397a039770497603973039720396f0796e0396d0796c0396b0396a03969039680396707966039651a964039630396203961039600195701956019550394f0394b0394a0394705946039430293f0293e0393b0393a039370993602933029320392f0592e0392d0787f0287b04877028730786f0786d0286b0786708865028630385f0285b03857028530584f0284b05847028430283f0283b02837028330582f0182b01827028230381f0381d0281b03817088150281303e7f03e7b03e7703e7305d7f04d7b04d7705d7303d6f03d6b03d6703d6302c7f02c7d02c7b02c7a02c7704c7602c7502c6f02c6b02c6702c6302c5f02c5b02c5702c5302b7f07b7e02b7d02b6f03b6e02b6b02b6a02b6703b6602b6302b6202b5f02b5b02b5a02b5705b5602b5302b4f02b4e02b4d01a7f04a7b01a7705a7301a6f03a6e01a6d01a6701a6503a6303a6201a5f05a5b01a5705a5301a4f02a4b01a4702a4301a3f01a3d02a3b02a3a05a3905a3801a3702a3601a3501a3402a3302a310397f0797e0397b0397a039770497603973039720196701966019650395f0395b0395a0395705956039530294f0294e0294b0294a029470294602943029420293f0293e0293d0293c0293b0293a03939039380293702936039351a934029330293202931029300392f0592e0392d0287f0287b02877028730286f0286b02867028630285f0285b02857028530284f0284b02847028430283f0283d0283b0283702835028330282f0182b01827028230281f0281d0281b02817028150281303d6f03d6b03d6703d6305c6f05c6b05c6705c6303c5f03c5b03c5703c5309b6f07b6e0db6b04b6a09b6704b6613b6307b6203b5f02b5e03b5b01b5a01b5701b5602b5302b5205b4f05b4b05b4a05b4705b4605b4309a6f02a6b09a6702a6303a5f02a5b03a5a03a5703a5602a5305a4f02a4b05a4702a4303a3f03a3e03a3d0196f0596b01967059630195f0395b01957039530194f0594b01947059430193f0193d0593b05939019370193505933059310192f0592b059290192702923059210a86f0286b0a867028630385f0285b03857028530584f0284b05847028430a83f0883d0283b0983708835028330282f0282b02827028230581f0181b018170281303d6f03d6b03d6703d6305c6f05c6b05c6705c6303c5f03c5b03c5703c53b336f0db6b0db67b236303b5f03b5b03b5703b5305b4f05b4b05b4705b4301a6f05a6b01a6705a6301a5f03a5e01a5d01a5701a5503a5303a5201a4f05a4b01a4705a4301a3f05a3b01a3705a330396f0796e0396b0396a039670496603963039620195701956019550394f0394b0394a0394705946039430393f0293e0393b0393a03937b113603933029320392f0592e0392d0a86f0a86b0a8670a8630385f0385b03857038530584f0584b05847058430a83f0a83b0a8370a8330582f0182b01827058230381f0381d0381b03817088150381301e7f01e7e01e7b04e7a01e7701e7601e7307e7203d7f03d7b03d7703d7301d6f01d6e03d6d04c7605b7e01b6e0eb6c01b6601b6403b5e06b5c03b5603b5407a7f04a7b04a7707a7301a6f09a6d01a6b01a6901a6701a6501a6302a6103a5f03a5b03a5703a5302a3919a350197f0197b01977019730196f0196e0196d0195f0195e0195b01959019530395201951019390593801935019340192f0192b019270192302e7f02e7e02e7d01d7f01d7e01d7b04d7a01d7701d7601d7307d7201d6f01d6e01d6d01d6c01d6b07d6a01d690ed6801d6701d6601d6501d6401d6307d6201d6107d6003c7f03c7b03c7703c7303c6f03c6d03c6b03c6903c6703c6503c6303c6101c5f01c5e03c5d05b7f04b7b04b7707b7305b6f05b6d07b6b05b6705b6507b6301b5f05b5d01b5b01b5701b5501b5303b4f03b4b03b4703b4302a7b04a7a02a7904a7704a7602a7302a7104a6704a6604a6501a5f09a5d01a5b01a5901a5701a5501a5302a5103a4f02a4b03a4702a4310a3f02a3b05a3702a330197f0197b01977019730196f0196d0196b01969019670196501963019610195f0195e0195d0194f0194e0194b019490194303942019410193f0193b01937019330192f0192b01927019230787f0287b04877028730786f0786d0286b0786708865028630185f0885d0185b0185701855018530384f0284b03847028430c83f0283b05837028330282f0282b02827028230181f0181b018170181301e7f01e7e01e7b04e7a01e7701e7601e7307e7203d7f03d7b03d7703d7301d6f01d6e03d6d05c7f04c7b04c7707c7301c6f05c6d01c6b01c6701c6501c6303c5f03c5b03c5703c5302b7f02b7d02b7b02b7a02b7704b7602b7501b6f02b6d01b6b01b6901b6701b6501b6302b6102b5f02b5b02b5702b5302b4f02b4b02b4702b4302a7f07a7e02a7d01a6f01a6e02a6d0ea6c01a6b01a6a01a6901a6801a6701a6601a6501a6401a6301a6202a6102a6002a5f03a5e02a5d06a5c02a5b02a5a02a5703a5602a5503a5402a5302a5202a4f02a4b02a4a02a4705a4602a4302a3f02a3e02a3d0197f0197b01977019730196f0196e0196d0195f0195e0195b019590195303952019510194f0194b01947019430193f0193b01937019330192f0192d0192b0292a01929059280192701926019250192401923019210287f0287b02877028730186f0286d0186b0186701865018630285f0285b02857028530284f0284b02847028430283f0283b02837028330282f0282d0282b0282702825028230181f0181b018170181301e7f01e7e01e7b04e7a01e7701e7601e7307e7203d7f03d7b03d7703d7301d6f01d6e03d6d07b7e04b7601b6e0eb6c01b6601b6403b5e03b5610a7f02a7b0da7702a7301a6f09a6d01a6b01a6901a6701a6501a6302a6103a5f02a5b03a5702a5302a4905a350197f0197b01977019730196f0196e0196d0195f0195e0195b0195901953039520195101939019350192f0192b019270192301e7f01e7e01e7b04e7a01e7701e7601e7307e7203d7f03d7b03d7703d7301d6f01d6e03d6d02b7f02b7b02b7702b7301b6f02b6d01b6b01b6901b6701b6501b6302b6102b5f02b5b02b5702b5302b4507a7e04a7601a6e0ea6c01a6601a6403a5e03a5602a3e0197f0197b01977019730196f0196e0196d0195f0195e0195b019590195303952019510193f0193b01937019330192905928019250192401d6f01d6e01d6b04d6a01d6701d6601d6307d6203c6f03c6b03c6703c6301c5f01c5e03c5d05b6f0db6b05b67af36301b5f05b5d01b5b01b5701b5501b5303b4f03b4b03b4703b43ae26f0da6b0da67ad26301a5f0ea5d01a5b01a5901a5701a5501a5302a5103a4f03a4b03a4703a43ac23f05a3b05a37ab2330196f0196b01967019630195f0195e0195d0194f0194e0194b019490194303942019410193f0193b01937019330192f0192b01927019230c86f0a86b0c8670a8630185f0885d0185b0185701855018530384f0384b03847038430c83f0583b058370a8330c82f0a82b0c8270a8230181f0181b018170181303e7f06e7e03e7d03d7b04d7a03d7903d7703d7603d7303d7103d6703d6603d6505b7e04b7603b6e03b6c03b6605b6403b5e03b5607a7f04a7b04a7707a7303a6f03a6d03a6b02a6903a6709a6503a6302a6103a5f03a5b03a5703a5302a3905a350197f0197b01977019730196f0196d0196b01969019670196501963019610195f0195b019570195301949019350192f0192b019270192303e7f03e7e04e7d03d7f03d7e03d7d03d6f03d6e03d6b03d6903d6304d6203d6103b7e05b7c03b7603b7404b6e04b6603b5e03b5603a7f09a7d03a7b02a7903a7703a7503a7302a7104a6f04a6b04a6704a6303a5f03a5b03a5703a5302a3905a350197f0197e0197d0197c0197b019790197701975019730397201971059700196f0196b01967019630195f0195b019570195301949019350192f0192b019270192302e7f02e7e02e7d07d7f04d7b04d7706d7307d6f03d6d06d6b06d6907d6703d6506d6306d6105b7e04b7605b6e05b6c05b6605b6405b5e03b5602a7b04a7a02a7904a7704a7602a7302a7104a6704a6604a6506a5f02a5b09a5702a5302a3905a350197f0197b01977019730196f0196d0196b01969019670196501963019610195f0195b019570195301949019350192f0192b019270192304e7f04e7b04e7704e7304c7e04c7605c6e03c6602b7f04b7e02b7d02b7702b7502b7302b7202b6f02b6b02b6702b6302b4902b4502a7704a7602a7502a6f06a6e02a6b02a6a02a6703a6602a6302a6202a4902a4802a4505a4402a3f02a3e02a3d0197f0197b01977019730196f0196b019670196301959019450193f0193b01937019330192f0192d0192b019290192701925019230192102e7f02e7e02e7d04d7f03d7d04d7b04d7904d7703d7504d7306d7104d6f04d6b04d6704d6304b7e05b7c04b7604b7404b6e04b6605b5e03b5604a7f04a7e07a7d04a6f04a6e02a6b02a6902a6304a6202a6106a5f02a5b09a5702a5302a3905a350197f0197e0197d0197c0197b019790197701975019730497201971059700196f0196b01967019630195f0195b019570195301949019350192f0192b019270192307e7f04e7b04e7706e7305c7e04c7605c6e03c6602b7f02b7d02b7b02b7a02b7704b7602b7502b6f02b6b02b6702b6302b4902b4502a7f07a7e02a7d02a6f06a6e02a6b02a6a02a6703a6602a6302a6202a5505a5402a4902a4802a4505a4402a3f02a3e02a3d0197f0197b01977019730196f0196b019670196301959019450193f0193b01937019330192f0192d0192b019290192701925019230192103e7f03e7b03e7703e7305c7e04c7603c6e03c6602b7f02b7b02b7702b7302b6f03b6e02b6d02b6702b6502b6302b6202b4902b4502a7f07a7e02a7b02a7a02a7704a7602a7302a7202a6703a6602a6502a4902a4802a4505a4402a3f02a3e02a3d0197f0197b01977019730196f0196b019670196301959019450193f0193b01937019330192f0192d0192b019290192701925019230192103e7f03e7e03e7b04e7a03e7703e7603e7307e7203d7f03d7b03d7703d7302d6f02d6e02d6d05b7e04b7603b6e05b6c03b6603b6403b5e03b5609a7f02a7b09a7702a7303a6f03a6e06a6d03a5f03a5e02a5b02a5902a5303a5202a5102a3905a350197f0197b01977019730196f0196d0196b01969019670196501963019610195f0195b019570195301949019350192f0192b0192701923a956f06d6ba856706d6305b6e04b6605b5e03b56a726fa626ba5267a426306a5fa325ba225706a5302a3905a350196f0196b01967019630195f0195b019570195301949019350192f0192b019270192302d6f02d6e04d6b04d6a04d6704d6605d6302d6207c6f04c6b04c6706c630ec5f03c5d06c5b06c590ec5703c5506c5306c5105b6f04b6705b5f01b5d01b5701b5505b4f05b4705a6f02a6b04a6702a6305a5f04a5d02a5b02a5904a5704a5502a5302a5106a4f02a4b09a4702a4302a3b05a370196f0496b01967059630195f0195d0195701955059530194f0594b01947059430593b019370192f0592b0592a0192709926029230786f048670a85f0885d0a857088550684f0a8470282f028270581f0181702e7f02e7e02e7d07d7f04d7b04d7706d7307d6f03d6d06d6b06d6907d6703d6506d6306d6105c7f04c7705c6f05c6d05c6705c6505c5f05c5702b7b04b7a02b7904b7704b7602b7302b7104b6704b6604b6506b5f02b5b09b5702b5302b4b05b4701a7f04a7b01a7705a7301a6f01a6d05a6b05a6901a6701a6505a6305a6101a5f05a5b01a5705a5301a4d01a4701a4501a3f05a3b05a3a01a3709a3602a330597f0797e0497b0497a049770497605973059720596f0796e0596d0796c0596b0596a0596905968059670796605965a0164059630596205961059600595f0695e0595b0395a059570395605953059520194701946019450293f0293e0593b0593a059370993602933029320787f048770786f0786d07867088650685f0a8570283f028370582f0582d018270a8250581f0581d0581708815 20 1048575 8 255 11 2047 20 1048575
def cc_66_6 : Nat → List (Nat × Nat) := unpackCursorV4 0x8cd4884e7f7d47a753816d38068b4864a4162f1b6002f5e9175c82157b4d563185323151b174e6354ce184ac224812b4552c414413ad67345682a99c241681a59c17a2b13b3f10b300ca410676300067 0x1d6f01d6b01d6701d6301c6f01c6b01c6701c6303c5f03c5b03c5703c5301b6f01b6e01b6b01b6a01b6701b6601b6301b6204b5f04b5e04b5b04b5a04b5704b5604b5304b5203b4f03b4e03b4b03b4a03b4703b4603b4303b4201a6f01a6704a5f04a5703a4f03a4702a3f02a3e02a3d0196f0196b01967019630495f0295b04957029530394f0294b03947029430292b02929029210186f018670485f048570384f038470583f0883d05837058350281f0281703e7f03e7e04e7d03d7f03d7e03d7d03d6f03d6e03d6b03d6903d6304d6203d6103c7f03c7e05c7d05c7c03c7b03c7a03c7903c7803c7703c7603c7503c7403c7303c7205c71df47004c6f04c6e04c6b04c6a04c6704c6604c6304c6203c5f03c5e03c5b03c5a03c5703c5603c5303c5203b7f05b7d03b7703b7504b6f04b6703b5f03b5702b4f02b4e02b4d03a7f09a7d02a7b02a7903a7703a7502a7302a7104a6f02a6b04a6702a6303a5f02a5b03a5702a5302a3b02a3902a310397f0397e0197dde17c0397b039790397701975039730397205971059700496f0496b04967049630395f0395b03957039530594f0194d0594b05949059470194505943059410593b059370292f0592b05927029230387f0887d03877038750486f048670385f0685d03857038550584f0884d05847058450282f028270581f0581702e7f02e7e02e7d07d7f04d7b04d7706d7307d6f03d6d06d6b06d6907d6703d6506d6306d6105c7f05c7e04c7b04c7a05c7904c7804c7704c7605c7307c7205c7107c7005c6f05c6e05c6d05c6c05c6b04c6a04c6704c6604c6504c6405c5f05c5e05c5b03c5a05c5703c5605c5306c5205b7f04b7705b6f05b6d07b6a05b6705b6605b6505b6405b5f05b5702b4f02b4e02b4d02a7b02a7a02a7902a7704a7602a7302a7102a6704a6602a6502a5f02a5b02a5702a5302a3b02a3902a310597f0497b04977059730596f0196d0596b05969059670196505963059610595f0595b05957059530594f0194d0594b05949059470194505943059410593b059370292f0292b02927029230287f028770286f0286d02867028650285f028570284f0284d02847028450282f028270281f0281702e7f02e7e02e7d04d7f03d7d04d7b04d7904d7703d7504d7306d7104d6f04d6b04d6704d6304c7f04c7e05c7d05c7c04c7704c7604c7504c7404c7304c7204c6f04c6e04c6b04c6a04c6904c6804c6704c6604c6304c6205c6107c6005c5f05c5e05c5b03c5a05c5703c5605c5306c5204b7f04b7e05b7d05b7c04b7704b7504b7204b6f04b6705b5f05b5702b4f02b4e02b4d02a7f04a7e02a7d02a6f04a6e02a6b02a6902a6302a6202a6102a5f02a5b02a5a02a5709a5602a5302a3b02a3902a3102a300497f0197d0497b04979049770197504973059710496f0496b04967049630595f0595b05957059530594f0194d0594b05949059470194505943059410593b059370292f0292d0292b0292705925029230287f0287d02877028750286f028670285f028570284f0284d02847028450282f0282d02827028250281f0281703e7f03e7e03e7b04e7a03e7703e7603e7307e7203d7f03d7b03d7703d7302d6f02d6e02d6d05c7f05c7e05c7b04c7a05c7704c7605c7307c7203c6f03c6e05c6d05c6c03c6703c6603c6503c6403c6303c6203c5f03c5e03c5b03c5a03c5903c5803c5703c5603c5303c5205c5106c5005b7f05b7703b6f03b6e05b6d05b6c03b6703b6503b6203b5f03b5702b4f02b4e02b4d02a7f02a7b02a7a02a7709a7602a7302a6f03a6e02a6d02a5f03a5e02a5b02a5902a5302a5202a5102a3b02a3902a310597f0597b05977059730396f0196d0396b03969039670196503963059610395f0395b03957039530594f0194d0594b05949059470194505943059410593b059370292f0292d0292b0292705925029230287f028770286f0286d02867028650285f028570284f0284d02847028450282f0282d02827028250281f02817e056f06d6bdd56706d6305c6f05c6e05c6b04c6a05c6704c6605c6307c6205c5f05c5e05c5b03c5a05c5703c5605c5306c5205b6f05b6705b5f05b5702b4f02b4e02b4ddc26f02a6bdb26702a6306a5f02a5bda25702a5302a3b02a3902a310596f0596b05967059630595f0595b05957059530594f0194d0594b05949059470194505943059410593b059370292f0592b05927029234e06f460670685f320570584f0884d05847058450282f028270581f0581703e7f06e7e03e7d03d7b04d7a03d7903d7703d7603d7303d7103d6703d6603d6502b7f02b7b02b7702b7302b6f02b6d02b6b02b6902b6702b6502b6302b6102b5f02b5b02b5702b5302b4507a7e07a7c04a7604a7403a6e03a6c03a660da6403a5e03a5602a3e0797f0497b04977059730396f0196d0396b05969039670196503963039610395f0395b03957039530293f0293b0293702933059290e92801925d112404d6f02d6b02d6702d6303c6f02c6b02c6702c6303c5f03c5b03c5309b6e09a6604a5603a460996f0596b09967059630495f0495b04957049530394f0394b039470394304d6f04d6d03c6f03c6d03c5f03c5b03c5302a6f02a6d02a6b02a6902a6702a6502a6302a6102a5f02a5b02a5702a5302a4f02a4b02a4702a431396f1396e0196d0196c0596b059691396701965059631396205961059600495f0495b04957049530394f0394b03947039430292f0292b029270292304c5f04c5b04c5704c5303b5f03b5b03b5703b5303b4f03b4b03b430195f0295b01957019530294f0294b02947029430293f0293b029370293301d6f01d6b01d6701d6301c6f01c6b01c6701c6303c5f03c5b03c5301a6f01a6b01a6701a6302a5f02a5b02a5702a5302a4f02a4b02a4702a4302a350196e0196c01966d51640495e049560394e039460292e03e7f03e7e04e7d03d7f03d7e03d7d03d6f03d6e03d6b03d6903d6304d6203d6103c7e05c7c02b7f03b7e02b7dd737c02b7b02b7902b7702b7502b7302b7202b7102b7002b6f02b6b02b6702b6302b5f02b5b02b5702b5302b4503a7ed627c03a7603a7404a6e07a6c04a6604a6403a5e06a5c03a5603a5402a3e0397f0397e0197dd417c0397b039790397701975039730397205971059700496f0496b04967049630395f0395b03957039530293f0293b0293702933059290e92801925cf1240ec5f06c5b0ec5706c5302a5f02a5b02a5702a5302a4f02a4b02a4702a430595f0595b05957059530594f0594b05947059430292f0292b029270292303d6f06d6e03d6d03c6b04c6a03c6903c6703c6603c6303c6103c5703c5603c5502a6f02a6b02a6702a6302a5f02a5d02a5b02a5902a5702a5502a5302a5102a4f02a4b02a4702a430196f0196b01967019630195f0195d0195b01959019570195501953019510194f0194b01947019430192f0192b019270192303c5f03c5b03c5302a5f02a5b02a5702a5302a4f02a4b02a4702a430195f0495b01957019530194f0394b01947019430292f0292b029270292303d6f03d6e04d6d03c6f03c6e03c6d03c5f03c5e03c5b03c5903c5304c5203c5102a6f02a6d02a6b02a6902a6702a6502a6302a6102a5f02a5b02a5702a5302a4f02a4b02a4702a430196f0196e0196d0196c0196b019690196701965019630396201961d01600195f0195b01957019530194f0194b01947019430192f0192b0192701923d145f06c5bcf45706c5302a5f02a5b02a5702a5302a4f02a4b02a4702a430195f0195b01957019530194f0194b01947019430192f0192b0192701923d856f06d6bd356706d6302b6f02b6b02b6702b6302b5f02b5b02b5702b5302b4507a6e04a6606a5e03a5602a3ec116f0596bb7167059630695f0595bab157059530293f0293b029370293305929d212801925ce12405d6b05d6901c6f01c6d01c6b01c6903c6703c6501c6301c6103c5f03c5b03c5703c5315a6f09a6d15a6b02a6915a6709a6515a6302a6107a5f04a5b04a5707a5303a4f03a4b03a4703a4301967019650195b01957019530194f0194b01947019430192f0192b019270192305e7e01e7d01d6d03d6903d6501d6107b7e04b7a04b7607b7201b6e01b6d01b6c01b6a10b6913b6801b6609b6509b6401b6201b6101b6002b5e03b5a03b5602b5201a6d02a6909a6501a6103a5a03a560497a01979019760197101966019650195e039520193d01939019350193101e7f05e7e01e7d03d7f03d7b03d7703d7301d6f01d6d01d6b03d6901d6703d6501d6301d6103c5e07b7e04b7601b6e01b6c01b66cc36403b5607a7f04a7b04a7707a7301a6f01a6d01a6b02a6901a6709a6501a6301a6103a5f03a5b03a5703a5302a39cb2350197b0497a01979019770197601973019710196701966019650195f0195e0195b019570195303952019390593801935019340192f0192b019270192302d6f02d6d05d6b05d6904d6702d6507d6305d6111c6f03c6d06c6b06c6909c6703c6506c6306c6107c5f04c5b04c5706c5305b6f05b6d09b6b05b6705b6509b6305b5f04b5b04b5707b5305b4f09b4b05b4706b4301a6f01a6e01a6d07a5f07a5e02a5b04a5702a5307a5206a4f02a4b09a4702a4309a3f02a3b05a3702a330196f0196d0196b01969019670196501963019610195f0195b01957019530194f0194b01947019430193f0193b01937019330192f0192d0192b0192701925019231186f0886d0286b0986708865028630785f0285b04857028530684f0284b30047028430983f0283b05837028330282f0282b02827028230181f0181b018170181302d6f02d6d05d6b05d6902d6702d6502d6302d6101c6f01c6d01c6b01c6903c6703c6501c6301c6103c5f03c5b03c5703c5305b6f05b6d11b6b05b6705b6511b6305b5f04b5b04b5707b5303b4f03b4b03b4703b4301a6f01a6d02a6b02a6901a6701a6501a6301a6102a5f02a5b02a5702a5302a4f01a4b02a4702a4302a3f02a3b02a3702a330196f0196d0196b01969019670196501963019610195f0195b01957019530194f0194b01947019430193f0193b01937019330192f0192b01927019230286f0286d0286b0286702865028630285f0285b02857028530284f0284b02847028430283f0283b02837028330282f0282b02827028230181f0181b018170181301e7f05e7e01e7d03d7f03d7b03d7703d7301d6f01d6d01d6b03d6901d6703d6501d6301d6105c7f04c7b04c7707c7301c6f01c6d01c6b01c6705c6501c6303c5f03c5b03c5703c5302b7f02b7b02b7702b7301b6f01b6d01b6b02b6901b6702b6501b6301b6102b5f03b5e02b5d02b5702b5502b5302b5202b4f02b4b02b4702b4302a7f07a7e02a7b02a7a02a7704a7602a7302a7201a6f01a6e01a6d01a6c01a6b01a6a02a6902a6801a6701a6602a65c826401a6301a6201a6101a6002a5703a5602a5502a4f02a4b02a4a02a4705a4602a4302a3f02a3e02a3d0197b0497a01979019770197601973019710196701966019650195f0195e0195b0195701953039520194f0194b01947019430193f0193b01937019330192f0192d0192b0292a01929059280192701926019250192401923019210287f0287b02877028730186f0186d0186b0186702865018630285f0285b02857028530284f0284b02847028430283f0283b02837028330282f0282d0282b0282702825028230181f0181b018170181303d6f03d6b03d6703d6303c6f03c6e03c6b03c6a03c6703c6605c6305c6201c5f01c5e02c5b02c5a01c5701c5601c5301c5205b6f04b6b04b6707b6303b5f03b5b03b5703b5305b4f05b4d15b4b05b4705b4515b4307a6f02a6b04a6702a6303a5f02a5b01a5702a5306a4f06a4d01a4b01a4901a4701a4501a4301a4110a3f02a3b05a3702a330196f0196b01967019630195f0195b01957019530194f0194d0194b01949019470194501943019410193f0193b01937019330192f0192b01927019230786f0286b04867028630385f0285b03857028530c84f0884d0284b0c84708845028430c83f0283b05837028330282f0282b02827028230181f0181b018170181301e7f05e7e01e7d03d7f03d7e03d7b04d7a03d7703d7603d7307d7201d6f01d6e01d6d01d6c01d6b01d6a03d69c656801d6701d6603d6503d6401d6301d6201d6101d6003c7f03c7b03c7703c7301c6f01c6d01c6b03c6901c6703c6501c6301c6102c5f02c5e02c5d05b7f04b7b04b7707b7301b6f01b6d01b6b01b6705b6501b6303b5f05b5d03b5b03b5703b5503b5303b4f03b4b03b4703b4307a7f02a7b04a7702a7301a6f01a6d01a6b02a6901a6709a6501a6301a6103a5f03a5e06a5d03a4f03a4e02a4b02a4902a4303a4202a4110a3f02a3b05a3702a330197b0497a01979019770197601973019710196701966019650195f0195e0195d0195c0195b019590195701955019530395201951059500194f0194e0194b0194701943039420193f0193b01937019330192f0192b01927019230787f0287b04877028730186f0186d0186b0186708865018630385f0885d0285b0385703855028530384f0284b03847028430c83f0283b05837028330282f0282b02827028230181f0181b018170181305d6b05d6915c6f03c6d06c6b06c6915c6703c6506c6306c6107c5f04c5b04c5706c5301a6f01a6d01a6b01a6905a6705a6501a6301a6107a5f02a5b04a5702a5306a4f02a4b10a4702a4301967019650195b01957019530194f0194b01947019430192f0192b019270192301e7f05e7e01e7d07d7f04d7b04d7706d7301d6f01d6d01d6b06d6901d6703d6501d6301d6107b7e04b7601b6e01b6c01b66c436406b5e03b5607a7f02a7b04a7702a7301a6f01a6d01a6b02a6901a6709a6501a6301a6106a5f02a5b10a5702a5302a4905a350197b0497a01979019770197601973019710196701966019650195f0195e0195b01957019530595201939019350192f0192b019270192305d6b05d6911c6f03c6d06c6b06c6911c6703c6506c6306c6107c5f04c5b04c5706c5301a6f01a6d02a6b02a6901a6701a6501a6301a6102a5f02a5b02a5702a5302a4f02a4b02a4702a430196701966019650195b0495a0195701956019530194f0194e0194b0194701943059420192f0192b019270192301e7f05e7e01e7d07d7f04d7b04d7706d7301d6f01d6d01d6b06d6901d6703d6501d6301d6102b7f02b7b02b7702b7301b6f01b6d01b6b02b6901b6702b6501b6301b6102b5f02b5b02b5702b5302b4507a7e04a7601a6e01a6c01a66c226406a5e03a5602a3e0197b0497a01979019770197601973019710196701966019650195f0195e0195b0195701953059520193f0193b01937019330192905928019250192401d6f05d6e01d6d07c6f04c6b04c6706c6301c5f01c5d01c5b06c5901c5703c5501c5301c5105b6f04b6b04b6707b6301b5f01b5d01b5b01b5705b5501b5305b4fca34b05b4706b4307a6f04a6b04a6707a6301a5f01a5d01a5b02a5901a57c925501a5301a5106a4fc724bc524706a43c323f05a3b05a37c12330196b0496a01969019670196601963019610195701956019550194f0194e0194b0194701943069420193f0193b01937019330192f0192b01927019230786f0486b04867078630185f0185d0185b0185708855018530684f0a84b2e047068432003f0583b058370a8331202f0a82b0c0270a8230181f0181b018170181304d6f04d6b04d6704d6304c6f04c6b04c6704c6305c5f05c5b05c5705c5304b6f02b6e04b6b01b6a01b6701b6602b6302b6206b5f06b5e0db5b03b5a09b5703b5606b5306b5205b4f05b4b05b4a05b4705b4605b4304a6f02a6b04a6a04a6704a6602a6306a5f02a5b09a5702a5305a4f02a4b05a4702a4304a3f04a3e04a3d0196f0496b01967049630195f0595b01957059530194f0594b01947059430193f0193d0593b05939019370193505933059310192f0592b059290192702923059210486f0286b04867028630685f0285b0a857028530584f0284b05847028430a83f0883d0283b0983708835028330282f0282b02827028230581f0181b0181702813 20 1048575 8 255 11 2047 20 1048575
def cc_66_7 : Nat → List (Nat × Nat) := unpackCursorV4 0x97e4d8fa848996184c4d7d3797a82b77b2d73c3f6db6168e4d6127c5e72b5ba2d577434d99e4786143b3d40f2c3f31c3d41f38f4534a45309412c8412a82022f791e24d19a48118820d0480537d00053 0xf5bc07adc03d6b01eb500f59c07acc07d6303eb100f1bc078d603c6701e3180b16c058b202c570162980b1440b6de04b6702daf816d74056ae02b5501da780ad1c054de02a6b0153380a98c054be02a5d0152d80a964054ae02a550152980a9440549e02a4b0152380a90c0547602a3702cb78125ac092ce0596302caf8065740b2b60595902cab8065540b2a60595101ca780e52c0728e0394302c9d8164dc0525e0292b0149380a48c050de028670142f80a174050ae028550142780a11c0505e028270140f80a05c07cfe03e7e01f3d8139e807cee03e7601f3981f9c807afe03d7b01ebb80f5cc0b8fe04c7701e3780f1b80b8da03c5f01e2f00f148056fe02b7d015bd80ade8056ee04b76015ba80adbc076dc02b6d7f9b600adac056d202b67015b280ad8c056c402b61015b000ad7c056b602b57015a980ad2c0568e02a7f03d3f00a9f4054de03a6e01536bf89b0054d602a6a0153480a9a0054ce03a660153280e990054c602a620153080a980054be03a5e0152e81a970054b602a5a0152b80e958054aa03a540152980a9480549a02a4b0152500a91c0b48c02a4502d2200a8fc0547c02a3d02cbf8125ec092ee0597301cb78065b4072d60396901cb3806594072c60596101caf80e56c072ae0395302ca581651c0527e0293b0149b80a4cc0525e0192d014958164a40524e019250149180a484050fe028770143780a1b4050ce028650142f80a15c0507e028370141780a0b40504e028250140f80a05c0fade04d6b026b381b58c0f8de04c6b0263381f18c0d8bf0045b7ea2b81b14c056de02b6d015b580ada8056ce04b66015b280ad7c056b602b57015a980ad3c0569602b47015a180a9bc0f4dc02a6d0152f81a978054b602a5a0152b80e958054a602a520152780a92c0549402a4702d2300a90c0547e02a3e0151e81e5bc092d60496703cb181a57d642b6ad157034a9a9053d3229684147390a180a4fc05276029370149980a4bc0325a0292b02c9480a49c0324a029230149080a1bc050d6028670143180a17c050b6028570142980a13c05096028470142180a0fc05076028370141980a0bc0505a0282b0141380a094050460281f0140d80a05c0502602d6b016b500b59c05acc02d6301e3780f1ac078ce03c6301e2f80f174078b603c5901e2b80f154078a603c51015b7812d9c056be02b5d025ab812d540769e03b470153780a9ac054ce02a630152f80a974054b602a590152b80a954054a602a510152780a92c0548e02a430151d80a8dc0b2de0496b024b381658c0b2be0195d02cad8165640b2ae0195502ca98165440729e0394b01ca380e50c0b276059370149780a4ac0524e029230143780a19c050be0285d0142b80a1540509e028470141780a09c0503e0281701ebf80f5ec07aee03d7301eb780f5b407ad603d6901eb380f59407ac603d610263d0131dc098ec04c6702633013194078be03c57015bf80adec056ee02b73015b780adb4056d602b69015b380ad94056c602b61015af80ed78056ba02b57015aa80ad4c056a402b4b015a380a9fc0f4fc02a7b0153d00a9dc094ec02a730153900a9bc0b4dc02a6d02d3600a9ac054d402a690153400a99c0b4cc02a657d93200a98c054c402a610153000a95c074ac02a550152580a9280548e05a460151f80a8f80547a0597f024bd8125dc0b2e60596f00cb68165ac0b2d20596700cb281658c0b2c20395f01cad80e55c072a60594b02ca380a4fc05276029370149980a4bc0325a0292b02c9480a49c0324a029230149080a1fc050ee0286f0143680a19c050ca0285f0142b80a0fc0506e0282f0141680a09c0504a0281f0140b80f5bc07ad603d6701eb1816dbc056d602b67015b180ed7c076bc03b5701da980ed48054de07a6e0153580a99c054c602a620152b80e958054aa02a3f0951f00a8f40f2de0496b024b381658c072be0395b01cab80e54c2127e0593b04c9b8164cc0525e0192d0149580a49c0324a0292301eb780f5ac07ace03d6302db7816db8056d602b6a015b380ad98056c602b6201dab80ed58054de02a6b0153380a98c054be02a5d0152b80a954054a602a3b0151c81e5bc092d60496702cb180e57c072b60395701ca984a4fc0327a0593b02c9c84a4dc0326a0593302c9880a4bc05256029270149180f9fc07cf603e7701f398135d80b8fc03c6e01e3300adfc056f602b77015b980adbc076dc02b6d015b380ad94056c602b62015a480ad200568af93440153f81e9f8054f602a7a0153b8129d8054e602a720153380e998054ca02a490152400a915f048802a3f0151f00a8f40f2fe0497b024bb8165cc072de0396b01cb380e58c0b292019450149f80a4ec0526e02933014978064b4052560592901493806494052460292101eb780f5ac07ace03d637d2378371ac1b8cef746301e2f80f16c078ae03c53015b780adac056ce02b63015af80ed78056ba02b57015aa80ad4c056a402b4f015a580ad1c0568602a6f03d3700a9ac054d402a670253300a98c054c402a5701d2b00a9540549e02a4b0152500a91c0b48c02a430151f80a8f80547ac716f06cb583659c1d2c60395f01cad80e55c072a6a314f074a5a0851c1d2860293f0149d80a4dc052660292f00c9680a4ac0b2520292700c9280a48c052420286f0143580a19c050c60285f0142d80a15c050a60284f0142580a11c050860283f0141d80a0dc050660282f0141680a0ac0504e028250141180a07c05036028170140980f5bc07ad603d6701eb180f1bc078d603c6a01e3380f198078be03c5e0162d80b168078ae02c5601e2980f148076de04b6701daf80ed5c0969e04b4d01da380ed140f4de02a6b0253380a98c074be02a5b01d2b80a94c0d49e06a4d0152580a9240b48e05a450152180a9040547605a3702cb78125ac092ce0596301caf80e56c072ae0395302ca78065340b2960594902ca38065140b2860594102c9d8164dc0525e0592b02c9380a48c0f0de0486701c2f80e15c1909e0884d064238221140505e0282702c0f81605c07afe03d7e01ebd8135e807aee03d7601eb981f5c807ade03d6e01eb680f5b007ad605d6a01eb4bd55a007ace03d6601eb280f59007ac605d6201eb0817580078fe03c7b01e3b80f1cc078de03c6d01e3580f1a4078ce03c6501e3180f184058be02c5e0162e812de8096ee04b76025b3812d98096ca03b5f01daf016d740b6b803b5701daa80ed480769e03b4703d3f80a9ec094ee02a7302d378169b4054d602a6902d33826994054c602a6101d2f80e9780d4ba03a4f01d2700a92c0549202a4301d2100a9040547605a3702cbf8125ec092ee0597302cb78065b40b2d60596902cb38065940b2c60596101caf806574072b60395901cab806554072a60595101ca780e52c0728e0394302c9d8164dc0525e0592b02c9380a48c0f0fe0487702c378161b40b0ce0886501c2f822174070ae0385501c2780e11c0505e0282702c0f81605c07ade03d6b01eb380f58c078de03c6e01e3580f1a8078ce03c6602e31817188058b602c5a03d3780a9ac094ce02a6301d2f80a96c054a606a4f0352681e5bc092d60496702cb180e57c072b60395701ca982653c0329a0594b02ca482651c0328a0594302ca080a4bc0b256099270149180f5bc07adc03d6b01eb380f58c0fac403c6f01e3580f19c078c602c5f0162f00b174076bc05a6f0153581299c0f4c603a5f01d2f00e93c0749c03a4b01d2480e90c0748406a4103cb78125ac092ce0596301caf806574072b60395700caa80e54c0729e0394b01ca380e50c1325e0592b04c9381648c07cfe03e7e01f3d8139e807cee03e7601f3981f9c807afe03d7b01ebb80f5cc05ade02d6e016b68131d8078dc05c6c02dbf00edb9e66d803b6601db200ed780d6b803b5601daa01e9fc054f604a770153980e9bc074dc06a6d01d2f80e978054b602a590152980e948054a202a390151c0268d5e44680797f024bd8125dc0b2e60396f00cb680e5ac072d20396700cb280e58c0b2c20395f01cad80e55c072a60593900c9a80a4bc0b256099270149180b9fc05cfc02e7d01ebf80f5f807af604d7a01ebc8135e007aee03d7601eb981f5c807ae207d7001eb780f5b807ada03d6c01eb58135a807ad204d6801eb380f59807aca03d6401eb181b58807ac206d6001e3f80f1ec078ee03c7301e3780f1b4078d606c6a01e3481b1a0078ce03c6601e3280f190078c603c610162f80b178058ba07b7f025bd812ddc0f6e607b6f02db681edac0f6ce05b6503db180ed7c0b6ba03b5b01dab80ed54076a603b4f01da580ed1c0768602a7b0153d00a9e4054ee04a760153980a9c4054ce04a660153280a97c074bc02a5d0152780e9380549602a490152180a9080548202a3f0151d80a8dc054660797f024bd8125dc0f2e60796f00cb681e5ac0b2d20796700cb281e58c0b2c20395f00cae80e56c072b20395700caa80e54c0b2a20394f01ca580e51c072860993f04c9d8264dc132660292f0149580a49c052460287f0143d80a1dc050e60286f0143680a1ac050ce028650143180a17c050ba0285b0142b80a154050a60284f0142580a11c050860283f0141d80a0dc050660282f0141580a09c050460281f0140d80a05c0502603d6f01eb700f5ac09ad403d6701eb300f58c0fac403c6f01e3580f19c078c602c5f0162f00b175e86de0db6b06db3bc4d8c076be05b5d01dad80ed5c076aa03b5301da780ed2c0768e03b437813780a9ac1b4ce02a6301d2f80e9780d4ba03a4f01d2700a92c0549202a4301d2100a905ce47e02a3b6d11b80a8cd8a2de0d96b06cb383a58c072be0195d01cad80e564072ae0195501ca98165440729e0394b01ca380e50d4427e0e93b4009b83a4cc0525e0e92b2989380a48c190de0286b0643380a18c070be0885d0142d80e15c070aa0285301c2780a12c0708e028430641f80a0ec1906e028330141780a0ac0504e028230640f80a06c1902e0281301f3f81b9f807cfa03d7b026bd00f5e407aee03d7601eb980f5c407ace03d6601eb281edf8096ec03b6e01db600ed981b6c803b5e01dab01e9fc054f604a770153980e9bc074da02a6b0153480e99c134ca02a630153080e97c054b603a570152980a9240b46a0797f024bd8125dc0b2e60396f00cb680e5ac0b2d20396700cb280e58c072c20395f01cad80e55c072a60593900c9a80a4bc0b25612927014918135bc09ada03c6f01e3680f17c078b603c5302d378169b4054d602a6901d3380e994054c602a610252f80a96c094ae02a5301d2780a92c0748e02a430151c85e5bc032da0596b02cb485e59c032ca0596302cb081257c092b604957024a980e53c072960394701ca180a4bc0b25612927014918135bc05ad604d67026b180f1bc058d603c6701e3180f17c078b603c5304db300e998074c804a5601d230265bc0b2d60996702cb181257c092b604957024a980e53c072960394701ca18075bc03ad601d6700eb18071bc038d601c6700e3180f17c078b603c5300d37006998094bc04a5601d2700e918032de0196b00cb380658c092be0295b024ab80a54c0729e0294b01ca380a50c052720592501f3f80f9f809cfa03d7f01ebf00f5f407ade03d6e01eb580f5a407ac604d6201eb080edf9da6f803b7601dba012db8096cc03b5e01dab00e9fc074fc09a7d7613e00a9ec054f203a7701d3a80a9cc074e402a71015380129bc054d604a670153180e97c054b603a570152980a9240b46a0397f01cbf0065f5d62f80397b01cbc80e5dc032ea0397301cb90165c40b2e00496f024b581259c092c60395f01cad80e55c072a60593900c9a80a4bc0b256129270149180b9fc05cfc02e7d03ebf8135ec09aee06d7303eb780f5b40dad606d6903eb380f5940dac606d6103e330171900f6fc07b7c025bb012dd00b6dc05b6c025b3012d900d6bc03b560153d80a9e8054f202a770253b00a9cc054e202a670253300a994054be06a5e0152d80a95c054a602a520152480a8d40f2fe0497b024bb8165cc0f2de0196d02cb58165a40f2ce0196502cb18165840d2be0595b084ab81654c0b272019350149780a4ac0b252029270149180a48405cfe02e7e0173e8135fc07afa04d7b026bc8135dc07aea04d73036b88135bc09ad604d67026b18131f80b8f804b7e02dbe012dd8096e804b6e03db6012d98096c806b5e01dab00a9fc094fc02a7d015378129b8054d602a690153180a988054c202a5f0152d80a95c054a602a490151a8125fc032fa0497b024bc8125dc032ea0497302cb88125bc092d604967024b181a57c0b2b60d95702ca98164e40326a0292f0149580a49c0524603e7f01f3f00f9ec09cf403e7701f3b00f9cc0fce403d7f01ebd80f5dc07ae602d6f016b700b5b4078dc05c6c03dbf012dd8076dc05b6c01db300ed90076bc06b5c01dab00ed50054fe02a7b0153b80a9cc054de03a6e0153680a97c074bc02a5b0152c80a94c054a402a510152480a8d4212fe0597b06cbb8165cc072de0196d01cb580e5a4072ce0196501cb1816584072be0395b01cab80e54c0b272019350149780a4ac0524e02923772b781b5add4ace06d6303db7012d980d6bc03b567493780a9add04ce02a630352f80a96dce4ae02a53015248168d5862de0596b5d0b381658c0d2be0595b560ab81654c0b27201935014978164aca424e0292301f3f81b9f807cfa03d7b026bd00f5e407aee03d7601eb980f5c407ace03d6601eb28171fc098ee03c6f01e3680f19c0b8ca03c5f01e2b80adfc056f602b77015b980adbc056da02b6b015b480ad9c056ca02b63015b080ad7c056b602b57015a980ad340568e02b450153f81e9f8054f602a7a0153b8129d8054e602a720153780e9b8054da03a6c0153580a9a8054d202a680153380e998054ca0da640153180a988054c202a600152f80e978054b602a5a0152b80e958054a602a52015238169180548a0597f024bd8125dc0b2e60396f00cb680e5ac0b2d20396700cb280e58c072c20395f01cad80e55c072a60594b02ca380a4fc05276029370149980a4bc0325a0292b02c9480a49c0324a029230149080a1fc050ee0286f0143680a19c050ca0285f0142b80a0fc0506e0282f0141680a09c0504a0281f0140b8135bc09ada02d6b016b480b59c05aca02d63016b080f1bc078da02c6b0163480b19c058ca02c630163080f17c078b602c5701e29816dbc0b6da03b6701db2812d7c096ae03b4f01da380a9bc054da02a6b0153380a994054be02a5b0152b80a94c0549e02a4b0152380a90c0547602a3702cb78065b40b2d60596902cb38065940b2c605961024af81256c092ae0495301ca780e52c0728e0394302c9d8164dc0525e0292b0149380a48c050de0286d0143380a194050be028570142780a11c0505e028270140f80a05c03ade01d6b00eb380758c038de01c6b00e3380718c078be03c5b0162b80f14c036de01b67025af812d5c0769e03b4700d378069ac034ce01a630152f80a96c054ae02a530152780a92c0548e02a430151e80a8dc0546a0196f00cb70065ac032d40196700cb300658c032c40295f024af00a56c052b402957024ab00a54c052a40294f01ca700a52c052940294701ca300a50c052840293702c9b00a4d4030de018670142f80a15c0509e028470141780a09c0503e0281d0140b80a05407cfe03e7e0273e80f5fc07afc03d7d01eb780f5b807ad603d6901eb181358807ac203c7f01e3f0171f40b8f803c7701e3a80f1c8098de04c6701e2f80f15c056fe02b7d015bd80ade4056ee02b75015b980adc4056de02b6b015b380ad8c056be02b5b015ab80ad4c0569a02b47015a280a9fc074fc02a7d7213e00a9ec054f402a790153c00a9dc074ec02a7501d3a00a9cc054e402a710153800a9bc094dc02a6b0153500a99c094cc02a630153100a97c074bc02a5b0152d00a95c074ac02a530152900a91c0b48c02a4501cbf80e5f8032fae317c01cbd80e5e4072ee0197501cb980e5c80b2e205970024b78125ac092ce0496301caf80e56c072ae0395302ca581651c0527e0293b0149b80a4cc0525e0192d014958164a40524e019250149180a484050fe0287d0143b80a1d4050de028670142f80a174050ae028550141f80a0dc0505e0282d0141380a0940503e0281772ab781b5adc4ace06d6302e3781719c0b8be05c57015b780adac056ce02b63015af80ad6c056ae02b53015a680ad1c0568a02a6f03d3700a9ac054d402a670253300a98c054c402a5f0352f00a96c054b402a5701d2b00a94c054a402a4702d2300a9140b2de0596b02cb381658c0b2be0595b02cab81654c0b296059470149f80a4ec0526e02933014978064b405256059290149380649405246029210143780a19c050be028570141f80a0dc0505e0282d0141380a0940503e0281701f3f81b9f807cfa03d7b026bd00f5e407aee03d7601eb980f5c407ace03d6601eb28171fc0b8fc04c7b0263d0131dc098ec05c7303e3900f1bc078dc03c6d01e3600f1ac078d405c6906e3400f19c078cc05c6502e3200f18c078c403c6101e3000f17c078bc03c5b01e2d00f164078b003c5701e2b00f14c078a405c5103628016dfc096ee03b6f01db680ed9c0b6ca03b5f01dab80ad3c0569c02b4d03d3f80a9ec094ee02a7301d3780e9b4054d602a6901d33826994054c602a6101d2f80a96c074ae02a530151d80a8e4054620597f024bd8125dc0b2e60396f00cb680e5ac0b2d20396700cb280e58c072c20395f01cad80e55c072a60594f00ca681652c0b2920594700ca281650c0b2820593b02c9b80a4bc0b256059270149181e1fc090ee0386f01c3680e19c110ca0385f01c2b81613c1109a0584702c2280a0bc0504e0581f02c0b80f5bc07adc03d6b01eb380f58c09ac404c6f0263380f17c078ae04b6f025b7012dac096d404b67025b3012d8c096c403b5f01daf00ed6c076b403b5701dab00ed4c076a402b4b015a500ed1c0568c04a6f0153581299c054c603a5f0152d80e95c054a602a4b0152480e91c0548202a3b0151c80e8dc0546602a31024b78125ac092ce0496301caf80e56c072ae0395302ca581651c0b27e0193d02c9d8164e40b26e0193502c998164c40525e0592b02c9380a48c090de0486701c2f81a174070ae0385505c1f8220f41706e088350141780a09c0b03e05817 20 1048575 8 255 11 2047 21 2097151
def cc_66_8 : Nat → List (Nat × Nat) := unpackCursorV4 0xf2f87966bde0f35a3cc9b9f00ccb7322c3b2ace828bd09cec267989073226b685a81fdb27b681c6ce68b218d2b5baf5484d4931ce67d2d7848561153843f2b07efc003f 0x1eb781b5b807ada03c6b0263500f1a4078ce03c6601e3180f184078ae03c5601e2a81edbc096d604b6703db180ed7c076ba03b5b01dab816d54076a603b4f01da580ed1c0768607a6f0253581299c0f4c603a5f01d2e80e96c054b203a5706d2a80e94c054a203a4f01d2580e91c07486ee23f7291db808ddb04660796f024b581259c0f2c60395f00cae80e56c0b2b20395700caa80e54c072a20394f01ca580e51c07286a913f0749da584dc1d2666d12f0749597c49c1d2460786f0243581219c0f0c60385f01c2e80e16c070ae0885501c2980e13c070960384701c218320fc170760c83705c198320bc170560c82705c1183207c170360c81705c098135bc09ada02d6b016b481359c09aca04d63016b080f1bc078da02c6b0163480f19c078ca03c630163080f17c078b603c5701e29826dbc0b6da09b6b04db3816d94136c604b5f025ad812d5c096a603b4f01da580ed1c0768603a6701d3300e994094be02a5b0252d01295c094ac02a5301d2780a92c0749403a4701d2300a90c1347eec23e0151d8268dc05466d723204cb78065b41d2d605969084b3806594132c605961024af81256c092ae0495301ca780e52c0728e0394304c9f83a4ed1a26e09933014978264ac1324e0292304c378221b4050d60b8670443280a18c090be0285b0242b80a14c0709e0284b01c2380a10c1307e0283b05c1b80a0cc0505e0282b05c1480a09c050460b82105c0f80a06c1702e0281300e2f80716c038ae01c5300daf806d6c036ae01b5301da780ed2c0768e03b4300d2f80696c034ae01a530252781292c0948e04a4301d1f80e8ec0746e03a3300caf80656c032ae01953024a781252c0928e0494301c9f80e4ec0726e0393375897b8c4adbc24ed412300c2f80616c030ae018530242781212c0908e0484301c1f80e0ec0706e0383305c1782e0ac1704e0b82305c0f82e06c1702e0b81301e2f80f16c078ae03c53025af812d6c096ae04b5301da780ed2c0768e03b430252f81296c094ae04a5301d2780e92c0748e03a4302d1f8168ec0b46e05a33024af81256c092ae0495301ca780e52c0728e0394302c9f8164ec0b26e0593302c978164ac0b24e059230242f81216c090ae0485301c2780e12c0708e0384302c1f8160ec0b06e058330541782a0ac1504e0a82302c0f81606c0b02e0581301eb780f5b809ada03c6f01e3700f1b4078be03c5e01e2d80f164078a604c5201e2880edbc0b6da03b6b01db380ed94076c604b5f025ad812d5c096a603b4f01da580ed1c0768603a6f8d93680e9ac054d203a6701d3280e98c054c204a5f0252d81295c094a603a4f01d2580e91c07486ea23f7111db748dda64660396f01cb70065b6342d80396b01cb480e59c032ca0396301cb1016586322c00495f024ad81255c092a60394f01ca580e51c07286a813f0749da304dc1d2666b12f0749597449c1d2460386f0443680e1ac070ce0386501c3181217c090b6048570242980e13c0d09a0384b01c2380e114070860b83f05c1d82e0dc170660b82f05c1582e09c170460b81f05c0d82e05c1702602d6b016b501359c05acc07d6303e378131ac098ce06c630962f80f1740d8b606c5904e2b80f1540d8a606c5102db7812d9c0b6be04b5d025ab812d540b69e05b4703d3781e9b8054d604a670153181e9880b4be05a5e02d2e81a93c0549609a470152180a8ec0b47405a3702d1b0165bc092d60496702cb181657c032ba0595b02cac81655c032aa0595302ca881653c0b2960594702ca18164ec0b26e0292f02c9581649c052460786f0243385e17c110ba098570442a81a13c7408e0282f0141381607c0b02e07c6f0263581319c0d8c605c5f01e2e81716c0d8b205c5701e2a81714c0b8a204b6a025b3812d98096ae04b56025aa816d3c0b68e07a6f0253581299c0f4c605a5f02d2e81696c054b205a578b92a81694c054a206a4f7d125bd091c0d48605a3b02d1b8165bc092d60496702cb181657c032ba0595b02cac81655c032aa0595302ca881653c0b2960594702ca18164ec0b26e0592f02c9581649c0b2460786f0243381617c0b0ba058570442a81a13c7208e1402f0681381607c0b02e04d6f026b581359c09ac604b6f015b7012dac096d404b67025b300ad8c056c406b5f035af036d6c076b409b5701dab01ad4c0d6a404a6f015358129a8094ce04a660153181a97c054b609a57015298125bc092d604967024b181a57c0b2b60d95702ca98424fc0327a0593b02c9c8264dc0326a0593302c9880a4bc0b25609927014918135bc09ad604d67026b18131b8096cc06b5e01dab0129bc094d604a670253181a97c1b4b60da570352980a8e62a46a0496f024b581259c092c60695f02cad83655c0b2a60593900c9a9a44bc0b2565b12702c9180b5ac05ad204d67026b180b584138de03c6d0363581b1a41b8ce03c650363181b184098be04c5b0262b81314c0b6de05b6d02db3816d94096be04b5702da7816d1c094ce04a660253281297c054b604a5a0252b812958054a606a4f0352700a92c1348e02a430352100a8ec0b47405a3702d1b0165bc032da0596b02cb481659c032ca0596302cb081257c092b604957024a981653c0b2960594702ca18164ec0b26e0292f02c958164a40b24e0292302c908261bc110da0b8670443281217c090ae0684f05c2380a0bc0504e0581f02c0b81315c098a608b5f035ad822d5c0d6a604b4f025a5812d1c0968605a5f02d2b81293c0948e05a3f02d1b82257c112b608957044a981253c0929604947024a181a4fc1b2760d937034998164ac0b24e0585f02c2d81615c0b0a60484f0242581211c090860583f02c1d8160dc0b0660582b02c1381607c0b0360581702c0981317c098b604c570262980a97c054b602a570152980a93c0549602a470152181257c092b604957024a981653c0b2960594702ca180a4bc0525602927014918131bc078da04c6b0263481319c078ca04c630363081317c098b604c5702629812dbc096dc05b6d025af812d78096a405b4f02da38129be264da04a6b0153481299c094ca04a630153081297c094b604a570252981a93c1b4960da47035218168ec0b46e0496f00cb68125ac092d20496700cb281258c0b2c20495f024ad81255c092a60594f02ca581651c0b2860593b02c9b8164bc0b2560592702c918121bc090dc0886d8903601219c090ca048628883001217c090ae0684f05c2382e0bc1704e0581f02c0b81f5bc09ad604d67036b1816dbc0b6dc02b6b015b5012d9c056cc07b6302db101ad7c0d6bc12b5b01dad026d5c076ac06b53035a901e9bc0f4dc02a6b0253380a98c0f4c406a5f0152dbe4968134aef22560152981e5bc092d60496702cb181a57c0b2b61995702ca98424fc0327a0593b02c9c8264dc0326a0593302c9880a4bcd025a0592b04c939644940524607d6f026b581359c0dac604c6602db701ad78076ac07a6f0253581299c0f4c606a5f7b92dbc495c0d4a602a398791a81e5bc092d60496702cb181a57c0b2b6af15702ca98164e40326a6612f02c9596049c0b24603d6f01eb580f59c07ac609b6f03db7036dac096d409b67025b304ed8c0f6c403b5f015af00ed6c076b403b5701dab00ad4c056a409a6f0153582699c054c603a5f0152d80e968074ae03a5601529b2c5bc0b2d60d96702cb180e57c072b60395701ca98424fc0327a0593b02c9c8264dc0326a0593302c9880a4bc0b256099270149180f5bc07ad603d6701eb180f1780f6dc04b6601dab4209bc1b4d60da678013180e97c074b603a5701d2980a8e61a46aca16f02cb583659c0b2c60395f01cad80e55c072a60593900c9a9904bc0b2565612702c9184f5bc0fadc09d6b026b503759c09acc09d6303eb100f1bc078d603c6701e3180b16c058b203c5701e2980b1440b6de05b6702daf816d740b6ae05b5501da780ed1c134df0626e0153582699c054c6ff26201d2b80e958074aa03a4f0152580e9280748e03a460152180a8ec0b47405a3702d1b0165bc0b2d60596702cb181657c032ba0595b02cac81655c032aa0595302ca880e53c072960394701ca18164ec0b26e0292f02c9581649c052460c86f0643382617c110ba0c8570442a80e13c0708e0282f0141381607c0b02e03d6f01eb700f5ac09ad403d6701eb300f58c0fac403c6f01e3580f19c078c605b6f02db380ed7c076bc05b5d01da780ed38076850526f06d3583699dfa4c603a5f8592e80e96c054b203a5701d2a80e94c054a203a4f01d2580e91c0748605a3b02d1b8165bc0b2d60596702cb180e57c032ba0395b01cac80e55c032aa0395302ca880e53c072960394701ca18164ec0b26e0592f02c9581649c0b2460c86f0643380e17c110ba0385701c2a80e13c0708e0c82f0641381607c0b02e02d6b016b480f1bc078da03c6b01e3480f19c078ca03c6301e3080f17c078b603c5701e2981299c094ca02a5b0252b80a94c0749e02a4b01d2380a90c132de0196d02cb58165a4132ce0196502cb18165840f2be0495b024ab81654c0729e0394b01ca380e50c0525e0592b04c9380a48c05cfe02e7e0173e80f5fc07af603d7701eb980f5bc07ada03d6b01eb480f59c07aca03d6301eb080f1780f6fc04b7603db701edb00f6cd0936401dab00a9ec094f402a790253b8129d8054e602a7102533812998094ca03a5f0152d80e95c054a602a3904d1a81e5fc092f60497702cb981e5bc032da0596b02cb481e59c032ca0596302cb080e57c072b60395701ca98164e40326a0292f02c9582649c0524603d6f01eb580f59c07ac603c6f0163700f1ac078d403c6701e3300b18c058c403c5f01e2f00f15c078a603c5202db7812d9c076be03b5702da7816d340b68e05b4501d3780a9ac094ce02a6301d2f80a96c074ae02a53025278129340549602a4901d2380e9140548602a410151d8168dc0b2de0496b024b381658c072be0395b01cab80e54c0b29e0194d02ca58165240b28e0194502ca18165040b27605937014978164ac0b24e0292303c3781219c070be03857064278221341908e088450141780a09c0b03e05817016b780b5b805ada07c6f03e368131ac098d404c6702633027194078c603c5f01e2e81316c098b403c5701e2b00f154078a803c5301db780edac076ce03b6301daf80ed74076b603b5701daa80ed4c0569603b4701da18169bc094ce05a5f02d2e81695c0b4aa05a4f02d2380e8fc0746e0596f024b581259c0b2c60595f02cad81655c0b2a60594f02ca581651c0b2860393f01c9d80e4dc072660592b02c9381e1bc090ce0785f03c2b82613c1308e0383f01c1b81607c0b02e02e7f0173f00b9f407afe03d7e01ebd8135e807aee03d7601eb981f5c807ade03d6e01eb680f5b007ad607d6a01eb4c1d5a007ace03d6601eb280f59007ac607d6201eb081f580078fe03c7b01e3b80f1cc078de03c6d01e3580f1a4078ce03c6501e3180f1840b6fe04b7702db7816db40b6ce05b6501daf80ed780b6ba03b4f01da700ed08054f604a7a0153c8129dc094ec02a730153881299c094cc04a6501d2f80e978134bb0625c0152d80a964074ae03a550152980e948054a202a5001d2780a92c0748e02a430151d8168dc0b2fe0497b024bb8165cc0b2de0196d02cb58165a40b2ce0196502cb1816584072be0195d01cad80e564072ae0195501ca98165440729e0394b01ca380e50c0b27605937014978164ac0b24e0292303c3f8121dc0f0de0786d03c33822194070be0885d01c2b80e1540709e038470141780a09c0b03e05817016b780b5b805ada07c6f0263581319c0d8c607c5f01e2e81b16c0d8b207c5701e2a81b14c0d8a207b6f025b5812d9c0f6c607b5f02dae81ed6c0f6ae05b5503da981ad3e1069705347035a180a9ac094d402a6902533812998054c602a610252b812958094aa06a4f01525bc091c05486e923f0151db708dc054660796f024b581259c0f2c60795f00cae81e56c0b2b20795700caa81e54c0b2a20694f598a5ab851c0d286a713f4f89da284dcf02660292f3109595449c052460786f0143581219c050c60785f03c2e80a16c0f0ae088550142981a13c0509637047014218940fc050761a0370141980a0bc05056028270141181c07c0503603017014098135bc09ad604d67026b18131bc098d604c670263181b17c1b8b60dc570362980adbc096dc02b6d015b380ad94056c602b62015af80ad6c056ae02b53015a780ad2c0568e02b4301533812998054ca02a5f0352f00a96c054b402a5701d2b00a94c054a402a4f0152580a9280548e05a460152180a8fc0547c02a3d024b78125ac092ce04963034af83656c1b2ae06953530a7a7452d1028e761430149f80a4ec0526e02933014978064b405256059290149380649405246029210143780a1ac050ce028630142f80a16c050ae028530142780a12c0508e028430141f80a0ec0506e028330141780a0b405056028270141280a08c0503e0281b0140b80a04c05ade02d6e016b68131bc078da04c6b0263481319c078ca04c630363081317c098b604c5702629812dbc0b6da04b6b025b3812d94096c604b5f025ad812d5c096a606b4f06da5836d1c0d68604a6f0253701e9b4094be04a5e0152d80a964054a604a520152881a93c054960da4701521ba08fc05476db237015198125bc032da0496b024b481259c032ca0496302cb081257c092b604957024a981a53c1b2960d947034a1a944fd36276861373a09980a4bcc225654127014918121bc110da0286b02433812194050c60485f0142d81215c050a60684f0142582e11c050860b83f0141d82e0dc050660282f0141580a09c050460b81f0140d82e05c0502603d6f01eb580f59c07ac607b6f03db700ad7c056bc02b5b015ad00ed5c076ac02b53015a900a9bc054d602a670152f80a96c054ae02a530151d80a8e40f2de0496b024b381658c072be0395b01cab80e54c2727e0193d02c9d8164e42726e0193502c998164c40525e0292b0149380a48c07cfe03e7b01f3b80f9cc07adc07c7e0263b00f198056fe02b7d015bd80ade8056ee04b76015ba80adbc056d602b67015b180ad240568a02a7f03d3f00a9f4054de03a6e0153580a9a8054ce03a660153180a988054aa05a540152480a9200548b012440151f80a8f80547a0797f024bd8125dc0b2e60396f01cb580e59c072c60594900ca280a4fc05276029370149980a4bc0325a0292b02c9480a49c0324a029230149080f5bc09ad604d6a026b38135980fac603c6f01e3580f19c078c602c5b0162b80b14c0b6de04b6702daf80ad5c0769e02b470153781e9b8054da02a5709d2b00a9540549e02a4b0152500a91c0748c02a430151d80a8e80546e05a3602cb78125ac092ce0596302caf81656c0b2ae0595301ca780e52c0728e0394302c9d8164dc0525e0292b0149380a48c050de028670142f80a15c0509e028470141780a09c0503e02817 18 262143 7 127 11 2047 21 2097151
def cur_66 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_66_8 (Nat.sub p 256)) (cc_66_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_66_6 (Nat.sub p 192)) (Nat.blt p 224)) (Bool.rec (cc_66_5 (Nat.sub p 160)) (cc_66_4 (Nat.sub p 128)) (Nat.blt p 160)) (Nat.blt p 192)) (Bool.rec (Bool.rec (cc_66_3 (Nat.sub p 96)) (cc_66_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (cc_66_1 (Nat.sub p 32)) (cc_66_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 128)
def f_66 : Nat → Nat × Nat := unpackForestF 0xc5f8ca6d8c96c8c96000c578ba5500b5f8aa3500b5b88a6d8886c8886000b5787a3500b5386a3500b4b85a5d00b4784b6482b4b835688325c82b4700a5f00a5b00a5780a447ec5b7f36c7f26c7ec5700a537da647bc6f7c3447c2447bc6300a4b7ad687836f7936c79234783637826f00a4773d6f75b7c75a7c7597c73d6773a6f73a6773a5700a3f7156f71a7c7197c7156700a3b6d56f6f4706f17c6d5676d26f6d2676d25700a376756f6a37c6a27c6a9646a17c675676712867c5f6816067c576712400a3365b6465a3560b4b60a556426460a4b6356860a476236460a3f6126460a330095f5f9360095b5ba6d5db7c5da7c5ba3f5c37c5c27c5ba33009575a9360095358b6f58b63589360094b55b6355a6f55a6355a3f55a33009475156f515675126f5126b51267512635125b512570093f501644c36f4f1344c36b4e17c4c3674d1344c3634c1360093b3dd6f47a3f4a34c47a3b47a3748a3c4834447a3346c7046a7d3dd6745c683da6f44a5c3da6b43c703da6742a5c3da6341a5c3da5b40c603da573e56f3e5673e26e3e2623da4d009373c96437b6f3b93437b6b3a97c37b673993437b633826a3826637936009333256f3627c32567352443246b33b4433a443246332a443245b0092f30b6f30b670092b28d6f2f37028d672e34828c6b2cb482ca4428c632bb4828c5b28a6f28a6728a5728a4f2894a009270092325a3726a4d25937259270085f0085b2026d23c702023721c7021a7d21a4d2013720b7020127008571f054008530084b1d5681d2651436f1c5681426f1ab6f1aa6e1425d19c601423717d6817a6517a5d1416f15c6015a6d15a4d1413714b601412700847133640ea6f124630ea3510b6410a350e96f0f3480f2440e9270083f0083b0d26f008370b82c0b824008330aa640846f09a640816f08a5c081470082f0082b05c6f0596f059470082700823041640336f031360081f0081b01b6f00817008130003f 9 11
set_option maxHeartbeats 0 in
theorem rc_66 : dagCheckRootsV4 fullMask g_66 ep_66 285 bds_66 (dagTraceF fullMask rootStock 11 f_66) (cur_66 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_0 : treeBlockF 0 32 (dagCheckNodeV4 fullMask g_66 ep_66 bds_66 285 (dagTraceF fullMask rootStock 11 f_66) cur_66) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_1 : treeBlockF 32 64 (dagCheckNodeV4 fullMask g_66 ep_66 bds_66 285 (dagTraceF fullMask rootStock 11 f_66) cur_66) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_2 : treeBlockF 64 96 (dagCheckNodeV4 fullMask g_66 ep_66 bds_66 285 (dagTraceF fullMask rootStock 11 f_66) cur_66) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_3 : treeBlockF 96 128 (dagCheckNodeV4 fullMask g_66 ep_66 bds_66 285 (dagTraceF fullMask rootStock 11 f_66) cur_66) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_4 : treeBlockF 128 160 (dagCheckNodeV4 fullMask g_66 ep_66 bds_66 285 (dagTraceF fullMask rootStock 11 f_66) cur_66) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_5 : treeBlockF 160 192 (dagCheckNodeV4 fullMask g_66 ep_66 bds_66 285 (dagTraceF fullMask rootStock 11 f_66) cur_66) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_6 : treeBlockF 192 224 (dagCheckNodeV4 fullMask g_66 ep_66 bds_66 285 (dagTraceF fullMask rootStock 11 f_66) cur_66) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_7 : treeBlockF 224 256 (dagCheckNodeV4 fullMask g_66 ep_66 bds_66 285 (dagTraceF fullMask rootStock 11 f_66) cur_66) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_8 : treeBlockF 256 285 (dagCheckNodeV4 fullMask g_66 ep_66 bds_66 285 (dagTraceF fullMask rootStock 11 f_66) cur_66) = true := by decide +kernel
theorem nj_66_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 fullMask g_66 ep_66 bds_66 285 (dagTraceF fullMask rootStock 11 f_66) cur_66) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_66_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_66_1 h1 h2)
theorem nj_66_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeV4 fullMask g_66 ep_66 bds_66 285 (dagTraceF fullMask rootStock 11 f_66) cur_66) i = true := block_join nj_66_1 (fun _ h1 h2 => treeBlockF_at nb_66_2 h1 h2)
theorem nj_66_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeV4 fullMask g_66 ep_66 bds_66 285 (dagTraceF fullMask rootStock 11 f_66) cur_66) i = true := block_join nj_66_2 (fun _ h1 h2 => treeBlockF_at nb_66_3 h1 h2)
theorem nj_66_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeV4 fullMask g_66 ep_66 bds_66 285 (dagTraceF fullMask rootStock 11 f_66) cur_66) i = true := block_join nj_66_3 (fun _ h1 h2 => treeBlockF_at nb_66_4 h1 h2)
theorem nj_66_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeV4 fullMask g_66 ep_66 bds_66 285 (dagTraceF fullMask rootStock 11 f_66) cur_66) i = true := block_join nj_66_4 (fun _ h1 h2 => treeBlockF_at nb_66_5 h1 h2)
theorem nj_66_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeV4 fullMask g_66 ep_66 bds_66 285 (dagTraceF fullMask rootStock 11 f_66) cur_66) i = true := block_join nj_66_5 (fun _ h1 h2 => treeBlockF_at nb_66_6 h1 h2)
theorem nj_66_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeV4 fullMask g_66 ep_66 bds_66 285 (dagTraceF fullMask rootStock 11 f_66) cur_66) i = true := block_join nj_66_6 (fun _ h1 h2 => treeBlockF_at nb_66_7 h1 h2)
theorem nj_66_8 : ∀ i, 0 ≤ i → i < 285 → (dagCheckNodeV4 fullMask g_66 ep_66 bds_66 285 (dagTraceF fullMask rootStock 11 f_66) cur_66) i = true := block_join nj_66_7 (fun _ h1 h2 => treeBlockF_at nb_66_8 h1 h2)
theorem nc_66 : ∀ i, 0 ≤ i → i < 285 → (dagCheckNodeV4 fullMask g_66 ep_66 bds_66 285 (dagTraceF fullMask rootStock 11 f_66) cur_66) i = true := nj_66_8
theorem lb_66 : LowerBin fullMask rootStock g_66 12 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_66 kn_66 sub_66 gl_66 rc_66 nc_66

def wg : List Gate := [⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [0, 2]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [3, 10]⟩, ⟨GateOp.and, [5, 7]⟩, ⟨GateOp.or, [6, 9]⟩, ⟨GateOp.and, [3, 13]⟩, ⟨GateOp.or, [8, 12]⟩, ⟨GateOp.or, [11, 13]⟩, ⟨GateOp.or, [14, 15]⟩, ⟨GateOp.and, [16, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276676744 * 2 ^ 32 + 4171278464) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276676744 * 2 ^ 32 + 4171278464)) (13 - 1) := by
  rw [show canon fullMask (4276676744 * 2 ^ 32 + 4171278464) = g_66 by decide]
  exact lb_66

end PEqualNP.Outside.L_meta_49345

theorem PEqualNP.Outside.L_meta_49345 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676744 * 2 ^ 32 + 4171278464) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676744 * 2 ^ 32 + 4171278464) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_49345.table2_from_lowerBin (4276676744 * 2 ^ 32 + 4171278464) 13 PEqualNP.Outside.L_meta_49345.root_lb PEqualNP.Outside.L_meta_49345.wg 18 rfl PEqualNP.Outside.L_meta_49345.wfits PEqualNP.Outside.L_meta_49345.weval
