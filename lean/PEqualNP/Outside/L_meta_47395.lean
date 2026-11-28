import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_47395

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

abbrev ReplayState := Nat × List Nat × List (Nat × Nat × Nat)

def RefTransfers (mask goal count : Nat) (states : Nat → Option ReplayState)
    (reference : Nat → Nat → ReplayState → Bool) : Prop :=
  ∀ parent token current, reference parent token current = true →
    ∃ dest saved, dest < count ∧ states dest = some saved ∧ saved.1 = current.1 ∧
      ∀ k, LiveBin mask goal k current.2.1.toFinset → LiveBin mask goal k saved.2.1.toFinset

theorem plainRefTransfers (mask goal count : Nat) (states : Nat → Option ReplayState)
    (links : Nat → Nat → Option Nat) :
    RefTransfers mask goal count states (dagRef count states links) := by
  intro parent token current h
  unfold dagRef at h
  cases he : links parent token with
  | none => simp [he] at h
  | some dest =>
    simp only [he, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨hlt, hmatch⟩ := h
    cases hs : states dest with
    | none => simp [hs] at hmatch
    | some saved =>
      simp only [hs, Bool.and_eq_true, Nat.beq_eq, beq_iff_eq] at hmatch
      exact ⟨dest, saved, hlt, hs, hmatch.1, fun _ hLive => hmatch.2 ▸ hLive⟩

def dagCheckNodeWith (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option ReplayState) (reference : Nat → Nat → ReplayState → Bool)
    (i : Nat) : Bool :=
  match states i with
  | none => false
  | some st => dagCheckChildren mask goal bounds (reference (i + 1)) st

theorem dagAllNodesWith {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {reference : Nat → Nat → ReplayState → Bool}
    (hrefs : RefTransfers mask goal count (dagTrace mask stock fuel forest) reference)
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1) (snd : stock.Nodup)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeWith mask goal bounds
      (dagTrace mask stock fuel forest) reference i = true) :
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
    unfold dagCheckNodeWith at hchk
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
          · obtain ⟨dest, saved, hdest, htr2, hfEq, hMove⟩ :=
              hrefs (i + 1) (makeToken a b op keep) _ href
            have hbelow : rem - 1 < cap := by omega
            exact ih (rem - 1) hbelow dest saved hdest htr2 hfEq k' (by omega) (hMove k' hlive')

theorem lowerDagWith {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {reference : Nat → Nat → ReplayState → Bool}
    (hrefs : RefTransfers mask goal count (dagTrace mask stock fuel forest) reference)
    (hgm : Masked mask goal) (hgnz : goal ≠ 0)
    (hcs : stock.all (fun w => Nat.beq (canon mask w) w) = true)
    (snd : stock.Nodup)
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hroots : dagCheckRoots mask goal bounds
      (reference 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeWith mask goal bounds
      (dagTrace mask stock fuel forest) reference i = true) :
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
  · obtain ⟨dest, saved, hdest, htr, hfEq, hMove⟩ := hrefs 0 tok _ href
    exact dagAllNodesWith hrefs hgm hknown hsub snd hnodes fuel dest saved hdest htr hfEq k
      (by omega) (hMove k hlive')

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
    LowerBin mask stock goal (fuel + 1) :=
  lowerDagWith (plainRefTransfers mask goal count (dagTrace mask stock fuel forest) links)
    hgm hgnz hcs snd hknown hsub hroots hnodes

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

theorem certBlock {lo hi : Nat} {f : Nat → Bool} (h : treeBlockF lo hi f = true) :
    ∀ i, lo ≤ i → i < hi → f i = true :=
  fun _ hi₁ hi₂ => treeBlockF_at h hi₁ hi₂

theorem joinChecks {lo mid hi : Nat} {f : Nat → Bool}
    (left : ∀ i, lo ≤ i → i < mid → f i = true)
    (right : ∀ i, mid ≤ i → i < hi → f i = true) :
    ∀ i, lo ≤ i → i < hi → f i = true := by
  intro i h₁ h₂
  by_cases hl : i < mid
  · exact left i h₁ hl
  · exact right i (Nat.le_of_not_gt hl) h₂

def selectRows (w : Nat) : List Nat → Nat
  | [] => 0
  | p :: ps => 2 * selectRows w ps + (w.testBit p).toNat

theorem selectRows_testBit (w : Nat) (rows : List Nat) (i : Nat) :
    (selectRows w rows).testBit i = (rows[i]?).any w.testBit := by
  induction rows generalizing i with
  | nil => simp [selectRows]
  | cons p ps ih =>
    cases i with
    | zero =>
      simp only [selectRows, Nat.testBit_zero, List.getElem?_cons_zero, Option.any_some]
      cases w.testBit p
      · change decide ((2 * selectRows w ps + 0) % 2 = 1) = false
        simp
      · change decide ((2 * selectRows w ps + 1) % 2 = 1) = true
        have ht : (2 * selectRows w ps + 1) % 2 = 1 := by omega
        simp [ht]
    | succ i =>
      simp only [selectRows, Nat.testBit_succ, List.getElem?_cons_succ]
      have hd : (2 * selectRows w ps + (w.testBit p).toNat) / 2 = selectRows w ps := by
        cases w.testBit p
        · change (2 * selectRows w ps + 0) / 2 = selectRows w ps
          omega
        · change (2 * selectRows w ps + 1) / 2 = selectRows w ps
          omega
      rw [hd, ih]

theorem selectRows_zero (rows : List Nat) : selectRows 0 rows = 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [selectRows_testBit, Nat.zero_testBit]
  cases rows[i]? <;> simp [Nat.zero_testBit]

theorem selectRows_and (rows : List Nat) (x y : Nat) :
    selectRows (x &&& y) rows = selectRows x rows &&& selectRows y rows := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and, selectRows_testBit]
  cases rows[i]? <;> simp [Nat.testBit_and]

theorem selectRows_or (rows : List Nat) (x y : Nat) :
    selectRows (x ||| y) rows = selectRows x rows ||| selectRows y rows := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_or, selectRows_testBit]
  cases rows[i]? <;> simp [Nat.testBit_or]

theorem selectRows_xor (rows : List Nat) (x y : Nat) :
    selectRows (x ^^^ y) rows = selectRows x rows ^^^ selectRows y rows := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_xor, selectRows_testBit]
  cases rows[i]? <;> simp [Nat.testBit_xor]

def rowProjection (rows : List Nat) (cut w : Nat) := canon cut (selectRows w rows)

theorem rowProjection_zero (rows : List Nat) (cut : Nat) :
    rowProjection rows cut 0 = 0 := by
  simp [rowProjection, selectRows_zero, canon_zero]

theorem rowProjection_canon {rows : List Nat} {mask cut : Nat}
    (hm : selectRows mask rows = cut) (w : Nat) :
    rowProjection rows cut (canon mask w) = rowProjection rows cut w := by
  have hp : rowProjection rows cut (w &&& mask) = rowProjection rows cut w := by
    simp only [rowProjection, selectRows_and, hm, canon_land]
  rcases canon_cases mask w with ⟨he, h0 | h1⟩ | ⟨_, h0 | h1⟩
  · rw [he, rowProjection_zero, ← hp, h0, rowProjection_zero]
  · rw [he, rowProjection_zero, ← hp, h1]
    simp [rowProjection, hm, canon_self]
  · rw [h0, hp]
  · rw [h1, ← hp]
    simp only [rowProjection, selectRows_xor, hm, canon_xor_mask]

theorem rowProjection_op {rows : List Nat} {mask cut : Nat}
    (hm : selectRows mask rows = cut) (op a b : Nat) :
    rowProjection rows cut (binOp mask op a b) =
      binOp cut op (selectRows a rows) (selectRows b rows) := by
  unfold binOp
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;>
    simp only [bsel_true, bsel_false, rowProjection_canon hm] <;>
    simp only [rowProjection, selectRows_and, selectRows_or, selectRows_xor, hm]

theorem rowProjection_avail {rows : List Nat} {mask cut : Nat} {big small : List Nat}
    (hm : selectRows mask rows = cut)
    (sub : ∀ x, Avail big x → Avail small (rowProjection rows cut x)) {y : Nat}
    (gate : GateBin mask big y) : GateBin cut small (rowProjection rows cut y) := by
  obtain ⟨a, b, op, _, ha, hb, rfl⟩ := gate
  have ea := sub a ha
  have eb := sub b hb
  have ca : canon cut (rowProjection rows cut a) = rowProjection rows cut a :=
    canon_idem _ _
  have cb : canon cut (rowProjection rows cut b) = rowProjection rows cut b :=
    canon_idem _ _
  have eq := rowProjection_op hm op a b
  have hs := canon_sub_binOp (op := op) (a := selectRows a rows)
    (b := selectRows b rows) (masked_self cut)
  rw [binOp_canon, ← eq] at hs
  change _ = 0 ∨ _ = rowProjection rows cut a ∨ _ = rowProjection rows cut b ∨ _ at hs
  rcases hs with h | h | h | ⟨op', hop', h⟩
  · exact ⟨0, 0, 0, by decide, Or.inl rfl, Or.inl rfl, by
      rw [h]; simp [binOp, bsel, canon_zero]⟩
  · exact ⟨_, _, 0, by decide, ea, ea, by rw [h]; simpa [binOp, bsel] using ca.symm⟩
  · exact ⟨_, _, 0, by decide, eb, eb, by rw [h]; simpa [binOp, bsel] using cb.symm⟩
  · exact ⟨_, _, op', hop', ea, eb, h⟩

theorem rowProjection_builds {rows : List Nat} {mask cut : Nat} {big small : List Nat}
    (hm : selectRows mask rows = cut)
    (sub : ∀ x, Avail big x → Avail small (rowProjection rows cut x))
    {vs : List Nat} (h : BuildsBin mask big vs) :
    BuildsBin cut small (vs.map (rowProjection rows cut)) := by
  induction vs generalizing big small with
  | nil => trivial
  | cons x xs ih =>
    refine ⟨rowProjection_avail hm sub h.1, ih ?_ h.2⟩
    intro y hy
    rcases hy with hz | hmem
    · exact Or.inl (by rw [hz, rowProjection_zero])
    · rcases List.mem_cons.mp hmem with rfl | hmem
      · exact Or.inr List.mem_cons_self
      · exact avail_weaken (fun z hz => List.mem_cons_of_mem _ hz) (sub y (Or.inr hmem))

theorem lowerByRows {mask cut goal smallGoal n : Nat} {big small : List Nat}
    (rows : List Nat) (hm : selectRows mask rows = cut)
    (hs : ∀ w ∈ big, Avail small (rowProjection rows cut w))
    (hg : rowProjection rows cut goal = smallGoal)
    (cert : LowerBin cut small smallGoal n) : LowerBin mask big goal n := by
  intro vs hv ha
  have sub (w : Nat) (hw : Avail big w) : Avail small (rowProjection rows cut w) := by
    rcases hw with rfl | hw
    · exact Or.inl (rowProjection_zero rows cut)
    · exact hs w hw
  have hv' := rowProjection_builds hm sub hv
  have ha' : Avail (vs.map (rowProjection rows cut) ++ small) smallGoal := by
    rw [← hg]
    rcases ha with rfl | ha
    · exact Or.inl (rowProjection_zero rows cut)
    · rcases List.mem_append.mp ha with ha | ha
      · exact Or.inr (List.mem_append_left _ (List.mem_map_of_mem ha))
      · exact avail_weaken (fun w hw => List.mem_append_right _ hw) (hs _ ha)
  simpa only [List.length_map] using cert _ hv' ha'

def idxA (i : Nat) : Nat :=
  if i < 64 then if i.testBit 1 == i.testBit 2 then i else i ^^^ 6 else i

def wordA (w : Nat) : Nat :=
  (((w >>> 64) <<< 64) ||| (w &&& 0xc3c3c3c3c3c3c3c3)) |||
    (((w &&& 0xc0c0c0c0c0c0c0c) <<< 2) ||| ((w &&& 0x3030303030303030) >>> 2))

set_option maxHeartbeats 0 in
theorem wordA_bit (w i : Nat) : (wordA w).testBit i = w.testBit (idxA i) := by
  by_cases hi : i < 64
  · interval_cases i <;>
      simp only [wordA, Nat.testBit_or, Nat.testBit_and,
        Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
    all_goals norm_num [idxA, Nat.testBit, Nat.shiftRight_eq_div_pow]
  · have h64 : 64 ≤ i := by omega
    have hh : 2 ≤ i := by omega
    have e64 : 64 + (i - 64) = i := by omega
    have hkeep : (0xc3c3c3c3c3c3c3c3 : Nat).testBit i = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 0xc3c3c3c3c3c3c3c3 < 2 ^ 64)
        (Nat.pow_le_pow_right (by decide) h64))
    have hlow : (0xc0c0c0c0c0c0c0c : Nat).testBit (i - 2) = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 0xc0c0c0c0c0c0c0c < 2 ^ 62)
        (Nat.pow_le_pow_right (by decide) (by omega)))
    have hhigh : (0x3030303030303030 : Nat).testBit (2 + i) = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 0x3030303030303030 < 2 ^ 64)
        (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [wordA, idxA, hi, h64, hh, e64, hkeep, hlow, hhigh,
      Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]


def idxB (i : Nat) : Nat :=
  if i < 64 then if i.testBit 4 == i.testBit 5 then i else i ^^^ 48 else i

def wordB (w : Nat) : Nat :=
  (((w >>> 64) <<< 64) ||| (w &&& 0xffff00000000ffff)) |||
    (((w &&& 0xffff0000) <<< 16) ||| ((w &&& 0xffff00000000) >>> 16))

set_option maxHeartbeats 0 in
theorem wordB_bit (w i : Nat) : (wordB w).testBit i = w.testBit (idxB i) := by
  by_cases hi : i < 64
  · interval_cases i <;>
      simp only [wordB, Nat.testBit_or, Nat.testBit_and,
        Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
    all_goals norm_num [idxB, Nat.testBit, Nat.shiftRight_eq_div_pow]
  · have h64 : 64 ≤ i := by omega
    have hh : 16 ≤ i := by omega
    have e64 : 64 + (i - 64) = i := by omega
    have hkeep : (0xffff00000000ffff : Nat).testBit i = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 0xffff00000000ffff < 2 ^ 64)
        (Nat.pow_le_pow_right (by decide) h64))
    have hlow : (0xffff0000 : Nat).testBit (i - 16) = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 0xffff0000 < 2 ^ 48)
        (Nat.pow_le_pow_right (by decide) (by omega)))
    have hhigh : (0xffff00000000 : Nat).testBit (16 + i) = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 0xffff00000000 < 2 ^ 64)
        (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [wordB, idxB, hi, h64, hh, e64, hkeep, hlow, hhigh,
      Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]


def swapIndex (phase : Fin 4) (i : Nat) : Nat :=
  let j := if phase.val.testBit 1 then idxB i else i
  if phase.val.testBit 0 then idxA j else j

def swapWord (phase : Fin 4) (w : Nat) : Nat :=
  let v := if phase.val.testBit 0 then wordA w else w
  if phase.val.testBit 1 then wordB v else v

theorem swapWord_bit (phase : Fin 4) (w i : Nat) :
    (swapWord phase w).testBit i = w.testBit (swapIndex phase i) := by
  cases h0 : phase.val.testBit 0 <;> cases h1 : phase.val.testBit 1 <;>
    simp [swapWord, swapIndex, h0, h1, wordA_bit, wordB_bit]

private theorem swapIndex_small : ∀ (p : Fin 4) (i : Fin 64), swapIndex p (swapIndex p i) = i :=
  by decide +kernel

theorem swapIndex_inv (phase : Fin 4) (i : Nat) : swapIndex phase (swapIndex phase i) = i := by
  by_cases hi : i < 64
  · exact swapIndex_small phase ⟨i, hi⟩
  · have key : swapIndex phase i = i := by simp [swapIndex, idxA, idxB, hi]
    rw [key, key]

theorem swapWord_inv (phase : Fin 4) (w : Nat) : swapWord phase (swapWord phase w) = w := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [swapWord_bit, swapIndex_inv]

theorem swapWord_injective (phase : Fin 4) : Function.Injective (swapWord phase) :=
  fun _ _ h => by simpa only [swapWord_inv] using congrArg (swapWord phase) h

theorem swapWord_and (phase : Fin 4) (x y : Nat) :
    swapWord phase (x &&& y) = swapWord phase x &&& swapWord phase y := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [swapWord_bit, Nat.testBit_and]

theorem swapWord_or (phase : Fin 4) (x y : Nat) :
    swapWord phase (x ||| y) = swapWord phase x ||| swapWord phase y := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [swapWord_bit, Nat.testBit_or]

theorem swapWord_xor (phase : Fin 4) (x y : Nat) :
    swapWord phase (x ^^^ y) = swapWord phase x ^^^ swapWord phase y := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [swapWord_bit, Nat.testBit_xor]

theorem swapWord_zero : ∀ phase : Fin 4, swapWord phase 0 = 0 := by decide +kernel

theorem canonByTopBit {mask top : Nat} (hp : mask < 2 ^ (top + 1) ∧ mask.testBit top = true) (w : Nat) :
    canon mask w =
      if (w &&& mask).testBit top then mask ^^^ (w &&& mask) else w &&& mask := by
  unfold canon; dsimp only
  set v := w &&& mask
  have hhigh (j : Nat) (hj : top < j) :
      v.testBit j = (mask ^^^ v).testBit j := by
    have hb : mask.testBit j = false := by
      apply Nat.testBit_eq_false_of_lt
      exact lt_of_lt_of_le hp.1 (Nat.pow_le_pow_right (by decide) (by omega))
    simp [Nat.testBit_xor, hb]
  have hone : mask.testBit top = true := hp.2
  by_cases hz : v = 0
  · rw [hz]
    simp [bsel]
  by_cases hf : v = mask
  · rw [hf]
    simp [bsel, hone]
  rw [beq_false_ne hz, beq_false_ne hf]
  simp only [Bool.or_false, bsel_false]
  cases hbit : v.testBit top
  · have hv : (mask ^^^ v).testBit top = true := by
      simp [Nat.testBit_xor, hone, hbit]
    have hlt := Nat.lt_of_testBit top hbit hv hhigh
    have hcheck : Nat.blt v (mask ^^^ v) = true := by simpa only [Nat.blt_eq] using hlt
    simp [hcheck, bsel]
  · have hv : (mask ^^^ v).testBit top = false := by
      simp [Nat.testBit_xor, hone, hbit]
    have hlt := Nat.lt_of_testBit top hv hbit (fun j hj => (hhigh j hj).symm)
    have hcheck : Nat.blt v (mask ^^^ v) = false := by
      cases hh : Nat.blt v (mask ^^^ v)
      · rfl
      · rw [Nat.blt_eq] at hh; omega
    simp [hcheck, bsel]

theorem swapWord_canon {phase : Fin 4} {mask top : Nat} (hp : mask < 2 ^ (top + 1) ∧ mask.testBit top = true)
    (hm : (swapWord phase) mask = mask) (ht : (swapIndex phase) top = top) (w : Nat) :
    (swapWord phase) (canon mask w) = canon mask ((swapWord phase) w) := by
  rw [canonByTopBit hp, canonByTopBit hp]
  have h : (((swapWord phase) w) &&& mask).testBit top = (w &&& mask).testBit top := by
    rw [← hm, ← swapWord_and, swapWord_bit, ht, hm]
  rw [h]
  by_cases htop : (w &&& mask).testBit top = true <;>
    simp [htop, swapWord_xor, swapWord_and, hm]

theorem swapWord_gate {phase : Fin 4} {mask top : Nat} (hp : mask < 2 ^ (top + 1) ∧ mask.testBit top = true)
    (hm : (swapWord phase) mask = mask) (ht : (swapIndex phase) top = top) (op a b : Nat) :
    (swapWord phase) (binOp mask op a b) = binOp mask op ((swapWord phase) a) ((swapWord phase) b) := by
  unfold binOp
  simp only [bsel]
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;>
    simp [swapWord_canon hp hm ht, swapWord_and, swapWord_or, swapWord_xor, hm]

theorem swapWord_drop {phase : Fin 4} (keep : Bool) (w : Nat) (S : Finset Nat) :
    (dropIf keep w S).image (swapWord phase) = dropIf keep ((swapWord phase) w) (S.image (swapWord phase)) := by
  cases keep <;> simp [dropIf, Finset.image_erase (swapWord_injective phase)]

theorem swapLiveBin {phase : Fin 4} {mask top goal fuel : Nat} {S : Finset Nat}
    (hp : mask < 2 ^ (top + 1) ∧ mask.testBit top = true) (hm : (swapWord phase) mask = mask) (ht : (swapIndex phase) top = top)
    (g : (swapWord phase) goal = goal)
    (h : LiveBin mask goal fuel S) : LiveBin mask goal fuel (S.image (swapWord phase)) := by
  induction h with
  | done => simpa only [Finset.image_singleton, g] using (LiveBin.done (mask := mask) (goal := goal))
  | @step k T a b op ha hb hab ha0 hb0 hop hz hf keepA keepB tail ih =>
    refine LiveBin.step (a := (swapWord phase) a) (b := (swapWord phase) b) (op := op)
      (Finset.mem_image_of_mem _ ha) (Finset.mem_image_of_mem _ hb)
      ((swapWord_injective phase).ne hab) ?_ ?_ hop ?_ ?_ keepA keepB ?_
    · intro h; exact ha0 (swapWord_injective phase (h.trans (swapWord_zero phase).symm))
    · intro h; exact hb0 (swapWord_injective phase (h.trans (swapWord_zero phase).symm))
    · rw [← swapWord_gate hp hm ht]
      intro h; exact hz (swapWord_injective phase (h.trans (swapWord_zero phase).symm))
    · rw [← swapWord_gate hp hm ht]
      intro h
      obtain ⟨x, hx, eq⟩ := Finset.mem_image.mp h
      exact hf ((swapWord_injective phase eq) ▸ hx)
    · simpa only [Finset.image_insert, swapWord_drop, swapWord_gate hp hm ht] using ih

def swapBankF (phase : Fin 4) (saved current : List Nat) : Bool :=
  Bool.rec false (allN (fun w => memN ((swapWord phase) w) current) saved)
    (allN (fun w => memN ((swapWord phase) w) saved) current)

theorem swapBank_image {phase : Fin 4} {saved current : List Nat} (h : swapBankF phase saved current = true) :
    current.toFinset.image (swapWord phase) = saved.toFinset := by
  unfold swapBankF at h
  have hboth : (allN (fun w => memN ((swapWord phase) w) saved) current) = true ∧
      (allN (fun w => memN ((swapWord phase) w) current) saved) = true := by
    cases ht : allN (fun w => memN ((swapWord phase) w) saved) current
    · rw [ht] at h; contradiction
    · rw [ht] at h; exact ⟨rfl, h⟩
  simp only [allN_eq, memN_eq, List.all_eq_true, List.contains_iff_mem] at hboth
  ext v; constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact List.mem_toFinset.mpr (hboth.1 w (List.mem_toFinset.mp hw))
  · intro hv
    exact Finset.mem_image.mpr
      ⟨(swapWord phase) v, List.mem_toFinset.mpr (hboth.2 v (List.mem_toFinset.mp hv)), swapWord_inv phase v⟩

def guardedSwap (mask top goal : Nat) (phase : Fin 4) (saved current : List Nat) : Bool :=
  Nat.beq (swapWord phase mask) mask && Nat.beq (swapIndex phase top) top &&
    Nat.beq (swapWord phase goal) goal && swapBankF phase saved current

def dagRefSwapF (mask top goal count : Nat) (states : Nat → Option ReplayState)
    (links : Nat → Nat → Option Nat) (parent token : Nat) (current : ReplayState) : Bool :=
  match links parent token with
  | none => false
  | some code =>
    let dest := Nat.shiftRight code 2
    let phase : Fin 4 := Fin.ofNat 4 code
    Bool.rec false
      (match states dest with
       | none => false
       | some saved =>
         Bool.rec false
           (Bool.rec (guardedSwap mask top goal phase saved.2.1 current.2.1)
             (eqListN saved.2.1 current.2.1) (Nat.beq phase.val 0))
           (Nat.beq saved.1 current.1))
      (Nat.blt dest count)

theorem swapRefTransfers {mask top goal count : Nat} (hp : mask < 2 ^ (top + 1) ∧ mask.testBit top = true)
    (states : Nat → Option ReplayState) (links : Nat → Nat → Option Nat) :
    RefTransfers mask goal count states (dagRefSwapF mask top goal count states links) := by
  intro parent token current h
  unfold dagRefSwapF at h
  cases he : links parent token with
  | none => rw [he] at h; contradiction
  | some code =>
    rw [he] at h
    let dest := Nat.shiftRight code 2
    let phase : Fin 4 := Fin.ofNat 4 code
    change Bool.rec false _ (Nat.blt dest count) = true at h
    cases hb : Nat.blt dest count
    · rw [hb] at h; contradiction
    · rw [hb] at h
      have hlt : dest < count := by simpa only [Nat.blt_eq] using hb
      cases hs : states dest with
      | none =>
        change (match states dest with | none => false | some _ => _) = true at h
        rw [hs] at h
        contradiction
      | some saved =>
        change (match states dest with | none => false | some _ => _) = true at h
        rw [hs] at h
        change Bool.rec false _ (Nat.beq saved.1 current.1) = true at h
        cases hf : Nat.beq saved.1 current.1
        · rw [hf] at h; contradiction
        · rw [hf] at h
          have hFuel := Nat.beq_eq.mp hf
          refine ⟨dest, saved, hlt, hs, hFuel, ?_⟩
          intro k hLive
          change Bool.rec (guardedSwap mask top goal phase saved.2.1 current.2.1)
            (eqListN saved.2.1 current.2.1) (Nat.beq phase.val 0) = true at h
          cases hz : Nat.beq phase.val 0
          · rw [hz] at h
            change guardedSwap mask top goal phase saved.2.1 current.2.1 = true at h
            simp only [guardedSwap, Bool.and_eq_true, Nat.beq_eq] at h
            obtain ⟨⟨⟨hm, ht⟩, hgoal⟩, hbank⟩ := h
            simpa only [swapBank_image hbank] using swapLiveBin hp hm ht hgoal hLive
          · rw [hz] at h
            change eqListN saved.2.1 current.2.1 = true at h
            rw [eqListN_eq, beq_iff_eq] at h
            exact h ▸ hLive

def dagCheckNodeWithF (mask goal : Nat) (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option ReplayState) (reference : Nat → Nat → ReplayState → Bool)
    (i : Nat) : Bool :=
  match states i with
  | none => false
  | some st => dagCheckChildrenF mask goal bounds (reference (Nat.add i 1)) st

theorem dagCheckNodeWithF_eq {mask goal : Nat} {bounds : List (Nat × List Nat × Nat × Nat)}
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (states : Nat → Option ReplayState) (reference : Nat → Nat → ReplayState → Bool) (i : Nat) :
    dagCheckNodeWithF mask goal bounds states reference i =
      dagCheckNodeWith mask goal bounds states reference i := by
  unfold dagCheckNodeWithF dagCheckNodeWith
  cases states i with
  | none => rfl
  | some state => exact dagCheckChildrenF_eq hgoals _ state

theorem lowerDagSwapF {mask top goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {links : Nat → Nat → Option Nat}
    (hp : mask < 2 ^ (top + 1) ∧ mask.testBit top = true) 
    (hgm : Masked mask goal) (hgnz : goal ≠ 0)
    (hcs : stock.all (fun w => Nat.beq (canon mask w) w) = true)
    (snd : stock.Nodup)
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hroots : dagCheckRootsF mask goal bounds
      (dagRefSwapF mask top goal count (dagTraceF mask stock fuel forest) links 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeWithF mask goal bounds
      (dagTraceF mask stock fuel forest)
      (dagRefSwapF mask top goal count (dagTraceF mask stock fuel forest) links) i = true) :
    LowerBin mask stock goal (fuel + 1) := by
  have htr : dagTraceF mask stock fuel forest = dagTrace mask stock fuel forest := by
    funext i; exact dagTraceF_eq mask stock fuel forest i
  rw [htr, dagCheckRootsF_eq hgoals] at hroots
  rw [htr] at hnodes
  refine lowerDagWith (swapRefTransfers hp _ _) hgm hgnz hcs snd hknown hsub hroots ?_
  intro i hlo hhi
  simpa only [dagCheckNodeWithF_eq hgoals] using hnodes i hlo hhi

def f_12 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_12 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
def m_12 : Nat := 0xaaaa
def s_12 : List Nat := [0x2222, 0xa0a, 0xaa]
def g_12 : Nat := 0x22a
def bds_12 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_12 : KnownBin bds_12 := by
  intro b hb
  simp [bds_12] at hb
theorem sub_12 : ∀ b ∈ bds_12, m_12 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_12] at hb
theorem gl_12 : ∀ b ∈ bds_12, canon b.1 g_12 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_12] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_12 : dagCheckRootsF m_12 g_12 bds_12 (dagRefSwapF m_12 15 g_12 1 (dagTraceF m_12 s_12 3 f_12) l_12 0) s_12 3 = true := by decide +kernel
def node_12 : Nat → Bool := dagCheckNodeWithF m_12 g_12 bds_12 (dagTraceF m_12 s_12 3 f_12) (dagRefSwapF m_12 15 g_12 1 (dagTraceF m_12 s_12 3 f_12) l_12)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_12_0 : treeBlockF 0 1 node_12 = true := by decide +kernel
theorem nc_12 : ∀ j, 0 ≤ j → j < 1 → node_12 j = true :=
  (certBlock nb_12_0)
theorem lb_12 : LowerBin m_12 s_12 g_12 4 :=
  lowerDagSwapF (top := 15) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_12 sub_12 gl_12 rc_12 nc_12

def m_32 : Nat := 0xaa00aa
def s_32 : List Nat := [0x220022, 0xa000a, 0xaa]
def g_32 : Nat := 0x2002a
theorem lb_32 : LowerBin m_32 s_32 g_32 4 := by
  refine lowerByRows [0, 1, 0, 3, 0, 5, 0, 7, 0, 17, 0, 19, 0, 21, 0, 23] (by decide +kernel) ?_ (by decide +kernel) lb_12
  intro w hw
  simp only [s_32, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_127 : Nat := 0xff000000
def s_127 : List Nat := [0x55000000, 0x33000000, 0xf000000]
def g_127 : Nat := 0x17000000
theorem lb_127 : LowerBin m_127 s_127 g_127 4 := by
  refine lowerByRows [0, 24, 0, 25, 0, 26, 0, 27, 0, 28, 0, 29, 0, 30, 0, 31] (by decide +kernel) ?_ (by decide +kernel) lb_12
  intro w hw
  simp only [s_127, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_143 : Nat := 0xaa000000aa
def s_143 : List Nat := [0x2200000022, 0xa0000000a, 0xaa]
def g_143 : Nat := 0x20000002a
theorem lb_143 : LowerBin m_143 s_143 g_143 4 := by
  refine lowerByRows [0, 1, 0, 3, 0, 5, 0, 7, 0, 33, 0, 35, 0, 37, 0, 39] (by decide +kernel) ?_ (by decide +kernel) lb_12
  intro w hw
  simp only [s_143, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_248 : Nat := 0xff0000000000
def s_248 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_248 : Nat := 0x170000000000
theorem lb_248 : LowerBin m_248 s_248 g_248 4 := by
  refine lowerByRows [0, 40, 0, 41, 0, 42, 0, 43, 0, 44, 0, 45, 0, 46, 0, 47] (by decide +kernel) ?_ (by decide +kernel) lb_12
  intro w hw
  simp only [s_248, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_354 : Nat := 0xff000000000000
def s_354 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_354 : Nat := 0x17000000000000
theorem lb_354 : LowerBin m_354 s_354 g_354 4 := by
  refine lowerByRows [0, 48, 0, 49, 0, 50, 0, 51, 0, 52, 0, 53, 0, 54, 0, 55] (by decide +kernel) ?_ (by decide +kernel) lb_12
  intro w hw
  simp only [s_354, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_517 : Nat := 0x4040404040404040
def s_517 : List Nat := [0x40004000400040, 0x404000004040, 0x40404040]
def g_517 : Nat := 0x4000404040
theorem lb_517 : LowerBin m_517 s_517 g_517 4 := by
  refine lowerByRows [0, 6, 0, 14, 0, 22, 0, 30, 0, 38, 0, 46, 0, 54, 0, 62] (by decide +kernel) ?_ (by decide +kernel) lb_12
  intro w hw
  simp only [s_517, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def f_673 : Nat → Nat × Nat := fun _ => (0, 0)
def l_673 : Nat → Nat → Option Nat := fun _ _ => none
def m_673 : Nat := 0xff00ff
def s_673 : List Nat := [0x550055, 0x330033, 0xf000f, 0xff]
def g_673 : Nat := 0x57007f
def bds_673 : List (Nat × List Nat × Nat × Nat) := [(m_32, s_32, 4, g_32)]
theorem kn_673 : KnownBin bds_673 := by
  intro b hb
  simp only [bds_673, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_32
theorem sub_673 : ∀ b ∈ bds_673, m_673 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_673, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_673 : ∀ b ∈ bds_673, canon b.1 g_673 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_673, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_673 : dagCheckRootsF m_673 g_673 bds_673 (dagRefF 0 (dagTraceF m_673 s_673 4 f_673) l_673 0) s_673 4 = true := by decide +kernel
def node_673 : Nat → Bool := dagCheckNodeF m_673 g_673 bds_673 0 (dagTraceF m_673 s_673 4 f_673) l_673
theorem nc_673 : ∀ j, 0 ≤ j → j < 0 → node_673 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_673 : LowerBin m_673 s_673 g_673 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_673 sub_673 gl_673 rc_673 nc_673

def m_691 : Nat := 0xaaaaaaaa
def s_691 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_691 : Nat := 0x202022a
def bds_691 : List (Nat × List Nat × Nat × Nat) := [(m_32, s_32, 4, g_32)]
theorem kn_691 : KnownBin bds_691 := by
  intro b hb
  simp only [bds_691, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_32
theorem sub_691 : ∀ b ∈ bds_691, m_691 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_691, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_691 : ∀ b ∈ bds_691, canon b.1 g_691 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_691, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_691 : dagCheckRootsF m_691 g_691 bds_691 (dagRefF 0 (dagTraceF m_691 s_691 4 f_673) l_673 0) s_691 4 = true := by decide +kernel
def node_691 : Nat → Bool := dagCheckNodeF m_691 g_691 bds_691 0 (dagTraceF m_691 s_691 4 f_673) l_673
theorem nc_691 : ∀ j, 0 ≤ j → j < 0 → node_691 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_691 : LowerBin m_691 s_691 g_691 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_691 sub_691 gl_691 rc_691 nc_691

def f_695 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_695 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0x3d14cf0503b04ce81038128dc4936028d4093124cc0902f04cb8102c13cac4d2a018a405270289809240188c0520120808d1c24c6c901a14c64501703c580d1502c50091212844490f02c38090b0202c4d0913c204d0603c140d0201008493f23ff88ef9237d08cf313fc84eed137a04ce512f884ae11277c48de03f740ed80374c0cd002f340acc0272808c701f1006c30170404c000f 12 5 10 8 6
def m_695 : Nat := 0xcccccccc
def s_695 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_695 : Nat := 0x444444c
def bds_695 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_695 : KnownBin bds_695 := by
  intro b hb
  simp [bds_695] at hb
theorem sub_695 : ∀ b ∈ bds_695, m_695 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_695] at hb
theorem gl_695 : ∀ b ∈ bds_695, canon b.1 g_695 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_695] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_695 : dagCheckRootsF m_695 g_695 bds_695 (dagRefSwapF m_695 31 g_695 64 (dagTraceF m_695 s_695 5 f_695) l_695 0) s_695 5 = true := by decide +kernel
def node_695 : Nat → Bool := dagCheckNodeWithF m_695 g_695 bds_695 (dagTraceF m_695 s_695 5 f_695) (dagRefSwapF m_695 31 g_695 64 (dagTraceF m_695 s_695 5 f_695) l_695)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_695_0 : treeBlockF 0 32 node_695 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_695_1 : treeBlockF 32 64 node_695 = true := by decide +kernel
theorem nc_695 : ∀ j, 0 ≤ j → j < 64 → node_695 j = true :=
  (joinChecks (certBlock nb_695_0) (certBlock nb_695_1))
theorem lb_695 : LowerBin m_695 s_695 g_695 6 :=
  lowerDagSwapF (top := 31) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_695 sub_695 gl_695 rc_695 nc_695

def m_700 : Nat := 0xff00ff00
def s_700 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_700 : Nat := 0x17005700
def bds_700 : List (Nat × List Nat × Nat × Nat) := [(m_127, s_127, 4, g_127)]
theorem kn_700 : KnownBin bds_700 := by
  intro b hb
  simp only [bds_700, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_127
theorem sub_700 : ∀ b ∈ bds_700, m_700 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_700, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_700 : ∀ b ∈ bds_700, canon b.1 g_700 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_700, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_700 : dagCheckRootsF m_700 g_700 bds_700 (dagRefF 0 (dagTraceF m_700 s_700 4 f_673) l_673 0) s_700 4 = true := by decide +kernel
def node_700 : Nat → Bool := dagCheckNodeF m_700 g_700 bds_700 0 (dagTraceF m_700 s_700 4 f_673) l_673
theorem nc_700 : ∀ j, 0 ≤ j → j < 0 → node_700 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_700 : LowerBin m_700 s_700 g_700 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_700 sub_700 gl_700 rc_700 nc_700

def m_702 : Nat := 0xff000000ff
def s_702 : List Nat := [0x5500000055, 0x3300000033, 0xf0000000f, 0xff]
def g_702 : Nat := 0x570000007f
def bds_702 : List (Nat × List Nat × Nat × Nat) := [(m_143, s_143, 4, g_143)]
theorem kn_702 : KnownBin bds_702 := by
  intro b hb
  simp only [bds_702, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_143
theorem sub_702 : ∀ b ∈ bds_702, m_702 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_702, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_702 : ∀ b ∈ bds_702, canon b.1 g_702 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_702, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_702 : dagCheckRootsF m_702 g_702 bds_702 (dagRefF 0 (dagTraceF m_702 s_702 4 f_673) l_673 0) s_702 4 = true := by decide +kernel
def node_702 : Nat → Bool := dagCheckNodeF m_702 g_702 bds_702 0 (dagTraceF m_702 s_702 4 f_673) l_673
theorem nc_702 : ∀ j, 0 ≤ j → j < 0 → node_702 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_702 : LowerBin m_702 s_702 g_702 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_702 sub_702 gl_702 rc_702 nc_702

def m_724 : Nat := 0xaaaa0000aaaa
def s_724 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_724 : Nat := 0x2020000022a
def bds_724 : List (Nat × List Nat × Nat × Nat) := [(m_143, s_143, 4, g_143)]
theorem kn_724 : KnownBin bds_724 := by
  intro b hb
  simp only [bds_724, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_143
theorem sub_724 : ∀ b ∈ bds_724, m_724 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_724, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_724 : ∀ b ∈ bds_724, canon b.1 g_724 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_724, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_724 : dagCheckRootsF m_724 g_724 bds_724 (dagRefF 0 (dagTraceF m_724 s_724 4 f_673) l_673 0) s_724 4 = true := by decide +kernel
def node_724 : Nat → Bool := dagCheckNodeF m_724 g_724 bds_724 0 (dagTraceF m_724 s_724 4 f_673) l_673
theorem nc_724 : ∀ j, 0 ≤ j → j < 0 → node_724 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_724 : LowerBin m_724 s_724 g_724 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_724 sub_724 gl_724 rc_724 nc_724

def m_729 : Nat := 0xcccc0000cccc
def s_729 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_729 : Nat := 0x4440000444c
theorem lb_729 : LowerBin m_729 s_729 g_729 6 := by
  refine lowerByRows [0, 0, 2, 3, 0, 0, 6, 7, 0, 0, 10, 11, 0, 0, 14, 15, 0, 0, 34, 35, 0, 0, 38, 39, 0, 0, 42, 43, 0, 0, 46, 47] (by decide +kernel) ?_ (by decide +kernel) lb_695
  intro w hw
  simp only [s_729, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_736 : Nat := 0xff000000ff00
def s_736 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_736 : Nat := 0x170000005700
def bds_736 : List (Nat × List Nat × Nat × Nat) := [(m_248, s_248, 4, g_248)]
theorem kn_736 : KnownBin bds_736 := by
  intro b hb
  simp only [bds_736, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_248
theorem sub_736 : ∀ b ∈ bds_736, m_736 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_736, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_736 : ∀ b ∈ bds_736, canon b.1 g_736 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_736, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_736 : dagCheckRootsF m_736 g_736 bds_736 (dagRefF 0 (dagTraceF m_736 s_736 4 f_673) l_673 0) s_736 4 = true := by decide +kernel
def node_736 : Nat → Bool := dagCheckNodeF m_736 g_736 bds_736 0 (dagTraceF m_736 s_736 4 f_673) l_673
theorem nc_736 : ∀ j, 0 ≤ j → j < 0 → node_736 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_736 : LowerBin m_736 s_736 g_736 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_736 sub_736 gl_736 rc_736 nc_736

def m_761 : Nat := 0xaa00aa00aa00aa
def s_761 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_761 : Nat := 0x200020002002a
def bds_761 : List (Nat × List Nat × Nat × Nat) := [(m_143, s_143, 4, g_143)]
theorem kn_761 : KnownBin bds_761 := by
  intro b hb
  simp only [bds_761, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_143
theorem sub_761 : ∀ b ∈ bds_761, m_761 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_761, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_761 : ∀ b ∈ bds_761, canon b.1 g_761 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_761, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_761 : dagCheckRootsF m_761 g_761 bds_761 (dagRefF 0 (dagTraceF m_761 s_761 4 f_673) l_673 0) s_761 4 = true := by decide +kernel
def node_761 : Nat → Bool := dagCheckNodeF m_761 g_761 bds_761 0 (dagTraceF m_761 s_761 4 f_673) l_673
theorem nc_761 : ∀ j, 0 ≤ j → j < 0 → node_761 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_761 : LowerBin m_761 s_761 g_761 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_761 sub_761 gl_761 rc_761 nc_761

def m_767 : Nat := 0xcc00cc00cc00cc
def s_767 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_767 : Nat := 0x400440044004c
theorem lb_767 : LowerBin m_767 s_767 g_767 6 := by
  refine lowerByRows [0, 0, 2, 3, 0, 0, 6, 7, 0, 0, 18, 19, 0, 0, 22, 23, 0, 0, 34, 35, 0, 0, 38, 39, 0, 0, 50, 51, 0, 0, 54, 55] (by decide +kernel) ?_ (by decide +kernel) lb_695
  intro w hw
  simp only [s_767, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_772 : Nat := 0xf000f000f000f0
def s_772 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_772 : Nat := 0x10005000500070
theorem lb_772 : LowerBin m_772 s_772 g_772 6 := by
  refine lowerByRows [0, 0, 4, 5, 0, 0, 6, 7, 0, 0, 20, 21, 0, 0, 22, 23, 0, 0, 36, 37, 0, 0, 38, 39, 0, 0, 52, 53, 0, 0, 54, 55] (by decide +kernel) ?_ (by decide +kernel) lb_695
  intro w hw
  simp only [s_772, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_776 : Nat := 0xff000000ff0000
def s_776 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_776 : Nat := 0x17000000570000
def bds_776 : List (Nat × List Nat × Nat × Nat) := [(m_354, s_354, 4, g_354)]
theorem kn_776 : KnownBin bds_776 := by
  intro b hb
  simp only [bds_776, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_354
theorem sub_776 : ∀ b ∈ bds_776, m_776 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_776, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_776 : ∀ b ∈ bds_776, canon b.1 g_776 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_776, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_776 : dagCheckRootsF m_776 g_776 bds_776 (dagRefF 0 (dagTraceF m_776 s_776 4 f_673) l_673 0) s_776 4 = true := by decide +kernel
def node_776 : Nat → Bool := dagCheckNodeF m_776 g_776 bds_776 0 (dagTraceF m_776 s_776 4 f_673) l_673
theorem nc_776 : ∀ j, 0 ≤ j → j < 0 → node_776 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_776 : LowerBin m_776 s_776 g_776 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_776 sub_776 gl_776 rc_776 nc_776

def m_778 : Nat := 0xff00ff00000000
def s_778 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_778 : Nat := 0x17005700000000
def bds_778 : List (Nat × List Nat × Nat × Nat) := [(m_354, s_354, 4, g_354)]
theorem kn_778 : KnownBin bds_778 := by
  intro b hb
  simp only [bds_778, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_354
theorem sub_778 : ∀ b ∈ bds_778, m_778 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_778, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_778 : ∀ b ∈ bds_778, canon b.1 g_778 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_778, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_778 : dagCheckRootsF m_778 g_778 bds_778 (dagRefF 0 (dagTraceF m_778 s_778 4 f_673) l_673 0) s_778 4 = true := by decide +kernel
def node_778 : Nat → Bool := dagCheckNodeF m_778 g_778 bds_778 0 (dagTraceF m_778 s_778 4 f_673) l_673
theorem nc_778 : ∀ j, 0 ≤ j → j < 0 → node_778 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_778 : LowerBin m_778 s_778 g_778 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_778 sub_778 gl_778 rc_778 nc_778

def m_798 : Nat := 0xa0a0a0a0a0a0a0a
def s_798 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_798 : Nat := 0x202020202020a
theorem lb_798 : LowerBin m_798 s_798 g_798 6 := by
  refine lowerByRows [0, 0, 1, 3, 0, 0, 9, 11, 0, 0, 17, 19, 0, 0, 25, 27, 0, 0, 33, 35, 0, 0, 41, 43, 0, 0, 49, 51, 0, 0, 57, 59] (by decide +kernel) ?_ (by decide +kernel) lb_695
  intro w hw
  simp only [s_798, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_832 : Nat := 0x2222222222222222
def s_832 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_832 : Nat := 0x2020202020222
theorem lb_832 : LowerBin m_832 s_832 g_832 6 := by
  refine lowerByRows [0, 0, 1, 5, 0, 0, 9, 13, 0, 0, 17, 21, 0, 0, 25, 29, 0, 0, 33, 37, 0, 0, 41, 45, 0, 0, 49, 53, 0, 0, 57, 61] (by decide +kernel) ?_ (by decide +kernel) lb_695
  intro w hw
  simp only [s_832, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_860 : Nat := 0x4444444444444444
def s_860 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_860 : Nat := 0x404044404444444
def bds_860 : List (Nat × List Nat × Nat × Nat) := [(m_517, s_517, 4, g_517)]
theorem kn_860 : KnownBin bds_860 := by
  intro b hb
  simp only [bds_860, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_517
theorem sub_860 : ∀ b ∈ bds_860, m_860 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_860, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_860 : ∀ b ∈ bds_860, canon b.1 g_860 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_860, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_860 : dagCheckRootsF m_860 g_860 bds_860 (dagRefF 0 (dagTraceF m_860 s_860 4 f_673) l_673 0) s_860 4 = true := by decide +kernel
def node_860 : Nat → Bool := dagCheckNodeF m_860 g_860 bds_860 0 (dagTraceF m_860 s_860 4 f_673) l_673
theorem nc_860 : ∀ j, 0 ≤ j → j < 0 → node_860 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_860 : LowerBin m_860 s_860 g_860 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_860 sub_860 gl_860 rc_860 nc_860

def m_924 : Nat := 0xc0c0c0c0c0c0c0c0
def s_924 : List Nat := [0x4040404040404040, 0xc000c000c000c0, 0xc0c00000c0c0, 0xc0c0c0c0]
def g_924 : Nat := 0x4000404040
def bds_924 : List (Nat × List Nat × Nat × Nat) := [(m_517, s_517, 4, g_517)]
theorem kn_924 : KnownBin bds_924 := by
  intro b hb
  simp only [bds_924, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_517
theorem sub_924 : ∀ b ∈ bds_924, m_924 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_924, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_924 : ∀ b ∈ bds_924, canon b.1 g_924 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_924, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_924 : dagCheckRootsF m_924 g_924 bds_924 (dagRefF 0 (dagTraceF m_924 s_924 4 f_673) l_673 0) s_924 4 = true := by decide +kernel
def node_924 : Nat → Bool := dagCheckNodeF m_924 g_924 bds_924 0 (dagTraceF m_924 s_924 4 f_673) l_673
theorem nc_924 : ∀ j, 0 ≤ j → j < 0 → node_924 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_924 : LowerBin m_924 s_924 g_924 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_924 sub_924 gl_924 rc_924 nc_924

def m_954 : Nat := 0xff000000ff000000
def s_954 : List Nat := [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000]
def g_954 : Nat := 0x1500000017000000
def bds_954 : List (Nat × List Nat × Nat × Nat) := [(m_127, s_127, 4, g_127)]
theorem kn_954 : KnownBin bds_954 := by
  intro b hb
  simp only [bds_954, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_127
theorem sub_954 : ∀ b ∈ bds_954, m_954 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_954, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_954 : ∀ b ∈ bds_954, canon b.1 g_954 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_954, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_954 : dagCheckRootsF m_954 g_954 bds_954 (dagRefF 0 (dagTraceF m_954 s_954 4 f_673) l_673 0) s_954 4 = true := by decide +kernel
def node_954 : Nat → Bool := dagCheckNodeF m_954 g_954 bds_954 0 (dagTraceF m_954 s_954 4 f_673) l_673
theorem nc_954 : ∀ j, 0 ≤ j → j < 0 → node_954 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_954 : LowerBin m_954 s_954 g_954 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_954 sub_954 gl_954 rc_954 nc_954

def m_956 : Nat := 0xff00ff0000000000
def s_956 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_956 : Nat := 0x1500170000000000
def bds_956 : List (Nat × List Nat × Nat × Nat) := [(m_248, s_248, 4, g_248)]
theorem kn_956 : KnownBin bds_956 := by
  intro b hb
  simp only [bds_956, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_248
theorem sub_956 : ∀ b ∈ bds_956, m_956 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_956, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_956 : ∀ b ∈ bds_956, canon b.1 g_956 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_956, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_956 : dagCheckRootsF m_956 g_956 bds_956 (dagRefF 0 (dagTraceF m_956 s_956 4 f_673) l_673 0) s_956 4 = true := by decide +kernel
def node_956 : Nat → Bool := dagCheckNodeF m_956 g_956 bds_956 0 (dagTraceF m_956 s_956 4 f_673) l_673
theorem nc_956 : ∀ j, 0 ≤ j → j < 0 → node_956 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_956 : LowerBin m_956 s_956 g_956 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_956 sub_956 gl_956 rc_956 nc_956

def m_958 : Nat := 0x5555555555555555
def s_958 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_958 : Nat := 0x1515155515555555
def bds_958 : List (Nat × List Nat × Nat × Nat) := [(m_860, s_860, 5, g_860)]
theorem kn_958 : KnownBin bds_958 := by
  intro b hb
  simp only [bds_958, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_860
theorem sub_958 : ∀ b ∈ bds_958, m_958 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_958, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_958 : ∀ b ∈ bds_958, canon b.1 g_958 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_958, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_958 : dagCheckRootsF m_958 g_958 bds_958 (dagRefF 0 (dagTraceF m_958 s_958 5 f_673) l_673 0) s_958 5 = true := by decide +kernel
def node_958 : Nat → Bool := dagCheckNodeF m_958 g_958 bds_958 0 (dagTraceF m_958 s_958 5 f_673) l_673
theorem nc_958 : ∀ j, 0 ≤ j → j < 0 → node_958 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_958 : LowerBin m_958 s_958 g_958 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_958 sub_958 gl_958 rc_958 nc_958

def f_960 : Nat → Nat × Nat := unpackForestF 0xa2e22343e43221301f 3 9
def l_960 : Nat → Nat → Option Nat := unpackLinksF 0x206986121c1 0xa0b902260f9032948e023204c01f 6 2 9 5 3
def m_960 : Nat := 0xaaaaaaaaaaaaaaaa
def s_960 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_960 : Nat := 0x202020202022a
def bds_960 : List (Nat × List Nat × Nat × Nat) := [(m_724, s_724, 5, g_724), (m_691, s_691, 5, g_691), (m_798, s_798, 6, g_798), (m_832, s_832, 6, g_832), (m_761, s_761, 5, g_761)]
theorem kn_960 : KnownBin bds_960 := by
  intro b hb
  simp only [bds_960, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact lb_724
  · exact lb_691
  · exact lb_798
  · exact lb_832
  · exact lb_761
theorem sub_960 : ∀ b ∈ bds_960, m_960 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_960, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_960 : ∀ b ∈ bds_960, canon b.1 g_960 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_960, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_960 : dagCheckRootsF m_960 g_960 bds_960 (dagRefSwapF m_960 63 g_960 6 (dagTraceF m_960 s_960 7 f_960) l_960 0) s_960 7 = true := by decide +kernel
def node_960 : Nat → Bool := dagCheckNodeWithF m_960 g_960 bds_960 (dagTraceF m_960 s_960 7 f_960) (dagRefSwapF m_960 63 g_960 6 (dagTraceF m_960 s_960 7 f_960) l_960)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_960_0 : treeBlockF 0 6 node_960 = true := by decide +kernel
theorem nc_960 : ∀ j, 0 ≤ j → j < 6 → node_960 j = true :=
  (certBlock nb_960_0)
theorem lb_960 : LowerBin m_960 s_960 g_960 8 :=
  lowerDagSwapF (top := 63) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_960 sub_960 gl_960 rc_960 nc_960

def m_961 : Nat := 0x3333333333333333
def s_961 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_961 : Nat := 0x1113131313131333
def bds_961 : List (Nat × List Nat × Nat × Nat) := [(m_832, s_832, 6, g_832)]
theorem kn_961 : KnownBin bds_961 := by
  intro b hb
  simp only [bds_961, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_832
theorem sub_961 : ∀ b ∈ bds_961, m_961 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_961, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_961 : ∀ b ∈ bds_961, canon b.1 g_961 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_961, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_961 : dagCheckRootsF m_961 g_961 bds_961 (dagRefF 0 (dagTraceF m_961 s_961 6 f_673) l_673 0) s_961 6 = true := by decide +kernel
def node_961 : Nat → Bool := dagCheckNodeF m_961 g_961 bds_961 0 (dagTraceF m_961 s_961 6 f_673) l_673
theorem nc_961 : ∀ j, 0 ≤ j → j < 0 → node_961 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_961 : LowerBin m_961 s_961 g_961 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_961 sub_961 gl_961 rc_961 nc_961

def f_962 : Nat → Nat × Nat := unpackForestF 0x17624bbcc14dd8926ec4877604bbb81f5dc0baec09376043005a7dd40a6e64737383eb9c175cc0e40169772029b4d28dbe8eedf05770044b7c11da6942dc07d6e02eb4c28da80eed405f6c044b5011da807ed50896a013b4c28002d1ed049368049b01af59c0a6c047365243b2815d9408ec04716383eb1c175800e6c10876082fb0411d8207ec102760038005a1d7c106ba48d5d846aec175740a4014974dc5fadc2453714e9b49f5935cac9365649329b4974da47ab1af558d4aac48556041a6d23554932a56a952a6ca9d2254a932a50514da43a6c15d4211aa105d4d829a70365381729c0a94e02ca6c1180290e6a8bf4c34a9aa2f52c1826a8af49c5ea4d22cd514a910533535aa3a3651cda26a4bf44b5da25aad1292a890933525ea09b6504952856b94124ca091e5040a26a4b74045c9a92bcfc9727b6c93da549ed264d494e744bd3a25d9d1234e89167447b3a0299a9294d40ae6e8bd374529b82f4dc0ba6a053358549ac164d408c014773435c995a14cc1026548d2d45e98a2f4c4d165a6a5300499692f4b717a5b6a52d85e96c174b40a4014672c03491da5caa4e25506923b4394120ca08e6504632814191c23496d0a4b49525a4692c94c8e0fa4828d2413e91c1700212e0e8bf21b4890d2441d14e0e6a71f1388f81c47c0d20e6971d8388ec1a41cd0e0e4a70704f8d4ae46a1b2350590704b83823c5cd7a2e6a5172418b8a0c5c10a0e08d1604c898aa44c1b2260991303c89c2244c0b20e0870703f87da943ed2a1f4950fa4687c94c1c0fa190d90c85c8642a4320f2190590703383817c2a51a1527d0702e83c3641e1720f0a90784c83c1641c08c01086db45f82ca536d17a086c1042606da2bc0b17a0508adb452805aa4020e201068db35b7f49c3fa0e1fd068db3536d9a5bf0951f8050fc0246d92dbe84a1f4050fa0246d929b6c92df007cf802e6d8ad3db1b1ed2d0db05f79daebced55e7492f394979c2536c179df2d8ef85477c263be0f1e12b8ef82c77c0e36c16ddd8b8db05776c2e3b0591d80a8ec02c6d829ba0179d00bae804674022ba00f9d005ce801d6d82936c0fdc78bce3c5271da938ed29c74bce3a5271c94b6c0f9c30a8e183c70c1636c0cdb605eddc5e6ee29376949bb2bcdd9526ec9f36c0b9b70a8db84c6dc1636c08c01076da15c6c0a1362901b1280d804663e2f358d51ac270d603463dadb540d18f6a6d32546989434c0918f4b6d202463d29b43179a128ac795267924b3c5258f0bccbc5e65dad32e979974a4cb92965c2931e0f9908bcc825a640af3205499027cc805263c170020cd8b0b0c614062c2a19317d85690c294861c1630a1218508864c5b5fdb02fe9817f2c0bf86c5fc3019315d79690bca485e4a42f21217908864c535d5a32ea8e57527464b525b62f2e41116d8a4b6b5e5b5a92da8e56d27464b4a59d262ce4a169088b382859c1219296d64050b202432529ac20a16104864a4b571262b84a15c050ae024325219928c5526a4ac134549a52ac49152462a91465489eaa44b8c92a4a2c5e53c2228b1494d268a2b52515a529449145462a295e514a928a4f54525c6494a509b0284580c90bea01504f5a2a7a5253d2426485e4e0b6270131380589c01c3242da651b1328c0993504c930264540c90ae9805c4a8b22541712a0a89504c4a81e2540b0c90a689a3144c2f2261751309a8984644c22a44485130889004444c1ea260b91c0988e04444c16a260b1170988b84445c1e226095140888a02444c0e9921490f6b087a4843cac19213d092b88484c42c262120f1090586484b3de2f1ef148f74627b85e40c161ee148f708c7b83d3dc171ee0b4fc69c7e3423dc161f40f0f704a7c0243dc0e992128f46907a148324239c1178f1270704523bda61c0d68ea6a0752503a8a81d4140e06ac7303c398161cc070e069c701413809c9c04c4e147070121324231bc130da2a86d04c368161b4070c90866c3403241799ad48cd69466a5a3352119a578cd2a46694a334a319a148cd0946482e328261940b0c9046008233142c18c900c50a80145f300a41840f0c00906004400a2d976d80bb2c05d86c2ec3000515cb66905b1482d82416c110028a6589382cc221620e0b10680135b2b81c15c0d0026a6558382ac1a004d2ca72705383829c1a004d0ca24a4511462889f1444b4022a44bc5e27c2212f1489d2484ba5225d2512e578972a44b93e25c968045289506840b5224c1a102d289124840a5223c921029288146046120204af1108c08924044144204a910c8c0812944193820c901025188125a011321fcb000417c7d4a03cb451e5248f4480790440105e1d4b60ea0b0750380105b1c2360e1180706c0381500082b8dc170692c83485c1a42a0d2130690580105319d180a64c8530bc2985d14c268a61185308a3012017c110a61105307c2d84c16c220a60f4530782b84c15c220a60d4540882a03414c0e8041485069028158008278965704d0982584c12c1600412c3a8bc1d45211d180744c83a0bc2203c0e8290741183a07c1d03d0f9a707cd083a0781d0350ec1a074074020941c1480082384b1783547012c520cda604ad682f6a017a500bc2804ad582c0781601c095a704a9042547212a310991c04c480250440104608c26040550200581001c0082183c5000207e0ab5a055a102a978154a40aa4a0552302a148150940103e04c160040cc036a401b4a00ca9006528030bc050440281e014070030a40383c01c0e0061280308c0183d00c0e8040c8010260001f 10 11
def l_962 : Nat → Nat → Option Nat := unpackLinksF 0xc9e2c9e0c8e8c864c822c820c820c728c6a4c35bc340c286c280c280c1c6c106c100bfe9bfc1bfc0bfc0bfa1be89be80be80bd69bd41bd40bd40bd21bd20bd20bd01bbe9ba4dba40ba40b929b920b809b7e1b7e0b7e0b6c9b6c0b6c0b5a9b581b580b580b580b580b469b270b260b12ab120b120b009aee9ae64ae60adc5ad82ad61ad60ad60ace4ac83ac80ac61ac60ac41aaccaac0aa82aa80aa80aa61aa60a9a6a962a960a941a80aa800a800a7e1a7e0a726a3faa383a380a269a260a1a6a1a0a1a0a0a8a0a0a043a021a0209fa49f819f619f609f609e0b9dc29dc09dc09da19da09da09ce69ce09c839c809c619c609c609be49be09be09be09be09be09be09a8b9a429a409a409a409a2198ac988198809804949c94809461946094229385938093809304930092849280928092809280914a900a90008fa38fa08fa08f248f208f208f208f208dea8de08de08de08de08cc98cc08cc08ba98a898a048a008a00896588e488e088e088c187e787e087e087a2872486e286c186c086c0864485e385e085c185a185818580840c840083c283c083c083c083c083a182e682a282a082a082a082a08281814a8140814081218120812080668022802080017eca7ec07ec07ea17ea07ea07de67aba7a437a40792979207920786678607860776877607760776077037700770076e1760775847580758075807523752075207501742773a473a073a073437321732072a472817261726072607260710b70c270c070c070c070c070a170a06fe66fe06f836f806f616f606f606ee46ee06ee06ee06ee06ee06ee06ee06d8b6d426d406d406d406d406d406d406d216bac6b816b806b806b046ac26ac06ac06ac06ac06ac06aa1692c6901690069006884651c650064e164e064e064a2640564006400640063846380634263406340634062c462c06282628062806204620062006184618061806180618061806180604a6040604060406040604060405f0a5dca5dc05dc05da15c895c805c805c805c615c605bc55ba15b815b615b605b415a865a805a805a805a805a42594859405940594057cc57c057c057a157a057a057a057a055ee55e055e055e055a255a05505550054c253a953a05362522a522052205201520051464f6f4f604f604f414f404f024f004f004f004d8c4d804d804d614d604d414d404d404ce34ce04ce04ce04ce04b2e4b204b204aa44aa04a814a804a614968494149404940490248844880488048804880488047a747a047814780478047804780478046a746624660466046034600458445614522452044e244e044e044e044a244a044a044a044a044054400440043c241d041c041c041c0412540e240c140c0408240613fc53fa13f623f413f403f403f023f003ec23ec03ea13ea03ea03e623e603e033e003dc23bef3be03be03b643b603b603b223b203b013b003b003b003b003a843a803a803a803a233a2039e239e039e039a2382c382038013800380037e13764376037033700370036e136c136a136a036a036813680368034ed34e034e0348330de30c030c030a12f892f802f802f612f602ec52ea12e812e802e612da62da02da02da02d622c682c602c602c222c202b852b802b422a292a2029e228aa28a02881288027c627c027c027c027c0264c2640264026212620260126002600260026002600244e24402402240023a323a0236223602303218c2180216121412140212120e220e020c120c020c0208220801eaf1ea01e241e201e011e001e001de11ce81cc11cc01c821c041c001c001c001c001b271b201b011b001b001b001b001a271a0119c219c019c01963196018e418e018c11882188018801880184218401840184017a517a017a0176215701560156014c51482148014421421138513611322132013011300130012c212c012c012a112a012a012621203120011c20fef0fe00f640f600f600f220f200f010f000f000f000e840e800e800e230e200de20de00de00de00da20c2c0c200c010c000be10b640b600b030ae10ac10aa10aa00aa00a810a800a80092b092008c308c008c008c008c008c008c008c008c008440840084007e307e007e007e0064d029e00330001 0x4ea350a60691590d4a7b1a550623e9d447b79c4a58d890de60296340433a8d62671a051826cabc488e805420b0a446a1527602957780f98d0195dc02e31c044ef8079d000eba01586cc280f581b232022570253bd0497790926f1121ce6241a644774b88e664118c8b153bc229776c526ec8a1b9f1418322770544e5af898b151239140a778012eed024dd804373c0830600ee0a01cb5e03162804662004d89898dd512961a242c480c6ea014b0c02162026461848ae801f30c032b9c05c60808ae911cdcd1396122477300e58401197e013a1069541892a77123307131b92252bfc48583018dc80295fc043428972e00225c423bab446f04c4eee1895dbf1238240777080aedf01197c013780294c084c8bd0913be04a75008d6e80f97f0195b802e2ec044f08172d80225aa044a584770444ed82891db403b8b806f6c80bed7011dac01fb50027678d76e3128dbc250a544776dc546d38a840f13b5fa2476d8146d302840e03b5f80465d004ed1124d06241a50473684525df8a0c0d139b40092ef81060601cd4c3529e44bd4189497d898d9d1295ea242be80c6ce014af4021a9c48945093ecc121c89143b2e25765448e44021d9602bb280465c804e260a92f61322e0244eb0179df02959003e5e80656380b8b701144e044adc48721c50d7c891bce04fb140876200bec3011d8401fb04027678d7ab6129d24249b344736488e2428a9c09149b1a2736044e178891c840538100936300e6c001c2f00232d40274189268611cc05149afa28301c4e5ae898c04049af80830180e5ae018d2234a6b42849c84c8b409140404aaf008c9c00cabb017164022a406955e891a008a5b57143aea25300012dab021d740292c0027590d62631a0506250abc489530d22ae12a506248ade2915b8122b412c4ee244aa84895a0d72761aa56626cac8499310d0276124552240a9c470768112af1af55c3529d869d418d36ad1214f82397fa29356450577890bfc049ab0082bb8086aa12654e23ca9c489548d52a813654c24ca0c47952c4a2a50142ea14044c26005006176918c321527fc2949504c9fe025544046a8405c5780893800f22601d4540508984e29f03653c05ca740a91181329c01657045fad88a7308d0ab5127d6224b9cc49558091eab1235482439062a6fe452da98a1ae9131a8e2575044a69b891a251219040a6fe012da9021ae8031a8c0575000a69b011a240212b40273d8d628c136506250a606954789768012aae71319c625283c48573018ce202941c0434a11b2841b0506260a2c4b94b45829603052845ea4c48ab8c4c670894a0d1215c40633800a506010d1c35da462534880a66811e51e46ca386d14389a2781304d0230a144a141917a7822ed1835da2c6ab45092a898a4c7f1415c22434481263f020ae00219f84a94288f2851ae50e36ca184a94209328311e505128a08051401172791364fa2509f84b93c0db27d1b24f82549ec4993c897a7812ecee2469d848b3a88f56f898ce912940a242b780c674014a040215b42807b84c00700c4e245e9c08a4b748c6400a938614a42426537817a3f0294dc02e2b00446d0078f700e9cc0283dc271360151ca0264d602ca648bf4b917a9522bd24452a406b546897e8812f50225b9fc4af3d094e731294af15b8f62a6fdc52d6c898ce512b9b625335448cf6890cae05b8f40a6fd812d6c018ce402b9b405335008cf60109540139a06b9334502660204c635299c68532891a5e894cbc02998c8bd310d165d894cba0299822931e450660024c780419788bd2e8d4a560ad1b61322a42452e017a3c0291b403296c05c54008a6422f4c235297c4bd2a456e3a8a9cb51299500b71d014e5a01494c0139480a92680f25801a4ac1389440a92701325501a49a24994c4832908e651118bf3149940282fd44e5a8898bbe049790073270d0a4d1254982465ae2632584a568890be204a4e80629c0085a79212d52327e629524851a4809f2d11327c00943b408475008cae34b950686fbc92da5921acd2337bc29527811a4a01f48e02e8d42b0d10501df028464044910691218922260a446205477c090ac85021909c44604c4e0060ac00c1570a04801388880991080f23f01c47c0344080611e00e23b01a14a13083c25107c0f07501046e058750089160112370ae3a61548d80d91a80b1a10a03a60488ac0811380e0ed1220621448c86bd188d49d31a73be34d884493180905f58a4c5e1418b8084ec80e5540111480128b0099138072270224561548a80d91481322801e44c02c77c038a985011f02001613c88c6a5110d2a211254402464e047c8f88f61f094acb1214b00625180492001e23e14c8740d90e01721b02a43403c8640585104c05381801512883e4a4fb4929f58a542c14685427cb2c4c8750970a712d54806434c084558160a713c84c0d90901721102a42004c83c05922917e42229c823538f46971d0d0e39129be724b68e486b1c8cda00a12a21322842451c013e34025b9e04a8cc08f16811a25021c4803f87807d0c00cd1201942e02f85005d07008c520113b01587ac0d8ef81420b0a52a0132280244f70175dd02ab9a03e41c064e000b84901140c46c8246c1040981e00b03be0607a80b90311794e09913c12281408ae600f90601937e02e120045018d520201c402034534060a60501ff09c39604c720078ff00e1fd01a20403052c280e184e1ca0261b40307e84a8fc80a1f801213a020270260fb04a1be01e37802c7d4050fa0090430101361306dc250dbc0f0200103da15d7c407cf800b9b400e3dc46c7b42d0f281a1d50303680307840a0ef9179d522ebd635d7a86aaf48925c8120bd01496f0282f381294801113401276c0a8f08071e10ae3ca16c7900a8f18131e201e3c002c77c038ee9171d60363b405076c0b8ea85b1da0b23b2054760058a384c8990913ac05e7540baea0119d3022ba403e408064e880b8430113a001d5182808001000809e39a45e7308a4e58d49ca1a539225e7204a46d08f90011eb8e12958a2428600c4980091d003c400298e28151c401e38602c25c2601d40c00789438045e6fc8a4df0949b792537a15e6f02a4dd84f96289904012e0ea25aa280c84b81085902c0ea278dc8151b802636e02c8308bf05117a0722bc084528006b6fe0d4dfb1a5bee25b7cc4a6f9092d60919bde15a5102644b0489ec02fbcc05e7780b6ee015dd7029b9e05273807ee300f9c20199ec03270405edd00b9b60118720226d02b8d90901b10a03441526cc284d801199c01f32a02e6b86a8d684e19b026358034664078d500d1a812a34e128650078d30091920163480246888bcd085159701f32002e67c492cc89059e0a4b241416708bccd8d699a12f33225257e262cc04a55d890b2e0523700626d00859522f32825a57a464c98579920a932213e576264c80148218108400116bc8bcd58d6da91a9b4a25b68c4a6adc8cda00a933a05e65807cc780b98c0a02de3505cc690a38541500a41e405c6340b0c581510202820e04861c058c48d21880a41dc054618090c28110ec0221d60443a8088768111831b03042606042c0c001b17f0301d20445c8490a78121711ac2fa3485f0490a705617b0a420c0585e8090bc81116f1a52ee3465d84729448c5590a929814a5d42744a04894302ea6805535805c088089720222e645e5c48a4b80d796f1a92dc239416462ab85494b0a52da13a248244888134f50229aa02e040044b481100a8162d624c5a82506a00f1680142ce02455a460488081559a02512402402603304800f8181a202c594050b200900901029523023c040a4cd010592011c1301182407181500e8181a002c588050b080900601000f02c57c498af04a0e202a1a603c574050ae0091559a929334a4f64bc944949059251c12465542a4a485288d0981b112a4f40bc940149050251c004636007aac04d0670982ac1245646a4ab8d2955118a8e14a55028ca984f5520970cc1225080ba990154ce01701e02253c088a684d0e192208e130528248a811794e22929835252c694a488c5480af28e15251827aa284b84609121e04d3d008a6680b80e0112863605082c09d81a1260302801502300409c11792622e9e434d4fc68a9f0524d10a0a7a12122c024980150ed02201502c4ec2d89d01313901627001c4d88d89a9181341a82662604c82a09381b12f02826005c4982d89785912e02e25a0544b00989580f12a0161141304880887681111d0162320244800788e00b11801222a01c2240409104848800924004445c0488e81311c02223204c4600888b80f00a81622801c4540888a00912811890e12249c0bc93017525026a0404a49008c9181152102223e03d47805c8d80b51a01622c025024044898075111ac22024843c2b0868161010221bc04442c0587401110b0261ce044398088868570e50aa21804c4280788480b0fd0161de0443f00584304c0ed02220602c3a00887d0090e70221fa34e3f06847d00f0078161f001c3980887c00910722f20c4524144624284890402f20405240408c7281150001e9fe02e3f805a7d80b0f901280c0223dc03a7a8d20f40a41ca048374080768d10f109c1de34c3b46a0760940eb0a81d40503a00787380b0e600e1c22302100407088e0830101e445e3c08a4770d68e91ab1ca34e36869a680524e40a09c6139388262700484820091bc04c01e0586e8550dc0261b602c3680386c0d008109800703002a24803c4900a8a400f1403586a46a8d28d412d1a624232a464690578d10a91a014a33c28c01c4b4ce02919a04a04e04201c4f0cb02619402c6288bec2116d7e22baf04535d06a4b60d296612dac6253580496ad890d5a118aa21525102944004894102fa7805e4dc0b698815d29029a2405243809e84012cf60251e604737c08c6c810cd701799802e324046010088c61201332502824904c8540a00a406c05c31c0b06281504302809204830807861c920c30a40640543040906001103002205e0440c40885f0d80bd93017a1602f00d85d81802e02213f14827c0905c8d209e92c1712482782b05c05204802c16e0482d80885981100b01e1692382d02700e0130b201c1620342562604a80c09492010f2302502804384c01102003203c2bc0705700d00901812713024c060494900859181241402142601481501002003003c2b00705580d00601801003c2a64705484e02802a03604c2a00705380d0a512913924a2424644c8528a40a314613e21c2645104b47f02e8e005505807c0780c89f02213a1242808bc4f11489c12913624a23a4644d0578990a913013e2142644b84b45002687004505407c0700c88a91812a03421a4601381109301a1152302442484348c0840a211e12423249c4549088691d10723623029c4505088609d1061361e809c3381084701d04c0362302404484d0890901142302202884308c08409c1061202506a4490d289012911c24a234460458578870a910a14a20828c4084b47902f0cc0521180941281181e01e8ff2601fc2c03b81a0640300fa2501e82403a91786422e86c34d1f068a3d8924191208f31221e40443701503102201603c1dc2d83b40f0760160ea01c1cc8d8391180711b00e12501c02a03281b06d0280dc05c1902d83685906c02e0d60541a809834c0f0690160c003419c4602f8110310220b803c1600682d80f05701a0ab02c1540383004805f8910be0221700982d8110580260ae04402c0782a40b05400e0aa0441500683348c8660990ca05e1900ba318134430250c404618408a2f01105d01f0b403d1640782b00d4090190a702d14c03a288d205092c0a01581380b02101102302209a03c1340981681102c02209c15c0ac2a82601304b81e09602c0fc0781981103e01e08e2300c40882200f02d02207e34e0f86840400f03b81607601c0b00881d80d04922f09045211a4642304c84502f08605210808c1581144101f08003d0f40781e00d40601907502d0e803a1c4920380a4056048088080188d103511c06634c0c46a01809402f8a805e0500b40781640b02c00e04f13009c0601388e02609006c45e0d08a4190d682e1ab05634e08069a0c09242a1208522390a046212c4882501104604c0200781105502181e04202c0800380f49001e0a000804002c4680408d00b1240102400706b40d8d081a12f0322520604940b89180411e82d1520562940b01481502500814c04e0780980b00c02201603c02a0580500700801e00f02c01c038088d48101a501f25203a4940785480e0a501a05e0240a40301280502300803d00e05a018074c422f97e45b2e88ae5a914cb01ad95a3532a8696530d0ca192912d24a202464508548960a51001321f80be3c01787402d8de0571a00a62901484f02789404b0e40941b811c2402303e04307407e0a00f812019804032bac69f728d2ed21a3d7e343ae44974d090e6911dcb223391a29706c50db589db1d13332224723012e0d021b6a03b63806664008c0100980001f 16 5 11 12 6
def m_962 : Nat := 0xcccccccccccccccc
def s_962 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_962 : Nat := 0x40404440444444c
def bds_962 : List (Nat × List Nat × Nat × Nat) := [(m_860, s_860, 5, g_860), (m_924, s_924, 5, g_924), (m_695, s_695, 6, g_695), (m_729, s_729, 6, g_729), (m_767, s_767, 6, g_767)]
theorem kn_962 : KnownBin bds_962 := by
  intro b hb
  simp only [bds_962, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact lb_860
  · exact lb_924
  · exact lb_695
  · exact lb_729
  · exact lb_767
theorem sub_962 : ∀ b ∈ bds_962, m_962 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_962, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_962 : ∀ b ∈ bds_962, canon b.1 g_962 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_962, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_962 : dagCheckRootsF m_962 g_962 bds_962 (dagRefSwapF m_962 63 g_962 757 (dagTraceF m_962 s_962 8 f_962) l_962 0) s_962 8 = true := by decide +kernel
def node_962 : Nat → Bool := dagCheckNodeWithF m_962 g_962 bds_962 (dagTraceF m_962 s_962 8 f_962) (dagRefSwapF m_962 63 g_962 757 (dagTraceF m_962 s_962 8 f_962) l_962)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_0 : treeBlockF 0 32 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_1 : treeBlockF 32 64 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_2 : treeBlockF 64 96 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_3 : treeBlockF 96 128 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_4 : treeBlockF 128 160 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_5 : treeBlockF 160 192 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_6 : treeBlockF 192 224 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_7 : treeBlockF 224 256 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_8 : treeBlockF 256 288 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_9 : treeBlockF 288 320 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_10 : treeBlockF 320 352 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_11 : treeBlockF 352 384 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_12 : treeBlockF 384 416 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_13 : treeBlockF 416 448 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_14 : treeBlockF 448 480 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_15 : treeBlockF 480 512 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_16 : treeBlockF 512 544 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_17 : treeBlockF 544 576 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_18 : treeBlockF 576 608 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_19 : treeBlockF 608 640 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_20 : treeBlockF 640 672 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_21 : treeBlockF 672 704 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_22 : treeBlockF 704 736 node_962 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_962_23 : treeBlockF 736 757 node_962 = true := by decide +kernel
theorem nc_962 : ∀ j, 0 ≤ j → j < 757 → node_962 j = true :=
  (joinChecks (joinChecks (joinChecks (joinChecks (certBlock nb_962_0) (joinChecks (certBlock nb_962_1) (certBlock nb_962_2))) (joinChecks (certBlock nb_962_3) (joinChecks (certBlock nb_962_4) (certBlock nb_962_5)))) (joinChecks (joinChecks (certBlock nb_962_6) (joinChecks (certBlock nb_962_7) (certBlock nb_962_8))) (joinChecks (certBlock nb_962_9) (joinChecks (certBlock nb_962_10) (certBlock nb_962_11))))) (joinChecks (joinChecks (joinChecks (certBlock nb_962_12) (joinChecks (certBlock nb_962_13) (certBlock nb_962_14))) (joinChecks (certBlock nb_962_15) (joinChecks (certBlock nb_962_16) (certBlock nb_962_17)))) (joinChecks (joinChecks (certBlock nb_962_18) (joinChecks (certBlock nb_962_19) (certBlock nb_962_20))) (joinChecks (certBlock nb_962_21) (joinChecks (certBlock nb_962_22) (certBlock nb_962_23))))))
theorem lb_962 : LowerBin m_962 s_962 g_962 9 :=
  lowerDagSwapF (top := 63) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_962 sub_962 gl_962 rc_962 nc_962

def f_963 : Nat → Nat × Nat := unpackForestF 0x3a781f 1 10
def l_963 : Nat → Nat → Option Nat := unpackLinksF 0x119 0x269e01f 3 1 10 3 2
def m_963 : Nat := 0xcccccccccccccccc
def s_963 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_963 : Nat := 0x40404440444444c
def bds_963 : List (Nat × List Nat × Nat × Nat) := [(m_729, s_729, 6, g_729), (m_924, s_924, 5, g_924), (m_767, s_767, 6, g_767), (m_695, s_695, 6, g_695), (m_860, s_860, 5, g_860)]
theorem kn_963 : KnownBin bds_963 := by
  intro b hb
  simp only [bds_963, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact lb_729
  · exact lb_924
  · exact lb_767
  · exact lb_695
  · exact lb_860
theorem sub_963 : ∀ b ∈ bds_963, m_963 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_963, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_963 : ∀ b ∈ bds_963, canon b.1 g_963 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_963, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_963 : dagCheckRootsF m_963 g_963 bds_963 (dagRefSwapF m_963 63 g_963 2 (dagTraceF m_963 s_963 7 f_963) l_963 0) s_963 7 = true := by decide +kernel
def node_963 : Nat → Bool := dagCheckNodeWithF m_963 g_963 bds_963 (dagTraceF m_963 s_963 7 f_963) (dagRefSwapF m_963 63 g_963 2 (dagTraceF m_963 s_963 7 f_963) l_963)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_963_0 : treeBlockF 0 2 node_963 = true := by decide +kernel
theorem nc_963 : ∀ j, 0 ≤ j → j < 2 → node_963 j = true :=
  (certBlock nb_963_0)
theorem lb_963 : LowerBin m_963 s_963 g_963 8 :=
  lowerDagSwapF (top := 63) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_963 sub_963 gl_963 rc_963 nc_963

def m_964 : Nat := 0xf0f0f0f0f0f0f0f
def s_964 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_964 : Nat := 0x50707070707070f
def bds_964 : List (Nat × List Nat × Nat × Nat) := [(m_798, s_798, 6, g_798)]
theorem kn_964 : KnownBin bds_964 := by
  intro b hb
  simp only [bds_964, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_798
theorem sub_964 : ∀ b ∈ bds_964, m_964 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_964, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_964 : ∀ b ∈ bds_964, canon b.1 g_964 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_964, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_964 : dagCheckRootsF m_964 g_964 bds_964 (dagRefF 0 (dagTraceF m_964 s_964 6 f_673) l_673 0) s_964 6 = true := by decide +kernel
def node_964 : Nat → Bool := dagCheckNodeF m_964 g_964 bds_964 0 (dagTraceF m_964 s_964 6 f_673) l_673
theorem nc_964 : ∀ j, 0 ≤ j → j < 0 → node_964 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_964 : LowerBin m_964 s_964 g_964 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_964 sub_964 gl_964 rc_964 nc_964

def m_965 : Nat := 0xf0f0f0f0f0f0f0f0
def s_965 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_965 : Nat := 0x1010105010505070
theorem lb_965 : LowerBin m_965 s_965 g_965 9 := by
  refine lowerByRows [0, 0, 4, 5, 0, 0, 6, 7, 0, 0, 12, 13, 0, 0, 14, 15, 0, 0, 20, 21, 0, 0, 22, 23, 0, 0, 28, 29, 0, 0, 30, 31, 0, 0, 36, 37, 0, 0, 38, 39, 0, 0, 44, 45, 0, 0, 46, 47, 0, 0, 52, 53, 0, 0, 54, 55, 0, 0, 60, 61, 0, 0, 62, 63] (by decide +kernel) ?_ (by decide +kernel) lb_962
  intro w hw
  simp only [s_965, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_966 : Nat := 0xf0f0f0f0f0f0f0f0
def s_966 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_966 : Nat := 0x1010105010505070
theorem lb_966 : LowerBin m_966 s_966 g_966 8 := by
  refine lowerByRows [0, 0, 4, 5, 0, 0, 6, 7, 0, 0, 12, 13, 0, 0, 14, 15, 0, 0, 20, 21, 0, 0, 22, 23, 0, 0, 28, 29, 0, 0, 30, 31, 0, 0, 36, 37, 0, 0, 38, 39, 0, 0, 44, 45, 0, 0, 46, 47, 0, 0, 52, 53, 0, 0, 54, 55, 0, 0, 60, 61, 0, 0, 62, 63] (by decide +kernel) ?_ (by decide +kernel) lb_963
  intro w hw
  simp only [s_966, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def f_967 : Nat → Nat × Nat := unpackForestF 0x93b4500a4f86b5f86b5d90c6c9086c9086086b578fc5e86b4d8ea6c86b478da5e86b458685f8b96c8b8548685b8946c8936c8916c8916086857879508785c871648685300a4785a546f45f84d6c6f45b83b566f45a81a6c8186c818606f4577d45e7d25e7f85c7d05e7da5c7d95c7d9507d0526f4567c35c7a5647a35c7a0387a0346f45377349773417725e77246772446f25675948759446f04f749487215c720347202c7284c720246f04b7125c6f0477004c6f9546f04300a376e35d6ba456c4586c4546c2546ba370084f673576a05c673476725b67b4a67b4667a56670360084b663455f25d6525c5f24763c6c63c605f23762147621275f15c60a4760a375f1505f14b5f147008475e05c563475c34a5c3465c2465603658a3b58a375892f5892b58927589235603457a375602c56a375602400843550544745f53b6c5386c47457528544725f518244725b5086c472574ea544ea444e824472534d8244724b4c35d4c150471564b35d4705647c5a47c5647b56479394805047856470460082b45b5845a543245f44b603245743a463235a41c5e41a5a41a563234a3eb4d3eb453fb4c3ea3a3e852322563d3583d2543215f3c14c3215b3b36032157391543914c39134321533814c3214b36b5036a5c3214734b4a34a56348463205a32b5a32a56328563204a008273105424b5f3006c24b572f05c24b472da362da3424a522ca4624a3a2b85c2b12a249562925d2995c2912a248562535a253562534a25346252562514a25056248360081b23a581b35f22a601b35721a501b347209361b25a1e15a1e1561e14a1e1461b23a1ba3a1b95a1c04a1b82c1b05a008171a0540135f1906c013571805c0134716a45168440115e12b4a12a5614144140441295e1314c1294601136118440d24f109500d2470f84c0d2370e8140d93a0d9360d12a011240625d0624d062450a2500a144060260693d088400693506842068400681a060140105601b5a04b5c01b5601b4a01b4601a5601a460184601036008130001f 9 11
def l_967 : Nat → Nat → Option Nat := unpackLinksF 0x4da498d5300e5a34b4096812c86523ca4093c727824b24960910f2186420c8408fc71f823f047e08f831c1a38047008d851a0a16f42c0848908860d241a082c505820b0416080d1018201140207fc4ff81ff03fe07ec8f9a1f303e417c80f901f203d487a80f501ea03d407a80f295e40bc807846f005dd1bba07740ee05db0bac57580e98dd303a417442daf1b5036056c00d801b0035846910d109a20340267c2cf819f033e066c8c6b98d031246240c30d86030c06088c1018202fe35fc0bf817a2af405e80b5416a02c865900b2016402bc65780af015e02bc05780af01554aaa05502aa01530a8ec51c0a30546028c0504aa081400a8004fc29f813d127a04f409e813a1a7404dc69b81360a6634cc0980d30026004c00980130025e14a4c8e351c0238046088c01151a2a0448688851102220428e8485090212042028401013a02040027e8cfd01f813f007d84fb01f603ec07c0cf801ee13dc07b04f221e403c807900ef19de03bc07780ec19bce37806e84dd01b4336806c08d801b0034ca6980cf219e033826494c90192032026118c20184030806100c20184030805d9caf615e02b445604a91952029865300a22144028805084a00932726404b8897012c1248843ac860906320c03e1c7b08ec51d4239886e28da11b0236006c00d421a8034086230c4018042f845d10b8116842d005908b20158627204e009a1128625004a009021200240047088e011c023803f4064d0c80190031086200c40188031006200a500d3c01c8001 0x20e25585a8d51793545a0d63cb55938d155393b4564dd5283b4520dcc301f30806c8c01719804e00b648dad51e02348ead5a00b46838d160aa355464e5508397ead724646c802d723a26c9145b2431609101b2420608f9179031254080960e5648ead723a26c7788d236b4e8d8979dc2344064d5011254020d5000258c01a21e0548c05b22e0546780d2200508a91b22836c6509b22616c8905821c0508805421e05c870590fa134928d7e4835d900d5df23558f0d36383478d0d15da2368cc57e2d15b88c55e1b1536ac52d931475364ed119373e44963205f8b016e2205786814daa04b64811d4c83b4420dcf80252fc07cbe01b22005c620138491a20e45485ad52162547c0d521256c809591e4c647909920e356808d56024587b91420ab6c8289b20916c81c5820806c818181fb1507e8141fe05c7e4141fab5c7e8971f815c7d85420245e7b117600b5e800979fd15e7d4549fc05e7d0149f035c7b9591e2c647b0d71e22647ac4e1e91347a80e1e8034790d25e2341780979de246770911d2048760521d61447401603a014748521c00447280503a038728131d015c73a111ce0347300b1c8024712d71c425c6f8101c004c6f85521445f84116e0c45a81115df245679914ddab56768959af15f69c56d8d1575dc54dd514f71c52dc31476f450dae05f69816d8c0575d814dd404f71812dc20476f010cbb01f2e806c8401717804db835d6c8d55b02363d44945c0126d1161b24546c2d51b02546dad15b62456b88dd4993b3ce4dd4912b3cc49c580123504d19e0346a0171a00541c84d1a234a680d199e25634a119aac576a8d5da634769096d7f25751692cefa475148ecef237342518d01361b04999c8466700d99034d660d15942564ca0e99425c628571841506411b18e4606205b18216062a91d8a14762049d84b4761091d822374c20e93002a65ad7592b47658975922476308dd8615c6005417e14b5f051d4193b3ae4dd4112b3ac49d2e83a4b80a8aa01a5e0171720545c2111700345780b15a0245d0d29723465c09193d129394494b901e5b08ed6a2374fe4ece99375a04bd6612b59049d621232dc0795e2375688dd763474e692ce3a474e48ece32372d44b96e8465821116e0365800d15c02c56009154054540db0cc9445381b1260644901114a054518090ad12c5081b13e2544f09113a02448e911220544d8091200364c8d75301504780d92c35d498d54ca8364801412845a499159243564884e51e0562cc0795245f53115d4825f51096d402574e094d3424b37e91d2e156322518b112e4a81591c046460d610a34840899116254420da1123604009510824a438918ce04a3f8d510a45e3f0d590825a418958db945358168560123f88e0fe34c408d35003453f08e8fa052350128cc03a150048520103d8d60f4254138040f014c3b0d80e8154398530e41343805304c010370d40dbb483689704a010358d28d4256348118ce35a330958ca05645117d10457430d690434a3e0958f215f3b856cea15738854cde14b36051cd005a32012848012310150c006c278190980342f01709a0542e2918b6a442e08d8b62341bc090b22462b0558a405625a118ae05c2b24e8ac12a16817094836250098a615c2a2d749eb552a09749e2552924e8a412a280d689e356270d289a3462609589614a250158c2c5f2fb15cc235f2f8d5cba3472d0948b0a4a2c08e8aa156288158928462480d88e258110040420201f89a08a2601000407a2582189403c0101fa528829461f84e8821360e0080360101d49687e15a1f05587a14a1e05187405a0d00807112c1c00b07004a1d29287423a1c85686e02c23317c88c57230d7c88357210d1c8025a1da9287623a1b45686c05a0c8040460141104902e0641a0150552341504d0401241901b0100640b01500a0340f80503c1241801700c0540221100803414c490518261440585cb451709144f93613c4985a04413651028044148510500441368e04c14c158d28542561385784a1460981580684609015046044088110421500801103a0380e05203e04c0e80503813a0d84d81a046112d3c40b4711093c402470f08dc3493a0d04a818046090050291240a0090200140a89402814408810024a3d0828d42413d0804d41e0420701001a82a06806830b5d042d542eb4d0b2d143025d0409542e24d0b09142793609c4982683609809818014048d701435a040d580e34a030d180a2560209180714601811866c5f18b15c6635f188d5c5e34716497849a461248d85815e122518481360c84901605601211804036932d3e18b4793093e182476e88ddad14f66c52d7b14755c50d1b93b31e4dd1b12b31c49dac04f66812d7a04755810d1a83b31a0dd1a02b31809c9101f24006c6a01700804c0001f 15 5 11 11 6
def m_967 : Nat := 0xff00ff00ff00ff
def s_967 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_967 : Nat := 0x1700570057007f
def bds_967 : List (Nat × List Nat × Nat × Nat) := [(m_778, s_778, 5, g_778), (m_702, s_702, 5, g_702), (m_776, s_776, 5, g_776), (m_673, s_673, 5, g_673), (m_767, s_767, 6, g_767), (m_761, s_761, 5, g_761), (m_772, s_772, 6, g_772)]
theorem kn_967 : KnownBin bds_967 := by
  intro b hb
  simp only [bds_967, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_778
  · exact lb_702
  · exact lb_776
  · exact lb_673
  · exact lb_767
  · exact lb_761
  · exact lb_772
theorem sub_967 : ∀ b ∈ bds_967, m_967 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_967, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_967 : ∀ b ∈ bds_967, canon b.1 g_967 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_967, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_967 : dagCheckRootsF m_967 g_967 bds_967 (dagRefSwapF m_967 55 g_967 296 (dagTraceF m_967 s_967 8 f_967) l_967 0) s_967 8 = true := by decide +kernel
def node_967 : Nat → Bool := dagCheckNodeWithF m_967 g_967 bds_967 (dagTraceF m_967 s_967 8 f_967) (dagRefSwapF m_967 55 g_967 296 (dagTraceF m_967 s_967 8 f_967) l_967)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_967_0 : treeBlockF 0 32 node_967 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_967_1 : treeBlockF 32 64 node_967 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_967_2 : treeBlockF 64 96 node_967 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_967_3 : treeBlockF 96 128 node_967 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_967_4 : treeBlockF 128 160 node_967 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_967_5 : treeBlockF 160 192 node_967 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_967_6 : treeBlockF 192 224 node_967 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_967_7 : treeBlockF 224 256 node_967 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_967_8 : treeBlockF 256 288 node_967 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_967_9 : treeBlockF 288 296 node_967 = true := by decide +kernel
theorem nc_967 : ∀ j, 0 ≤ j → j < 296 → node_967 j = true :=
  (joinChecks (joinChecks (joinChecks (certBlock nb_967_0) (certBlock nb_967_1)) (joinChecks (certBlock nb_967_2) (joinChecks (certBlock nb_967_3) (certBlock nb_967_4)))) (joinChecks (joinChecks (certBlock nb_967_5) (certBlock nb_967_6)) (joinChecks (certBlock nb_967_7) (joinChecks (certBlock nb_967_8) (certBlock nb_967_9)))))
theorem lb_967 : LowerBin m_967 s_967 g_967 9 :=
  lowerDagSwapF (top := 55) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_967 sub_967 gl_967 rc_967 nc_967

def f_968 : Nat → Nat × Nat := unpackForestF 0x1f 1 5
def l_968 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x1f 2 1 5 1 2
def m_968 : Nat := 0xff00ff00ff00ff
def s_968 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_968 : Nat := 0x1700570057007f
def bds_968 : List (Nat × List Nat × Nat × Nat) := [(m_776, s_776, 5, g_776), (m_702, s_702, 5, g_702), (m_778, s_778, 5, g_778), (m_673, s_673, 5, g_673), (m_767, s_767, 6, g_767), (m_761, s_761, 5, g_761), (m_772, s_772, 6, g_772)]
theorem kn_968 : KnownBin bds_968 := by
  intro b hb
  simp only [bds_968, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_776
  · exact lb_702
  · exact lb_778
  · exact lb_673
  · exact lb_767
  · exact lb_761
  · exact lb_772
theorem sub_968 : ∀ b ∈ bds_968, m_968 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_968, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_968 : ∀ b ∈ bds_968, canon b.1 g_968 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_968, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_968 : dagCheckRootsF m_968 g_968 bds_968 (dagRefSwapF m_968 55 g_968 1 (dagTraceF m_968 s_968 7 f_968) l_968 0) s_968 7 = true := by decide +kernel
def node_968 : Nat → Bool := dagCheckNodeWithF m_968 g_968 bds_968 (dagTraceF m_968 s_968 7 f_968) (dagRefSwapF m_968 55 g_968 1 (dagTraceF m_968 s_968 7 f_968) l_968)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_968_0 : treeBlockF 0 1 node_968 = true := by decide +kernel
theorem nc_968 : ∀ j, 0 ≤ j → j < 1 → node_968 j = true :=
  (certBlock nb_968_0)
theorem lb_968 : LowerBin m_968 s_968 g_968 8 :=
  lowerDagSwapF (top := 55) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_968 sub_968 gl_968 rc_968 nc_968

def f_969 : Nat → Nat × Nat := unpackForestF 0x37b49ded140a4fd0d7b435dd095b424ed091b423e0292eab5eaad76ab5caad4aab51aad430250aa93aaa49b6972da50b6172a85eacd72b350ac572b150aa1480a47a4d42925c72d5a825c72d55ca5e72975ca4e72935ca4c72919ca458c91a323272911ca3e86911ca3d7e931fa447e4a1c82a74531d14474061d014720980a434d179b3444d149335a66d4133564cd35325e4c96932564c94932464c8f951284c0a938184e0513026028ecd45e35169125c35158d4523e930d25a38d40e25034958d239028dcc24404d78b34404d48a24c04d147b4e1ed087a3e1e8f4134404978634404968425012900423404958323c04948123e06d10123d028cc001f 7 11
def l_969 : Nat → Nat → Option Nat := unpackLinksF 0x3fc1fc1f077787b83d82eb0f583a45b6ed62eb03581a06cd1e493241901c806403201900c426203101880c406012aad521a90530e9814a1a505282941405a004e8e5cd2c19604912481240910c8824412208d246823411a08d04491cece417203809bc2de06d13605ac2d41690b4059c2cc16603209900c8062127513429a04d0258920690046123011808824309944c806023001708b805a12d01604b0058026313009804a125012809024232100f887c03e01e086c4058001 0x4425cd045e9a45d4834de0349de3455ab41da25ad8259be2569a251be246d62456ea3e2e232a4244a025444b5c14b500c2380ca4c3aa44da35ed835dbc355843526834a3c346d6256bc255d424e5e24ad224616242d023e8423d14b5cbb15cb3150ba05cb205044b5cc025cb915cb1150b805cb005066248382443a234c024ea62426623a8ca36c0250ba25cb8250b605caf050b235cb0350ae15cac150bc45e8845dcc35eca35dc835c5eb5942355c6352c4351c2350be25e9c25dbe24ebc249a22429e2416423a36236b515eab152b405eaa05212234a6350a425c8e234a025c3aa44831287b124820287a024142406ca3c2c2300ca4c8623c81128791248002878024122408624a8e2466ca3e8c232862448224c802447e128771247a14c7814476018740149a35d8435aa23569e3556ab4e2a3429c25e9a25d9824e9624d9424c5a24a92246902458a2440a2428823e8423d7d12a731267c02a7202644a446c3443ea440c234663503025c282440c2481423c44b5c3aa4406230063445412851124500184e0146e45e6a4526835a6435662b4e6234d34345043426025e5e25a5c2565a25258246342455623e0423d5312a4d1265202a4c0262423044b5c4425c3ab44222403a2343e24c182303a350382500623c4845e4645a42456404523cb5a36b563434e0834d3c25a3625634a4e08a4d34a3e3423926a32262311c2302434c302442c344142342824c122342434e223421824a102462023e1e23d183441224014b5014250102340ca4c0c23c063442ec5e2ac522e35e2a35204b4d0434a26b46263451c3441a25e1625a0e2560a25208a4e04a4d0823e0423ddcb4fceb4ba8b4770b43dc24fce24ba8247702434aa3f4a23b32237022330001f 13 5 11 9 6
def m_969 : Nat := 0xff00ff00ff00ff00
def s_969 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_969 : Nat := 0x1500170017005700
def bds_969 : List (Nat × List Nat × Nat × Nat) := [(m_954, s_954, 5, g_954), (m_956, s_956, 5, g_956), (m_700, s_700, 5, g_700), (m_736, s_736, 5, g_736)]
theorem kn_969 : KnownBin bds_969 := by
  intro b hb
  simp only [bds_969, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact lb_954
  · exact lb_956
  · exact lb_700
  · exact lb_736
theorem sub_969 : ∀ b ∈ bds_969, m_969 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_969, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_969 : ∀ b ∈ bds_969, canon b.1 g_969 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_969, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_969 : dagCheckRootsF m_969 g_969 bds_969 (dagRefSwapF m_969 63 g_969 113 (dagTraceF m_969 s_969 7 f_969) l_969 0) s_969 7 = true := by decide +kernel
def node_969 : Nat → Bool := dagCheckNodeWithF m_969 g_969 bds_969 (dagTraceF m_969 s_969 7 f_969) (dagRefSwapF m_969 63 g_969 113 (dagTraceF m_969 s_969 7 f_969) l_969)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_969_0 : treeBlockF 0 32 node_969 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_969_1 : treeBlockF 32 64 node_969 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_969_2 : treeBlockF 64 96 node_969 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_969_3 : treeBlockF 96 113 node_969 = true := by decide +kernel
theorem nc_969 : ∀ j, 0 ≤ j → j < 113 → node_969 j = true :=
  (joinChecks (joinChecks (certBlock nb_969_0) (certBlock nb_969_1)) (joinChecks (certBlock nb_969_2) (certBlock nb_969_3)))
theorem lb_969 : LowerBin m_969 s_969 g_969 8 :=
  lowerDagSwapF (top := 63) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_969 sub_969 gl_969 rc_969 nc_969

def f_970 : Nat → Nat × Nat := unpackForestF 0x64f192e75c9d406476931a44190c63b18dcb4418cc01f 4 10
def l_970 : Nat → Nat → Option Nat := unpackLinksF 0x26130984c22510883c9e0e1703443801 0xa35c9350724c624422302344c74fb74b87475743c24fb24b82475243463f423b32371233001f 9 4 10 6 5
def m_970 : Nat := 0xff00ff00ff00ff00
def s_970 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_970 : Nat := 0x1500170017005700
def bds_970 : List (Nat × List Nat × Nat × Nat) := [(m_736, s_736, 5, g_736), (m_700, s_700, 5, g_700), (m_956, s_956, 5, g_956), (m_954, s_954, 5, g_954)]
theorem kn_970 : KnownBin bds_970 := by
  intro b hb
  simp only [bds_970, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact lb_736
  · exact lb_700
  · exact lb_956
  · exact lb_954
theorem sub_970 : ∀ b ∈ bds_970, m_970 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_970, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_970 : ∀ b ∈ bds_970, canon b.1 g_970 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_970, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_970 : dagCheckRootsF m_970 g_970 bds_970 (dagRefSwapF m_970 63 g_970 13 (dagTraceF m_970 s_970 6 f_970) l_970 0) s_970 6 = true := by decide +kernel
def node_970 : Nat → Bool := dagCheckNodeWithF m_970 g_970 bds_970 (dagTraceF m_970 s_970 6 f_970) (dagRefSwapF m_970 63 g_970 13 (dagTraceF m_970 s_970 6 f_970) l_970)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_970_0 : treeBlockF 0 13 node_970 = true := by decide +kernel
theorem nc_970 : ∀ j, 0 ≤ j → j < 13 → node_970 j = true :=
  (certBlock nb_970_0)
theorem lb_970 : LowerBin m_970 s_970 g_970 7 :=
  lowerDagSwapF (top := 63) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_970 sub_970 gl_970 rc_970 nc_970

def m_971 : Nat := 0xffff0000ffff
def s_971 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_971 : Nat := 0x17570000577f
theorem lb_971 : LowerBin m_971 s_971 g_971 9 := by
  refine lowerByRows [0, 1, 2, 3, 4, 5, 6, 7, 16, 16, 16, 16, 16, 16, 16, 16, 8, 9, 10, 11, 12, 13, 14, 15, 16, 16, 16, 16, 16, 16, 16, 16, 32, 33, 34, 35, 36, 37, 38, 39, 16, 16, 16, 16, 16, 16, 16, 16, 40, 41, 42, 43, 44, 45, 46, 47] (by decide +kernel) ?_ (by decide +kernel) lb_967
  intro w hw
  simp only [s_971, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_972 : Nat := 0xffff0000ffff
def s_972 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_972 : Nat := 0x17570000577f
theorem lb_972 : LowerBin m_972 s_972 g_972 8 := by
  refine lowerByRows [0, 1, 2, 3, 4, 5, 6, 7, 16, 16, 16, 16, 16, 16, 16, 16, 8, 9, 10, 11, 12, 13, 14, 15, 16, 16, 16, 16, 16, 16, 16, 16, 32, 33, 34, 35, 36, 37, 38, 39, 16, 16, 16, 16, 16, 16, 16, 16, 40, 41, 42, 43, 44, 45, 46, 47] (by decide +kernel) ?_ (by decide +kernel) lb_968
  intro w hw
  simp only [s_972, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_973 : Nat := 0xffff0000ffff0000
def s_973 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_973 : Nat := 0x1517000017570000
theorem lb_973 : LowerBin m_973 s_973 g_973 8 := by
  refine lowerByRows [0, 0, 0, 0, 0, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 23, 0, 0, 0, 0, 0, 0, 0, 0, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 0, 0, 0, 0, 0, 0, 48, 49, 50, 51, 52, 53, 54, 55, 0, 0, 0, 0, 0, 0, 0, 0, 56, 57, 58, 59, 60, 61, 62, 63] (by decide +kernel) ?_ (by decide +kernel) lb_969
  intro w hw
  simp only [s_973, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_974 : Nat := 0xffff0000ffff0000
def s_974 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_974 : Nat := 0x1517000017570000
theorem lb_974 : LowerBin m_974 s_974 g_974 7 := by
  refine lowerByRows [0, 0, 0, 0, 0, 0, 0, 0, 16, 17, 18, 19, 20, 21, 22, 23, 0, 0, 0, 0, 0, 0, 0, 0, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 0, 0, 0, 0, 0, 0, 48, 49, 50, 51, 52, 53, 54, 55, 0, 0, 0, 0, 0, 0, 0, 0, 56, 57, 58, 59, 60, 61, 62, 63] (by decide +kernel) ?_ (by decide +kernel) lb_970
  intro w hw
  simp only [s_974, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_975 : Nat := 0xffffffff
def s_975 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_975 : Nat := 0x1757577f
theorem lb_975 : LowerBin m_975 s_975 g_975 9 := by
  refine lowerByRows [0, 1, 2, 3, 4, 5, 6, 7, 32, 32, 32, 32, 32, 32, 32, 32, 8, 9, 10, 11, 12, 13, 14, 15, 32, 32, 32, 32, 32, 32, 32, 32, 16, 17, 18, 19, 20, 21, 22, 23, 32, 32, 32, 32, 32, 32, 32, 32, 24, 25, 26, 27, 28, 29, 30, 31] (by decide +kernel) ?_ (by decide +kernel) lb_967
  intro w hw
  simp only [s_975, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_976 : Nat := 0xffffffff
def s_976 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_976 : Nat := 0x1757577f
theorem lb_976 : LowerBin m_976 s_976 g_976 8 := by
  refine lowerByRows [0, 1, 2, 3, 4, 5, 6, 7, 32, 32, 32, 32, 32, 32, 32, 32, 8, 9, 10, 11, 12, 13, 14, 15, 32, 32, 32, 32, 32, 32, 32, 32, 16, 17, 18, 19, 20, 21, 22, 23, 32, 32, 32, 32, 32, 32, 32, 32, 24, 25, 26, 27, 28, 29, 30, 31] (by decide +kernel) ?_ (by decide +kernel) lb_968
  intro w hw
  simp only [s_976, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_977 : Nat := 0xffffffff00000000
def s_977 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_977 : Nat := 0x1517175700000000
theorem lb_977 : LowerBin m_977 s_977 g_977 8 := by
  refine lowerByRows [0, 0, 0, 0, 0, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 0, 0, 0, 0, 0, 0, 0, 0, 40, 41, 42, 43, 44, 45, 46, 47, 0, 0, 0, 0, 0, 0, 0, 0, 48, 49, 50, 51, 52, 53, 54, 55, 0, 0, 0, 0, 0, 0, 0, 0, 56, 57, 58, 59, 60, 61, 62, 63] (by decide +kernel) ?_ (by decide +kernel) lb_969
  intro w hw
  simp only [s_977, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def m_978 : Nat := 0xffffffff00000000
def s_978 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_978 : Nat := 0x1517175700000000
theorem lb_978 : LowerBin m_978 s_978 g_978 7 := by
  refine lowerByRows [0, 0, 0, 0, 0, 0, 0, 0, 32, 33, 34, 35, 36, 37, 38, 39, 0, 0, 0, 0, 0, 0, 0, 0, 40, 41, 42, 43, 44, 45, 46, 47, 0, 0, 0, 0, 0, 0, 0, 0, 48, 49, 50, 51, 52, 53, 54, 55, 0, 0, 0, 0, 0, 0, 0, 0, 56, 57, 58, 59, 60, 61, 62, 63] (by decide +kernel) ?_ (by decide +kernel) lb_970
  intro w hw
  simp only [s_978, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold Avail <;> decide +kernel

def f_1022 : Nat → Nat × Nat := unpackForestF 0x160455005afd7a96ebd0b75646fab236d5915eb8afb5c256ab131d5b5f6b50d95a366ab5b8d5a9c6b14d957271abcb655c5c6ad0ad56063005abd4a92ea950952a43a9425d4c212a508740d6ba8125d42d66a14b35004ba06b550359a9b8d94da48a6c2450358e996ad40b66a4b3d52c16292ce54a46ea4eb05249da814a74167aa39ac51c96282ce54607ca2dbb504d86824c34446ea0eb050c9f2834a34217ca0ca8d041da810a600b479fd324fd5f66d8cf38e7b9c63b4f59ea714dd3ab669d42dcec0b2750a738a6c9c9be4e40d2710c736c579be384dd59e6d48c00a5b995374d216e690a732a6c999be4cc0d2650c731c5798d2300294e600b73005397d324975be548fd2a27e96835cb418e544f92ad8c955c64ad1f2550692a07392eb3c9d1be4fafb27a7193c2b49c18e4b4cd2656a92d2b0028ee490c92457d82e33c6b9ee358ed220348d5b1c84092354c71f67a8f930c7c586350dd1b3668d92dc744a2364a71b15b8dc9e46c54e350d905c578cc32460df2314c91807c8b6b3c5c1722d6ad05b6b8ac3a454e3220cef1406c881b344c9c221acf10a5b8852bc424ae212471003482da5c3c5921d0f90cd6786c9e434112198b705a6b85e3841959e158c109a6684d2e4189ae114b90625b83e3041a59a0d2b90616b82c2300216e09068ff36381c123fc98e044c3021617f8373fe96dff4a6ff95b7fca9bfc1b1f28aefe06c7d9b33ee96df74aefb92b7dc91bec0d1f2696fa25c7cd2dbe4118010a6f6a5b7b529bda56ded2a6f606456ab7bb51f9e7b18f447c79c1a3b4dcde3b18f247c78c123b49cde04e2f01717683f3b69addb4c6ed96b76cb1bb41f15aaceec27475c4639b9ddd50d8e6b6674d3839d59dce4b6e725773895b9c48dcd068ad36b72c3638ad99c64b6e325771895b8c48dc5068ad3637083f3841f1b66ece01686dd37b7cdf1b74d6dba676ed36374dd1b74c6db92b6dc91b6c0d15a6b6da1746cc463399ddb1278d80446723db5c0f1ab488d613c6ac223391ada90d8ce26669cb833b59da5270ceb6b6889c3444d19d6b6ce95b674abb3a4fd9d266ce02456935b340f197488cc13c65c223191ad950d8c62666489c3244d18d6b6c695b634abb1a4fd8d266c602456931b144f189088ba47b61c9e30c111748e6c193860c9a2eadad80270c01345d5b1afcda1752debe27c5d4b5aea59d792d8bc2745d4b1aea4fd75266ba0245692dacb1bd70afab825659531ada9f96d4f8b2a4b5a6bead2dc5692acb2963598bf2cc5f165296ad06656eb52c49b15b4d6b026c56d31abc5b15b2d6ae16c56cb1ab415801076ac07c546b2aa517d552e0a9457548adaa454d510c85746f53c3227f5fd4d0c89fd7d4feb3a940913f4e6a3c7d51cb8a7e1f9408dea046750f3e28115d402d6a01634fc3e15d19d3d0a88d67b4e82b2741511acf49c07c46b3b26c15133af899a584cc2a2359cd318cc8d4764bc1223498d28cf4961484a33925558128aec94161468372375bd25cf88dd6b46eb3a451b120ce89014846eb1a3cd591b6cc8d95b46ca9a341b0ae8ae8c17445c4620f5dd150c88927c44cb22241f107ace8805c41d2b21c5c1088ce8596c42cb021115d082968414741c1215c9ad050c88127c40cb22041f0f9ace8005c3e52b1fa5b0fd2c07d4573e8a59f451cf9048572633dc361e89d0f52d87a07435f3f9e41d0ef518781743bc461af9dcec0fc7607c35d3b1d4150e8cf47406c35d331ca5a0e52c86c56f388be1c45c0d8ace6c16f37d3e1b05acd82ce6e16c36d3a1b058cd82b66c15735c1215c92cd48fa6a455311b799b5f8d18d866d79336b919b5c4cdae06234732a3e994518c42c66297e314be18d5c0c52ac6213b2b8331851a0afade5fc722fe3815f59caf8d45e4602e8b3174570af2d65c4602d8b316c570af2c65a1442c2bd1651c0b02ec5815c2bcad95c118010465607c296b294d17ca94e0534572992d94c94ca50c80146f28c321275fca10c849d7d24eb393c0d0936e64dc7d26d389261f8948de4a46725f3e12915c944d64a26324c3e00519c910a83767b2382b11c1506ecf44607c1bb3b11415087af843b5821c2a0dd9cc858cc3747620c1a0dcd8c7ccf4402481f3390fd5807caec3e2611b8370df5bc79cf837d6b1beb38ed1b074ce83a2481beb18e4d586f6cc37a5b1bd298dc1b0028ae362741ac460b75dc690c83337c19d320cc1f05bace3205c16dab0c49c05c8ce2fa6c17d300b915c5c4962e24716c1a004dac590c82b37c15d320ac1f04dace2a05c135ab0a29b0514c0274571392589c91c4d0680136312c36090dd0494d8240740af3f88c1d0437182227410c460579dc400fc2007c0adbb07c1503ccf41e06c0adb30729a0394c81656f0d93e06c9c02cace1626f0cdbe0589ac2c4ce1826c0bdba05898c2c4b6162570ac1a004d2c288fa14455061b78435f8258d810d79086b90435c421ae00c34707a3e83c918184c60ca7e0653e0355c0194ac0c23b0083302d1a003ade09c7204e3800759c038d4084600393301c970034d60646002933014970034c604244012bd00d1c0044ec0225c00d2d804118010260003f 10 11
def l_1022 : Nat → Nat → Option Nat := unpackLinksF 0x980397279720972095ac94e69464942293e2930792c292c092a19262922292209201920091e191a290c78eb18ea08ea08e628e608e608e228c4f8c028c008c008bc28b068a848a2389c38963882a87c386e786e086e0868386808661860384ca84c084c084c0846384608441840283c283c083a183a0838183808361830381ca7f927f807f617ea67e817e617e607e037e007e007e007de17cc97cc07cc07c827b4a7b407b217a6678ec78a278a078a078057800780077c2772576c375c875c075c0752574e274a27462746074607387736173607360734172e371e871a271a071a071a07143708670616fa66e4b6e406e216d666d416d216d206ce26ce06ca26ca06ca06ca06c436c406c406c406c216c206c206c016ae969aa69a06981698069616922692068e26807680067e167a267a06781678067616760676067606760668765c665c065a16562656065416502642764206401640063e163e063a263a063816380636163606322626660ec60e060a260a0606260606060602260206020602060205f855ee55ee05ec15ec05ec05ec05ec05e255da45da05d815d235c285c205c205c205c205b855b425b025ae15ae05ac15a635a415a405a2159c359c059c05982598059805980598058a757a857a057815742574057215720570157005700570057005627556655605541554055405540554054a554245420542053e253e053a25381536153415340532153015300530052085165516051415102510050e150a250a05062506050224fc34fc04fa14fa04f814f804f614f604f604f224f204f204f204f204e474d864d804d424d404d024ca34ca04c814c804c804c424c404c404c404c404ba54b244b204ae24a834a804a4249e349e049e049a249a049a0496249604922490148e148c148c048a1488148804880478846e546a246a046a0464346404640460246004600460045a345a045a0456244a6448144804461446044414440442144204401434641eb41e041c141c041c041a141a041a04105408440804042404040213fc33fc03f823f803f803f423f403f403f403f213f203f203e473ceb3ce03c833c803c803c423c403c023c003be13bc13ba13b243b013ac23ac03a823a803a803a423a403a213a2039853961394139213901390038e138e038a238a0388138803880374a35cc35c035a1356235603522352034e2348334803442344034213420342033e233e033e033073208320031c231c031823123312030e230e030e030a230a030a030052f462f402f022f002ec22e632e602e222e202de22d832d802d802d232d202d012d002ca32ca02ca02c622c602c602c222c012be12bc12ba12ba02b812b612b602b602a68298729802980290428e128e028c128c028c028c028252820282027a427a027a027a02781272326662660264126402640260225e125e025c125c02582258025612560252225202501250024e124e0248323c6224c2240222122202220220122002200216520e420e020a220a02081202320201fe21fe01fe01fa21fa01fa01fa01f811f801f801ea71d4b1d401ce31ce01ce01ca21ca01c621c601c411c211c011b841b611b221b201ae21ae01ae01aa21aa01a811a8019e519c119a1198119611960194119401902190018e118e018e017aa162c1620160115c215c015821580154214e314e014a214a01481148014801442144014401367126812601222122011e21183118011421140114011021100110010650fa60fa00f620f600f220ec30ec00e820e800e420de30de00de00d830d800d610d600d030d000d000cc20cc00cc00c820c610c410c210c010c000be10bc10bc00bc00ac809e709e009e00964094109400921092009200920088508800880080408000800080007e1078306c606c006a106a006a00662064106400621062005e205e005c105c005820580056105600541054004e3042602ac00340001 0xabc48d57011956013b008ab2f292debca5aa11237ad096a8008ca4009d72271af84b72ea926b68b8d7b15b7ab292a7448eb6038d7a05b7a9092a7008ca2009cfc26b9222d6a6448e48035a980232800274c8d114b891a9602327c026f4e565e942cd69171ad00e35c95f6b812b56717179b2b75981c5e642d93a0139616b2f2e966b5036568366ac00cd57499aae03356226cabc2d95809c6ae0b8d6c57dacc6e32a2d6eb2138bc5a5b52646756815abc237d7646da788cb5d115e981a356e2639f44b729a92eac8b1c8f15b7672969f448eac031c8e05b7650969f008c92009d522849e84f95302124003e4f827ba5c4c355092ea8121c8d17ba422c353c52ea58a1a791239180f7480186a7025d4a0434f004648004ea28acd44059a886b3508966a3125d4114b4e624750012d3901191a013a74ada9bc48d370119160134d62469a808c89009d1f151a3c0a244004e96128d1d1514d22474e91b295130d38248a362c34dc52132891d1a061a6c09099008c86009a631234c404642804e991ab4f625b9162b698448e4502da600232100274989d2968ac52c058a508dd4995828b8a8d16051a5ccf54a99ca9213b48717b8222e74545864303dc10073a280c241004e8f1ac51c258a1c0e94601f28b1bb50a076a0e4ed4181da8823750c27ca102f943958285128d06151a40cf54699ca711bdcca373a286c320c9ee06939d122614ba4674101daa42b5d3e56aa78acd4d158e986335303669c04d732098e91129c6916b7f62c740c54d19891c6806b7f40c740814d190118da0139fc4c93f15f67b22b4dca5675b2b6eb216c6a009cf427c9e04b93d19ea738b0ce60619d80593c319a781b346516b9de2b73ac54e32035cee05b9d40a634004e731be4e40349f0cf73db5da7b23b4f226e9d04d917c5ee718b1c5e07b9c40c632804e6f2384dc5678b62d6ea656e2d035ba885b18c0273eb59e7d233ce04579b54ad36891a2c8b5b9995b7322971601adcc42db9804b16802733c58667030cd515b9a62a735016e690298b001399c6f93300d26b1374d026c9962c732818c55009b9595b7290b629804e6422bcc6a5698c48ce2656dc48a5b8885b71009626004e618adcc11539840b730014c4a009cbe26411c0272c45c658038caf17195c0e32dc5ae5a8b1c5515b96c0d72d018e2a02d88a0139580692b11f2582c64ae38c9540692e91fa5c13f4b227c9522e714c5ae54039c5206b10802728c5c651038ca257d9404e327815a52237c9d16370729727018dc142587e0130f40272615aa278b5bf716389c0d6fd818c3b009cbc56f94cacf26899a4b12b43f16b7d62c6dae56e1f035bea0636d50b615004e4903249057d9148ad14ad6db2d2da2d2338590ad2001f23c02e47e07c9100691f01f24201248067a8fc4c31f05863a09446e13c8f18cd1e0d9a30135c7625b8e44a70e85ae380adc6c1534522472319ee456bb48a4768bc6f7218d8e1c13dc822634464671e81ba350364660648c44c9190df23003e4288668b80b917959e2d5b345a3566bf4d6d7c96e124334240568ac0e9150e322501a45006c8984e112959e2412dc462578682d6d6e56e22095c421238a4cef138d9a1913db55a6b8410cd1000d21e0b243b27c8740f90d84f21a922434044870acf0cb1ae1922dc19a668324ad06219a0c02b42e4708548c10a099a1312e42225c83c8c107059a0d0ae42c5678484d708096e0c0b5b5195b43e24723b59e47233c684578b06d70fad6e1f1a5c3026b66f4b6cdc92d06919c1685682c08d0281f20901a40807c81c049028986040b0c0425b8044a700056dff0a9a091238206c703098d01919c0606e7f80d8fe01b1fa12dbf22576672b6fc04adf7091bf636665b4d6f9a199f601a3e825c7cc4b6ca656cff891bfa4577d56b6fa8d2d8bd2db1724b3e2466f92159f20233e025b7bc4a6f7056ded0a99ed1233ce466f60191e91b8bca2717a0068f411f1e92c63c208c79c068f20091e423e3ca58c780118f18091e1138bc01717784d6ee898dd712dbb816b76c2c6d9856cf1891bd447e7986e6eb0dade2139b6426b3ba466ef81f9da03e3b027475c118e900d1d50363a6270748acee8896dd012bb6016b6242b6e784adce091bac6777506ccd789ed88135ac2066734068e581b1c912db902576182b6e384adc6091b943666144d6af8199c501a38607e7080f8df09e1c00b43762646f86f8dd0981bb1363743746fc4dede89adbc133b722636ac2d6cb858db8095b6e1237046ecd509ed96139ad80766d8068da05d1b304634c0246c4278d80111a401235c03c688068d604f1a209a35a2446ac088d08091a903634e170694270d184e1a209a34c5676906d6d08d6da00adb3e15767827ece84cdb233bb5e47b6a88d6d409995d033338024668078c900d19809e324134664488cb81119101232a06c64c270c904d1911adb2015b63c2aec704fd8d099b2c46b6504ccad81998c01231413c60c268c4e9118902230402461c278c004d186d2230c0445fc048c204e18309a302138600268bf0da17c0bc2f21645f04f8bc0581790b62f02746086d6bf8d8d7d0b7af616b5e82cebb858d7609faea1336208f6c291cd65d3b2ca0765d0048b889c56b0b8ae257d5c04acb505c56e13f2da27c5acafab50dc5690ab2ce17e5982f8b911bd6f131ad824b5a02c6b2852ceb8919d31235884d8b009b15e0b62b816c58cad4b089ad5f131aba16b56c2c673c48deb2b7bb25677306d6e20d8db51adb3626b62c4c6b9896cd6919ac80665680acac01f1550b82ac45f5508aea9856d520a99e894b55caca79a96d51032182856520118a781914d032262454509118a101f1470462940245208faa385c54333e28a46f5108cea1115d410b5a8016345c2b677a52d4e2bfa9857d4dcaeaa5959d3022b2922734584d677296d4603f27e07c2f90ac9681f0d002e27a0544ec0ac9d01513533ea7007c4d80a89601b0d123026a57c4d04b09581f13302a23c04c4c48cc8e81712803e25e0244a8ce89605212a2b025a67a4acce46815e9292bb250161494af09111912533e2425604888d89099d1200a423c356498ade9215ad232b3a3e5634758cc8e8d99120b5a041634702b68d854d3c33da7267a4dccec9919cd306bb2604764444f68089cd2e13199807649c0dc8d01b1180ba22e08c4340488601b11503221816c44c2c88a09f11203e2140242ed0cc8801710e0b821816c42c2c086b59d0d233a144574252b684255d090a5a10147459cee8b15dd112b3a1ea6643c4ac5ca198b902b20e0243f80d8828190fe0b62061644104f88101f0fc01216e8664000b87f05b0fd0b01f84573ed2b67d255cfb0a59f4147404ace7fa998ff12b16a8662d40ac7c8090f70361ca0643d42d8728590f613a1e80743900487181f0f203a1c617c3c02e8788a30ef0461c20243b40fc7601f0b142b1d40543a4cf46281d8e80361cc1683942c87185f0e20b81be1783702c86f89f0db0b01b816c36c4e87215bce12b39c016f3782d66e859cda0b19b215b3602ae7999fcee33b9d627639c4cc6201d8af4331ae0243548fa691174d422a996171344af86891b0d22bf1a057933cae46715c4cd2b8196d7d32c8fa652558ca0a318c5703202fc6385f0c50ab1a6c6f34c6de660d1cc90b198894b3102766111a0c023917e4702cc2b65e1180bb0b317415c2e08c05b8598b60ae1681442c88e05995e8b10bb16015c304ade5f159cbd23517216b2d42c657856d506b7a7cd675408de9f119d1922ba0c26b3e04c66b296cd61259860662b90ac570118ac03e1522702a88be54115ca712d94c253121496559594475ad94a0640550ac4e0230a30321420642148a84b22309603e13608c2780684e11f49b13892e67c2648de4c119c9622b92a26b2504c635896c4352594457f280afa4595d49f2b39084562746e6350dac425ad93407e24c0f80921588103e04805c2440a84781588e02a11267d2300f84501508003604a460224af8440d607f03e10e0541c80984291987102e0f807c20c0683f19d0801240fc560204cf43f99c8242bd0fa5761f04c23c95e0762320f267c1d4ac03b11b07533a0e82481c86ac3d15bc782b58ee5671ccac638b198711b30cc26b1584c638096c6f12992067b234cf44599d886339908d762108ec328dec551b99043630800ec3d81b86e0360d82741ac1183080d0600360d20641804d8338990681be0cc07c17806807a1986402e0c42701804d82f8980616b38c24671788ae2ea96c5c52b8ba24b17048e3539dc6a2bb8ca56718d6cc318d580d43301a05616c0682901b0590320a426c15c4c82c0df05603e0a003402d0cc2a0170521360a22601408ae27a96c4e52b89e24b13848e2a959c535b30a63560250cc0481584d01a09606c0e40c82489b0391320943741200e81c00d03703e08c0740dc4f82209d0451c608608c0d40682081f84003e00a8560f80a81e99e81903b07806c0e84d01c89903713e06c2700cc4f0180990331be05e2600c04d8178dd0382b786a5670d04de1909ac3113385c2630b44b616095c4733f8846770fc6ec1d8d981803b0068660ac0681491f42622e85045507c4e21295f02523604c57e090af21195c8222b884257007dafa0f91f41e52b03c246068ae00e09f81b13e03225609d8de138dbc201a383a2630614960c08ec1623402847204c8e003896c1023001e2660384b80611800b13301425c0204880311c0072bd00a2760104b80a95bc122b382246a0344d604898c0312d948d6f249ace5211bc922338da4571686d6260d8c2a5ad85434b05c0cc0121580202357ec5faad8af5f8d7eab1abd003479b04b731094e4a525c9423b82a2b6f8c54d59ca5ab313b2b624705016df1029ab284b56407656808c0100980003f 16 5 11 12 6
def m_1022 : Nat := 0xffffffffffffffff
def s_1022 : List Nat := [0x5555555555555555, 0x3333333333333333, 0xf0f0f0f0f0f0f0f, 0xff00ff00ff00ff, 0xffff0000ffff, 0xffffffff]
def g_1022 : Nat := 0x151717571757577f
def bds_1022 : List (Nat × List Nat × Nat × Nat) := [(m_964, s_964, 7, g_964), (m_961, s_961, 7, g_961), (m_960, s_960, 8, g_960), (m_958, s_958, 6, g_958), (m_976, s_976, 8, g_976), (m_966, s_966, 8, g_966), (m_968, s_968, 8, g_968), (m_972, s_972, 8, g_972), (m_978, s_978, 7, g_978), (m_963, s_963, 8, g_963), (m_970, s_970, 7, g_970), (m_974, s_974, 7, g_974), (m_969, s_969, 8, g_969), (m_967, s_967, 9, g_967), (m_962, s_962, 9, g_962), (m_971, s_971, 9, g_971), (m_973, s_973, 8, g_973), (m_975, s_975, 9, g_975), (m_977, s_977, 8, g_977), (m_965, s_965, 9, g_965)]
theorem kn_1022 : KnownBin bds_1022 := by
  intro b hb
  simp only [bds_1022, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_964
  · exact lb_961
  · exact lb_960
  · exact lb_958
  · exact lb_976
  · exact lb_966
  · exact lb_968
  · exact lb_972
  · exact lb_978
  · exact lb_963
  · exact lb_970
  · exact lb_974
  · exact lb_969
  · exact lb_967
  · exact lb_962
  · exact lb_971
  · exact lb_973
  · exact lb_975
  · exact lb_977
  · exact lb_965
theorem sub_1022 : ∀ b ∈ bds_1022, m_1022 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1022, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_1022 : ∀ b ∈ bds_1022, canon b.1 g_1022 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1022, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1022 : dagCheckRootsF m_1022 g_1022 bds_1022 (dagRefSwapF m_1022 63 g_1022 705 (dagTraceF m_1022 s_1022 11 f_1022) l_1022 0) s_1022 11 = true := by decide +kernel
def node_1022 : Nat → Bool := dagCheckNodeWithF m_1022 g_1022 bds_1022 (dagTraceF m_1022 s_1022 11 f_1022) (dagRefSwapF m_1022 63 g_1022 705 (dagTraceF m_1022 s_1022 11 f_1022) l_1022)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_0 : treeBlockF 0 32 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_1 : treeBlockF 32 64 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_2 : treeBlockF 64 96 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_3 : treeBlockF 96 128 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_4 : treeBlockF 128 160 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_5 : treeBlockF 160 192 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_6 : treeBlockF 192 224 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_7 : treeBlockF 224 256 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_8 : treeBlockF 256 288 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_9 : treeBlockF 288 320 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_10 : treeBlockF 320 352 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_11 : treeBlockF 352 384 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_12 : treeBlockF 384 416 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_13 : treeBlockF 416 448 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_14 : treeBlockF 448 480 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_15 : treeBlockF 480 512 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_16 : treeBlockF 512 544 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_17 : treeBlockF 544 576 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_18 : treeBlockF 576 608 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_19 : treeBlockF 608 640 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_20 : treeBlockF 640 672 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_21 : treeBlockF 672 704 node_1022 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1022_22 : treeBlockF 704 705 node_1022 = true := by decide +kernel
theorem nc_1022 : ∀ j, 0 ≤ j → j < 705 → node_1022 j = true :=
  (joinChecks (joinChecks (joinChecks (joinChecks (certBlock nb_1022_0) (certBlock nb_1022_1)) (joinChecks (certBlock nb_1022_2) (joinChecks (certBlock nb_1022_3) (certBlock nb_1022_4)))) (joinChecks (joinChecks (certBlock nb_1022_5) (joinChecks (certBlock nb_1022_6) (certBlock nb_1022_7))) (joinChecks (certBlock nb_1022_8) (joinChecks (certBlock nb_1022_9) (certBlock nb_1022_10))))) (joinChecks (joinChecks (joinChecks (certBlock nb_1022_11) (joinChecks (certBlock nb_1022_12) (certBlock nb_1022_13))) (joinChecks (certBlock nb_1022_14) (joinChecks (certBlock nb_1022_15) (certBlock nb_1022_16)))) (joinChecks (joinChecks (certBlock nb_1022_17) (joinChecks (certBlock nb_1022_18) (certBlock nb_1022_19))) (joinChecks (certBlock nb_1022_20) (joinChecks (certBlock nb_1022_21) (certBlock nb_1022_22))))))
theorem lb_1022 : LowerBin m_1022 s_1022 g_1022 12 :=
  lowerDagSwapF (top := 63) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1022 sub_1022 gl_1022 rc_1022 nc_1022

def wg : List Gate :=
  [⟨GateOp.and, [1, 2]⟩,
    ⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.and, [3, 4]⟩,
    ⟨GateOp.or, [3, 4]⟩,
    ⟨GateOp.and, [7, 9]⟩,
    ⟨GateOp.or, [5, 10]⟩,
    ⟨GateOp.and, [0, 11]⟩,
    ⟨GateOp.or, [6, 12]⟩,
    ⟨GateOp.and, [0, 7]⟩,
    ⟨GateOp.and, [5, 10]⟩,
    ⟨GateOp.or, [8, 14]⟩,
    ⟨GateOp.or, [15, 16]⟩,
    ⟨GateOp.and, [13, 17]⟩]

theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg
  simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) =
    Nat.testBit (3941132456 * 2 ^ 32 + 3903367296) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

theorem root_lb : LowerBin fullMask rootStock (canon fullMask (3941132456 * 2 ^ 32 + 3903367296)) (13 - 1) := by
  exact lb_1022

end PEqualNP.Outside.L_meta_47395

theorem PEqualNP.Outside.L_meta_47395 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941132456 * 2 ^ 32 + 3903367296) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941132456 * 2 ^ 32 + 3903367296) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact PEqualNP.Outside.L_meta_47395.table2_from_lowerBin
    (3941132456 * 2 ^ 32 + 3903367296) 13 PEqualNP.Outside.L_meta_47395.root_lb
    PEqualNP.Outside.L_meta_47395.wg 18 rfl
    PEqualNP.Outside.L_meta_47395.wfits PEqualNP.Outside.L_meta_47395.weval
