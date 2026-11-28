import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_49369

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

def m_0 : Nat := 0xff00
def s_0 : List Nat := [0x5500, 0x3300, 0xf00]
def g_0 : Nat := 0x1700
def ep_0 : Nat := 0x60000000000000012000000000000001400
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

def m_2 : Nat := 0xf0f000000000000
def s_2 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_2 : Nat := 0x107000000000000
def ep_2 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
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

def m_3 : Nat := 0x3300330000000000
def s_3 : List Nat := [0x1100110000000000, 0x300030000000000, 0x330000000000]
def g_3 : Nat := 0x100130000000000
def ep_3 : Nat := 0x1200000000000000000000000000010002000000000000000000000000000100100000000000
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

def m_4 : Nat := 0xf000f0000000000
def s_4 : List Nat := [0x500050000000000, 0x300030000000000, 0xf0000000000]
def g_4 : Nat := 0x100070000000000
def ep_4 : Nat := 0x600000000000000000000000000000000000000000001000200000000000100040000000000
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

def m_5 : Nat := 0xf0f0
def s_5 : List Nat := [0x5050, 0x3030, 0xf0]
def g_5 : Nat := 0x1070
def ep_5 : Nat := 0x60000000000000000000000000000010200000000000001040
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

def m_6 : Nat := 0x5050505000000000
def s_6 : List Nat := [0x1010101000000000, 0x50005000000000, 0x505000000000]
def g_6 : Nat := 0x10105000000000
def ep_6 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000000000000000000
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

def m_7 : Nat := 0x4444444400000000
def s_7 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_7 : Nat := 0x4044400000000
def ep_7 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
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

def m_8 : Nat := 0xff000000000000
def s_8 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_8 : Nat := 0x17000000000000
def ep_8 : Nat := 0x600000000000000120000000000000014000000000000
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

def m_9 : Nat := 0xff000000
def s_9 : List Nat := [0x55000000, 0x33000000, 0xf000000]
def g_9 : Nat := 0x17000000
def ep_9 : Nat := 0x600000000000000120000000000000014000000
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

def m_10 : Nat := 0x5500000055000000
def s_10 : List Nat := [0x1100000011000000, 0x500000005000000, 0x55000000]
def g_10 : Nat := 0x100000015000000
def ep_10 : Nat := 0x1400000000000000000000000000000000000000010000000400000001000000100000000000000000000000
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

def m_11 : Nat := 0x3300000033000000
def s_11 : List Nat := [0x1100000011000000, 0x300000003000000, 0x33000000]
def g_11 : Nat := 0x100000013000000
def ep_11 : Nat := 0x1200000000000000000000000000000000000000010000000200000000000000000000000100000010000000
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

def m_12 : Nat := 0xf0000000f000000
def s_12 : List Nat := [0x500000005000000, 0x300000003000000, 0xf000000]
def g_12 : Nat := 0x100000007000000
def ep_12 : Nat := 0x600000000000000000000000000000000000000000000000000000001000000020000000100000004000000
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

def m_13 : Nat := 0xaa000000aa
def s_13 : List Nat := [0x2200000022, 0xa0000000a, 0xaa]
def g_13 : Nat := 0x20000002a
def ep_13 : Nat := 0x2800000000000000000000000000000000000000020000000800000002000000200000000000000000
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

def m_14 : Nat := 0xff0000000000
def s_14 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_14 : Nat := 0x170000000000
def ep_14 : Nat := 0x6000000000000001200000000000000140000000000
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

def m_15 : Nat := 0x2222000022220000
def s_15 : List Nat := [0x202000002020000, 0x22000000220000, 0x22220000]
def g_15 : Nat := 0x2000002220000
def ep_15 : Nat := 0x220000000000000000000000002000000200000000200000200000000000000000000000000000000000000
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

def m_16 : Nat := 0x3030000030300000
def s_16 : List Nat := [0x1010000010100000, 0x30000000300000, 0x30300000]
def g_16 : Nat := 0x10000010300000
def ep_16 : Nat := 0x1020000000000000000000000010000000200000000000000000000000000000000000000010000010000000
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

def m_17 : Nat := 0x5555000000000000
def s_17 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_17 : Nat := 0x115000000000000
def ep_17 : Nat := 0x14000000000000010400000000000001100000000000000000000000000000
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

def m_18 : Nat := 0x3333000000000000
def s_18 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_18 : Nat := 0x113000000000000
def ep_18 : Nat := 0x12000000000000010200000000000000000000000000000110000000000000
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

def m_19 : Nat := 0xaaaa
def s_19 : List Nat := [0x2222, 0xa0a, 0xaa]
def g_19 : Nat := 0x22a
def ep_19 : Nat := 0x28000000000000020800000000000002200000000000000000
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

def m_20 : Nat := 0xcccc
def s_20 : List Nat := [0x4444, 0xc0c, 0xcc]
def g_20 : Nat := 0x44c
def ep_20 : Nat := 0x48000000000000040800000000000000000000000000000440
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

def m_21 : Nat := 0xcc00cc
def s_21 : List Nat := [0x440044, 0xc000c, 0xcc]
def g_21 : Nat := 0x4004c
def ep_21 : Nat := 0x480000000000000000000000000004000800000000000000000000000000040040
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

def m_22 : Nat := 0x2288228822882288
def s_22 : List Nat := [0x88008800880088, 0x208020802080208, 0x228800002288, 0x22882288]
def g_22 : Nat := 0x20002000208
def ep_22 : Nat := 0x200000800000200000000080000000000000000000002000200020800000000000000000000000000000000
theorem epk_22 : ep_22 = edgePack m_22 g_22 := by decide +kernel
def bds_22 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_22 : KnownBin bds_22 := by intro b hb; simp [bds_22] at hb
theorem sub_22 : ∀ b ∈ bds_22, m_22 &&& b.1 = b.1 := by intro b hb; simp [bds_22] at hb
theorem gl_22 : ∀ b ∈ bds_22, canon b.1 g_22 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_22] at hb
def cur_22 : Nat → List (Nat × Nat) := unpackCursorV4 0x16ac58b12a44890e8701 0x31303060c8f08181a3c226128fa119393e526480f8419000f 7 127 3 7 10 1023 15 32767
def f_22 : Nat → Nat × Nat := unpackForestF 0xc7c63229f68f0a6443e51e24c086400f 3 10
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV4 m_22 g_22 ep_22 10 bds_22 (dagTraceF m_22 s_22 4 f_22) (cur_22 0) s_22 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_22 : treeBlockF 0 10 (dagCheckNodeV4 m_22 g_22 ep_22 bds_22 10 (dagTraceF m_22 s_22 4 f_22) cur_22) = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 10 → (dagCheckNodeV4 m_22 g_22 ep_22 bds_22 10 (dagTraceF m_22 s_22 4 f_22) cur_22) i = true := fun _ h1 h2 => treeBlockF_at nb_22 h1 h2
theorem lb_22 : LowerBin m_22 s_22 g_22 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_22 kn_22 sub_22 gl_22 rc_22 nc_22

def m_23 : Nat := 0x3300330000330033
def s_23 : List Nat := [0x1100110000110011, 0x300030000030003, 0x330033, 0x330000000033]
def g_23 : Nat := 0x100130000330033
def ep_23 : Nat := 0x1200000000000000000000000000010002000000000000000000000000000100100000000000
theorem epk_23 : ep_23 = edgePack m_23 g_23 := by decide +kernel
def bds_23 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_23 : KnownBin bds_23 := by
  intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_23 : ∀ b ∈ bds_23, m_23 &&& b.1 = b.1 := by intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_23 : ∀ b ∈ bds_23, canon b.1 g_23 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_23 : Nat → List (Nat × Nat) := fun _ => []
def f_23 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV4 m_23 g_23 ep_23 0 bds_23 (dagTraceF m_23 s_23 4 f_23) (cur_23 0) s_23 4 = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_23 g_23 ep_23 bds_23 0 (dagTraceF m_23 s_23 4 f_23) cur_23 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_23 : LowerBin m_23 s_23 g_23 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_23 kn_23 sub_23 gl_23 rc_23 nc_23

def m_24 : Nat := 0xff00ff0000000000
def s_24 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_24 : Nat := 0x100170000000000
def ep_24 : Nat := 0x1600000000000000000000000000010006000000000001001200000000000100140000000000
theorem epk_24 : ep_24 = edgePack m_24 g_24 := by decide +kernel
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4), (m_14, s_14, 4, g_14), (m_1, s_1, 4, g_1), (m_3, s_3, 4, g_3)]
theorem kn_24 : KnownBin bds_24 := by
  intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_4
  · exact lb_14
  · exact lb_1
  · exact lb_3
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
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2), (m_8, s_8, 4, g_8), (m_17, s_17, 4, g_17), (m_18, s_18, 4, g_18)]
theorem kn_25 : KnownBin bds_25 := by
  intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_2
  · exact lb_8
  · exact lb_17
  · exact lb_18
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

def m_26 : Nat := 0xff00ff00000000
def s_26 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_26 : Nat := 0x17005700000000
def ep_26 : Nat := 0x40000000000000000000000000000600020000000000120002000000000014005400000000
theorem epk_26 : ep_26 = edgePack m_26 g_26 := by decide +kernel
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
theorem kn_26 : KnownBin bds_26 := by
  intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_8
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
def g_27 : Nat := 0x10105000000000
def ep_27 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000010105000000000
theorem epk_27 : ep_27 = edgePack m_27 g_27 := by decide +kernel
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
theorem kn_27 : KnownBin bds_27 := by
  intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_6
theorem sub_27 : ∀ b ∈ bds_27, m_27 &&& b.1 = b.1 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_27 : ∀ b ∈ bds_27, canon b.1 g_27 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_27 : Nat → List (Nat × Nat) := fun _ => []
def f_27 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV4 m_27 g_27 ep_27 0 bds_27 (dagTraceF m_27 s_27 4 f_27) (cur_27 0) s_27 4 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_27 g_27 ep_27 bds_27 0 (dagTraceF m_27 s_27 4 f_27) cur_27 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_27 kn_27 sub_27 gl_27 rc_27 nc_27

def m_28 : Nat := 0xcccccccc00000000
def s_28 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_28 : Nat := 0x4044400000000
def ep_28 : Nat := 0x440000000000004004000000000000404000000000000000000000000000004044400000000
theorem epk_28 : ep_28 = edgePack m_28 g_28 := by decide +kernel
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
theorem kn_28 : KnownBin bds_28 := by
  intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_7
theorem sub_28 : ∀ b ∈ bds_28, m_28 &&& b.1 = b.1 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_28 : ∀ b ∈ bds_28, canon b.1 g_28 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_28 : Nat → List (Nat × Nat) := fun _ => []
def f_28 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV4 m_28 g_28 ep_28 0 bds_28 (dagTraceF m_28 s_28 4 f_28) (cur_28 0) s_28 4 = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_28 g_28 ep_28 bds_28 0 (dagTraceF m_28 s_28 4 f_28) cur_28 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_28 : LowerBin m_28 s_28 g_28 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_28 kn_28 sub_28 gl_28 rc_28 nc_28

def m_29 : Nat := 0xaa00aa00aa00aa
def s_29 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_29 : Nat := 0x200020022002a
def ep_29 : Nat := 0x20002800000000000000080000000000000000000200020000000800020002002200200000000000000000
theorem epk_29 : ep_29 = edgePack m_29 g_29 := by decide +kernel
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
theorem kn_29 : KnownBin bds_29 := by
  intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_13
theorem sub_29 : ∀ b ∈ bds_29, m_29 &&& b.1 = b.1 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_29 : ∀ b ∈ bds_29, canon b.1 g_29 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_29 : Nat → List (Nat × Nat) := fun _ => []
def f_29 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV4 m_29 g_29 ep_29 0 bds_29 (dagTraceF m_29 s_29 4 f_29) (cur_29 0) s_29 4 = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_29 g_29 ep_29 bds_29 0 (dagTraceF m_29 s_29 4 f_29) cur_29 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_29 : LowerBin m_29 s_29 g_29 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_29 kn_29 sub_29 gl_29 rc_29 nc_29

def m_30 : Nat := 0x5555555500000000
def s_30 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_30 : Nat := 0x115155500000000
def ep_30 : Nat := 0x1440000000000014004000000000010404000000000001101000000000000000000000000000
theorem epk_30 : ep_30 = edgePack m_30 g_30 := by decide +kernel
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1), (m_17, s_17, 4, g_17), (m_6, s_6, 4, g_6), (m_7, s_7, 4, g_7)]
theorem kn_30 : KnownBin bds_30 := by
  intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_1
  · exact lb_17
  · exact lb_6
  · exact lb_7
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

def m_31 : Nat := 0x3030303030303030
def s_31 : List Nat := [0x1010101010101010, 0x30003000300030, 0x303000003030, 0x30303030]
def g_31 : Nat := 0x10101010301030
def ep_31 : Nat := 0x1020002000001000000000000010000000200020000000000000000000000000000000000010101010001000
theorem epk_31 : ep_31 = edgePack m_31 g_31 := by decide +kernel
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16)]
theorem kn_31 : KnownBin bds_31 := by
  intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_16
theorem sub_31 : ∀ b ∈ bds_31, m_31 &&& b.1 = b.1 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_31 : ∀ b ∈ bds_31, canon b.1 g_31 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_31 : Nat → List (Nat × Nat) := fun _ => []
def f_31 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV4 m_31 g_31 ep_31 0 bds_31 (dagTraceF m_31 s_31 4 f_31) (cur_31 0) s_31 4 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_31 g_31 ep_31 bds_31 0 (dagTraceF m_31 s_31 4 f_31) cur_31 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_31 kn_31 sub_31 gl_31 rc_31 nc_31

def m_32 : Nat := 0xcccc0000cccc
def s_32 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_32 : Nat := 0x4440000044c
def ep_32 : Nat := 0x800000000000000000000004000000048000004000000040800000000000000000000044400000440
theorem epk_32 : ep_32 = edgePack m_32 g_32 := by decide +kernel
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_20, s_20, 4, g_20)]
theorem kn_32 : KnownBin bds_32 := by
  intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_20
theorem sub_32 : ∀ b ∈ bds_32, m_32 &&& b.1 = b.1 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_32 : ∀ b ∈ bds_32, canon b.1 g_32 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_32 : Nat → List (Nat × Nat) := fun _ => []
def f_32 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV4 m_32 g_32 ep_32 0 bds_32 (dagTraceF m_32 s_32 4 f_32) (cur_32 0) s_32 4 = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_32 g_32 ep_32 bds_32 0 (dagTraceF m_32 s_32 4 f_32) cur_32 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_32 : LowerBin m_32 s_32 g_32 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_32 kn_32 sub_32 gl_32 rc_32 nc_32

def m_33 : Nat := 0x3333000033330000
def s_33 : List Nat := [0x1111000011110000, 0x303000003030000, 0x33000000330000, 0x33330000]
def g_33 : Nat := 0x113000013330000
def ep_33 : Nat := 0x1220000000000000000000000012000000200000010200000200000000000000000000000110000010000000
theorem epk_33 : ep_33 = edgePack m_33 g_33 := by decide +kernel
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11), (m_18, s_18, 4, g_18), (m_16, s_16, 4, g_16), (m_15, s_15, 4, g_15)]
theorem kn_33 : KnownBin bds_33 := by
  intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_11
  · exact lb_18
  · exact lb_16
  · exact lb_15
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

def m_34 : Nat := 0xaaaa0000aaaa0000
def s_34 : List Nat := [0x2222000022220000, 0xa0a00000a0a0000, 0xaa000000aa0000, 0xaaaa0000]
def g_34 : Nat := 0x2000002220000
def ep_34 : Nat := 0x220000000000000000000000002000000200000000200000200000000020000022200000000000000000000
theorem epk_34 : ep_34 = edgePack m_34 g_34 := by decide +kernel
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
theorem kn_34 : KnownBin bds_34 := by
  intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_15
theorem sub_34 : ∀ b ∈ bds_34, m_34 &&& b.1 = b.1 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_34 : ∀ b ∈ bds_34, canon b.1 g_34 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_34 : Nat → List (Nat × Nat) := fun _ => []
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV4 m_34 g_34 ep_34 0 bds_34 (dagTraceF m_34 s_34 4 f_34) (cur_34 0) s_34 4 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_34 g_34 ep_34 bds_34 0 (dagTraceF m_34 s_34 4 f_34) cur_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_34 kn_34 sub_34 gl_34 rc_34 nc_34

def m_35 : Nat := 0xff000000ff
def s_35 : List Nat := [0x5500000055, 0x3300000033, 0xf0000000f, 0xff]
def g_35 : Nat := 0x570000007f
def ep_35 : Nat := 0x2800000000000000000000000000000000000000020000000800000002000000200000005400000040
theorem epk_35 : ep_35 = edgePack m_35 g_35 := by decide +kernel
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
theorem kn_35 : KnownBin bds_35 := by
  intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_13
theorem sub_35 : ∀ b ∈ bds_35, m_35 &&& b.1 = b.1 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_35 : ∀ b ∈ bds_35, canon b.1 g_35 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_35 : Nat → List (Nat × Nat) := fun _ => []
def f_35 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV4 m_35 g_35 ep_35 0 bds_35 (dagTraceF m_35 s_35 4 f_35) (cur_35 0) s_35 4 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_35 g_35 ep_35 bds_35 0 (dagTraceF m_35 s_35 4 f_35) cur_35 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_35 : LowerBin m_35 s_35 g_35 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_35 kn_35 sub_35 gl_35 rc_35 nc_35

def m_36 : Nat := 0xf0f00000f0f0
def s_36 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_36 : Nat := 0x105000001070
def ep_36 : Nat := 0x2000000000000000000000004000000060000000000000000000001000000010200000105000001040
theorem epk_36 : ep_36 = edgePack m_36 g_36 := by decide +kernel
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
theorem kn_36 : KnownBin bds_36 := by
  intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_5
theorem sub_36 : ∀ b ∈ bds_36, m_36 &&& b.1 = b.1 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_36 : ∀ b ∈ bds_36, canon b.1 g_36 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_36 : Nat → List (Nat × Nat) := fun _ => []
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV4 m_36 g_36 ep_36 0 bds_36 (dagTraceF m_36 s_36 4 f_36) (cur_36 0) s_36 4 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_36 g_36 ep_36 bds_36 0 (dagTraceF m_36 s_36 4 f_36) cur_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_36 kn_36 sub_36 gl_36 rc_36 nc_36

def m_37 : Nat := 0xaaaa0000aaaa
def s_37 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_37 : Nat := 0x2020000022a
def ep_37 : Nat := 0x2800000000000000000000000000000028000002020000020800000202000002200000000000000000
theorem epk_37 : ep_37 = edgePack m_37 g_37 := by decide +kernel
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
theorem kn_37 : KnownBin bds_37 := by
  intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_13
theorem sub_37 : ∀ b ∈ bds_37, m_37 &&& b.1 = b.1 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_37 : ∀ b ∈ bds_37, canon b.1 g_37 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_37 : Nat → List (Nat × Nat) := fun _ => []
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV4 m_37 g_37 ep_37 0 bds_37 (dagTraceF m_37 s_37 4 f_37) (cur_37 0) s_37 4 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_37 g_37 ep_37 bds_37 0 (dagTraceF m_37 s_37 4 f_37) cur_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_37 kn_37 sub_37 gl_37 rc_37 nc_37

def m_38 : Nat := 0xcc00cc00cc00cc
def s_38 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_38 : Nat := 0x400440004004c
def ep_38 : Nat := 0x800000040000000480000000000000000000400000004000800000000000000000004004400040040
theorem epk_38 : ep_38 = edgePack m_38 g_38 := by decide +kernel
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_21, s_21, 4, g_21)]
theorem kn_38 : KnownBin bds_38 := by
  intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_21
theorem sub_38 : ∀ b ∈ bds_38, m_38 &&& b.1 = b.1 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_38 : ∀ b ∈ bds_38, canon b.1 g_38 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV4 m_38 g_38 ep_38 0 bds_38 (dagTraceF m_38 s_38 4 f_38) (cur_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_38 g_38 ep_38 bds_38 0 (dagTraceF m_38 s_38 4 f_38) cur_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_38 kn_38 sub_38 gl_38 rc_38 nc_38

def m_39 : Nat := 0xffff
def s_39 : List Nat := [0x5555, 0x3333, 0xf0f, 0xff]
def g_39 : Nat := 0x177f
def ep_39 : Nat := 0x68000000000000060800000000000012200000000000001440
theorem epk_39 : ep_39 = edgePack m_39 g_39 := by decide +kernel
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_5, s_5, 4, g_5), (m_20, s_20, 4, g_20), (m_19, s_19, 4, g_19)]
theorem kn_39 : KnownBin bds_39 := by
  intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_0
  · exact lb_5
  · exact lb_20
  · exact lb_19
theorem sub_39 : ∀ b ∈ bds_39, m_39 &&& b.1 = b.1 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_39 : ∀ b ∈ bds_39, canon b.1 g_39 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_39_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xf64f60c97c80c42c40c02a10a00a009c29829809429218a46b06a06a06626606606225e25a25815044e1464270032001 0x59003c6015407c9a07d3a36950b460fa10592a048c0e3e071e83529e28c153e069e854b81a520d22069083481d07a40350a16a2094183a30150b18200901a6028146d2685925448a16410f1eb48d5929a0d492ca2835043a7ac1350e27070f8f04c201654a6035003c6080340690060502a4016400f180550102681f4e59a528d183e84164a4d23244f41a7241350698854b5124a78460a1f050b8202c624c0b2012d203e801d30141a0548030480c2006a0074c0188028340608034c02a400c300c1207938d4945a460f21058f8a47442360b1903528728c0d3a189b08118206c0c2e060f078fc2c7742370b19874fc1a7721370699854bc1a56e1270691870fd706e142f38138307c102e000f 12 4095 5 31 10 1023 17 131071
def cc_39_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe81d023bc607c8f808b90020038432003 0x2e9c174d0f27059343c7c16390b19058c42c61514d06a4c25141a821d3d989a854b6024b484d5022870f5a06a142d4c1283d002c600d407c9203d381e9b3a4d0b24c29142c821e3d991a875381a9a1d3e069c834c81a620d3006953c49a509a58450e1eb00d4183a38158826039003c600d407c9a038c01a601520 11 2047 5 31 10 1023 17 131071
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

def m_40 : Nat := 0xff00ff
def s_40 : List Nat := [0x550055, 0x330033, 0xf000f, 0xff]
def g_40 : Nat := 0x37007f
def ep_40 : Nat := 0x480000000000000000000000000004000800000000003200200000000000040040
theorem epk_40 : ep_40 = edgePack m_40 g_40 := by decide +kernel
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_21, s_21, 4, g_21)]
theorem kn_40 : KnownBin bds_40 := by
  intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_21
theorem sub_40 : ∀ b ∈ bds_40, m_40 &&& b.1 = b.1 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_40 : ∀ b ∈ bds_40, canon b.1 g_40 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_40 : Nat → List (Nat × Nat) := fun _ => []
def f_40 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV4 m_40 g_40 ep_40 0 bds_40 (dagTraceF m_40 s_40 4 f_40) (cur_40 0) s_40 4 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_40 g_40 ep_40 bds_40 0 (dagTraceF m_40 s_40 4 f_40) cur_40 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_40 : LowerBin m_40 s_40 g_40 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_40 kn_40 sub_40 gl_40 rc_40 nc_40

def m_41 : Nat := 0xf0f0f0f0
def s_41 : List Nat := [0x50505050, 0x30303030, 0xf000f0, 0xf0f0]
def g_41 : Nat := 0x10301070
def ep_41 : Nat := 0x400000000000200060000000000000000000000000103010200000000010001040
theorem epk_41 : ep_41 = edgePack m_41 g_41 := by decide +kernel
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
theorem kn_41 : KnownBin bds_41 := by
  intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_5
theorem sub_41 : ∀ b ∈ bds_41, m_41 &&& b.1 = b.1 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_41 : ∀ b ∈ bds_41, canon b.1 g_41 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV4 m_41 g_41 ep_41 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_41 g_41 ep_41 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_41 kn_41 sub_41 gl_41 rc_41 nc_41

def m_42 : Nat := 0xcccccccc
def s_42 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_42 : Nat := 0x404044c
def ep_42 : Nat := 0x480000000000000048000000000404040800000000000000000000000004040440
theorem epk_42 : ep_42 = edgePack m_42 g_42 := by decide +kernel
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_20, s_20, 4, g_20)]
theorem kn_42 : KnownBin bds_42 := by
  intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_20
theorem sub_42 : ∀ b ∈ bds_42, m_42 &&& b.1 = b.1 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_42 : ∀ b ∈ bds_42, canon b.1 g_42 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_42 : Nat → List (Nat × Nat) := fun _ => []
def f_42 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV4 m_42 g_42 ep_42 0 bds_42 (dagTraceF m_42 s_42 4 f_42) (cur_42 0) s_42 4 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_42 g_42 ep_42 bds_42 0 (dagTraceF m_42 s_42 4 f_42) cur_42 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_42 kn_42 sub_42 gl_42 rc_42 nc_42

def m_43 : Nat := 0xaaaaaaaa
def s_43 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_43 : Nat := 0x222022a
def ep_43 : Nat := 0x80000000000200028000000000200020800000000022202200000000000000000
theorem epk_43 : ep_43 = edgePack m_43 g_43 := by decide +kernel
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_19, s_19, 4, g_19)]
theorem kn_43 : KnownBin bds_43 := by
  intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_19
theorem sub_43 : ∀ b ∈ bds_43, m_43 &&& b.1 = b.1 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_43 : ∀ b ∈ bds_43, canon b.1 g_43 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_43 : Nat → List (Nat × Nat) := fun _ => []
def f_43 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV4 m_43 g_43 ep_43 0 bds_43 (dagTraceF m_43 s_43 4 f_43) (cur_43 0) s_43 4 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_43 g_43 ep_43 bds_43 0 (dagTraceF m_43 s_43 4 f_43) cur_43 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_43 : LowerBin m_43 s_43 g_43 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_43 kn_43 sub_43 gl_43 rc_43 nc_43

def m_44 : Nat := 0xff000000ff000000
def s_44 : List Nat := [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000]
def g_44 : Nat := 0x100000017000000
def ep_44 : Nat := 0x1600000000000000000000000000000000000000010000000600000001000000120000000100000014000000
theorem epk_44 : ep_44 = edgePack m_44 g_44 := by decide +kernel
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12), (m_9, s_9, 4, g_9), (m_10, s_10, 4, g_10), (m_11, s_11, 4, g_11)]
theorem kn_44 : KnownBin bds_44 := by
  intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_12
  · exact lb_9
  · exact lb_10
  · exact lb_11
theorem sub_44 : ∀ b ∈ bds_44, m_44 &&& b.1 = b.1 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_44 : ∀ b ∈ bds_44, canon b.1 g_44 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_44_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_44_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_44 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_44_1 (Nat.sub p 32)) (cc_44_0 p) (Nat.blt p 32)
def f_44 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV4 m_44 g_44 ep_44 43 bds_44 (dagTraceF m_44 s_44 6 f_44) (cur_44 0) s_44 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_0 : treeBlockF 0 32 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 43 (dagTraceF m_44 s_44 6 f_44) cur_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_1 : treeBlockF 32 43 (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 43 (dagTraceF m_44 s_44 6 f_44) cur_44) = true := by decide +kernel
theorem nj_44_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 43 (dagTraceF m_44 s_44 6 f_44) cur_44) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_44_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_44_1 h1 h2)
theorem nc_44 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeV4 m_44 g_44 ep_44 bds_44 43 (dagTraceF m_44 s_44 6 f_44) cur_44) i = true := nj_44_1
theorem lb_44 : LowerBin m_44 s_44 g_44 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_44 kn_44 sub_44 gl_44 rc_44 nc_44

def m_45 : Nat := 0xff000000ff0000
def s_45 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_45 : Nat := 0x17000000370000
def ep_45 : Nat := 0x20000000000000000000000000000000000000000600000004000000120000003200000014000000040000
theorem epk_45 : ep_45 = edgePack m_45 g_45 := by decide +kernel
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
theorem kn_45 : KnownBin bds_45 := by
  intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_8
theorem sub_45 : ∀ b ∈ bds_45, m_45 &&& b.1 = b.1 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_45 : ∀ b ∈ bds_45, canon b.1 g_45 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_45 : Nat → List (Nat × Nat) := fun _ => []
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV4 m_45 g_45 ep_45 0 bds_45 (dagTraceF m_45 s_45 4 f_45) (cur_45 0) s_45 4 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_45 g_45 ep_45 bds_45 0 (dagTraceF m_45 s_45 4 f_45) cur_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin m_45 s_45 g_45 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_45 kn_45 sub_45 gl_45 rc_45 nc_45

def m_46 : Nat := 0xf000f000f000f0
def s_46 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_46 : Nat := 0x10005000300070
def ep_46 : Nat := 0x20002000000040000000400000000000000000000000000000000000100000003000200010005000000040
theorem epk_46 : ep_46 = edgePack m_46 g_46 := by decide +kernel
def bds_46 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_46 : KnownBin bds_46 := by intro b hb; simp [bds_46] at hb
theorem sub_46 : ∀ b ∈ bds_46, m_46 &&& b.1 = b.1 := by intro b hb; simp [bds_46] at hb
theorem gl_46 : ∀ b ∈ bds_46, canon b.1 g_46 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_46] at hb
def cur_46 : Nat → List (Nat × Nat) := unpackCursorV4 0x9 0xf 2 3 1 1 4 15 5 31
def f_46 : Nat → Nat × Nat := unpackForestF 0xf 1 4
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV4 m_46 g_46 ep_46 1 bds_46 (dagTraceF m_46 s_46 3 f_46) (cur_46 0) s_46 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46 : treeBlockF 0 1 (dagCheckNodeV4 m_46 g_46 ep_46 bds_46 1 (dagTraceF m_46 s_46 3 f_46) cur_46) = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 1 → (dagCheckNodeV4 m_46 g_46 ep_46 bds_46 1 (dagTraceF m_46 s_46 3 f_46) cur_46) i = true := fun _ h1 h2 => treeBlockF_at nb_46 h1 h2
theorem lb_46 : LowerBin m_46 s_46 g_46 4 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_46 kn_46 sub_46 gl_46 rc_46 nc_46

def m_47 : Nat := 0xf0f00000f0f00000
def s_47 : List Nat := [0x5050000050500000, 0x3030000030300000, 0xf0000000f00000, 0xf0f00000]
def g_47 : Nat := 0x10000010300000
def ep_47 : Nat := 0x1020000000000000000000000010000000200000000000000000000000100000103000000010000010000000
theorem epk_47 : ep_47 = edgePack m_47 g_47 := by decide +kernel
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16)]
theorem kn_47 : KnownBin bds_47 := by
  intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_16
theorem sub_47 : ∀ b ∈ bds_47, m_47 &&& b.1 = b.1 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_47 : ∀ b ∈ bds_47, canon b.1 g_47 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_47 : Nat → List (Nat × Nat) := fun _ => []
def f_47 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV4 m_47 g_47 ep_47 0 bds_47 (dagTraceF m_47 s_47 4 f_47) (cur_47 0) s_47 4 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_47 g_47 ep_47 bds_47 0 (dagTraceF m_47 s_47 4 f_47) cur_47 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_47 : LowerBin m_47 s_47 g_47 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_47 kn_47 sub_47 gl_47 rc_47 nc_47

def m_48 : Nat := 0x4444444444444444
def s_48 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_48 : Nat := 0x4044404040444
def ep_48 : Nat := 0x400000000000440000000400004004000000040000404000404040000000000000000000000000000000000
theorem epk_48 : ep_48 = edgePack m_48 g_48 := by decide +kernel
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
theorem kn_48 : KnownBin bds_48 := by
  intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_7
theorem sub_48 : ∀ b ∈ bds_48, m_48 &&& b.1 = b.1 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_48 : ∀ b ∈ bds_48, canon b.1 g_48 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_48 : Nat → List (Nat × Nat) := fun _ => []
def f_48 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV4 m_48 g_48 ep_48 0 bds_48 (dagTraceF m_48 s_48 4 f_48) (cur_48 0) s_48 4 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_48 g_48 ep_48 bds_48 0 (dagTraceF m_48 s_48 4 f_48) cur_48 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_48 : LowerBin m_48 s_48 g_48 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_48 kn_48 sub_48 gl_48 rc_48 nc_48

def m_49 : Nat := 0x2222222222222222
def s_49 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_49 : Nat := 0x2020202220222
def ep_49 : Nat := 0x220002000000200000000000002000000200020000202020200020000000000000000000000000000000000
theorem epk_49 : ep_49 = edgePack m_49 g_49 := by decide +kernel
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
theorem kn_49 : KnownBin bds_49 := by
  intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_15
theorem sub_49 : ∀ b ∈ bds_49, m_49 &&& b.1 = b.1 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_49 : ∀ b ∈ bds_49, canon b.1 g_49 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_49 : Nat → List (Nat × Nat) := fun _ => []
def f_49 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV4 m_49 g_49 ep_49 0 bds_49 (dagTraceF m_49 s_49 4 f_49) (cur_49 0) s_49 4 = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_49 g_49 ep_49 bds_49 0 (dagTraceF m_49 s_49 4 f_49) cur_49 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_49 : LowerBin m_49 s_49 g_49 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_49 kn_49 sub_49 gl_49 rc_49 nc_49

def m_50 : Nat := 0xa0a0a0a0a0a0a0a
def s_50 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_50 : Nat := 0x202020202020a
def ep_50 : Nat := 0x200000800000200000000080002000000000008000000000000000000020202020202000000000000000000
theorem epk_50 : ep_50 = edgePack m_50 g_50 := by decide +kernel
def bds_50 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_50 : KnownBin bds_50 := by intro b hb; simp [bds_50] at hb
theorem sub_50 : ∀ b ∈ bds_50, m_50 &&& b.1 = b.1 := by intro b hb; simp [bds_50] at hb
theorem gl_50 : ∀ b ∈ bds_50, canon b.1 g_50 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_50] at hb
def cc_50_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0xe24c6d20345319280b83c581a2a0b14048912844921e0b0e04858202c9a124f08268303c141a040402249fa3ff91df28df4467993fc89dda4de8267292f8895c249df246f03f741db00dd3066802f34159809ca046381f100d8605c1026000f 11 2047 5 31 10 1023 17 131071
def cc_50_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0x3d299e140ec26741038251b924d8146a09314998240bc265c102c2795934a80c5205270513024900c4605202410234 8 255 3 7 10 1023 17 131071
def cur_50 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_50_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_50_0 p) (Nat.blt p 32)
def f_50 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV4 m_50 g_50 ep_50 64 bds_50 (dagTraceF m_50 s_50 5 f_50) (cur_50 0) s_50 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_0 : treeBlockF 0 32 (dagCheckNodeV4 m_50 g_50 ep_50 bds_50 64 (dagTraceF m_50 s_50 5 f_50) cur_50) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_1 : treeBlockF 32 64 (dagCheckNodeV4 m_50 g_50 ep_50 bds_50 64 (dagTraceF m_50 s_50 5 f_50) cur_50) = true := by decide +kernel
theorem nj_50_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_50 g_50 ep_50 bds_50 64 (dagTraceF m_50 s_50 5 f_50) cur_50) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_50_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_50_1 h1 h2)
theorem nc_50 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_50 g_50 ep_50 bds_50 64 (dagTraceF m_50 s_50 5 f_50) cur_50) i = true := nj_50_1
theorem lb_50 : LowerBin m_50 s_50 g_50 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_50 kn_50 sub_50 gl_50 rc_50 nc_50

def m_51 : Nat := 0xc0c0c0c0c0c0c0c
def s_51 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_51 : Nat := 0x404040404040c
def ep_51 : Nat := 0x400000800000400000000080004000000000008000000000000000000000000000000000004040404040400
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

def m_52 : Nat := 0x4488448844884488
def s_52 : List Nat := [0x88008800880088, 0x408040804080408, 0x448800004488, 0x44884488]
def g_52 : Nat := 0x40004000408
def ep_52 : Nat := 0x400000800000400000000080000000000000000000004000400040800000000000000000000000000000000
theorem epk_52 : ep_52 = edgePack m_52 g_52 := by decide +kernel
def bds_52 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_52 : KnownBin bds_52 := by intro b hb; simp [bds_52] at hb
theorem sub_52 : ∀ b ∈ bds_52, m_52 &&& b.1 = b.1 := by intro b hb; simp [bds_52] at hb
theorem gl_52 : ∀ b ∈ bds_52, canon b.1 g_52 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_52] at hb
def cur_52 : Nat → List (Nat × Nat) := unpackCursorV4 0x16ac58b12a44890e8701 0x31303060c8f08181a3c226128fa119393e526480f8419000f 7 127 3 7 10 1023 15 32767
def f_52 : Nat → Nat × Nat := unpackForestF 0xc7c63229f68f0a6443e51e24c086400f 3 10
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV4 m_52 g_52 ep_52 10 bds_52 (dagTraceF m_52 s_52 4 f_52) (cur_52 0) s_52 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52 : treeBlockF 0 10 (dagCheckNodeV4 m_52 g_52 ep_52 bds_52 10 (dagTraceF m_52 s_52 4 f_52) cur_52) = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 10 → (dagCheckNodeV4 m_52 g_52 ep_52 bds_52 10 (dagTraceF m_52 s_52 4 f_52) cur_52) i = true := fun _ h1 h2 => treeBlockF_at nb_52 h1 h2
theorem lb_52 : LowerBin m_52 s_52 g_52 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_52 kn_52 sub_52 gl_52 rc_52 nc_52

def m_53 : Nat := 0xaaaaaaaaaaaaaaaa
def s_53 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_53 : Nat := 0x202020222022a
def ep_53 : Nat := 0x220002800000200000000080002000000200028000202020200020800020202022202200000000000000000
theorem epk_53 : ep_53 = edgePack m_53 g_53 := by decide +kernel
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_50, s_50, 6, g_50), (m_43, s_43, 5, g_43), (m_29, s_29, 5, g_29), (m_37, s_37, 5, g_37), (m_34, s_34, 5, g_34), (m_22, s_22, 5, g_22), (m_49, s_49, 5, g_49), (m_19, s_19, 4, g_19), (m_15, s_15, 4, g_15)]
theorem kn_53 : KnownBin bds_53 := by
  intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_50
  · exact lb_43
  · exact lb_29
  · exact lb_37
  · exact lb_34
  · exact lb_22
  · exact lb_49
  · exact lb_19
  · exact lb_15
theorem sub_53 : ∀ b ∈ bds_53, m_53 &&& b.1 = b.1 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_53 : ∀ b ∈ bds_53, canon b.1 g_53 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_53 : Nat → List (Nat × Nat) := unpackCursorV4 0xd00a18a007186a3643640339038001 0x2ebabd68bab17552cbc5974b1f2e3d2a7294c4e96ad2a4a5294a16931d253a489484a1ca031185b00a4612ac211abad5686ab0d551a7c64c8697252218bc317581f143a286cb0c9217442d485870a8e133c253848908860f341d3c6834d061a15343a485050baf23523c7a58d46af19521a7a54e869b0d351a6874a8693105e68b4d1596290c3e187a90b8e151c2648443078a0e964f6c96591dd219d4f4a96751d2a19d2f2a56549d2918c4f6896311d4218c2f2856309c4118c1f3836305d209801f 12 4095 5 31 10 1023 15 32767
def f_53 : Nat → Nat × Nat := unpackForestF 0x2029190d83e110cb52254885e108c01f 4 10
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV4 m_53 g_53 ep_53 9 bds_53 (dagTraceF m_53 s_53 7 f_53) (cur_53 0) s_53 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53 : treeBlockF 0 9 (dagCheckNodeV4 m_53 g_53 ep_53 bds_53 9 (dagTraceF m_53 s_53 7 f_53) cur_53) = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 9 → (dagCheckNodeV4 m_53 g_53 ep_53 bds_53 9 (dagTraceF m_53 s_53 7 f_53) cur_53) i = true := fun _ h1 h2 => treeBlockF_at nb_53 h1 h2
theorem lb_53 : LowerBin m_53 s_53 g_53 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_53 kn_53 sub_53 gl_53 rc_53 nc_53

def m_54 : Nat := 0xff00ff00ff00ff00
def s_54 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_54 : Nat := 0x100170017001700
def ep_54 : Nat := 0x1600000000001600000000000000000000000000010006000600060001001200120012000100140014001400
theorem epk_54 : ep_54 = edgePack m_54 g_54 := by decide +kernel
def bds_54 : List (Nat × List Nat × Nat × Nat) := [(m_24, s_24, 7, g_24)]
theorem kn_54 : KnownBin bds_54 := by
  intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_24
theorem sub_54 : ∀ b ∈ bds_54, m_54 &&& b.1 = b.1 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_54 : ∀ b ∈ bds_54, canon b.1 g_54 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_54 : Nat → List (Nat × Nat) := fun _ => []
def f_54 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV4 m_54 g_54 ep_54 0 bds_54 (dagTraceF m_54 s_54 7 f_54) (cur_54 0) s_54 7 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_54 g_54 ep_54 bds_54 0 (dagTraceF m_54 s_54 7 f_54) cur_54 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_54 : LowerBin m_54 s_54 g_54 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_54 kn_54 sub_54 gl_54 rc_54 nc_54

def m_55 : Nat := 0xf0f0f0f0f0f0f0f0
def s_55 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_55 : Nat := 0x10105010301070
def ep_55 : Nat := 0x1020002000001040000000400010004000200060000000000000000000101000103010200010105010001040
theorem epk_55 : ep_55 = edgePack m_55 g_55 := by decide +kernel
def bds_55 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6), (m_47, s_47, 5, g_47), (m_31, s_31, 5, g_31), (m_36, s_36, 5, g_36), (m_41, s_41, 5, g_41), (m_46, s_46, 4, g_46), (m_16, s_16, 4, g_16), (m_5, s_5, 4, g_5)]
theorem kn_55 : KnownBin bds_55 := by
  intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_6
  · exact lb_47
  · exact lb_31
  · exact lb_36
  · exact lb_41
  · exact lb_46
  · exact lb_16
  · exact lb_5
theorem sub_55 : ∀ b ∈ bds_55, m_55 &&& b.1 = b.1 := by intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_55 : ∀ b ∈ bds_55, canon b.1 g_55 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_55 : Nat → List (Nat × Nat) := unpackCursorV4 0x6e03321942bd6dd8ae83740aa85486a412388f147823c11c18c1448e202d5e6a03501a04b4e4a825012809022af0eb4078001 0x162e8ad7724a22a499120968f7a4725a35691886544d2a0393d0c9c8e4d43262284e0c9c0e4d0b8ba2b4dd9a48ad14b6825a512d1f448c8729a19491ca286504a07d03501522120f328a25b5da1a73cd08b4bb824e15250a919a484392d0c948e4943242304eb813120909089535e2da90ad38b69a5a5ea1290a92854922a462d208a8d8546aa15e34a90e4f4327239350c98864a43242284e1421120f4906b035034a841140729819400c940e4909048192c162f4914a26bcf3522da68ad28568c2b45712f34948549c5a4d151f0a8f502bc69520c9c864c4725a692a0c94864a1824c39251c9206484509c2842241692094729891440da68a8fc74762a371d198e4fc727639371c99a84bc5256292740919e0b8d6826a3f151d8a8dcd466194d0c9f864ec326e19330c97864ac324e1923341f060589278413415a78ad0c949e4a4328a78c50c527e293b149b8a4cc925e492b24939248c709e784e0c219a108507e183b141b860cc705e182b1c138608c703e181b1c0b8604c547e2a3b151b8a8cc527e193b149b864cc725e192b1c938648c507c2b4fe1a1e893ec487323f151d8a8dd6466394f38a70650cc284393f0c9d8a4dc3266392f0c958e49c3246483f101f0a0dc2064482f24138607c702e001f 13 8191 5 31 11 2047 17 131071
def f_55 : Nat → Nat × Nat := unpackForestF 0xea390b43db490a4fbc51ba4eb8260a43a35ea2520a3f6452635e84506352625e625261260a33412f49444123094e0942194f21341943083e0832001f 5 11
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV4 m_55 g_55 ep_55 30 bds_55 (dagTraceF m_55 s_55 7 f_55) (cur_55 0) s_55 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55 : treeBlockF 0 30 (dagCheckNodeV4 m_55 g_55 ep_55 bds_55 30 (dagTraceF m_55 s_55 7 f_55) cur_55) = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 30 → (dagCheckNodeV4 m_55 g_55 ep_55 bds_55 30 (dagTraceF m_55 s_55 7 f_55) cur_55) i = true := fun _ h1 h2 => treeBlockF_at nb_55 h1 h2
theorem lb_55 : LowerBin m_55 s_55 g_55 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_55 kn_55 sub_55 gl_55 rc_55 nc_55

def m_56 : Nat := 0xcccccccccccccccc
def s_56 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_56 : Nat := 0x404440404044c
def ep_56 : Nat := 0x400000800000440000000480004004000000048000404000404040800000000000000000004044404040440
theorem epk_56 : ep_56 = edgePack m_56 g_56 := by decide +kernel
def bds_56 : List (Nat × List Nat × Nat × Nat) := [(m_51, s_51, 6, g_51), (m_32, s_32, 5, g_32), (m_42, s_42, 5, g_42), (m_38, s_38, 5, g_38), (m_28, s_28, 5, g_28), (m_52, s_52, 5, g_52), (m_48, s_48, 5, g_48), (m_20, s_20, 4, g_20), (m_7, s_7, 4, g_7)]
theorem kn_56 : KnownBin bds_56 := by
  intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_51
  · exact lb_32
  · exact lb_42
  · exact lb_38
  · exact lb_28
  · exact lb_52
  · exact lb_48
  · exact lb_20
  · exact lb_7
theorem sub_56 : ∀ b ∈ bds_56, m_56 &&& b.1 = b.1 := by intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_56 : ∀ b ∈ bds_56, canon b.1 g_56 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_56 : Nat → List (Nat × Nat) := unpackCursorV4 0xd00a18a007186a3643640339038001 0x3ebabd68fab1f553cbc7974f1f2e3d3a7284c4696c1291a4ab484e1ca431285ab0a9214a428584c5094a1224211cbad96872b0e551c7c68c86af0d5d627c74e8e9b2d321a5cd4b4614a421283b106920ca418782c5054a0a24111c6834d0a1a1e343a485090faf23521cbc694871e9e3a1c6c38d471a115e6ab4d5596a90d3e1a7a34b8e96943d286a50b4612941d483250552089e4f6c96791dd218d4f6a96351d4a18d2f3a56349c491944f4896511d221942f3856509d211941f1836305d209801f 12 4095 5 31 10 1023 15 32767
def f_56 : Nat → Nat × Nat := unpackForestF 0x2129190d93e150cb52294895e148c01f 4 10
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV4 m_56 g_56 ep_56 9 bds_56 (dagTraceF m_56 s_56 7 f_56) (cur_56 0) s_56 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56 : treeBlockF 0 9 (dagCheckNodeV4 m_56 g_56 ep_56 bds_56 9 (dagTraceF m_56 s_56 7 f_56) cur_56) = true := by decide +kernel
theorem nc_56 : ∀ i, 0 ≤ i → i < 9 → (dagCheckNodeV4 m_56 g_56 ep_56 bds_56 9 (dagTraceF m_56 s_56 7 f_56) cur_56) i = true := fun _ h1 h2 => treeBlockF_at nb_56 h1 h2
theorem lb_56 : LowerBin m_56 s_56 g_56 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_56 kn_56 sub_56 gl_56 rc_56 nc_56

def m_57 : Nat := 0xff00ff00ff00ff
def s_57 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_57 : Nat := 0x1700570037007f
def ep_57 : Nat := 0x20002800000040000000480000000000000000000600020004000800120002003200200014005400040040
theorem epk_57 : ep_57 = edgePack m_57 g_57 := by decide +kernel
def bds_57 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13), (m_21, s_21, 4, g_21), (m_40, s_40, 5, g_40), (m_26, s_26, 5, g_26), (m_45, s_45, 5, g_45), (m_46, s_46, 4, g_46), (m_8, s_8, 4, g_8)]
theorem kn_57 : KnownBin bds_57 := by
  intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_13
  · exact lb_21
  · exact lb_40
  · exact lb_26
  · exact lb_45
  · exact lb_46
  · exact lb_8
theorem sub_57 : ∀ b ∈ bds_57, m_57 &&& b.1 = b.1 := by intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_57 : ∀ b ∈ bds_57, canon b.1 g_57 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_57 : Nat → List (Nat × Nat) := unpackCursorV4 0x6e03321942bd6de06e85740aa85502a432388f1460e2851408a04486202d5e6a03501a0495e3d69e80f407622d70ec0078001 0xe2f06d27a4ba5a59892a96947048a1a3d811a864e830ba18590c2a86144308a18440c260e100b6aa5b4a79a316954349c5a4ad923069094294182d1c1486094704249400e28388d0b8bd935d0dacc4d5436a383452d24d48e9a46d715224a8204e830ba38590c2a8e14492a05b5aa9ab06d38369a5b450da11696a84ac1a462d22868f8347a194a0ca3124a49242505a0c2b060f4306a182d0c14860943042183c1c181254030b83850712206111c488184c922d4515836b503562da706d35e4b4d2560d2706934347c5a390d19068c4929249410c9d064d860b418560c2706134309818490c22b0108308238400c168609522b849500da586d1d449682470d1f868ec346e1a3324a59251c925e492b24939248c3096684a0c2386118307e183b0c1b860cc305e182b0c138608c303e181b0c0b8604c347a192f0c958649c3246182f0c158609c3046181f0c0d8605c3026404c1c20068fca47632370d199a4e8308a183f1c1d8e0dc3066382f1c158e09c70461b4e0d278692c348e1a430d1a8653c329619470ca1864bc325619270c918610830541b4be1a3e892ec48e1a3f991dac8dc3466493b389d184d83266492b24918e12c409418470823060fc307618370c19860bc705618271c118607c7026001f 13 8191 5 31 11 2047 17 131071
def f_57 : Nat → Nat × Nat := unpackForestF 0xea5d0b47da460a4bbb5dbb45b9520a47a356a2560a3b645a64566356625a7244625660420a37424b495c4247093a09361a3b204c1a37084a0846001f 5 11
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV4 m_57 g_57 ep_57 30 bds_57 (dagTraceF m_57 s_57 7 f_57) (cur_57 0) s_57 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57 : treeBlockF 0 30 (dagCheckNodeV4 m_57 g_57 ep_57 bds_57 30 (dagTraceF m_57 s_57 7 f_57) cur_57) = true := by decide +kernel
theorem nc_57 : ∀ i, 0 ≤ i → i < 30 → (dagCheckNodeV4 m_57 g_57 ep_57 bds_57 30 (dagTraceF m_57 s_57 7 f_57) cur_57) i = true := fun _ h1 h2 => treeBlockF_at nb_57 h1 h2
theorem lb_57 : LowerBin m_57 s_57 g_57 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_57 kn_57 sub_57 gl_57 rc_57 nc_57

def m_58 : Nat := 0xffffffff
def s_58 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_58 : Nat := 0x1737177f
def ep_58 : Nat := 0x480000000000200068000000000604060800000000123212200000000014041440
theorem epk_58 : ep_58 = edgePack m_58 g_58 := by decide +kernel
def bds_58 : List (Nat × List Nat × Nat × Nat) := [(m_39, s_39, 7, g_39)]
theorem kn_58 : KnownBin bds_58 := by
  intro b hb; simp only [bds_58, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_39
theorem sub_58 : ∀ b ∈ bds_58, m_58 &&& b.1 = b.1 := by intro b hb; simp only [bds_58, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_58 : ∀ b ∈ bds_58, canon b.1 g_58 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_58, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_58 : Nat → List (Nat × Nat) := fun _ => []
def f_58 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV4 m_58 g_58 ep_58 0 bds_58 (dagTraceF m_58 s_58 7 f_58) (cur_58 0) s_58 7 = true := by decide +kernel
theorem nc_58 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_58 g_58 ep_58 bds_58 0 (dagTraceF m_58 s_58 7 f_58) cur_58 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_58 : LowerBin m_58 s_58 g_58 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_58 kn_58 sub_58 gl_58 rc_58 nc_58

def m_59 : Nat := 0xffff0000ffff
def s_59 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_59 : Nat := 0x17570000177f
def ep_59 : Nat := 0x2800000000000000000000004000000068000006020000060800001202000012200000145400001440
theorem epk_59 : ep_59 = edgePack m_59 g_59 := by decide +kernel
def bds_59 : List (Nat × List Nat × Nat × Nat) := [(m_39, s_39, 7, g_39)]
theorem kn_59 : KnownBin bds_59 := by
  intro b hb; simp only [bds_59, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_39
theorem sub_59 : ∀ b ∈ bds_59, m_59 &&& b.1 = b.1 := by intro b hb; simp only [bds_59, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_59 : ∀ b ∈ bds_59, canon b.1 g_59 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_59, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_59 : Nat → List (Nat × Nat) := fun _ => []
def f_59 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_59 : dagCheckRootsV4 m_59 g_59 ep_59 0 bds_59 (dagTraceF m_59 s_59 7 f_59) (cur_59 0) s_59 7 = true := by decide +kernel
theorem nc_59 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_59 g_59 ep_59 bds_59 0 (dagTraceF m_59 s_59 7 f_59) cur_59 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_59 : LowerBin m_59 s_59 g_59 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_59 kn_59 sub_59 gl_59 rc_59 nc_59

def g_60 : Nat := 0x11717571737177f
def ep_60 : Nat := 0x1620002800001640000000480016004000200068010606020604060801121202123212200114145414041440
theorem epk_60 : ep_60 = edgePack fullMask g_60 := by decide +kernel
def bds_60 : List (Nat × List Nat × Nat × Nat) := [(m_33, s_33, 7, g_33), (m_30, s_30, 7, g_30), (m_58, s_58, 8, g_58), (m_54, s_54, 8, g_54), (m_59, s_59, 8, g_59), (m_55, s_55, 8, g_55), (m_57, s_57, 8, g_57), (m_51, s_51, 6, g_51), (m_24, s_24, 7, g_24), (m_39, s_39, 7, g_39), (m_53, s_53, 8, g_53), (m_44, s_44, 7, g_44), (m_56, s_56, 8, g_56), (m_50, s_50, 6, g_50), (m_25, s_25, 7, g_25), (m_13, s_13, 4, g_13), (m_21, s_21, 4, g_21), (m_4, s_4, 4, g_4), (m_32, s_32, 5, g_32), (m_41, s_41, 5, g_41), (m_2, s_2, 4, g_2), (m_12, s_12, 4, g_12), (m_43, s_43, 5, g_43)]
theorem kn_60 : KnownBin bds_60 := by
  intro b hb; simp only [bds_60, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_33
  · exact lb_30
  · exact lb_58
  · exact lb_54
  · exact lb_59
  · exact lb_55
  · exact lb_57
  · exact lb_51
  · exact lb_24
  · exact lb_39
  · exact lb_53
  · exact lb_44
  · exact lb_56
  · exact lb_50
  · exact lb_25
  · exact lb_13
  · exact lb_21
  · exact lb_4
  · exact lb_32
  · exact lb_41
  · exact lb_2
  · exact lb_12
  · exact lb_43
theorem sub_60 : ∀ b ∈ bds_60, fullMask &&& b.1 = b.1 := by intro b hb; simp only [bds_60, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_60 : ∀ b ∈ bds_60, canon b.1 g_60 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_60, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_60_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x9d2419a42e9614390e538937b82a697c76379c2b75e3e7332b6f3406c1326a0216742c614605e62e582645364c4ea4c483673fe8537688313632ac67224881bd67135880ad8805d5003d200013c00001 0x75fc03af601d7700eb98175b4038fc01c7602e2f006dfc036f601b7700db980ed7c076b603b5701da980ed240768a0197f00cbd8065dc032e60195f00cad80655c032a60194900ca28064fc0327a0193b00c9d0064dc0726c0193500c3f8061f8030f60187a00c3b8061d8030e60187200c2f816178030ba0585c00c2d806168030ae0585600c2a81e150030a60185200c248061200308a0784400c1f80a0f80307a0181f00c0f00607403ade01d6e00eb58075a803ace01d6600eb1807588036de01b6b00db3806d8c0f6be07b5d00dad806d64036ae01b5500da9806d44034de01a6b00d3380698c054a602a5101d1f80e8ec0746e03a3300c378061ac030ce0186300c29806148030a20183f00c1d8060dc030660182f00c158060a80304e0382600f3d0079c8038fe01c7b00e3b8071cc198da05c5100dbf806dec036ee01b7301db680ed840769e03b4b01da380ed0c032fe0197b00cbb8065cc032da0296c00cb08065800329e0194b00ca380650c0327e0193d00c9d8064e80326e0393600c9a8061fc030fc0187b00c3d0061dc030ec0187300c390061b43a0d80186100c3000613c0b09c0184d02c2600612c030940184703c230061140f0880184300c210060fc0507c0183d00c0f8060780303a01d6b00eb18071bc038d601c6700e3181717c038a601b6f00db7006dac036d401b6700db3006d8c036c407b5f03daf006d4c036a401b4b00da5006d1c0368c01b4300d378069ac034ce01a6301d2f80e94c0749e03a4b01d2380e90c0747e03a3d0151d80a8e40746e03a3501d1980a8c4032de0196702ca781651c1327e0493d04c9b8124d40725e0392700c378061ac030ce0186300c2f80614c0309e0184b00c2380610c0307e0183d00c1d8060e40306e0183500c198060c40305e0182d00c158060a80304e0382600c1280608c030360181a00c0b82e05803cf601e7300ebf8075ec03aee01d7302eb78175b40baca01c7f00e3f0071ec038f401c7700e3b0071cc038e405c6f066370171b4036fe01b7b00dbb806dcc076de03b6301daf80ed6c076ae03b5301da780ed340769603b4901da380ed140768603b4100d3f8069dc0b4be05a5702d278129340b48e04a4501d1f80e8dc032fe0197b00cbb8065cc032de0196300caf80656c032ae0195300ca7806534032960194900ca3806514032860194100c9f8064f4032760193a00c9b80e4d80326a0192b00c9500649c1724c0187f00c3f0061ec030f40187700c3b0061cc030e40186f03c3700618c030c40185f02c2f00616c030b40185702c2b00614c030a40184f02c270061340b0980184b00c25006124030900184702c23006114360880184300c21006104030800183f0141f0060f4030560182a00c138120980303e0181e00c0e8075bc03ad601d6700eb18071bc038dc01c6b00e3500719c038cc01c6300e3101f17c0f8bc07c5b03e2b81f14c0f8a401b6f00db5806d9c036c607b5f02dad81ed680f6ae07b5602da9806d3c0369c01b4d00d378069ac034ce01a6301d2f80e96c074ae03a5301d2780e9340549602a4901d2380e9140748602a4101d1f80e8ec0747203a3701d1980e8c4032de0196b00cb380658c0f2be0795b03cab81e54c0f29e0494d03ca581e51c0928a0794302c9f81e4ec0f26e0593301c9780e4ac0724e0392300c378061ac030ce0186300c2f80616c030ae0185300c27806134030960184900c23806114030860184100c1f8060ec030720183700c198060c40305e0182b00c1380608c0303e0181b00c0b80604c03ade01d6b00eb380758c038de01c6b00e3380718c3e8be1e45b0e22b86914c036de01b6b00db3806d8c076be03b5b01dab80ed4c0769e03b4b01da380ed0c034de01a6b00d3380698c134be0ba5b04d2b82e94c1349e0ba4b04d2382e90c0747e03a3b01d1b80e8cc032de0196b00cb380658c032be0195b00cab80654c0329e0194b00ca380650c0327e0193d00c9d8064e80326e0393600c9a8064bc032560192a00c9382e498032460186f00c370061ac030d40186700c3300618c030c40185f0642f00616c030ae0185300c2900613c0b09c0184b00c2500611c3208c0184300c210060fc0507c0183d00c178060ac03054018270241300608c0303e0181e00c0e8075bc03adc01b6b00db3806d8c036ae01b5500d378069ac034ce01a6305d2f81a974114b603a5905d2b81a954114a603a5102d1f81e8ec0f46e05a3300c378061ac030ce0186300c2f806174030b60185900c2b806154030a60185100c1f8060ec0306e0183300c178060ac0304e0182300f3f8079f80bcfa01c7b00e3d0071e4038ee01c7600e398171c4038ce01c6600e32806dfc036f601b7700db981edbc0d6da08b6b01db482ad9c0d6ca07b6301db0816d3c0f69607b4702da18228f8032fc0197603cb701e5b0152cc1716402ca701e5180727c0693600c3f8061ec030ee0187300c378061b4030d60186900c33806194030c60186100c2780612c0308e0184300c1f8060ec0306e0183300c14806054038de01c6b00e33806dbc036dc01b4f00da70069bc034d601a6700d3181693c0b49605a4702d2182e8fc0d47a08a3b01d1c82e8dc0d46a08a3301d188061bc030d60186700c3180613c030960184700c218060fc0307a0183b00c1c8060dc0306a0183300c188060bc030560182700c118075fc0bafa01d7b00ebd0075dc03aec01d7500e3f8071f80b8fa01c5f00e2f007174036fe01b7b00dbb806dcc0b6be05b5b02dab816d4c0b69e05b4d02da580ed240b68e06b4502da180ed040b48c04a440451f0065f8032ec0595e02cab0165380b298059460a8a200e4f80d26c0187f00c3d8061dc030e60185f00c2d80615c030a60184f00c2680612c030920184700c2280610c030820183f00c1d8060dc030660182900c0a81f1bc0f8dc01c6b00e3500719c038cc07c630563101edbc036d601b6702db182e9bc034d601a670453181e93c0d49a07a4b01d2481e91c0d48a07a4301d208168fc0f47607a3702d198061bc030d60186700c3180a13c0509a0184b00c2480a11c0508a0184300c2080a0fc0507a0183b0141b80a0d4030660282f00c1580a09c030461646f00e3580719c288c60bb6f00db5806d9c116c60bb4f045a582ed1c1168608a3e054b70065980b29c1314601c9f01a4d8030de0186b00c3380618c0509e0184b0142380610c0507e0183b0141b8060cc030520281500e378071b8038d601c6a00e33807198038c601c6200db7806dac036ce01b6300da1806d04034de01a6b00d3380698c1149e06a4d0452580e9241148e06a450452180e9040b47e07a3b03d1b8168cc030de0186b00c3380618c0309e0184d00c1d8060dc030660182f00c1580609c030460181500ebf8075f803af601d7a00ebb8075d803ae601d7202eb68071fc038f601c7700e39817184036fe01b7b00dbb806dcc0f6be06b5d045ad80ed64116ae06b5503da980ed440b69e07b4b03da3816d0c032fe0197b00cbd0065dc032ec0197300caf806574032b60195900cab806554032a60195100ca780652c0328e0194300c9f8224f8032760193700c998064c80324a0187f00c3f0061ec030f40187700c3b0061cc030e40185f03c2f0061740f0b80185b00c2d006164030b0018570642b006154220a80185300c29006144030a00184f02c2700612c030940184703c2300610c030840183f01c1f0060ec03074018370341b0060cc030640182500e378071ac038ce01c6300db7806db8036d601b6a00db3806d98036c601b6200da5806d28034de01a6b00d3380698c0b49e05a4b02d2381690c1147e06a3d0451d80e8e41146e06a350451980e8c4030de0186b00c3500619c030cc0186300c2780612c030860183f00c1e8060bc030560182700c1180605403afe01d7b00ebb8075cc0bada01c7f00e3f0071ec038f401c7700e3b0071cc038e405c6d00dbf806dec036ee01b7302daf816d6c0b6ae05b5302da7816d340b69603b4902da381ad140b68603b4100cbf8065ec032f40197700cbb0065cc032be0195b00cab80654c0329e0194d00ca5806528032920194800ca38165180328a0294400ca18065040327e0893e00c9d8064dc032660193200c928061fc030fc0187b00c3d0061dc030ec0187300c3900617c0b0bc0185b00c2d00615c0b0ac0185300c2900613c0b09c0184d02c2600612c030940184900c2400611c0b08c018450782200610c030840184100c200060fc0707c0183b00c1d0060dc0d06c0183300c1900609403ad601d6300e378071b8038d601c6a00e33807198038c601c6203e2f81f1780f8a607c5200db7806dac036ce01b6303daf816d4c0369e01b4e00da68069bc034d601a6700d3181e97c0f4a607a4f0352681e92c0749207a470352281e90c0748205a3f03d1d81e8dc0b4660196f00cb381253c0529a02947014a28124fc0927a049370249a8124bc0924e0186f00c3580619c030c60185f00c2980613c0309a0184700c2280610c0307e0183b00c1c8060dc030660183100c178060ac0304e0182300c0d80605c03ad601d6300e378071ac038ce01c630822f83914c036de01b6b00db3806d8c116be08b53045a7822d2c1168e08b4300d3780699c0949e04a470251f8128dc032de0196b00cb500659c032cc0196300caf80654c0329e0194b00ca380650c0327e0893e00c9d8064dc032660193200c9680649c0324a0186f00c370061ac030d40186700c3300618c030c40185f0642f00614c030a40184f02c2700612c03094018470682300610c030840183f01c1f0060ec03074018370341b0060cc03064018270141300609403cf401d6d00e3f8071ec038ee01c7303e2f82b1740f8b605c5903e2b8531540f8a605c5100dbf806dec036ee01b7303daf81ad74116b603b59055ab81ad540f6a603b5107da781ed2c0f68e08b4300d3f8069f8034f601a7a00d3b8069d8034e601a720152f80a978054ba02a5c0152d82a968054b20ea580152b80a958054aa02a540152981e948054a207a500152780a9380549607a4a0152380a9180548605a420151f80a8f80547606a3a0151b80a8d80546603a32024ab0125500927c0192e00c3f8061ec030f40187700c3b0061cc030be0185d00c2d806168030b20185800c2b80a158030aa0285400c298061440309e0184b00c2380610c0307e0283e00c1d8060dc030660183200c0c8079fc03cfc05e7d00ebd8075cc0fad60cd6903eb182b584038f601c7a00e3c8071dc038ec01c7302e3880719c038cc01c6503e2f81714c036fe01b7b00dbb806dcc0f6de06b6d045b580eda4156ce06b6503db180ed840f6be07b5302da781ed2c0f68e05b4300d3f8069f8034f601a7a00d3b8069d8034e601a720153780a9b8054da02a6c0153582a9a8054d20ea680153380a998054ca02a640153181e988054c207a600152f80a978054a607a520152780a9380549607a4a0152380a9180548605a420151f80a8f80547606a3a0151b80a8d80546603a3200cbf8065dc092de0496d024b38125941d2b404956024a781251c0927e0493e0249b8224c80325e0192e00c968061fc030f60187a00c3b8061d8030e60186f00c368061ac030d40186900c3400619c050cc018650143200618c030c20185f00c2980613c030960184700c218060fc0507c0183b00c1b8060cc030640181b00c0c80604403cf601e7300ebf8175f403af601d7a00ebb8075d803aea05d6f02eb18071fc038fc05c7d02e378331b80b8c605c6200e2f807178038ba01b7f00dbd806ddc036e60fb6f045b1816d7c0b6b605b5702da9816d3c0b69a05b4b01da4816d1c0d68a05b4301da08069fc034fc01a7b00d3d0069dc034ec01a7300d3900a9bc054dc02a6303d3100a97c054bc02a5b02d2d00a95c054ac02a5302d2900a93c0549c02a4d0152600a92c0b49402a490752400a91c0548c02a450152200a90c0b48402a4102d2000a8fc0547c02a3b0351d00a8dc0546c02a3301d190065fc032ee0e96a024b301257c092ae0494f024a68165280928e04946024a28125100927e0493e0249b8224c80325e0192e00c968061fc030f60187a00c3b8061d8030e60186f00c3180617c030b60185700c2980613c0309a0184b00c25006124030900184701423006114050880184300c208060fc0507c0183b00c1b8060cc030640181b00c0c80604419afe0ad7e00ebd8075e803aee01d7603eb982b5c80bada07c7f00e3d8071dc0b8e605c6106dbf806dec036ee08b7303daf81ad74116b603b59065ab81ad540f6a603b5102da781ed2c0f68e05b430153f80a9f8034f601a7a00d3b8069d8054e60aa720152f80a978054ba02a5c0152d832968054b20ea580152b80a958054aa02a540152981e948054a207a500152780a9380549607a4a0152380a9180548605a420151f80a8f80547606a3a0151b80a8d80546603a32024ab0125500927c0192e00c3f8061ec1d0f4018770143b0061cc050be0285d00c2d806164050ae0285500c298061440509e0184b0142380610c0507e0283e00c1d80a0dc030660b83200c0c8175fc03af601d7702eb98175b40b8fe0ac7e00e3d8071e8038ee01c7602e398171c80b8da10b7f00dbd806ddc116e605b5f02dad816d5c0b6a605b4f02da6816d2c0769205b47035a2816d0c0768202a7f0153f0069ec034f401a7700d3b00a9cc154e402a5f0152f00a96c0b4b402a570152b00a94c0b4a402a4f0152700a9340549802a4b02d2500a9241d49002a470152300a9140548802a4302d2100a9040b48002a3f0151f00a8ec0d47402a370151b00a8cc0746404946024a20124f80325c0187f00c3d83a1e8030ee0287600c3980a17c030b60285700c2980a13c0509a0184b02c2500612403090028470142300a114050880184300c2080a0fc0507c0183b0141b8060cc170640181900f3f8079f807cfa01d7b00eb981b5ac19ad206d63036b08071fc038f601c7700e3981b1bc0d8da06c6b02e3481b19c298ca06c6302e3083717c218a601b7b00dbd006de4036ee01b7600db980edc4036ce01b6600db281ad7c076a606b4f01da581ad1c0768601a7f00d3f0069ec034f401a7700d3b0069cc034e402a6f0153700a9b4054d802a6b0353500a9a41d4d002a670153300a994054c802a630353100a9840d4c002a5f0152f00a94c194a402a4f0152700a92c1b49402a470152300a90c0b48402a3f0151f00a8ec0d47402a370151b00a8cc074640197f00cbb8125bc092da0696a024b3812598092ca0496405cad0125580929e0494701c9f80e4f80926e0393200c978064b80325a0187f00c3d8061e8030ee0187600c398061bc030da0186b00c350061a4030d00186701433006194050c80186300c3080617c030a60184f00c2580611c030860183f0141f0060ec0306e0183300c1900606c0303201811036bf82b5f803af601d7a00ebb8075d80dae606d7201eb681f1fc038f601c7707e3981b17c0d8ba06c5b02e2c81b15c298aa06c5302e2881adfc036f601b7701db980ed840d69e03b4b035a380ed0c054fe02a7e00d3d8069e8034ee01a760153982a9c8054be02a5e0152e80a970054b606a5a0152c83a960054ae02a560152a80a950054a606a520152881a9400549e02a4e0152581e9280548e02a46015218169080547e02a3e0151d81a8e80546e02a360151980e8c8092ac0495401c9f0064b8030fe0187b0443d0061dc050ec018730142f80a174030b60685a00c2c806160050ae028560142a80a150030a6018510142780612c0508e018430141f80a0f8030760283700c1980e0c80303201e7b07f398175fc03af601d7702eb98175bc0bac605c7f0563f0071ec038f401c7700e3b0171cc0b8e405c6f0663701718c0b8c403c5f01e2f00f1740d6fe01b7b00dbb80edcc0d6de03b6301dad816d68076b205b5702dab00ed4c076a205b4702da301ad14054fe02a7e00d3d8069e8034ee01a760153982a9c8054de02a6e0153181e988054be02a5e0152d816968054ae02a56015298169480549e02a4e0152680a9300549605a4a0152483a9200548e02a460152280a9100548605a42015208169000547e02a3e0151d81a8e80546e02a360151980e8c8092fe0197705cb5012598092be04957024a78125340b29404947024a3012514092880393f01c9f0124dc072640192f00c970064b4030fe0187b0443d0061dc050ec018730143780618c050be0185b0142b80614c0509e0284d00c2581612803092018480142380a1180508a0284400c218061040507e0283e00c1d80a0dc030660383200c0d8060640302201e7b03f3981b5fc0dafc01d7b00ebd0075dc03aec06d73056b901b5bc0dadc06d63066b101f1fc038f601c7702e3981f1bc0b8c603c5f01e2f00f1740d6fe01b7b00dbb80edcc0d6de03b6302daf816d780b6ba05b4f02da700ed2c0769203b4302da100ed04054fe02a7e00d3d8069e8034ee01a760153982a9c8054de02a6e0153181e988054be02a5e0152e80a970054b606a5a0152c81a960054ae02a560152a80a950054a606a520152883a9400549e02a4e0152581e9280548e02a46015218169080547e02a3e0151d81a8e80546e02a360151980e8c8092fe0197705cb5012598092be0495e024ae812570092ae04955034a901253c0928e0393f01c9f0124dc072640192f00c970064b4030fe0187b0443d0061dc050ec018730143780618c050be0285e0142e80a170030b6018590142b80a154030a60685200c288061400509e0184b0142380610c0507e0283e00c1d80a0dc030660383200c0d8060640302201d6b05ab18291bc038d601c6704a3182117c0e8a60636f00db5806d9c116c60535f045a9810d3c1169603347045a180a9bc054dc01a6b00d3500699c034cc02a630553100a97c054bc02a530652900a93c0549c02a4b0752500a91c0548c02a4302d2100a8fc0547c02a3b0351d00a8dc0546c02a3301d190125bc032ce0e95a024ab01253c0928e0493f0249f0124dc112640192f00c970064b4030de0186b0743500619c050cc018630142f80614c0509e0184b0142380610c0507e0283e00c1d80a0dc030660b83200c0d8060640302201c6f00e3580719c038c601b6f00db5806d9c036c608b4f045a5822d1c116860196f00cb580659c032c60194f00ca580651c032860193f00c9d8064dc032660192500c370061980b09c0984601c1f01a0d80303d9445fc922de4115f1c8a78d35fc61ade24d5f106a78734fc31a5e0cd1f046877d25fb992dda495ebc4a75924fa7925d1491e744873023f9691dca88de404671815f8b0adc2855e0c2a70014f7b8a5b9851dc2286d413f6989db404dd9c266bd12f57095a9449d382469605f4682d9f015cee0a66f04f3682598411cba0865003f2781d9300dc940663902f1501588409c300461201f0600d80805c020260003f 20 1048575 8 255 11 2047 21 2097151
def cc_60_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb0e2eacf3fa7e519ff7f99867935638e84d86a7e829417f9307b643765516e38267c676641860c585dd2f5ac315505c510404a967468413e5833499c2a9a022e7b1ef3f1ae4112b830c86307b4d0007b 0x1bade2b5b80eb581d6a03ace075986eb18ad620f6de06dac0db385b630f6be1ed7415ad82b59056ae0ad5415a982b51074de069ac0d3383a63034a6069441d1f83a3b0746e0e8cc0c378186b030ce0618c142f8285e050ba0a0fc0c1d8283703066060ac1c15028270504c0608c0f3d0ae720f8fe071ec0e3b85c73198da171441dbf81b7b036ee0edcc1db683b610769e0ed2c1da383b43054fe2a9f80d3d81a7a034ee069d8153982a72054daf89b0153082a600549e16938152582a4a0548e1e918152182a420347e068f80d1e8187f030f6061dc0c398286d050d8061840c300284f030960a11c0c218183b07074060e4141b8283603066060c41413828260504a075ac3eb185c6f038d60719c2e3185c5f058a642dbc55b701b6b036d406d9c0db310b63156c41ed7c3daf02b53056a40ad2c15a502b470568c0ad0c1d3781a6b034ce0e98c1d2f83a530749e0e92c1d2383a430747e0e8f40d1d81a390746e0e8d41d1981a31132de0659c2ca7859471327e124f44c9b849350725e0e49c0c378186b030ce0618c142f818530509e0612c1423818430507e0a0f40c1d818390506e0a0d40c19818310505e060ac1c15028270504c0608c0c0d8881a0502e0a0580f3d87e730bafe075ec0ebb85d730bade175b42eb285c7f158fc071ec0e3d01c77038ec171cc2e3905c6f198dc171b41dbf81b7b036ee0edcc1db783b63076be0ed6c1dab83b530769e0ed341da583b4a076920ed201da385b460768a1ad101da183b41054fe2a9f80d3d81a7a034ee069d8153982a72054de1e9b8153182a62054be16978152d82a5a054ae16958152982a520549e16938152685a4c054960a928152482a480548e169181522bc244054860a908152082a400347e068f80d1e8997f032ee1657c2cab8594f0929a1651c24a28393f0726e0a4bc1496829270924a061fc0c3d81877030e60a1bc0c318285f030b60a15c0c298284f0509a0612c0c24828470508a0610c0c208183b07074060e4141b8283603066060c41413828260504a0606c440d028170502c1f5bc0eb581d670fac61f1bc3e3701c6b038d40719c0e3307c63158c41f17c3e2f07c5b0f8ae1f14c3e2907b6f036d606d9c2db187b5f0b6b61ed5c2da982b4f0569c0ad341d3781a6b034ce0e98c1d2f83a5b074ae0e94c1d2783a4d03496069241d2383a4507486069041d1f83a3b074720e8dc1d1983a31132de065ac0cb3899630f2be1e56c3cab879530f29e125343ca5879470928a1e50c2c9f8793b0f26e164cc1c978392b0724e0e48c0c378186b030ce0618c142f8185b050ae0614c14278284d03096061241423828450308606104141f8283d030760a0dc141a818330505e060ac1413818230503e0606c140b8181390ade075ac0eb3c6563888de071ac0e33c2463808befd16dea2bbb453076de06dac0db383b63076be0ed6c1dab83b530769e0ed2c1da383b43054de2a9b80d3581a6a034ce06998153182a62054be32978152d82a57054a60a948152785a4e054960a9281523ba246054860a9080d1f81a3e0347a265bc0cb581967132c62657c4cad89957132a62653c4ca589947132860e4fc1c9d83937072660a4bc14968292b0524e1249414918186f030d60619c0c318285f030b60a15c0c298284f030960a11c0c218183b07074060e4141b8283603066060c41413828260504a0a07c0c0d8881a0502e0a0580c0981d6b03ac6071bc0e3701c6b038d40719c0e3301c63038c41717c2e2f01c53038a406dbc0db581b67036c606d7c2da981b4f0369606d240da181b41034de069ac0d3381a630d4be0e94c352782a4d074960e924152382a45074860e9042d1f83a3b0d46e0e8cc0cb7819671329e125344ca3849450b27e1e4dc1c9786927030de061ac0c3381863030be0614c0c278184d03096061240c238184503086061040c1f8183b0306e060cc0c178182b0304e0608c0c0d8181703cf6079cc0ebf81d7e03af6075e80ebb81d7603ae6075c82eb785d6e0bada071fc0e3d81c77038e6171a42e3185c61036fe06dec0dbb81b730d6de0ed8c35af86b5d076b60ed6435ab86b55076a60ed442da783b4b0d68e0ed0c0d3f81a770f4be129744d2b84a550b49e1e91c1d1f86a37032fe065ec0cbd01977032ec065cc0cb781963032be065740cad81959032ae065540ca9819510329e0652c0ca3819430327e0e4f80c9e819370326a064cc0c990192b0324e061fc0c3f0187b030f4061dc0c3b01873030e4061bc3c3701863030c40617c3c2f0185d0f0b80616c0c2d01859030b00615c642b01855700a80614c0c2901851030a00613c2c270184b030940611c3c230184303084060dc141b018350305a060ac0c15018270904c0609578120181f0303c060740ebf81d7b03aee075cc2eb681c7e038ec171780dbf81b7b036ee06dcc2daf83b5b0b6ae0ed4c1da486b45032fe065ec0cbd01977032ec065cc0caf8195b032ae0654c0ca4819450327e0e4f80c9e819370326a064cc0c990187f030fc061ec0c3d01877030ec061cc0c390185f0b0bc0616c0c2d018570b0ac0614c0c290184903090061143c22018370506c060d40c12ae0240303e060780c0e81d6f03adc075ac0eb501d6703acc0758c0eb101b6f036d606d9c0db187b5f0f6ba06d6c0dac81b57036aa06d4c0da881a6f034d60699c0d3182a5f054ba168fc1d1d86a3707466061bc0c358186a030ce061980c3181853030a4061440c1f8183b0306e060cc0c178382e0304e0608c0c1101e7a03ce4071fc0e3d81c77038e6331b42e2881b7f036f606ddc0db986b6d076c216d3c1da586b4707686065fc0cbd8197a032ee065d80cb98196d052d8065840cb00194f032960651c0ca18193f0727c064f40c9b8193503266064c80c3f8187e030f6061e80c3b81876030e6061c80c36b506c030c2061800c278584e03096061280c238784603086061080c1b828360306a0609568120181f0303c060740eb581d63038de071ac0e3381c630b8be0714c0db781b6e036d606da80db381b66036c606d883daf87b5e036a606d480da581b4a0368e06d180da181a6f034d60699c0d3186a5f074a61693c1d2585a4707486168fc151e83a3b074720a8dc151a83a3307462065bc0cb38594f0b28e264fc249e899370926a0e4bc34938186f030d6061a80c3381866030c60617c0c298184f030960611c0c218183f0307a060ec0c1c818370306a060cc0c188182f0305a060ac0c1381825030460606c0c0b81e7b03ce6075fc0ebd81d7703ae6175bc2eb685d65038fe071f80e3d81c7a038ee071d80e3981c720b8de331b82e3681b7f036f606ddc0db986b6f076c616d7c1dad85b57076a616d3c2da683b4b0769216d1c35a283b4307682069fc0d3b85a5f0b4ae1693c252685a470948a0e8fc351b8197f032f6065e80cbb81976032e6065bc0cb18195f032b60655c0ca98194f0329a0652c0ca501949032900651c2ca301945052880650c0ca08193f0727c064f40c9b8193503266064c80c9581927030fe061f80c3d8187a030ee061d80c3981872030de1e1b80c3181862030be161780c2d8185a030ae161580c29818520309e161380c268584c03096061280c24818480308e161180c22b304403086061080c20818400306e0a0d80c1a8182d03056060a80c13848260304ab00900c0f8181e0303a075bc0eb581d6703ac6071bc0e3701c6b038d40719c0e3301c63038c41f17c3e2f07c5b0f8ae1f14c3e2901b6f036d606d9c0db187b5f0b6b61ed5c2da981b4f0369c06d340d3781a6b034ce0698c352f83a5b0d4ae0e94c352782a4d074960e924152382a45074860e9042d1f86a3d074761a8dc351a83a33032de065ac0cb3819630f2be1e56c3cab879530f29e125343ca5879470928a1e50c2c9f8793b0f26e164cc1c978692b0d24e0e48c0c378186b030ce0618c0c2f8185b030ae0614c0c278184d03096061240c238184503086061040c1f8183b03072060dc0c19818310305e060ac0c13818230303e0606c0c0b81813036be06d6c0dab81b53034be0696c0d2b81a530d47e0e8ec351b83a33030be0616c0c2b818530307e060ec0c1b818330305e060ac0c138182303ad60758c0e3781c6e038d6071a80e3381c66038c6071882e2f85c5e0b8ba06dbc0db581b67036c616d642da985b51034de069ac0d3381a630d4be0e94c352786a4d074960e924352386a45074860e9042d1f83a3b0d46e0e8cc0cb78196b032ce0658c24af849530929e1253424a5849490928e1251424a1849410927e124ec249b849330725e124ac14938186f030d6061a80c3381866030c60617c0c298184f0309a0612c0c24818470308a0610c0c208183f03076060dc0c198182f0705c060ac0c1381823030440606c0c0b81813038de071ac0e3381c630b8ba06db80db305b4e034de069ac0d3381a630b49e0e92c2d2383a43074721a8d40cb78196b032ce0658c24a78494b0928e1250c249c849350524e061bc0c358186a030ce061980c318184f030960611c0c21818390306a060bc1c170182703046060880c0d81d6a03ac406dbc0db581b67036c632d742da081a6f034d60699c0d3186a5d074a2168fc1d1d86a3707466065bc0cb581967032c61257424a88493f09276124dc249982927030de061ac0c3501867030cc0618c0c2e8285c030a2061400c1f8183b0306e060cc0c178382e0304e0608c0c110181b03ad60758c0e3781c6b038ce0718c2e2f85c5d0b8aa06dbc0db701b6b036d406d9c0db301b63036c416d7c65af05b5d034de069ac0d3381a630d4be0e94c2d2783a4b0b48e0e90c2d1f85a3d074760e8e42d1b86a35074660e8c40cb78196b032ce0658c24af849530929e1252c24a3849430927e124f4249d849390926e124d42499849310725e124ac14938186f030d6061a80c3381866030c60617c0c298184f030960611c0c218183f0307a060ec0c1d0183903070060dc2c1b0183505068060cc0c188182f0705c060ac0c1381823030440606c0c0b81813038be0716c0e2b81c53036be06d6c0dab81b535e69eb8d2d69a3ac343034be0696c0d2b81a530d49e0e92c352383a430d47e0e8ec351b83a33032be0656c0cab819530929e1252c24a3849430927e124ec249b849330725e124ac149383923030be0616c0c2d01857030ac0614c0c278184b0308e0610c0c1f8183b0306e060cc0c178382e030560609c0c11818220303e0606c0c0b8181303ade075ac0eb381d63038de071ac0e3381c636e8bed916da22bb2453036de06dac0db381b630d6be0ed6c35ab83b530d69e0ed2c35a383b43034de069ac0d3381a63134be2e96c4d2b8ba531349e2e92c4d238ba430747e1a8ec351b83a33032de065ac0cb501967032cc0658c0caf8195b032ae0654c0ca78194b0328e0650c0c9f8393e0327a064dc0c9a8193303264064bc0c958192703246061bc0c370186b030d40619c0c3301863030c40617c642f0185b030ae0614c0c290184f0b09c0612c0c25018476208c0610c0c21018370506c060d40c178182d60058060ac0c15018270904c060955812018230303e060780c0e81e7e03af4071fc0e3d81c77038e6171a48e3281b7f036fc06dec0dbd01b77036ec06dcc0db902b69116d00ad9415b202b4f0569c0ad2c3da502b470568c0ad0c2da101a7f034f6069dc0d3983a690d4ca1a93c1d2586a4707486068fc0d1f01a3d030fe061ec0c3d01877030ec061cc0c3481868030ca0a1900c278184b0308e0610c0c1f8283e0307a060bc14170182b030520608c0c110182103cf6079e80f3b01d6f03adc075b40e3f81c7b038ee071cc3e3787c630f8be2b1743e2d85c590f8ae471543e2985c51036fe06df80dbd81b7a036ee06dd80db981b72056de0adb815b187b62056be0ad7815ae82b5c056b622d6815ac88b58056ae0ad5815aa82b54056a61ed4815a887b500569e0ad3815a587b4a0568e0ad1815a185b42034fe069ec0d3b81a730d4de0e98c352f86a5d074b6229681d2c83a580d4ae1a958352a86a54074a60e944352783a4b0d48e0e90c0d1f81a3e0347a065fc0cbb8795f092ba2655c24aa8994f0f28e0a4fc249e829370526a0e4bc34938187f030f6061e80c3b81876030e6061bc0c318185f030ba0616c0c2d01859030b00615c142b01855050a80614c0c288184f030960611c0c218183f0507c060f40c178282e03056060a40c1181822030420606c0c0b81e7f03cfc179f40ebf81d7b03aee075cc3eb787d6b19ad21f59c3eb18ad61038f6071e80e3c81c77038ec071cc2e3881c67038cc071943e2f85c5b0f8ae1714c0dbf81b7e036f606de80dbb81b76036e606dc815b782b6e056da0adb015b588b6a056d222da015b382b66056ca0ad9015b187b62056c21ed8015af82b5e056b60ad5c15a987b520569e0ad3815a587b4a0568e0ad1815a185b42034fe069ec0d3b81a730d4de1a9b41d3583a690d4ce1a9941d3183a610d4be0e96c352b83a530b49e0e92c352383a430347e068f80d1e8197f032f6065dc0cb98796f092da265ac4cb3849650f2c61e57c4cad899570f2a61653c3ca5879470b2860a4fc249e8293b0526e0a4d414998392f0d2561a49c1c918187f030f6061e80c3b81876030e6061bc0c368186b030d4061a40c3401867050cc06194143201863030c20617c0c2d81857030a60613c0c258184703086060fc141f0183d0305e0a0b80c158182903046060880c108181f030360605c0c0981e7f03cf6079dc0f3981d7f0bafa075ec0ebd01d7703aec075d42eb785d6b0bace1758c0e3f81c7e0b8fa171bc663705c6b0b8ce1718c2e3101c5f038bc071740dbf81b7e036f606de80dbb81b76036e606dc815b782b6e056d60ad9c15b187b62056be0ad7815ad85b5a056ae0ad5815a985b520569e0ad3815a682b4c0569616d2815a488b480568e0ad1815a282b440568616d0815a085b40034fe069ec0d3b81a730d4de0e9ac353383a630b4be0e96c2d2b83a530b49e169341d2585a4a074920e9202d2385a460d48a1a9101d2183a410347e068f80d1e8197f032f6065dc0cb98996f132d62659c4cb18595f0b2b61655c2ca98594f0929a1652c2ca3849450b2860a4fc249e8293b0526e0a4d414998392f0d2561a49c1c918187f030f6061e80c3b81876030e6061bc0c3581867030c60617c0c2d81857030a60613c0c268184b03094061240c24018470508c0611414220184303082060fc141f0183d0305e0a0b80c158182903046060880c108181f030360605c0c0981e7b0fce6335fc56bf01d7b03af4075dc0ebb07d7315ae4175bc2eb705d6d0f8fe071ec0e3b85c730b8d21718c2e3082b7f056fc06dec0dbd01b77036ec0adcc45b902b6f056dc0ad8c3db102b5f056bc0ad7415ae02b5b116b40ad6445ac02b57056ac0ad5415aa02b530f6a40ad443da802b4f0569c0ad2c3da502b470568c0ad0c2da106a7f034f6069dc1d3986a6f074c61a97c352e83a5b074b21a95c352a83a53074a21693c1d2586a4707486068fc0d1f01a3d132fe065dc3caf8495d132ae125542ca7879470527e124f4149b829350725e1a49c0c3f8187b110f4061dc143b01873050de0618c142f8285d030b606164142b82855030a60614414278184b0508e0610c141f8283e0507a0a0bc14170182b030520608c1c1101821030360a05c2ebf81d7b03aee175cc2eb68ac7e038ec1717815bf82b7e036f606de80dbb81b76056e622dc815af82b5e056b616d6815ab82b56056a616d4815a487b480568a0ad10353f81a7b034ee0e9cc2d2f83a5b0b4ae0e94c1d2486a450347e068f80d1e8187f030f6221e80c3b82876030e60a17c0c2d82857030a60612414228283f0507c0a0f414178282e03056060a40c118382203042079e8573907c7f038f6071dc2e398cc6d0b8a20adfc15bf01b7b036f406ddc0dbb02b73116e40adb415b602b61116c00ad3c15a702b4b0f6940ad1c15a302b430b6841a9fc0d3d81a77074e61a9b41d3085a4f074961a91c1d2181a3f0347c068f40c3f8187b110f4061dc143b01873050da0a1b00c30818600509e0612c1423818430507e0a0f8141e8282f0505c060ac0c148182307044060840f3d87e730bafe075ec0ebb85d730bade175b42eb285c7f158fc071ec0e3d01c77038ec171cc2e3905c6f198dc171b415bf82b7e036f606de80dbb81b76056e622dc815b782b6e056c61ed8815af82b5e056b616d6815ab82b56056a616d4815a782b4e0569a0ad3015a585b4a0569222d2015a382b460568a0ad1015a185b420568216d00353f81a7b034ee0e9cc353783a630b4be0e96c2d2b83a530b49e169341d2585a4a074920e9202d2385a460d48a1a9101d2183a410347e068f80d1e8997f032ee1657c2cab8594f0929a1651c24a28293f0927a0a4dc149a8392f0d24e061fc0c3d8887a030ee0a1d80c398286f030c60a17c0c2d82857030a60a13c14268184b0b094061240c24028470508c0a114142201843030820a0fc141f0283d0505e0a0b80c1581829030460e0880c108181b0502ea55bc0eb581d6750ac69d1bc0e3581c674c8c69517d222da3457448a60adbc15b701b6b036d406d9c0db302b63116c40ad7c15af02b5b056ae0ad4c45a902b4f0569c0ad2c45a502b470568c0ad0c2da106a6f034d60699c1d3186a5f074b61a95c1d2986a4f074961a91c1d2181a3f0347c068f44cb78196b032ce2658c4caf8995b132ae2654c4ca78994b1328e2650c149f8493d052760a4dc149a829330725e1a4ac349383923030de061ac443501867050cc0618c142f8185b050ae0614c14278184b0508e0610c141f8283e0507a0a0bc14170182b030520608c1c11018210503e0606c140b8181303ad60758c0e3781c6e038d6071a80e3381c66038c6071882e2f85c5e038a6071480db781b6b036ce06d8c0daf85b530369e06d2c0da481b4303682069bc0d3581a67034c60e97c1d2983a4f0749a0a92c152483a470748a0e90c152083a3f074760e8dc1d198196f032ce2653c24a6899470928a164fc3c9b8392f0724e061bc0c3581867030c60617c0c298184f0309a0612c0c24818470308a0610c0c208183f03076060dc0c198182f030560609c0c118181b0302e079ec0f3981d7f03afc075ec0ebd01d7703aec075cc0eb905d6f0badc175b40e3f81c7b038ee071cc2e3485c630b8c206dfc0dbd81b77036e60edbc1db183b5f076ba0ed6c1dac83b57076aa0ed4c1da883b4f076960ed1c1da181a7f034ee1e97c252e89a57094aa1693c3d2383a3f0746e065fc0cbd81977032e6065bc0cb18195f032ba0656c0cac81957032aa0654c0ca88194f032960651c0ca18193f0327a064ec0c9d019370726c064d40c958192a0324e2e4980c3f8187e030f6061e80c3b81876030e6061c80c378786e030c6061880c2f8785e030ba1e1700c2d8185a030b2061600c2b8c856030aa801500c2981852030a2061400c278584e03096061280c238784603086061080c1f8283e0307a060ac0c15018270904c0607c0c0f0181d 20 1048575 8 255 11 2047 19 524287
def cc_60_2 : Nat → List (Nat × Nat) := unpackCursorV4 0xaba30a6c4ea412ba023f9bd4596c518ed7f885687ed9879e4f7237b6f82b6b93f67a3f617635b6615892d54c3d4eb614ae3d44b6341e2d3e13d390513117f2a56c20d981a16c1059c0b84d03d7b0003d 0xe2d81c53036be06d6c0dab81b530f69e1ed0c0d2f81a5b034ae0694c3d2787a431147e1e8ec3d1b88a33032be0656c0cab819530529e1250c249f8493b0926e124cc24978492b0924e1248c0c2f8185b030ae0614c0c27818430307e060ec0c1b818330305e060ac0c13818230302e0604c0eb581d63038de071ac0e3381c630f8be1f14c0db781b6b036ce06d8c3daf87b531169e1ed2c3da388b43034de0699c4d2787a471147e228dc0cb78196b032ce0658c0caf8195d032aa0653e88a70194b0328e0650c0ca10193f03276064dc0c998192b0324e061bc0c370186b030d40619c0c3301863030c40617c142f0185d0309e161380c258184a0308f801180c21818420307e0e0f80c1d8183a0306e1a0d80c19818320305b7c0b00c158182a0304e120980c12de02403ade075b80eb581d6a03ace075980eb181d62036de06dac0db381b63036b606d640d3781a6b034ce0698c852f86a5d114b60e964852b86a55114a60e9442d1f85a3b0b46e168cc0c378186b030ce0618c0c2b8185503076060dc0c198182f030560609c0c1181e7e03af4071fc0e3d81c77038e6171a42e3281b7f036fc06dec0dbd01b77036ec06dcc0db902b69056d00ad96e1b201b4f0369c06d340d3f81a7b034ee069cc1d3486a650b49e1692c2d2385a430547e0a8f4151d83a390546e1a8d4151982a31030fe061ec0c3b81873030d2061a00c328286403096061280c24818470508c0610c0c20818370506c060d40c178182b0304e0608c0eb581d63038d60719c0e3181c5f038a606dbc0db701b6b036ce06d8c0db102b5f0f6bc0ad4c15a902b4f0f69c0ad340d3781a6b034ce0698c3d2f87a530f49e1e92c3d2387a430547e0a8f4151d82a370d46a0a8cc0cb7819670f29e1e51c149f8293d0526e124d4449789927030de061ac0c3381863030be0a1780c29818520309e0612c0c248184703086061040c1b828360306a060bc0c1581827030460606c0c0b81d6b03ac6071ac0e3501c67038cc0718c0e2f81c5e038a6071480db781b6b036ce06d8c2daf85b530b69e16d340da581b490368e06d140da181b41034de069ac0d3381a630f4be1e94c852786a4d114960e924852386a45114860e9042d1f85a3b0b46e168cc0cb7819671329e125344ca3849450b27e164dc449789927030de061ac0c3381863030be0a1780c29818520309e061340c25818490308e061140c21818410307e060ec0c1d018370506c060cc0c178182b0304e0608c0c0d8181703cf6079e80f3b01d6f03adc075b40e3f81c7b038ee071cc2e3785c630b8be171742e2d85c5a0b8b2171602e2b87c560b8ab691502e2985c51036fe06df80dbd81b7a036ee06dd80db981b72056de1edb815b182b62056be1ed7815ae87b5c056b60ad6815ac82b58056ae1ed5815aad9354056a60ad4815a882b500369e06d380da681a7f034f6069dc0d3987a6f0f4c61e97c352e87a5b074b21e95c352a87a53074a21693c2d2585a470b4860a8fc151e82a3b074720a8dc351a82a3305462065fc0cbb8795f092ba1e55c24aa8594f0b28e0a4fc149e829370926a224bc4c938187f030f6061dc0c398186f050dc0618c0c310185f030ba0616c0c2c81857030aa0614c0c288184b03094061240c238284603086061040c1b828360306a060bc0c1581827030460606c0c0b81d6f03ada075ac0eb481d6703aca0758c0eb090c6f218d61f1a4863390c630f8c20717c0e2d81c57038a616dbc2db681b6b036d206d9c0db281b63036c206d7c0dad81b57036a616d3c2da585b470b686069bc0d3681a6b034d20699c0d3282a63054c20697c0d2d81a57034a61a93c1d2586a4707486168fc0d1d85a3707466265bc24b68996b132ce125944cb18195f032b60655c0ca98994f132962651c4ca18593f0b276164dc2c998392f0d2561a49c1c918186f030da061ac0c3481867030ca0618c0c308185f030b60615c0c298184f030960611c0c218183f03076060dc0c198182f030560609c0c118181f030360605c0c0981e7f03cfc0f9f40ebf81d7b03aee075cc36b786d6b0fad21b59c36b186d61038fe071ec0e3b81c730b8de171b42e3585c690b8ce171942e3185c610b8be1716c2e2b85c53036fe06df80dbd81b7a036ee06dd80db981b72056de1adb815b686b6c056d60ada815b482b68056ce1ad9815b2d7364056c60ad8815b082b60056be32d7815ad82b57056a60ad480da781b4e0369a069ec0d3d01a79034ee069d80d3983a71034ce069980d3286a5f074b61a95c1d2985a4f074961691c1d2182a3f0547a0a8ec1d1c82a370d46a0a8cc15188197f032f6065dc0cb98696f092da1a5ac34b3849650d2c62657c4cad89957132a61653c2ca5859470b2860a4fc149e8293b0526e124d414998392f0d2561a49c1c918187f030f6061dc0c398186f030da061ac0c3481867030ca0618c0c308185f050bc0616c0c2b81853030a40612c0c25018490308e0a1180c21818410306e0a0d80c1a8182f030560609c0c118181f030360605c0c0990d6f15adc075ac0eb501d6703acc4358c56b101c6b0f8c60f16c1e2c82c53058a216dbc0db581b670b6c616d7c2dae81b5b036b216d5c2daa85b53036a216d3c2da186a6f034d60699c1d3182a5f054b60a964152982a510549e0e90c2d1f83a3b0b46e0e8cc4cb781967132be125744cab849550b27e164dc1c9786927030de061ac0c3381863050be0a1740c2d81859050ae0a1540c29818510509e0a1380c21878420507e060ec141b818330505e060ac141381823030360a05c0f3d87e730dafe2b5f80ebd81d7a03aee075d836b986d7207ade0f5b81eb685c7f038f6071dc2e3985c6f0b8c61717c2e2e85c5b0b8b21715c2e2a85c530b8a20adfc55bf01b7b036f406ddc0dbb02b73056e40adbc3db702b63056c40ad7c35af02b5d0d6b80ad6c15ad02b59056b00ad5c35ab02b55aa6a80ad4c15a902b51056a006d3c0da701b4d0d4fe069ec0d3b83a73074d20e98c1d3085a4f074961691c1d2182a3f0547a0a8ec1d1c82a370d46a0a8cc15188997f032ee1a57c24ae86957092aa1653c2ca38293f0527a0a4dc249a8392f0d24e061fc0c3d81877030e60a1bc1437018630f0c40a17c142e8185b030b20a15c142a81853030a20612c2c25018490508e0a1180c21818410506e0a0d8141a8282f030560a09c0c118181b0502e431bc563701c6b038d40719c0e3310c63158c416dbc0db581b670b6c606d0c0da086a6f034d60699c1d3186a4f0d49a0a92c152482a470548a0a90c152085a3f07476168dc1d198186f030d60619c0c318284f0509a060ec141b818330505e060ac14138182303cf42b9c82e3f81c7b038ee171cc2e3685c61056fe2adf80dbd81b7a036ee06dd815b982b72056db4cdb015b082b600369e06d380da686a7f034f6069dc1d3986a6d074a21693c1d2585a47074860a8fc151e82a3b074720a8dc351a82a3305462061fc0c3d81877030e60a1b4143601861030c00612c2c25018490508e0a1180c21818410506e0a0d8141a8282f030560a09c0c1181d6b03ac6071bc0e3581c67038c61717c2e2981b6f036d606d9c0db182b5f056a606d3c0da701b4d034de069ac0d3381a630f4be1e94c2d2785a4b0b48e1690c151f82a3b0546e0a8cc0cb7819670b29e1651c149f829371125e2249c0c378186b030ce0618c0c2f8285e030ba0613c0c258184a0308e161180c21818370506c060d40c178182b0304e0608c0c0e8181b0302e06056dab781d6b03acf6158c2e3781c6b038ce1718c2e2f85c5b0b8ae1714c15b78ab6e036d606da80db381b66056c60ad8815af8cb5e056b60ad5c15a982b520369e06d380da6d626f034d60699c4531d425f114b74895c452985a4f0b4961691c2d2182a3f0547a0a8ec1d1c82a370d46a0a8cc15188996f032d60659c4cb18995f132b62655c4ca98594f0b2961651c2ca18293f0527a0a4ec149b8493505266224bc4c958992711246061bc0c3581867030c60a17c142f0185b050ae0614e88290184b0b094061241423828460308606104141b828360506a0a0bc0c1582827030460a07c0c0d8281703026075bc0eb581d6703ac6071bc0e3581c67038c61f17c2e2d87c570b8a606dbc0db581b67036c61ed7c45ad88b570f6a616d3c3da587b470b686069bc0d3581a67034c61e97c752d89a570f4a61693c3d2587a470b486228fc451d88a3711466065bc0cb581967032c60657c0cad81957032a60653c2ca70194d0328e065140ca1819420327e064ec0c9b819330325e064ac0c9381923030de061b80c358186a030ce061980c3181862030be321780c2d81857030a6061480c23828460308a060fc1c1f0183b03074060dc341b0183303064060bc0c158182a0304e120980c118181f0303c060743e3781c6b038ce1718c6db78ab6e036d606da80db381b661b6c62ad880da581b4a0d4de069ac0d3383a630b49e0e92c352383a430d47e1a8f4151d82a390546e0a8d4151982a31030de061ac0c33818630509e0a1380c25818430b0840a0fc141e8282f030560a09c0c1181e7a15ce40b1fc163f01c7b038f4071dc0e3b02c73158e40b1b4163602c619c8c01edfc0dbd81b770b6e61edb42db081b4f0369c06d34353f81a7b034ee0e9cc353683a510549e1a934152582a490548e0a914152183a410b47e0e8ec351b83a33030fe061ec0c3b81873050da0618414278284e0509a0a0fc141f0183b03072060cc2c19018310505e060ac1413818231bade075ac0eb387d63058de0b1b80e3581c6a038ce0719816318ac62058be0b178162d82c57058a6331483db781b6b036ce16d8c3daf85b5b0f6ae16d4c0da781b4e0369a369bc0d3581a67114c61e97c452dcd2570f4a60a93c352682a4b054920a91c152282a4307482168fc3d1d87a370b466265bc0cb581967132c61e57c4cad899570f2a60a53c24a68294b0528e0a51414a18593f0f2761e4dc2c998892f132562649c44918186f030d60619c0c318285f030b60a15c0c298284f0509c0a134141f8283e03076060e40c1985832030620a0bc0c1582827030460a07c0c0d8281703026075ac0eb181c6f038d60719c0e3181c5f038bc071740db781b6b036ce06d8c2daf85b530569e0ad3415a582b470b68a0ad0c0d3781a6b034ce0698c3d2f87a530549e0a92c152382a430b47e168ec2d1b85a33032de0659c14a7829470b27e164dc449788927030de061ac0c3381863030be0614c0c23828460308a060fc141f0183d0305e060ac0c1381823030360605c0eb781d6b03ace0758c0e3781c6b038ce0718c2e2f85c5b0b8ae1714c0db781b6b036ce06d8c45af88b5b116ae22d4c2da785b4b0b68e16d0c0d3781a6b034ce0698c4d2f8ea5b134ae3a94c2d2785a4b0b48e1690c451f88a3b1146e228cc0cb78196b032ce0658c0cafcb15e032b60655c0ca9819520329e065340ca58194a0328e165180ca28193f03276064dc0c998192f032560649c0c918186f030dc061ac0c3501867030cc0618c0c310185f190bc0616c0c2b81853030a40613c14270184d0307e0e0f80c1d8183a0306e1a0d80c19818320305e060ac0c15018270904c0608c0c0f8181e0303a075bc0eb701d6b03ad40759c0eb301d6303ac406dbc0db581b67036c636d7c3dae96b5b0b6b236d5c3daa96b530b6a2069bc0d3581a67034c60696c0d2c83a3f074760e8dc1d198186f030d60619c0c3181857030aa060fc0c1d8183703066060ac0c15018270504c0608c0f3f01d7a038fe071ec0e3b81c730b8d2471940dbf81b7b036ee06dcc1db483b650769e0ed2c1da383b43034fe069f80d3d81a7a034ee069d80d3981a72054d20a9a01532c92640549e16938152582a4a0548e1e918152182a420347e068f80d1e8187f030f6061dc0c3981869030ca0613c0c258184703086060ec0c1d018390306e0a0d80c19818310304e0a0980c1281d6b03ac6071ac0e3501c67038cc0718c0e2f81c5e038a6071480db781b6b036ce06d8c3daf87b530f69e1ed3485a585b490f68e1ed1485a185b41034de069ac0d3381a63074be0e94c1d2783a4d03496069240d2381a4503486069041d1f83a3b0746e0e8cc0cb7819671329e125344ca3849451327e1e4dc1c9783927030de061ac0c3381863030be0614c0c278184d03096061240c238184503086061040c1f8183b0306e060cc0c178182b030540609c14130182303036060680c0b8281603cf6079e80f3b01d6f03adc075b40e3f81c7b038ee071cc3e3787c630f8be2b1743e2d85c590f8ae471543e2985c51036fe06dec0dbb81b73076de0ed8c1daf83b5d076b60ed681dac83b58076ae2ad581daa86b54076a60ed441da783b4b0768e0ed0c0d3f81a7e034f6069e80d3b81a76034e6069c8153787a6e054c60a988152f87a5e054ba1e970152d82a5a054b20a960152b8aa56054ab1c950152982a52054a20a940152785a4e054960a928152387a46054860a9080d1f81a3e0347a065fc0cbb8795f092ba2655c24aa8994f0f28e0e4fc1c9b8292f0525a0a49c24928187f030f6061dc0c398186f030c60617c0c2e8185b030b20615c0c2a81853030a20613c0c258184703086060ec0c1d018390306e0a0d80c19818310304e0a0980c128181b030340605c140b01d6f03adc075ac0eb501d6703acc0758c0eb101c6f038d60719c0e3191c5f0f8b61f1648e2b87c530f8a206dbc0db581b67036c606d7c0dae81b5b036b206d5c0daa82b53056a21ed3c2da587b470b686069bc0d3581a67034c60e97c1d2e81a5b034b20695c0d2a81a53034a20e93c1d2583a4707486068fc1d1d83a3707466065bc0cb581967032c62657c24ae8995b132ae125544ca98794f132962651c3ca18593f0f2761e4dc2c998392f072560e49c1c918186f030d60619c0c318185f030ba0616c0c2c81857030aa0614c0c288184f030960611c0c218183f03076060dc0c198182f03056060a80c1382826030460607c0c0d8181a0302e0a0580c0981e7f03cfc179f40ebf81d7b03aee075cc3eb787d6b19ad21f59c3eb18ad61038f6071e80e3c81c77038ec071cc2e3881c67038cc071943e2f85c5b0f8ae1714c0dbf81b7b036ee06dcc1db783b6d076d60eda41db383b65076c60ed841daf83b5b076ae0ed4c1da783b4b0768e0ed0c0d3f81a7e034f6069e80d3b81a76034e6069c8153787a6e054da1e9b0153582a6a054d20a9a015338aa66054cb14990153182a62054c20a980152f87a5e054b60a95c152982a520549e16938152582a4a0548e1e918152182a420347e068f80d1e8197f032f6065dc0cb98796f092da265ac4cb3849650f2c61e57c4cad899570f2a61653c3ca5879470b2860e4fc1c9d83937072660a4bc14968292b0524e1249414918187f030f6061dc0c398186f030da061ac0c3481867030ca0618c0c308185f030b60615c0c298184f030960611c0c218183b03074060e40c1b8283603066060c40c13828260304a0607c0c0d8181a0302e0a0580c0981d6f03ad60759c0eb181c6f038d60719c0e3185c5f0b8b61715c2e2981b6f036dc06dac0db501b67036cc06d8c0db113b5f0f6bc4ed6c9dab93b530f6a406d3c0da702b4b0569406d1c0da301b4303684069bc0d3581a67034c60e97c1d2d83a57074a60e93c1d2581a47074860e8fc1d1e81a3b03472068dc0d1a81a3303462065bc0cb581967032c62657c4cad89957132a61653c2ca5859470b286264fc249e8993b1326e124d44c998392f072560e49c1c918186f030d60619c0c318185f030b60615c0c298184f030960611c0c218183f0307a060ec0c1c818370306a060cc0c188182f03056060a80c1382826030460607c0c0d8181a0302e0a0580c0981e7f03cf6079dc0f3981d7f0bafa075ec0ebd01d7703aec075d42eb785d6b0bace1758c0e3f81c7e0b8fa171bc663705c6b0b8ce1718c2e3101c5f038bc071740dbf81b7b036ee06dcc1db783b6b076ce0ed8c1daf83b5b076ae0ed4c1da783b4d076960ed281da483b480768e16d181da286b44076860ed040d3f81a7e034f6069e80d3b81a76034e6069c8153787a6e054d60a99c153182a62054be16978152d82a5a054ae16958152982a520549e16938152685a4c054960a928152482a480548e169181522c3244054860a908152082a400347e068f80d1e8197f032f6065dc0cb98996f132d62659c4cb18595f0b2b61655c2ca98594f0929a1652c2ca3849450b2860e4fc1c9d83937072660a4bc14968292b0524e1249414918187f030f6061dc0c398186f030d60619c0c318185f030b60615c0c298184f0309a0612c0c24818470308a0610c0c208183b03074060e40c1b8283603066060c40c13828260304a0607c0c0d8181a0302e0a0580c0981d6b0fac6371bc563701c6b038d40719c0e330dc63158c41717c2e2f02c53058a41edbc0db581b670b6c60ad7c2da982b4f056960ad2415a182b41074de069ac0d3383a63074be0e94c1d2783a4d03496069241d2383a4507486069041d1f83a3b0746e0e8cc4cb7819671329e125344ca3849450b27e1e4dc1c9783927030de061ac0c3381863050be0614c14278284d03096061241423828450308606104141f8183b0506e060cc14178182b0504e0608c0c0d8281703cf61f9cc66bf8ad7e03af6075e80ebb81d760fae62b5c82eb785d6e0bada1f1fc0e3d81c770b8e6171a42e3185c61076fe06dec0dbb83b73076de0ed8c1daf83b5d076b60ed641dab83b55076a60ed441da783b4b0768e0ed0c153f8aa7e034f6069e80d3b81a76054e60a9c8153787a6e054c60a988152f87a5e054ba1e970152d82a5a054b20a960152b8ca56054ab04950152982a52054a20a940152785a4e054960a928152387a46054860a9080d1f81a3e0347a265fc0cbb8795f092ba2655c24aa8594f0f28e0e4fc1c9b8292f0525a0a49c24928187f030f6061dc0c398286f030c60a17c142e8185b030b20a15c142a81853030a20a13c0c258284703086060ec1c1d018390506e0a0d80c19818310504e0a09814128181b110340a05c140b05d7f03af6075dc2eb985d6d158fc071d82e2f03b7f036f606ddc1db983b5f076b60ed5c1da983b490768a0a9fc553f01a7b034f4069dc0d3b02a73054e40a97c2d2f02a5b054b40a95c2d2b02a53054a40a924152402a450f488068fc0d1f01a3d030fe061ec0c3b81873050be0616c142b81853030920a1140c1d8383a030720a0dc141b01833030620a09c141302825 20 1048575 8 255 11 2047 19 524287
def cc_60_3 : Nat → List (Nat × Nat) := unpackCursorV4 0x8f57085b9a7f6657b541762536e9796806961f615d04f5527e502504b54d43a7b3eb4f3707b3264a2f4322d4202a92b26a3f23f2b1fa451c63419b2b15c3f1312b0f43d0c92b08c3d06c200185400018 0x1d6f01d6b01d6701d6301c6f01c6b01c6701c6307c5f05c5b07c5705c5301b6f01b6e01b6b01b6a01b6701b6601b6301b6207b5f07b5e10b5b10b5707b5307b5201b4f01b4e03b4b03b4a01b4701b4601b4301b4201a6f01a6b01a6701a6306a5f03a5b06a5703a5305a4f05a4e03a4b01a4703a4305a4205a3f05a3d01a3b01a3901a3701a3501a3301a310196f0196b01967019630795f0995b09957079530594f0794b07947059430993f0493d0993b0993704935099330392f0692b06927039230186f0186e0186b0186701863018620185f0185b01857018530184f0184b01847018430183f0183d0183b01839018370183501833018310182f0182b0182a0182702826018230181f0181b0181a01817028160181301e7f01e7e01e7d01d7f01d7b01d7901d7701d7307d7101d6f01d6b01d6701d6301c7f01c7e06c7d06c7c01c7b01c7a01c7901c7801c7701c7601c7501c7401c7301c7206c717e47001c6f01c6e01c6b01c6a01c6701c6601c6301c6206c5f06c5e06c5b06c5706c530cc5201b7f07b7d01b7b01b7901b7701b7501b7305b7101b6f01b6b01b6701b6307b5f05b5b07b5705b5303b4f03b4e03b4d01a7f06a7d01a7b01a7901a7701a7501a7303a7101a6f01a6b01a6701a6306a5f03a5b06a5703a5305a4f05a4e05a4d05a3f05a3e03a3b03a3903a3305a3203a310197f0497d0197b0197701975019730196f0196b01967019630795f0995b09957079530694f0494d0694b0694704945069430593f0793b07937059330392f0692b06927039230187f0187e0187d0186f0186e0186b018690186301862018610185f0185b01857018530184f0184d0184b01849018470184501843018410183f0183b01837018330182f0182b0182a0182702826018230181f0181b0181a01817028160181301d6f01d6e01d6d01c6f01c6b01c6901c6701c630cc6101c5f01c5b01c5701c5301b6f8c36d01b6b01b6901b6701b6501b6305b6101b5f01b5b01b5701b538a34f8934b873478534301a6f06a6d01a6b01a6901a6701a6501a6303a6101a5f01a5b01a5701a538324f08a4b8124708a437f23f08a3b7d23708a330196f0496d0196b0196701965019630195f0195b01957019530994f0994b09947099430993f0993b09937099330892f0992b09927089230186f0186e0186d0185f0185e0185b018590185301852018510184f0184b01847018430183f0183b01837018330182f0182b0182a0182702826018230181f0181b0181a01817028160181301d7f01d7b01d7701d7305d6d01c7e01c7605c5e01b7f01b7b01b7701b7305b5f05b5b05b5705b5303b4906b450197f0197d0197b0197a0197701976019750195f0195b019570195301949019450193f0193b01937019330187f0187e0187d0185f0585e0185d0585c0185b0185a018570585601855078540185301852018490184801845078440183f0383e0183b0183a018370683601833018320181f0181e0181d01d6b01d6301c6f01c6b01c6701c6305c5f05c5d05c5501c5301b6f01b6e01b6b01b6a01b6701b6601b6301b6207b5f07b5e01b5301b5201b4b01b4a01b4701b4601b4301a6f01a6b01a6701a6307a5f07a5305a4f05a4b05a4705a4308a3f06a3d08a3b03a3908a3706a3508a3303a310196f019670594f059470993f0493d09937049350892f089270186f0186d0186b0186a018670186601865018630185f018530184f0184b01847018430183f0183d0183b01839018370183501833018310182f0182b01827018230181b0181701e7b01e7301d7f01d7b01d7701d7305d6f05d6d05d6501c7f01c7e01c7b01c7a01c7701c7601c7301c7205c6f0cc6e05c6d01b7f01b7b01b7701b7307b6f07b6305b5f05b5b05b5705b5305b4f05b4d05b4b03b4905b4706b4505b4303b4101a7f01a7705a5f05a5705a4f04a4d05a4704a4508a3f08a370197f0197d0197b0197a0197701976019750196f019630195f0195b01957019530194f0194d0194b01949019470194501943019410193f0193b01937019330192b019270187f0187e0187d0186f0786e01863018620185f0585e0185b0185a018570585601853018520184f0584e0184d0584c0184b0184a01849018480184705846018457a044018430184201841018400183f0383e0183b0183a018370683601833018320182b0182a01827048260181f0181e0181d01d6f01d6b01d6701d6301c6f01c6e01c6b01c6a01c6701c6601c6301c6207c5f07c5e07c5b07c5707c5307c5201b6f01b6e01b6b01b6701b6301b6207b5f05b5b07b5a07b5707b5605b5301b4f01b4e01b4d01a6f01a6b01a6701a6307a5f07a5b07a5707a5307a4f06a4d07a4b03a4907a4706a4507a4303a4105a3f07a3b07a3705a330196f0196b01967019630795f0795b07957079530794f0494d0794b0794704945079430593f0793b07937059330892f0892b08927089230186f0186b01867018630185f0185b01857018530184f0184d0184b01849018470184501843018410183f0183b018390183701833018310182f0182b01827018230181f0181b018170181301d6f01d6b01d6701d6301c6f01c6b01c6701c630dc5f7b45b0dc577945301b6f01b6b01b6701b6308b5f08b5b08b5708b5308b4f08b4b08b4708b4301a6f01a6b01a6701a6309a5f0ea5b09a570ea5309a4f0da4b09a470ea4308a3f08a3b08a3708a330196f0196d0196b0196a0196701966019650195f0195b01957019530194f0194b01947019430193f0193b01937019330192f0192b01927019230186f0186e0186d0185f0c85e0185b0185701853018520184f0584e0184b0184a018477804601843018420183f0383e0183b0183a018370683601833018320182f0182b0182a0182704826018230181f0181e0181d01d6f01d6e01d6b01d6a01d6701d6601d6301d6201c6b01c6301c5b01c5901c5301c5101b6f01b6b01b6701b6302b5f02b5d01b5b01b5901b5701b5501b5301b5105b4f05b4301a6f01a6b01a6701a6313a5f06a5d08a5b03a5913a5706a5508a5303a5107a4f07a4305a3f05a3b05a3705a330196f019670995f0495d09957049550593f059370892f099270186f0186b01867018630185f0185b0185901853018510184f018430183f0283e0183b0183701833018320182f0182b01827018230181b0181701e7b01e7301d7f01d7e01d7b01d7a01d7701d7601d7301d7201d6f01d6e01d6d01c7f05c7d01c7b01c7a01c7701c7601c7505c6f05c6302c5f02c5d02c5b05c5902c5705c5502c5302c5101b7f01b7e05b7d05b6f07b6e05b6d07b6c05b6505b6305b6202b5f02b5e02b5d02b5c02b5b02b5a05b5905b5802b5702b5605b557635402b5302b5202b5102b5001b4f01b4e01b4d01a7f01a7b01a7701a7307a6f07a6302a5f02a5d02a5b03a5902a5706a5502a5302a5105a4f05a4b05a4705a4305a3f05a3d05a3b03a3905a3706a3505a3303a310197f019770295f0295d02957049550594f059470593f0493d05937049350892f099270187f0187b01877018730186901863018610184f0284e0184b0184701843018420183f0183d0183b01839018370183501833018310182f0182b01827018230181b0181707d6f07d6e01d6b01d6a01d6701d6607d630ad6201c6b07c6301c5b01c5907c5301c5107b6f01b6b01b6705b6302b5f02b5e02b5d07b4f07b4e05b4307b420da6f01a6b01a6708a6307a5f06a5d07a5b03a5907a5706a5507a5303a5107a4f07a4305a3f07a3b07a3705a330996f019670795f0495d07957049550593f079370892f099270186f0186b01867018630285f0285e0185b018590185305852018510284f018430283f0283e0283d0183b028370283501833058320282f0182b02827018230181b0281701d6f01d6d01d6b01d6901d6701d6501d6301d6101c6b01c6901c6301c6101c5b01c5307b6f07b6d10b6b05b6907b6707b6510b6305b6101b5f01b5b01b5701b5307b4f07b4301a6f01a6d01a6b01a6901a6701a6502a6302a6101a5f01a5b01a5701a5306a4f03a4306a3f03a3b06a3703a330996f0496d09967049650195f019570993f079370392f069270186f0186b0186901863018610185f0185b01857018530184f018430183f0183b01837018330182f0182b01827018230181b0181701e7f01e7e03e7d01d7b01d7306d6b07d6906d6306d6101c7f01c7e01c7b01c7a01c7701c7601c7301c7202c6f06c6e02c6d06c6c02c6b02c6a02c6902c6802c6706c6602c657346402c6302c6202c6102c6001c5f01c5e01c5d01b7f01b7b01b7701b7306b6f06b6d06b6b05b6906b6707b6506b6305b6107b5f07b5302b4f02b4d02b4b05b4902b470db4502b4302b4101a7b01a7a01a7901a7701a7601a7303a7101a6701a6601a6506a5f03a5302a4f02a4d02a4b03a4902a4706a4502a4302a4106a3f03a3b06a3703a330197f019770696f0496d06967049650294f0294d02947049450993f079370392f069270187f0187b01877018730186f0186d0186b01869018670186501863018610185901853018510183f0283e0183b0183701833018320182f0182b01827018230181b0181710d6f0ad6e01d6b01d6a01d6701d6610d630ad6201c6b07c6301c5b01c5905c5301c5105b6f01b6b01b6705b6302b5f02b5d03b5b03b5902b5702b5502b5302b5105b4f05b4306a6f01a6b01a6703a6302a5f02a5d02a5b02a5906a5706a5502a5302a5106a4f03a4302a3f03a3b05a3703a330996f019670995f0495d09957049550593f059370392f069270186f0186b01867018630285f0185b0185901853018510284f018430283f0283e0183b0283701833058320282f0182b02827018230181b0281701e7b07e7302d7f0ad7e01d7b01d7a01d7701d7602d7302d7201d6f01d6e01d6d05c7f01c7b01c7705c7305c6f05c6302c5f02c5d02c5b05c5902c5705c5502c5302c5105b7f0ab7e01b7b01b7a01b7701b7605b7305b7205b6f07b6e05b6305b6202b5f02b5e02b5d02b5c02b5b02b5a05b5905b5802b5702b5605b557135402b5302b5202b5102b5003b4f03b4e03b4d06a7f01a7b01a7703a7306a6f03a6302a5f02a5d02a5b03a5902a5706a5502a5302a5103a4b05a4a03a4905a4705a4603a4303a4105a3705a3606a350997f019770295f0295d02957049550594f059470593f0493d05937049350392f069270187f0187b01877018730186901863018610284f0284e0184b0284701843058420283f0283d0183b01839028370283501833018310282f0182b02827018230181b0281701d6b07d6302c6f0ac6e01c6b01c6a01c6701c6602c6302c6201c5f01c5e01c5d07b6f01b6b01b677536307b5f07b5302b4f02b4d02b4b05b4902b477434502b4302b417226f01a6b01a6708a6307a5f07a5302a4f02a4d02a4b03a4902a4706a4502a4302a417023f07a3b07a3708a330996f019670294f0294d02947049450993f079370892f099270186f0186b01867018630185901853018510283f0283e0183b02837018334b0320282f0182b02827018230181b0281701c6f01c6e01c6b01c6a01c6701c6601c6301c6201b6f01b6b01b6701b6301a6f01a6b01a6701a6307a4f06a4d07a4b03a4907a4706a4507a4303a4105a3f07a3b07a3705a330186f0186b01867018630184f0184d0184b01849018470184501843018410183f0183b018390183701833018310182f0182b018270182301c6f01c6b01c6701c6301b6f01b6b01b6701b6308b4f08b4b08b4708b430196f0196b01967019630195d0194f0194b01947019430193f0193b01937019330186e018660584e6e0460383e068360181e01c6301c6201b6b01b6701b6301b4f01b4d01a6f01a6b01a6701a6316a4f06a4d08a4b03a4916a4706a4508a4303a4105a3f07a3b07a3705a330186f0186b01867018630184f0184d0184b01849018470184501843018410183f0183b01837018330182f0182b018270182301e7f01e7e05e7d01d7a01d7207d6a6c56807d6207d6001b7b01b7a01b7901b7701b7601b7305b7101b6701b6601b6507b5d07b5c05b5105b5001a7f01a7b01a7701a7307a6f06a6d07a6b03a6907a6706a6507a6303a6106a5d03a5105a3f07a3b07a3705a330187f0187b01877018730186f0186d0186b01869018670186501863018610185d018410183f0183b01837018330182f0182b018270182301c6301c6201b6f01b6b01b6701b4301b4101a6f01a6b01a6701a6313a4f06a4d08a4b03a4913a4706a4508a4303a4105a3f05a3b05a3705a330186f0186b01867018630184f0184d0184b01849018470184501843018410183f0183b01837018330182f0182b018270182301e7a01e7201c7f05c7d01c7b01c7a01c7701c7601c7505c6d0dc6c05c6105c6001b7f01b7e05b7d05b6d6a36c05b6105b6005b5d0cb5c01b4f01b4e01b4d01a7f01a7b01a7701a7306a6d03a6105a4f05a4b05a4705a4305a3f05a3d05a3b03a3905a3706a3505a3303a310187f0187b01877018730186d018510184f0184b01847018430183f0183d0183b0183a01839018380183702836018350283401833018310182f0182b018270182307c6f0ac6e01c6b01c6a01c6701c6607c6307c6207b6f07b6e01b6b01b6705b630db620da6f01a6b01a6708a6307a4f06a4d07a4b03a4907a4706a4507a4303a4105a3f07a3b07a3705a330186f0186b01867018630284f0284d0184b01849028470284501843018410283f0283d0183b0283702835018330282f0182b028270182301c6301c6201b6f01b6b01b6701b630db4f07b4d10b4b05b490db4707b4510b4305b4101a6b01a6701a6301a4f01a4d06a3f03a3b06a3703a330186f0186b01867018630184f0184d0184b01849018470184501843018410183f0183b01837018330182f0182b018270182301e7f01e7e03e7d01d7a01d7206d6a6756806d6206d6001b7f01b7b01b7701b7306b6f06b6d06b6b05b6906b6707b6506b6305b610db5d05b5101a7b01a7a01a7901a7701a7601a7303a7101a6701a6601a6506a5d06a5c03a5103a5006a3f03a3b06a3703a330187f0187b01877018730186f0186d0186b01869018670186501863018610185d018410183f0183b01837018330182f0182b018270182310c6f0ac6e01c6b01c6a01c6701c6610c630ac6205b6f01b6b01b6705b6303b4303b4106a6f01a6b01a6703a6306a4f06a4d03a3b05a3703a330186f0186b01867018630284f0284d0184b01849028470284501843018410283f0183b02837018330282f0182b028270182301e7a0ae7205c7f01c7b01c7705c7305c6d05c6105b7f0ab7e01b7b01b7a01b7701b7605b7305b7205b6d6536c05b6105b6003b4f03b4e03b4d06a7f01a7b01a7703a7306a6d03a6103a4b05a4a03a4905a4705a4603a4303a4105a3705a3606a350187f0187b01877018730286d018510284f0184b02847018430283f0283d0183b01839028370283501833018310282f0182b028270182307c6f01c6b01c6705c630db6f0ab6e01b6b01b6a01b6701b660db630ab6203b4b03b4a06a6f01a6b01a6703a6305a4f03a4b03a4305a3f05a3d0186f0186b01867018630284f0184b02847018430283f0283d0183b01839028370283501833018310282f0182b028270182301e7a0ae7206c7f06c7e01c7b01c7a01c7701c7606c730ac7206c6d06c6c06c616346007b7f01b7b01b7705b7307b6d05b6103b4f03b4e03b4d06a7f01a7b01a7703a7306a6d03a6105a4f05a4e05a4d05a3f05a3e03a3b03a3903a3305a3203a310187f0187b01877018730286d018510284f0284d0184b01849028470284501843018410283f0183b02837018330282f0182b028270182301d6a0ad626b36f01b6b01b67693636835d05b516626f01a6b01a6708a6306a5d03a516423f08a3b6223708a330186f0186b01867018630285d018410283f0183b02837018330282f0182b028270182301d6b01d6301c6f01c6e01c6b01c6a01c6701c6601c6301c6202c5f02c5e07c5302c5201b6f01b6b01b6a01b6701b6601b6307b5f07b5e05b5307b5201b4f01b4e01b4d01a6f01a6b01a6701a6307a5f07a5307a4f06a4d07a4b03a4907a4706a4507a4303a4105a3f08a3d07a3b07a3707a3505a330196f019670794f0494d07947049450593f079370892f089270186f0186b01867018630185f018530184f0584e0184d018470184501843018420183f0583e0183b01839018370183301832018310182f0182b01827018230181b0181701b5f01b5b01b5701b5301a5f01a5b01a5701a5308a3f07a3b07a3708a330185f0185b01857018530183f0183b01837018330182f0182b0182701823 20 1048575 8 255 11 2047 20 1048575
def cc_60_4 : Nat → List (Nat × Nat) := unpackCursorV4 0xaeb3eab734a9621a593d9dc7d963799243f88e9682d617e04d7637d7243f6f4306b341660535df8157867513654aa6945b4f3da813994136831327412d65124a8c1f951178811492f10a3f09e6c0009e 0x5d7f05d7d01d7b01d7a01d7701d7605d7505c7f0ac7e05c7d01c5f01c5e01c5d03b7f01b7b01b7703b7303b5f03b5b03b5703b5303b4f03b4d03b4b03b4903b4703b4503b4303b4103a360a97e019760595e059560594e0594c059469f1440393e0187f0187b01877018730585f0185b05857018530584f0284d0184b01849058470284501843018410383f0183b038370183308825018190281507c6f07c6e07c6b01c6a07c6701c6607c630ac6207b6f05b6b0db6a07b6707b6605b6303a6f03a6b03a6703a6303a4f03a4d03a4b03a4903a4703a4503a4303a4103a3f03a3b03a3903a3703a3303a310886f0886b08867088630784f0284d0784b01849078470284507843018410583f0783b07837058330382f0382b0382703823a346fa246ba04679e46303b6f03b6b03b6703b6303b4f03b4b03b4703b4303a360a96e019660594e9d1460393e0886f0886b08867088630884f0884b08847088430383f0383b038370383308825018190281501e7f01e7e01e7d01c7f01c7b01c7701c7301c6f02c6d01c6b01c6901c6701c6501c6302c6105c5d01b7e01b7601b6e02b6c01b6601b6405b4e01a7f01a7b01a7701a7301a6f02a6d01a6b01a6901a6701a6501a6302a6105a4f05a4b05a4705a4303a3906a350187b0187a01879018770187601873018710186701866018650184f0184b018470184301839018350182f0182b018270182301e7f01e7e01e7d01d7b01d7301d6b01d6901d6302d6101c7f01c7b01c7701c7301c6f02c6d01c6b01c6901c6701c6501c6302c6105c5f05c5d05c5501b7f01b7e05b7d0ab7c01b7b01b7a01b7701b7601b7501b7401b7301b7201b6f01b6e02b6d02b6c01b6b01b6a01b6901b6801b6701b6601b6501b6401b6301b6202b6102b6005b5f0cb5e05b5d01a7f01a7b01a7701a7301a6f02a6d01a6b01a6901a6701a6501a6302a6107a5f07a5305a4f05a4b05a4705a4305a3f05a3d05a3b03a3905a3706a3505a3303a310197f019770196f0296d01967019650594f059470593f0493d05937049350892f099270187b0187a01879018770187601873018710186701866018650185f018530184f0184b01847018430183f0183d0183b01839018370183501833018310182f0182b01827018230181b0181701e7f01e7e01e7d01d7b01d7301d6b01d6901d6302d6101c7f01c7e01c7b01c7a01c7701c7601c7301c7201c6f01c6e02c6d02c6c01c6b01c6a01c6901c6801c6701c6601c6501c6401c6301c6202c6102c6003c5f03c5e03c5d01b7f01b7b01b7701b7301b6f02b6d01b6b01b6901b6701b6501b6302b6107b5f07b5306b4f06b4d06b4b05b4906b470db4506b4305b4101a7f01a7b01a7701a7301a6f02a6d01a6b01a6901a6701a6501a6302a6103a5903a5303a5106a3f03a3b06a3703a330197f019770196f0296d01967019650694f0494d06947049450993f079370392f069270187b0187a01879018770187601873018710186701866018650185f018530184f0184d0184b01849018470184501843018410183f0183b01837018330182f0182b01827018230181b0181701e7f01e7e01e7d01d7a01d7201d6a01d6801d6202d6001b7f01b7b01b7701b7301b6f02b6d01b6b01b6901b6701b6501b6302b610db5d05b5101a7f01a7b01a7701a7301a6f02a6d01a6b01a6901a6701a6501a6302a6106a5d03a4106a3f03a3b06a3703a330187b0187a01879018770187601873018710186701866018650185d0285c01851018500183f0183b01837018330182f0182b018270182301e7f01e7e01e7d01d7f01d7b01d7701d7301d6f01d6b01d6901d6701d6302d6101c7f01c7b01c7701c7301c6f02c6d01c6b01c6901c6701c6501c6302c6105c5f05c5b05c5705c5301b7f01b7e01b7b01b7a01b7701b7601b7301b7201b6f01b6e02b6d02b6c01b6b01b6a01b6901b6801b6701b6601b6501b6401b6301b6202b6102b6005b5f0cb5e05b5b05b5705b5305b5203b4f03b4e03b4d01a7f01a7b01a7701a7301a6f02a6d01a6b01a6901a6701a6501a6302a6106a5f03a5b06a5703a5303a4b05a4a03a4905a4705a4603a4303a4105a3705a3606a350197f0197b01977019730196f0296d0196b0196701965019630995f0995b09957099530594f0594b05947059430593f0493d0593b0593704935059330392f0692b06927039230187b0187a01879018770187601873018710186701866018650185f0185b01857018530184f0184b01847018430183f0183d0183b01839018370183501833018310182f0182b01827018230181f0181b018170181301d6f01d6e01d6d01c6f01c6b01c6701c6301c5f01c5b01c5901c5701c5302c5101b6f01b6b01b6701b6301b5f02b5d01b5b01b5901b5701b5501b5302b510db4f9b34b0db479a34301a6f01a6b01a6701a6301a5f02a5d01a5b01a5901a5701a5501a5302a519924f08a4b9824708a439723f08a3b0da3708a330196f0196b01967019630195f0295d0195b0195701955019530994f0994b09947099430993f0993b09937099330892f0992b09927089230186b0186a01869018670186601863018610185701856018550184f0184b01847018430183f0183b01837018330182f0182b01827018230181f0181b018170181301d6b01d6301c6f01c6e01c6b01c6a01c6701c6601c6301c6205c5f05c5e01c5301c5201b6f01b6b01b6701b6301b5f05b5301b4f01b4b01b4901b4301b4101a6f01a6b01a6701a6307a5f07a5308a4f06a4d08a4b03a4908a4706a4508a4303a4105a3f07a3b07a3705a330196f019670994f0494d09947049450593f079370892f089270186f0186b01867018630185f018530184f0184d0184b01849018470184501843018410183f0183b01837018330182f0182b01827018230181b0181701e7b01e7301d7f01d7e01d7b01d7a01d7701d7601d7301d7205d6f05d6e05d6d01c7f01c7b01c7701c7305c6905c6305c6101b7f01b7b01b7701b7307b6f07b6307b5f06b5d08b5b03b5908b5706b5507b5303b5105b4f07b4b07b4705b4301a7f01a7707a5f04a5d09a5704a5505a4f07a4708a3f08a370197f0197e0197d019770197501973019720196f019630195f0195d0195b01959019570195501953019510194f0194b01947019430193f0193b0193a0193708936019330192b0192a019270e9260187701876018750186f0786e01863018620185f0785e0185d0785c0185b0185a0185901858018570c8560185595054018530185201851018500184f0584e0184b0184a018470784601843018420183f0383e0183b0183a018370683601833018320182b0182a01827048260181f0181e0181d01d7f01d7b01d7701d7305d6d01c7e01c7605c5e01b7f01b7b01b7701b7305b5f05b5b05b5705b5303b4906b450197f0197e0197d019770197501973019720195f0195b019570195301949019450193f0193b0193a0193708936019330187701876018750185f0585e0185b0185a01857058560185301852018490184801845078440183f0383e0183b0183a018370683601833018320181f0181e0181d01d6b01d6a01b6f01b6b01b6701b6307b5f07b5d01b5b01b5901b5701b5501b5301b5101a6f01a6b01a6701a6308a5f06a5d08a5b03a5908a5706a5508a5303a5105a3f07a3b07a3705a330186f0186e0186701863018620185301852018510183f0183b01837018330182f0182b0182a01827088260182301e7a01e7201c7f01c7b01c7701c730cc6d05c5101b7f01b7b01b7701b7306b6d03b6105b4f07b4b07b4705b430197f0197e0197d019770197501973019720196d0296c01961019600194f0194b01947019430193f0193b0193a0193708936019330187701876018750186d9206c01861018600184f0584e0184b0184a018470784601843018420183f0383e0183b0183a018370683601833018320181f0181e0181d01d6b01d6301c6f01c6b01c6701c6305c5f01c5301b6f01b6e01b6b01b6a01b6701b6601b6301b6207b5f07b5e01b5301b5201b4b01b4a01b4701b4601b4301a6f01a6b01a6701a6307a5f07a5305a4f05a4b05a4705a4308a3f06a3d08a3b03a3908a3706a3508a3303a310196f019670594f059470993f0493d09937049350892f089270186f0186d0186b0186701865018630185f018530184f0184b01847018430183f0183d0183b01839018370183501833018310182f0182b0182a0182708826018230181b0181a018170e81601e7b01e7301d7f01d7b01d7701d7305d6f05d6d05d6501c7f01c7e01c7b01c7a01c7701c7601c7301c7205c6f0cc6e05c6d01b7f01b7b01b7701b7307b6f07b6305b5f05b5b05b5705b5305b4f05b4d05b4b03b4905b4706b4505b4303b4101a7f01a7705a5f05a5705a4f04a4d05a4704a4508a3f08a370197f0197e0197d019770197501973019720196f019630195f0195b01957019530194f0194d0194b0194a01949019480194705946019450294401943019410193f0193b0193a0193708936019330192b0192a019270e9260187701876018750186f0786e01863018620185f0585e0185b0185a018570585601853018520184f0584e0184d0584c0184b0184a018490184801847058460184590044018430184201841018400183f0383e0183b0183a018370683601833018320182b0182a01827048260181f0181e0181d01d6f01d6b01d6701d6301c6f01c6e01c6b01c6a01c6701c6601c6301c6207c5f07c5e07c5b07c5707c5307c5201b6f01b6b01b6a01b6701b6601b6307b5f05b5b07b5705b5301b4f01b4e01b4d01a6f01a6b01a6701a6307a5f07a5b07a5707a5307a4f06a4d07a4b03a4907a4706a4507a4303a4105a3f07a3b07a3705a330196f0196b01967019630795f0795b07957079530794f0494d0794b0794704945079430593f0793b07937059330892f0892b08927089230186f0186b01867018630185f0185b01857018530184f0184d0184b01849018470184501843018410183f0183b018390183701833018310182f0182b01827018230181f0181b018170181301d6f01d6b01d6701d6301c6f01c6b01c6701c639445f9345b914578f45301b6f01b6b01b6701b6308b5f08b5b08b5708b5308b4f08b4b08b4708b4301a6f01a6b01a6701a6309a5f0ea5b09a570ea5309a4f0ea4b09a470ea4308a3f08a3b08a3708a330196f0196e0196d019670196501963019620195f0195b01957019530194f0194b01947019430193f0193b0193a0193708936019330192f0192b0192a019270e926019230186701866018650185f0c85e0185b0185701853018520184f0584e0184b0184a018478e04601843018420183f0383e0183b0183a018370683601833018320182f0182b0182a0182704826018230181f0181e0181d01d6f01d6e01d6b01d6a01d6701d6601d6301d6201c6f01c6b01c6701c6307c5f07c5b07c5907c5707c5307c5101b6f01b6b01b6a01b6701b6601b6301b5701b5601b5507b4f07b4e05b4b07b4705b4307b4201a6f01a6b01a6701a6307a5f06a5d07a5b03a5907a5706a5507a5303a5107a4f07a4b07a4707a4305a3f07a3b07a3705a330196f0196b01967019630795f0495d0795b0795704955079530794f0794b07947079430593f0793b07937059330892f0992b09927089230186f0186b01867018630185f0185d0185b01859018570185501853018510184f0184b01847018430183f0183d0183b0183701835018330182f0182b01827018230181f0181b018170181301d6f01d6e01d6b01d6a01d6701d6601d6301d6201c6b01c6301c5b01c5905c5305c5101b6f01b6b01b6701b6301b5b01b5901b5701b5301b5101b4f05b4905b4305b4101a6f01a6b01a6701a6310a5f06a5d08a5b03a5910a5706a5508a5303a5107a4f07a4305a3f07a3b07a3705a330196f019670995f0495d09957049550593f079370892f099270186f0186b01867018630185f0185d0185b01859018570185501853018510184f018430183f0183b01837018330182f0182b01827018230181b0181701e7f01e7e01e7d01d7b01d7901d7307d7101d6b01d6301c7f01c7e0cc7d8b47c01c7b01c7a01c7901c7801c7701c7601c7501c7401c7301c7207c7107c7001c6f01c6e01c6b01c6a01c6701c6601c6301c6205c5f05c5e05c5d01b7f01b7e07b7d07b7c01b7b01b7901b7701b7501b7301b7205b7105b7001b6f01b6b01b6701b6305b5905b5305b5101a7f06a7d01a7b01a7901a7701a7501a7303a7101a6f01a6b01a6701a6307a5f07a5307a4f06a4d08a4b03a490ca4706a4507a4303a4105a3f07a3b07a3705a330197f0497d01977019750196f019670794f0494d09947049450593f079370892f099270187f0187e0187d0186f0186e0186b018690186301862018610185f018530184f0184d0184b01849018470184501843018410183f0183b01837018330182f0182b0182a0182702826018230181b0181a018170281601e7f01e7e01e7d01d7207d7001c7f05c7d01c7b01c7901c7701c7501c7305c7101c6f01c6b01c6701c6305c5d01b7e07b7c01b7601b7401b6e01b6605b4e01a7f06a7d01a7b01a7901a7701a7501a7303a7101a6f01a6b01a6701a6305a4f05a4b05a4705a4303a3906a350187f0187e0187d0186f0186e0186b018690186301862018610184f0184b018470184301839018350182f0182b0182a01827028260182301c6b01c6a01b6f01b6b01b6701b6305b5107b4f07b4d01b4b01b4901b4701b4501b4301b4101a6f01a6b01a6701a6310a4f06a4d08a4b03a4910a4706a4508a4303a4105a3f07a3b07a3705a330186f0186e0186b01863018620184f0284e0184d0183f0183b01837018330182f0182b0182a01827028260182301e7f01e7e01e7d01d7a01d7801d728857001d6a01d6201b7f07b7d01b7b01b7901b7701b7501b7305b7101b6f01b6b01b6701b630cb5d05b4101a7f06a7d01a7b01a7901a7701a7501a7303a7101a6f01a6b01a6701a6306a5d03a5105a3f07a3b07a3705a330187f0187e0187d0186f0186e0186b018690186301862018610185d0285c01851018500183f0183b01837018330182f0182b0182a01827028260182301d6f01d6e01d6b01d6a01d6701d6601d6301d6201c6b01c6301c5b01c5907c5307c5101b6f01b6b01b6701b6301b5f01b5d01b5b01b5701b5505b4f01b4301a6f01a6b01a6701a6310a5f06a5d08a5b03a5910a5706a5508a5303a5107a4f07a4305a3f05a3b05a3705a330196f019670995f0495d09957049550593f059370892f099270186f0186b01867018630185f0185d0185b01859018570185501853018510184f018430183f0183b01837018330182f0182b0182a0182702826018230181b0181a018170281601e7f01e7e01e7d01d7e01d7b01d7901d7301d7207d7107d7001d6b01d6301c7f01c7e05c7d07c7c01c7b01c7901c7701c7501c7301c7205c7105c7001c6f01c6b01c6701c6305c5f05c5d05c5501b7f01b7e05b7d8637c01b7b01b7a01b7901b7801b7701b7601b7501b7401b7301b7205b7105b7001b6f01b6e05b6d0ab6c01b6b01b6a01b6701b6601b6501b6401b6301b6205b5f0cb5e05b5d01a7f06a7d01a7b01a7901a7701a7501a7303a7101a6f01a6b01a6701a6307a5f07a5305a4f05a4b05a4705a4305a3f05a3d05a3b03a3905a3706a3505a3303a310197f0497d01977019750196f019670594f059470593f0493d05937049350892f099270187f0187e0187d0186f0186e0186b018690186301862018610185f018530184f0184b01847018430183f0183d0183b0183a01839018380183702836018350283401833018310182f0182b0182a0182702826018230181b0181a018170281601d6f01d6e01d6b01d6a01d6701d6601d6301d6201c6b01c6301c5b01c5903c5303c5101b6f01b6b01b6701b6307b5f07b5d10b5b05b5907b5707b5510b5305b5107b4f07b4301a6f01a6b01a6701a6301a5b01a5901a5701a5301a5101a4f03a4306a3f03a3b06a3703a330196f019670995f0495d09957049550993f079370392f069270186f0186b01867018630185f0185d0185b01859018570185501853018510184f018430183f0183b01837018330182f0182b0182a0182702826018230181b0181a018170281601e7f01e7e01e7d01d7b01d7901d7307d7101d6b01d6301c7f01c7e06c7d8447c01c7b01c7a01c7901c7801c7701c7601c7501c7401c7301c7206c7106c7001c6f01c6e01c6b01c6a01c6701c6601c6301c6203c5f03c5e03c5d01b7f07b7d01b7b01b7901b7701b7501b7305b7101b6f01b6b01b6701b6307b5f07b5306b4f06b4d06b4b05b4906b470db4506b4305b4101a7f01a7e06a7d06a7c01a7b01a7901a7701a7501a7301a7203a7103a7001a6f01a6b01a6701a6303a5903a5303a5106a3f03a3b06a3703a330197f0497d01977019750196f019670694f0494d06947049450993f079370392f069270187f0187e0187d0186f0186e0186b018690186301862018610185f018530184f0184d0184b01849018470184501843018410183f0183b01837018330182f0182b0182a0182702826018230181b0181a018170281601c6b01c6a01b6f01b6b01b6701b6310b4f07b4d10b4b05b4910b4707b4510b4305b4101a6f01a6b01a6701a6306a4f06a4d01a4b01a4901a4701a4501a4301a4106a3f03a3b06a3703a330186f0186e0186b01863018620184f0184d0183f0183b01837018330182f0182b0182a01827028260182301e7f01e7e01e7d01d7a01d7801d728257001d6a01d6201b7f07b7d01b7b01b7901b7701b7501b7305b7101b6f01b6b01b6701b630db5d05b5101a7f06a7d01a7b01a7901a7701a7501a7303a7101a6f01a6b01a6701a6306a5d03a4106a3f03a3b06a3703a330187f0187e0187d0186f0186e0186b018690186301862018610185d018510183f0183b01837018330182f0182b0182a01827028260182301d6f01d6e01d6b01d6a01d6701d6601d6301d6201c6f01c6b01c6701c6310c5f10c5b07c5910c5710c5307c5101b6f01b6b01b6701b6301b5f01b5d01b5b01b5901b5701b5503b5303b5105b4f05b4b05b4705b4301a6f01a6b01a6701a6306a5f06a5d01a5b01a5901a5701a5501a5301a5106a4f03a4b06a4703a4301a3f03a3b05a3703a330196f0196b01967019630995f0495d0995b0995704955099530994f0994b09947099430593f0593b05937059330392f0692b06927039230186f0186b01867018630185f0185d0185b01859018570185501853018510184f0184b01847018430183f0183b01837018330182f0182b0182a0182702826018230181f0181b0181a01817028160181301e7f01e7e01e7d01d7f01d7b01d7901d7701d7307d7101d6f01d6b01d6701d6301c7f05c7d01c7b01c7901c7701c7501c7305c7101c6f01c6b01c6701c6305c5f05c5b05c5705c5301b7f01b7e05b7d8037c01b7b01b7a01b7901b7801b7701b7601b7501b7401b7301b7205b7105b7001b6f01b6e01b6b01b6a01b6701b6601b6301b6205b5f0cb5e05b5b05b5705b5305b5203b4f03b4e03b4d01a7f01a7e06a7d06a7c01a7b01a7901a7701a7501a7301a7203a7103a7001a6f01a6b01a6701a6306a5f03a5b06a5703a5303a4b05a4a03a4905a4705a4603a4303a4105a3705a3606a350197f0497d0197b0197701975019730196f0196b01967019630995f0995b09957099530594f0594b05947059430593f0493d0593b0593704935059330392f0692b06927039230187f0187e0187d0186f0186e0186b018690186301862018610185f0185b01857018530184f0184b01847018430183f0183d0183b01839018370183501833018310182f0182b0182a0182702826018230181f0181b0181a018170281601813 20 1048575 8 255 11 2047 20 1048575
def cc_60_5 : Nat → List (Nat × Nat) := unpackCursorV4 0x82a4c7e04a7b52b7763f7373f7092e6c84169d2b65c4162a32612185e0325ae3257a345463452d1950b224ad5e44b623d07b3557b2d77e255821f75e1956214b4a11e2d0e03e0a0400712f02f420002f 0x7d6b07d6307c6f07c6e07c6b01c6a07c6701c6607c630ac6207c5f07c5e07c5307c5207b6f05b6b07b6705b6307b5f05b5303b4f03b4e03b4d03a6f03a6b03a6703a6303a5f03a5303a4f03a4d03a4703a4503a4303a3f03a3b03a3903a3703a3303a310496f049670494f0494d04947049450493f0493d04937049350392f039270886f0886b08867088630785f078530784f0284d0784b01849078470284507843018410583f0783b07837058330382f0382b03827038230481b04817cc56bca563c846fc746bc5467c3463c145fbf45303b6f03b6b03b6703b6303b5f03b5303b4f03b4b03b4703b4303a6f0aa6e03a6b01a6a03a6701a6603a6303a6203a5f0ca5e03a5303a5203a4f05a4e03a4b03a4a03a47be24603a4303a420496f049670494f049470393a03937039360392703926049250886f0886b08867088630885f088530884f0884b08847088430383f0383b03837038330382f0282d0382b01829038270282503823018210881d0481b048170481505d6f05d6e01b6b01b6705b6301b5701b5506a6f01a6b01a6703a6306a5f04a5d03a5b03a5904a5704a5503a5303a5105a3f03a3b06a3703a330186f0186b01867018630985f0285d0185b01859098570285501853018510583f0183b07837018330382f0182b068270182305e7f05e7e05e7d01c7b01c7a05c7901c7701c7605c7305c7101c6701c6601c6506b7f01b7b01b7703b7306b6f06b6d03b6b03b6906b6706b6503b6303b6105b4f03b4b06b4703b4303a3e0a97e019760796e0796c0a966bc1640594e07946049360187f0187b01877018730786f0286d0186b01869098670286501863018610584f0184b07847018430383f0183b0683701833018190181802815b301401d7f01d7e05d7d01d7701d7501d7301d7201c7701c7601c7501c5f05c5e01c5d01b7f01b7b01b7701b7305b5f03b5b05b5703b5301b4f01b4d01b4b03b4901b4706b4501b4301b4103a3e0197e019760595e059560194e0194c019460d944049360187f0187b01877018730185f0185b01857018530184f0184d0184b01849018470184501843018410183f0183b0183701833018190181801815b201401d6f01d6d07b6f07b6d01b5f01b5b01b5304a6f04a6d01a6b01a6901a6701a6501a6301a6101a5f01a5b01a5701a5305a3f03a3b06a3703a330196e0196c0392e0186f0186d0186b01869018670186501863018610185f0185b01857018530183f0183b01837018330182f0182b018270182301e7f01e7e01e7d01c7f01c7e0ac7d01c6f01c6e01c6b01c6901c6301c6205c6101b7f06b7d01b7b01b7901b7701b7501b7303b7101b6f01b6b01b6701b6305b4f03b4b06b4703b4301a7e04a7c03a3e0197eb917c01976019740196e019660594e07946049360187f0187d0187b01879018770187501873018710186f0186b01867018630184f0184b01847018430183f0183b0183701833018190181801815b101405c6f01c6b01c670ab6f07b6e01b4f01b4e06a6f01a6b01a6703a6305a4f03a4b05a4703a4305a3f04a3d03a3b03a3904a3704a3503a3303a310186f0186b01867018630584f0184b05847018430983f0283d0183b01839098370283501833018310382f0182b068270182305d7f05d7d01d7b01d7a01d7701d7605d7505c7f0ac7e05c7d01c5f01c5e01c5d06b7f01b7b01b7703b7305b5f03b5b05b5703b5305b4f05b4d03b4b03b4905b4706b4503b4303b4105a4604a4403a3e0a97e019760595e059560594e0594c05946b7144049360187f0187b01877018730585f0185b05857018530584f0284d0184b01849058470284501843018410383f0183b0683701833018190181802815b001407c6f07c6e07c6b01c6a07c6701c6607c630ac6207b6f05b6b07b6705b6306a6f03a6b06a6703a6306a4f04a4d03a4b03a4904a4704a4503a4303a4105a3f06a3d03a3b06a3706a3503a330986f0886b09867088630784f0284d0784b01849078470284507843018410583f0783b07837058330382f0682b068270382301b5f01b5b01b5701b5301a5f01a5b01a5701a5306a3f03a3b06a3703a330185f0185b01857018530183f0183b01837018330182f0182b018270182305d6f05d6e05d6d01b6b01b6a05b6901b6701b6605b6305b6101b5701b5601b5506a6f01a6b01a6703a6306a5f06a5d03a5b03a5906a5706a5503a5303a5105a3f03a3b06a3703a330392e0286f0186b01867028630285f0285d0285b02859028570285502853028510283f0283b02837028330282f0282b028270182301c6f01c6e05c6d01c6701c6501c6301c6201b6701b6601b6501b4f05b4e01b4d01a6f01a6b01a6701a6305a4f03a4b05a4703a4301a3f01a3d01a3b03a3901a3706a3501a3301a310392e0186f0186b01867018630284f0284b02847028430183f0183d0183b02839018370283501833018310182f0182b028270182301d6f01d6e01d6d01b6f01b6e0ab6d01b5f01b5e01b5b01b5901b5301b5205b5101a6f06a6d01a6b01a6901a6701a6501a6303a6101a5f01a5b01a5701a5305a3f03a3b06a3703a330196e0496c0392e0186f0286d0186b01869018670186501863028610185f0185b01857018530283f0283b02837028330182f0182b028270182305c6f05c6d01c6b01c6a01c6701c6605c6505b6f0ab6e05b6d01b4f01b4e01b4d06a6f01a6b01a6703a6305a4f03a4b05a4703a4305a3f05a3d03a3b03a3905a3706a3503a3303a3105936049340392e0286f0186b01867028630284f0284b02847028430283f0283d0283b02839028370283502833028310282f0282b0282701823b335fb235bb1357b035306a5f03a5b06a5703a5306a3f03a3b06a3703a330392e0285f0285b02857028530283f0283b02837028330282f0282b0282702823bb46fba46bb8467b646306b6f03b6b06b6703b6306b4f03b4b06b4703b4303a3e0a96e019660594eb5146049360986f0886b09867088630984f0884b09847088430383f0683b068370383301819b401802815af01401e7201d6d01c7f01c7b01c7701c7301c5f01c5d01c5b05c5901c5715c5501c5301c5101b7f01b7e01b7b01b7a01b7701b7601b7301b7201b5f01b5e01b5d01b5c01b5b01b5a04b590bb5801b5701b5604b5504b5401b5301b5201b5101b5004b4f04b4e04b4b07b4a04b4704b4604b4305b4201a7f01a7b01a7701a7301a5f01a5d01a5b03a5901a5706a5501a5301a5106a4f03a4b06a4703a4301956049540393e0392e0187f0187b01877018730185f0185d0185b01859018570185501853018510184f0184b01847018430183f0183d0183b01839018370183501833018310182f0182b018270182301e7a01d6d07c7f01c7b01c770ac7307c5f0ac5d07c5b05c5907c5715c5507c5305c5104b7f04b7e01b7b01b7a01b7701b7604b730ab7204b5f04b5e04b5d04b5c04b5b0ab5a04b590bb5804b5704b5604b5504b5404b5307b5204b5107b5004b4f04b4e04b4b07b4a04b4704b4604b4305b4206a7f01a7b01a7703a7306a5f06a5d03a5b0aa5a03a5903a5806a5706a5606a5506a5403a5303a5106a4f03a4b06a4703a4304956049540393e0392e0187f0187b01877018730785f0285d0185b01859098570285501853018510984f0184b07847018430483f0283d0183b01839048370283501833018310382f0182b068270182305e7f05e7e05e7d01d7b07d7307d6b0cd6907d630ad6101c7b01c7a05c7901c7701c7605c7305c7101c6701c6601c6507c5f05c5304b7f04b7e01b7b01b7a01b7701b7604b730ab7204b6f04b6e04b6d04b6c04b6b0ab6a04b690bb6804b6704b6604b6504b6404b6307b6204b6107b6004b5f04b5e04b5307b5204b4f04b4e04b4b07b4a04b4704b4604b4305b4206a7f01a7b01a7703a7306a6f06a6d03a6b03a6906a6706a6503a6303a6106a5f03a5305a4f03a4b06a4703a430497f019770496f0496d04967049650b95a049560494f049470393f0393e0393d0392f0392e039220187f0187b01877018730786f0286d0186b01869098670286501863018610785f018530584f0184b07847018430483f0283d0183b01839048370283501833018310382f0182b06827018230181b0481701e7b01e7301d7f01d7e05d7d01d7701d7501d7301d7205d6f05d6301c7701c7601c7501c6f0cc6e01c6301c6201c5f05c5e01c5d01b7f01b7e01b7b01b7a01b7701b7601b7301b7204b6f04b6e04b6307b6204b5f04b5e04b5b05b5a04b5704b5604b5305b5201b4f01b4e01b4d01b4c01b4b01b4a04b490bb4801b4701b4604b4504b4401b4301b4201b4101b4001a7f01a7b01a7701a7306a6f03a6305a5f03a5b05a5703a5301a4f01a4d01a4b03a4901a4706a4501a4301a410197f019770b96a049660495f049570194f0194d01947049450393f0393e0393d0392f0392e039220187f0187b01877018730186f018630185f0185b01857018530184f0184d0184b01849018470184501843018410183f0183d0183b01839018370183501833018310182f0182b01827018230181b0181701e7f01e7e01e7d01d7b01d7901d730cd7101d6b01d6301c7f01c7e0ac7d01c6f01c6e01c6b01c6901c6301c6205c6107c5f05c5301b7f01b7e04b7d04b7c01b7b01b7a01b7901b7801b7701b7601b7501b7401b7301b7204b710bb7001b6f01b6e01b6b01b6a01b6701b6601b6301b6204b5f04b5e04b5307b5204b4f04b4e04b4b07b4a04b4704b4604b4305b4201a7f06a7d01a7b01a7901a7701a7501a7303a7101a6f01a6b01a6701a6306a5f03a5305a4f03a4b06a4703a430197f0197e0497d0497c0197701975019720196f019670b95a049560494f049470393f0393e0393d0392f0392e039220187f0187d0187b01879018770187501873018710186f0186b01867018630185f018530184f0184b01847018430183f0183d0183b01839018370183501833018310182f0182b01827018230181b0181701e7b0ae7305d7f05d7d01d7b01d7a01d7701d7605d7505d6f05d6305c7f0ac7e05c7d05c6f0cc6e05c6305c6201c5f01c5e01c5d04b7f04b7e01b7b01b7a01b7701b7604b730ab7204b6f04b6e04b6307b6204b5f04b5e04b5b05b5a04b5704b5604b5305b5204b4f04b4e04b4d04b4c04b4b05b4a04b490bb4804b4704b4604b4504b4404b4305b4204b4105b4006a7f01a7b01a7703a7306a6f03a6305a5f03a5b05a5703a5305a4f05a4d03a4b05a4a03a4903a4805a4705a4606a4506a4403a4303a410497f019770b96a049660495f049570494f0494d0594a049470494604945049440393f0393e0393d0392f0392e039220187f0187b01877018730986f018630585f0185b05857018530584f0284d0184b01849058470284501843018410483f0283d0183b01839048370283501833018310382f0182b06827018230181b048170cd7f0ad7e07d7b01d7a0cd7701d7607d730ad7205d6d07c7f05c7b07c7705c7305c6104b7f04b7e04b7b01b7a04b7701b7604b730ab7204b5f04b5e04b5d04b5c04b5b0bb5a04b590bb5804b5704b5604b5504b5404b5307b5204b5107b5004b4f04b4e04b4b07b4a04b4704b4604b4305b4206a7f03a7b06a7703a7306a5f06a5d03a5b03a5906a5706a5503a5303a5105a4f03a4b06a4703a4304956049540393e0392e0987f0887b09877088730785f0285d0885b01859098570285507853018510584f0784b07847058430483f0283d0483b01839048370283504833018310382f0682b068270382305d7f05d7b05d7705d7305d6d05c7f0ac7e05c7b01c7a05c7701c7605c7305c7205c6d04b7f04b7e04b7b01b7a04b7701b7604b730ab7204b5f04b5e04b5b05b5a04b5704b5604b5305b5204b4f04b4e04b4d04b4c04b4b05b4a04b490bb4804b4704b4604b4504b4404b4305b4204b4105b4006a7f03a7b06a7703a7305a5f03a5b05a5703a5305a4f05a4d03a4b05a4a03a4903a4805a4705a4606a4506a4403a4303a4104946049440393e0392e0987f0887b09877088730585f0585b05857058530584f0284d0584b01849058470284505843018410483f0283d0483b01839048370283504833018310382f0682b0682703823ad56bac563ab46faa46ba9467a8463a745fa645304b6f04b6e04b6b01b6a04b6701b6604b630ab6204b5f04b5e04b530bb5204b4f04b4e04b4b0bb4a04b4704b4604b4305b4206a6f03a6b06a6703a6306a5f03a5306a4f03a4b06a4703a430496f049670b95a049560494f049470393f0393e0393d0392f0392e039220986f0886b09867088630985f088530984f0884b09847088430483f0283d0483b01839048370283504833018310382f0682b06827038230481b0481705d6f05d6e01b6b01b6a01b6701b6605b6301b5701b5503a6f01a6b01a6703a6303a5f03a5d03a5b03a5903a5703a5503a5303a5103a3f03a3b03a3703a330186f0186b01867018630885f0285d0185b01859088570285501853018510583f0183b07837018330382f0182b038270182305e7f05e7e05e7d01c7b01c7a05c7901c7701c7605c7305c7101c6701c6601c6503b7f01b7b01b7703b7303b6f03b6d03b6b03b6903b6703b6503b6303b6103b4f03b4b03b4703b4303a360a97e019760796e0796c0a966a41640594e079460393e0187f0187b01877018730786f0286d0186b01869088670286501863018610584f0184b07847018430383f0183b038370183308825018190281501d7f01d7e05d7d01d7701d7501d7301d7201c7701c7601c7501c5f05c5e01c5d01b7f01b7b01b7701b7303b5f03b5b03b5703b5301b4f01b4d01b4b03b4901b4703b4501b4301b4103a360197e019760595e0595c059560d9540194e0194c019460d9440393e0187f0187b01877018730185f0185b01857018530184f0184d0184b01849018470184501843018410183f0183b018370183301825018190181501d6f01d6d07b6f07b6d01b5f01b5b01b5301a6f01a6d01a6b01a6901a6701a6503a6303a6101a5f01a5b01a5701a5303a3f03a3b03a3703a330196e0196c039260186f0186d0186b01869018670186501863018610185f0185b01857018530183f0183b01837018330182f0182b01827018230181501e7f01e7e01e7d01c7f01c7e0ac7d01c6f01c6e01c6b01c6901c6301c6205c6101b7f03b7d01b7b01b7901b7701b7501b7303b7101b6f01b6b01b6701b6303b4f03b4b03b4703b4301a7e04a7c03a360197ea117c01976019740196e019660594e0594c07946079440393e0187f0187d0187b01879018770187501873018710186f0186b01867018630184f0184b01847018430183f0183b018370183301825018190181505c6f01c6b01c6a01c6701c660ab6f07b6e01b4f01b4e03a6f01a6b01a6703a6303a4f03a4b03a4703a4303a3f03a3d03a3b03a3903a3703a3503a3303a31039260186f0186b01867018630584f0184b05847018430883f0283d0183b01839088370283501833018310382f0182b038270182308815 20 1048575 8 255 11 2047 20 1048575
def cc_60_6 : Nat → List (Nat × Nat) := unpackCursorV4 0x9ac572feb647b0c67cf854f700f35e27f3af2b701badb0a5a3a53372061f9eb4de557a429aa9514429ceb522aea2ead3fcc275f34cd3d95cfb266a63d1f865e888c7f0eb5a11d74185680061 0x1c6b04b6f0ab6e01b6b04b6304b6204b4f07b4e04b4d0aa6f01a6b01a670aa6307a4f07a4b07a4707a4304a3f04a3d04a3b04a3706a3504a330496e049360186f0186b01867018630784f0184b07847018430483f0283d0183b0483702835018330982f0182b098270182301c6b01c6a05b6f01b6b05b6305b4f05b4d0aa6f01a6b01a670aa630fa4f06a4d0ba4b03a490fa4706a450ba4303a4105a3f05a3b05a3705a330496e049360186f0186b01867018630984f0284d0184b01849098470284501843018410583f0183b05837018330982f0182b098270182301e7a01d6d05c7f01c7b01c7705c7305c5f05c5d05c5b05c5a05c5905c5805c5707c5605c55de45405c5305c5104b7f0ab7e01b7b01b7a01b7701b7604b7304b7204b5f07b5e04b5d07b5c04b5b04b5a04b5904b5804b5707b5604b55dd35404b5304b5204b5104b500aa7f01a7b01a770aa7307a5f06a5d07a5b03a5907a5706a5507a5303a5105a4f05a4b05a4705a4304a3f04a3d04a3b03a3904a3706a3504a3303a310497e04946049360187f0187b01877018730785f0285d0185b01859078570285501853018510584f0184b05847018430483f0283d0183b01839048370283501833018310982f0182b098270182301d6f01d6d03d6b03d6901d6701d6504d6303d610fc6b07c690fc6307c6101c5b0ac5305b6f05b6d05b6705b6505b6305b5f01b5b01b5705b5305b4f05b4304a6f01a6d03a6b03a6901a6701a6503a6303a6104a5f01a5b01a5703a5306a4f03a4305a3f03a3b05a3703a330496f0496d04967049650495f0495e019570a9520493f049370392f049270986f0286d0186b01869098670286501863018610185f0185b01857018530984f018430583f0183b05837018330382f0182b06827018230181b0481703e7f03e7e03e7d01d7b0ad7306d6b07d6906d6306d6105c7f01c7b01c7705c7305c6f05c6d05c6b05c6905c6705c6505c6305c6105c5f05c5304b7f0ab7e01b7b01b7a01b7701b7604b7304b7204b6f06b6e04b6d06b6c04b6b04b6a04b6904b6804b6706b6604b65db36404b6304b6204b6104b6004b5f0cb5e04b5304b5201a7b01a7a03a7901a7701a7603a7303a7101a6701a6601a6506a5f03a5305a4f03a4b05a4703a4304a3f04a3d03a3b03a3904a3706a3503a3303a310497f0497e019770a9720496f0496d04967049650594a04947049460493704936049350392f049270187f0187b01877018730686f0286d0186b01869068670286501863018610985f018530584f0184b05847018430483f0283d0183b01839048370283501833018310382f0182b06827018230181b0481701d6f01d6e01d6b01d6a01d6701d6601d6301d6201c6b01c630fc5b07c590fc5307c5101b6f01b6b01b6701b6301b5f01b5d01b5b01b5701b5505b4f05b4301a6f01a6b01a6701a6306a5f06a5d03a5b03a5904a5704a5503a5303a5106a4f03a4305a3f03a3b05a3703a330196f019670495f0495d01957019550193f049370392f049270186f0186b01867018630185f0185d0185b01859018570185501853018510184f018430183f0183b01837018330182f0182b01827018230181b0181701e7f01e7e01e7d01d7b01d7901d7307d7101d6b01d6301c7f05c7d01c7b01c7901c7701c7501c7305c7101c6f01c6b01c6701c6305c5f05c5301b7f01b7e04b7dd937c01b7b01b7a01b7901b7801b7701b7601b7501b7401b7301b7204b7104b7001b6f01b6e01b6b01b6a01b6701b6601b6301b6204b5f0cb5e04b5304b5201a7f01a7e06a7d01a6f01a6e01a6b01a6901a6301a6203a6106a5f03a5305a4f03a4b05a4703a4304a3f04a3d03a3b03a3904a3706a3503a3303a310197f0197e0497d0497c0197701975019720196f0196e01967019620594a04947049460493704936049350392f049270187f0187d0187b01879018770187501873018710186f0186b01867018630185f018530184f0184b01847018430183f0183d0183b01839018370183501833018310182f0182b01827018230181b018170fd6f0ad6e0fd6b01d6a0fd6701d660fd630ad6205b6f05b6b05b6705b6305b5f05b5d06a6f03a6b06a6703a6303a5303a5105a3f05a3703a330986f0886b09867088630985f0285d0885b01859098570285508853018510583f0583b05837058330382f0682b068270382306d7f0ad7e06d7b01d7a06d7701d7606d7306d7203d6d05c7f05c7b05c7705c7305c5f05c5d05c5b05c5905c5705c5505c5305c5104b7f0ab7e04b7b01b7a04b7701b7604b7304b7204b5f06b5e04b5d06b5c04b5b04b5a04b5904b5804b5706b5604b55d735404b5304b5204b5104b5006a7f03a7b06a7703a7303a6105a4f03a4b05a4703a4304a3f04a3d03a3b03a3904a3706a3503a3303a310497e04946049360987f0887b09877088730685f0285d0685b01859068570285506853018510584f0584b05847058430483f0283d0483b01839048370283504833018310382f0682b068270382305c6f01c6b01c6705c6304b6f01b6b01b6a01b6701b6604b630aa6f01a6b01a670aa6305a4f05a4b05a4705a4304a3f04a3b04a3704a330496e05946049360186f0186b01867018630584f0184b05847018430483f0183b04837018330982f0182b0982701823df56bdc56305c6f05c6b05c6705c6305c5f05c5304b6f0ab6e04b6b01b6a04b6701b6604b6304b6204b5f0cb5e04b5304b52da26f0ba6bd82670ba63d625f0ba5305a4f05a4b05a4705a4304a3f04a3d04a3b03a3904a3706a3504a3303a310496f0496e04967d51620594a04947049460493704936049350492f049270986f0986b09867098630985f098530584f0584b05847058430483f0283d0483b01839048370283504833018310982f0982b09827098230481b0481707c6f05c6b07c6705c630bb6f0bb6b0bb670bb6305b4f07b4b07b4705b4305a4e0a96e01966049460393e069360986f0e86b098670d8630584f0784b07847058430983f0b83b098370b833018190281501d6b01d6301c6f01c6b01c6701c6307c5f05c5301b6f01b6e01b6b01b6a01b6701b6601b6301b6207b5f07b5e07b5307b5201b4f01b4e01b4701b4301b4201a6f01a6b01a6701a6306a5f03a5305a4f03a4b06a4703a4306a3f06a3d03a3b03a3904a3704a3503a3303a310196f019670494f0494e01947059420493f0493d01937019350392f049270186f0186b01867018630185f018530184f0184b01847018430183f0183d0183b01839018370183501833018310182f0182b01827018230181b0181701e7f01e7e01e7d01d7b01d7901d7307d7101d6b01d6301c7f01c7e04c7d04c7c01c7b01c7a01c7901c7801c7701c7601c7501c7401c7301c7204c71d247001c6f01c6e01c6b01c6a01c6701c6601c6301c6204c5f04c5e04c530cc5201b7f07b7d01b7b01b7901b7701b7501b7305b7101b6f01b6b01b6701b6307b5f05b5301a7f01a7e06a7d01a6f01a6e01a6b01a6901a6301a6203a6106a5f03a5304a4f06a4d03a4b03a4904a4704a4503a4303a4105a3f03a3b06a3703a330197f0497d01977019750196f019670494f0494e0494d0493f0493e059320392f049270187f0187d0187b01879018770187501873018710186f0186b01867018630185f018530184f0184d0184b01849018470184501843018410183f0183b01837018330182f0182b01827018230181b0181707d6b07d6304c6f04c6e04c6b01c6a04c6701c6604c630ac6204c5f04c5e04c530cc5207b6f05b6b07b6705b6307b5f05b530da6f0ba6bd12670ba6307a5f07a5304a4f06a4d04a4b03a4904a4704a4504a4303a4105a3f07a3b07a3705a330496f049670494f0494e0494d0493f0493e059320492f049270986f0986b09867098630785f078530484f0284d0484b01849048470284504843018410583f0783b07837058330982f0982b09827098230481b0481705b6f01b6b01b6705b6304b5f04b5d04b5b04b5705b5504b530aa6f01a6b01a670aa6304a5f04a5b04a5704a5305a3f05a3b05a3705a3301966049560493e0186f0186b01867018630485f0185b04857018530583f0183b05837018330982f0182b098270182305c6f05c6b05c6705c630bb6f0bb6b0bb670bb6305b4f05b4b05b4705b43cf26e05a460a96e019660494e0393e069360986f0e86b098670e8630584f0584b05847058430983f0b83b098370b833018190281501c6301c6201b6f01b6b01b6701b6307b4f07b4d12b4b05b4907b4707b4512b4305b4101a6b01a6701a6301a4f01a4d03a3f03a3b03a3703a33039260186f0186b01867018630184f0184d0184b01849018470184501843018410183f0183b01837018330182f0182b01827018230181501e7201d6d01c7f01c7b01c7701c7301c5f01c5d01c5b05c5901c5711c5501c5301c5101b7f01b7b01b7701b7301b5f01b5d01b5b03b5901b5703b5501b5301b5103b4f03b4b03b4703b4301a7f01a7e01a7b01a7a01a7701a7601a7301a7201a5f01a5e01a5d01a5c01a5b01a5a03a5903a5801a5701a5603a55cd25401a5301a5201a5101a5003a4f05a4e03a4b03a4a03a4707a4603a4303a4203936039260187f0187b01877018730185f0185d0185b01859018570185501853018510184f0184b01847018430183f0183b01837018330182f0182d0182b01829018270182501823018210181501c6b01c6a07b6f01b6b01b670ab6307b4f07b4d0fb4b05b4907b4707b450fb4305b4103a6f01a6b03a6303a4f03a4d03a3f03a3b03a3703a33039260186f0186b01867018630884f0284d0184b01849088470284501843018410883f0183b07837018330382f0182b03827018230481501e7a01d6d07c7f01c7b01c770ac7307c5f0ac5d07c5b05c5907c5711c5507c5305c5103b7f01b7b01b7703b7303b5f03b5d03b5b03b5a03b5903b5803b570ab5603b5506b5403b5303b5103b4f03b4b03b4703b4303a7f0aa7e01a7b01a7a01a7701a7603a7303a7203a5f07a5e03a5d07a5c03a5b03a5a03a5903a5803a570aa5603a55cb25403a5303a5203a5103a5003a4f05a4e03a4b03a4a03a4707a4603a4303a4203936039260187f0187b01877018730785f0285d0185b01859088570285501853018510884f0184b07847018430383f0183b03837018330382f0282d0182b01829038270282501823018210481505d6f05d6e01d6b01d6a01d6701d6603d6303d6201c6b07c6307c5b07c5907c5307c5103b6f01b6b01b6705b6303b5f01b5d03b5b03b5901b5701b5503b5303b5107b4f05b4303a6f01a6b01a6703a6303a5f03a5d03a5703a5503a5303a4f03a4303a3f03a3b03a3703a330496f019670495f0495d04957049550493f049370392f039270186f0186b01867018630885f0285d0185b01859088570285501853018510784f018430583f0183b07837018330382f0182b03827018230181b0481705e7f05e7e05e7d01d7b07d7307d6b0cd6907d630ad6101c7b01c7a05c7901c7701c7605c7305c7101c6701c6601c6507c5f05c5303b7f01b7b01b7703b7303b6f03b6d03b6b03b6903b6703b6503b6303b6103b5f03b5303b4f03b4b03b4703b4303a7f0aa7e01a7b01a7a01a7701a7603a7303a7203a6f07a6e03a6d07a6c03a6b03a6a03a6903a6803a670aa6603a65c926403a6303a6203a6103a6003a5f07a5e03a5303a5203a4f05a4e03a4b03a4a03a4707a4603a4303a420497f019770496f0496d04967049650494f049470393a03937039360392703926049250187f0187b01877018730786f0286d0186b01869088670286501863018610785f018530584f0184b07847018430383f0183b03837018330382f0282d0182b01829038270282501823018210881d0181b048170481501e7b01e7301d7f01d7e05d7d01d7701d7501d7301d7205d6f05d6301c7701c7601c7501c6f0cc6e01c6301c6201c5f05c5e01c5d01b7f01b7b01b7701b7303b6f03b6303b5f03b5b03b5703b5301b4f01b4d01b4b03b4901b4703b4501b4301b4101a7f01a7e01a7b01a7a01a7701a7601a7301a7203a6f07a6e03a6303a6203a5f05a5e03a5b03a5a03a5705a5603a5303a5201a4f01a4e01a4d01a4c01a4b01a4a03a4903a4801a4701a4603a450da4401a4301a4201a4101a400197f019770495f049570194f0194d01947049450393a03937039360392703926049250187f0187b01877018730186f018630185f0185b01857018530184f0184d0184b01849018470184501843018410183f0183b01837018330182f0182d0182b01829018270182501823018210181d0181b018170181501d6f01d6d01d6b01d6901d6701d6501d6301d6107c6b07c6907c6307c6101c5b01c5307b6f07b6d03b6b03b6903b6703b6503b6303b6101b5f01b5b01b5701b5307b4f05b4301a6f01a6d01a6b01a6701a6501a5f01a5b01a5701a5303a4f03a4303a3f03a3b03a3703a330496f0496e0496d0196701965019620195f019570493f049370192f0392a03927039260186f0186d0186b01869018670186501863018610185f0185b01857018530184f018430183f0183b01837018330182f0182b01827018230181d0181b018170181501e7f01e7e01e7d01d7b01d7901d730cd7101d6b01d6301c7f01c7e0ac7d01c6f01c6e01c6b01c6901c6301c6205c6107c5f05c5301b7f03b7d01b7b01b7901b7701b7501b7303b7101b6f01b6b01b6701b6303b5f03b5303b4f03b4b03b4703b4301a7f01a7e03a7dc627c01a7b01a7a01a7901a7801a7701a7601a7501a7401a7301a7203a7103a7001a6f01a6e01a6b01a6a01a6701a6601a6301a6203a5f07a5e03a5303a5203a4f05a4e03a4b03a4a03a4707a4603a4303a420197f0197e0497d0497c0197701975019720196f019670494f049470393a03937039360392703926049250187f0187d0187b01879018770187501873018710186f0186b01867018630185f018530184f0184b01847018430183f0183b01837018330182f0182d0182b01829018270182501823018210181d0181b018170181501d6b0ad6305c6f01c6b01c6703c6305c5f05c530ab6f07b6e01b6b01b6a01b6701b6603b6303b620fb5f07b5e0fb5307b5201b4f01b4e03b4b03b4a03b4703b4603b4301b4203a6f01a6b01a6703a6303a5f03a5303a4f03a4b03a4703a4303a3f03a3d03a3703a3503a330496f019670494f049470493f0493d04937049350392f0392a03927039260186f0186b01867018630885f018530584f0184b05847018430883f0283d0183b01839088370283501833018310382f0182b03827018230881d0181b048170481501e7b0ae7305d7f05d7d01d7b01d7a01d7701d7605d7505d6f05d6305c7f0ac7e05c7d05c6f0cc6e05c6305c6201c5f01c5e01c5d03b7f01b7b01b7703b7303b6f03b6303b5f03b5b03b5703b5303b4f03b4d03b4b03b4a03b4903b4803b4705b4603b4506b4403b4303b4103a7f0aa7e01a7b01a7a01a7701a7603a7303a7203a6f07a6e03a6303a6203a5f05a5e03a5b03a5a03a5705a5603a5303a5203a4f05a4e03a4d05a4c03a4b03a4a03a4903a4803a4705a4603a45c424403a4303a4203a4103a400497f019770495f049570494f0494d04947049450393a03937039360392703926049250187f0187b01877018730886f018630585f0185b05857018530584f0284d0184b01849058470284501843018410383f0183b03837018330382f0282d0182b01829038270282501823018210881d0181b04817048150dc6f0ac6e11c6b01c6a11c6701c660dc630ac6207b6f05b6b07b6705b6303b4303b4103a6f03a6b03a6703a6303a4f03a4d03a3b03a3703a33039260886f0886b08867088630884f0284d0884b01849088470284508843018410583f0783b07837058330382f0382b0382703823048150cd7f0ad7e07d7b01d7a0cd7701d7607d730ad7205d6d07c7f05c7b07c7705c7305c6103b7f03b7b03b7703b7303b5f03b5d03b5b03b5903b5703b5503b5303b5103b4f03b4b03b4703b4303a7f0aa7e03a7b01a7a03a7701a7603a7303a7203a5f07a5e03a5d07a5c03a5b03a5a03a5903a5803a570ca5603a55c225403a5303a5203a5103a5003a4f05a4e03a4b03a4a03a4707a4603a4303a4203936039260887f0887b08877088730785f0285d0885b01859088570285507853018510584f0784b07847058430383f0383b03837038330382f0282d0382b01829038270282503823018210481505c6f05c6b05c6705c6312b6f0ab6e12b6b01b6a12b6701b6612b630ab6203b4b03b4a03a6f03a6b03a6703a6303a4f03a4b03a4303a3f03a3d039260886f0886b08867088630584f0584b05847058430883f0283d0883b01839088370283508833018310382f0382b03827038230481505d7f05d7b05d7705d7305d6d05c7f0ac7e05c7b01c7a05c7701c7605c7305c7205c6d03b7f03b7b03b7703b7303b5f03b5b03b5703b5303b4f03b4d03b4b03b4a03b4903b4803b4705b4603b4506b4403b4303b4103a7f0aa7e03a7b01a7a03a7701a7603a7303a7203a5f05a5e03a5b03a5a03a5705a5603a5303a5203a4f05a4e03a4d05a4c03a4b03a4a03a4903a4803a4705a4603a45c024403a4303a4203a4103a4003936039260887f0887b08877088730585f0585b05857058530584f0284d0584b01849058470284505843018410383f0383b03837038330382f0282d0382b018290382702825038230182104815 19 524287 7 127 11 2047 20 1048575
def cc_60_7 : Nat → List (Nat × Nat) := unpackCursorV4 0xd30ff2cbfc54bef4c1b78b6bdc1a96c294a29f8b65dc18f506243280f05ed2d7271db0b2668b579c1588bd42bf4b0b50bc13d0bcd4bf30e88a43f232bc6e3d154c845200beac005f 0x5e7f05e7e05e7d01c7b01c7a05c7901c7701c7605c7305c7101c6701c6601c650ab7f01b7b01b770ab7307b6f06b6d07b6b03b6907b6706b6507b6303b6105b4f07b4b07b4705b430ba360a97e019760796e0796c07966ff1640594e079460393e069360187f0187b01877018730786f0286d0186b01869078670286501863018610584f0184b07847018430983f0183b09837018330e825018190281501d7f01d7e05d7d01d7701d7501d7301d7201c7701c7601c7501c5f05c5e01c5d01b7f01b7b01b7701b7305b5f05b5b05b5705b5301b4f01b4d01b4b03b4901b4706b4501b4301b410ba360197e019760595e059560194e0194c019460d9440393e069360187f0187b01877018730185f0185b01857018530184f0184d0184b01849018470184501843018410183f0183b018370183301825018190181501d6f01d6d07b6f07b6d01b5f01b5b01b530ba6f06a6d0ba6b03a690ba6706a650ba6303a6101a5f01a5b01a5701a5305a3f07a3b07a3705a330196e0196c0b9260186f0186d0186b01869018670186501863018610185f0185b01857018530183f0183b01837018330182f0182b01827018230181501e7f01e7e01e7d01c7f01c7e07c7d01c6f01c6e01c6b01c6901c6301c6205c6101b7f06b7d01b7b01b7901b7701b7501b7303b7101b6f01b6b01b6701b6305b4f07b4b07b4705b4301a7e04a7c0ba360197efc17c01976019740196e019660594e079460393e069360187f0187d0187b01879018770187501873018710186f0186b01867018630184f0184b01847018430183f0183b018370183301825018190181505c6f01c6b01c6707b6f07b6e01b4f01b4e0aa6f01a6b01a670aa6305a4f05a4b05a4705a430ba3f06a3d0ba3b03a390ba3706a350ba3303a310b9260186f0186b01867018630584f0184b05847018430983f0283d0183b01839098370283501833018310982f0182b09827018230e81505d7f05d7d01d7b01d7a01d7701d7605d7505c7f07c7e05c7d01c5f01c5e01c5d0ab7f01b7b01b770ab7305b5f05b5b05b5705b5305b4f05b4d05b4b03b4905b4706b4505b4303b4105a4604a440ba360a97e019760595e059560594e0594c05946fa1440393e069360187f0187b01877018730585f0185b05857018530584f0284d0184b01849058470284501843018410983f0183b09837018330e825018190281507c6f07c6e07c6b01c6a07c6701c6607c630ac6207b6f05b6b07b6705b630ba6f0ba6b0ba670ba6307a4f06a4d07a4b03a4907a4706a4507a4303a4105a3f07a3b07a3705a330986f0d86b098670d8630784f0284d0784b01849078470284507843018410583f0783b07837058330982f0b82b098270b823fe46ffd46bfb467f94630bb6f0bb6b0bb670bb630bb4f0bb4b0bb470bb430ba360a96e019660594ef81460393e069360986f0e86b098670e8630984f0e84b098470e8430983f0b83b098370b8330e825018190281505c6305c6201b6b05b6901b6705b6305b6101b4f01b4d0aa6f01a6b01a670aa630fa4f06a4d0ba4b03a490fa4706a450ba4303a4105a3f07a3b07a3705a330186f0186b01867018630984f0284d0184b01849098470284501843018410583f0183b07837018330982f0182b098270182305e7f05e7e05e7d01d7a0ad7207d6af656807d6207d6001b7b01b7a05b7901b7701b7605b7305b7101b6701b6601b6507b5d07b5c05b5105b500aa7f01a7b01a770aa7307a6f06a6d07a6b03a6907a6706a6507a6303a6106a5d03a5105a3f07a3b07a3705a33049260187f0187b01877018730786f0286d0186b01869078670286501863018610285d018510583f0183b07837018330982f0182b09827018230481501e7a01e7801e720ae7001c7f01c7e05c7d01c7701c7501c7301c7205c6d05c6101b7701b7601b7501b6d0db6c01b6101b6001b4f05b4e01b4d01a7f01a7b01a7701a7306a6d03a6105a4f05a4b05a4705a4301a3f01a3d01a3b03a3901a3706a3501a3301a31049260187f0187b01877018730186d018610184f0184b01847018430183f0183d0183b01839018370183501833018310182f0182b01827018230181501c6b01c6a01b6f01b6e01b6b01b6901b6301b6205b6107b4f07b4d01a6f01a6b01a6701a630fa4f06a4d0ba4b03a490fa4706a450ba4303a4105a3f07a3b07a3705a330494e049260186f0186b01867018630184f0184d0184b01849018470184501843018410183f0183b01837018330182f0182b01827018230181501e7f01e7e01e7d01d7a01d7801d72f357001d6a01d6201b7f01b7e07b7d01b6f01b6e01b6b01b6901b6301b6205b6107b5d05b5101a7f06a7d01a7b01a7901a7701a7501a7303a7101a6f01a6b01a6701a6306a5d03a5105a3f07a3b07a3705a330197e0497c049260187f0187d0187b01879018770187501873018710186f0186b01867018630185d018510183f0183b01837018330182f0182b01827018230181507c6307c6205b6f01b6b01b6701b4301b410aa6f01a6b01a670aa630fa4f06a4d0ba4b03a490fa4706a450ba4303a4105a3f05a3b05a3705a33049260186f0186b01867018630984f0284d0184b01849098470284501843018410583f0183b05837018330982f0182b09827018230481501e7a01e780ae720ae7005c7f05c7d01c7b01c7a01c7701c7605c7505c6d0dc6c05c6105c6005b7f07b7e05b7d05b6df136c05b6105b6005b5d0cb5c01b4f01b4e01b4d0aa7f01a7b01a770aa7306a6d03a6105a4f05a4b05a4705a4305a3f05a3d05a3b03a3905a3706a3505a3303a310493604934049260187f0187b01877018730286d018610584f0184b05847018430583f0283d0183b01839058370283501833018310982f0182b09827018230481507c6f0ac6e07c6b01c6a07c6701c6607c6307c6207b6f07b6e05b6b07b6705b630db620da6f0ba6b0da670ba6307a4f06a4d07a4b03a4907a4706a4507a4303a4105a3f07a3b07a3705a330986f0986b09867098630784f0284d0784b01849078470284507843018410583f0783b07837058330982f0982b098270982303c6303c620ab6f01b6b01b670ab630db4f07b4d0fb4b05b490db4707b450fb4305b4101a6b01a6703a6301a4f01a4d06a3f03a3b06a3703a33049260186f0186b01867018630984f0284d0184b01849098470284501843018410983f0183b09837018330382f0182b06827018230481503e7f03e7e03e7d01d7a0ad7206d6aee56806d6206d600ab7f01b7b01b770ab7306b6f06b6d06b6b05b6906b6707b6506b6305b610db5d05b5101a7b01a7a03a7901a7701a7603a7303a7101a6701a6601a6506a5d06a5c03a5103a5006a3f03a3b06a3703a33049260187f0187b01877018730686f0286d0186b01869068670286501863018610285d018510983f0183b09837018330382f0182b06827018230481501c6b01c6a01b6f01b6b01b6701b630fb4f07b4d0fb4b05b490fb4707b450fb4305b4101a6f01a6e01a6b01a6301a6206a4f06a4d06a3f03a3b06a3703a33049260186f0186b01867018630184f0184d0184b01849018470184501843018410183f0183b01837018330182f0182b01827018230181501e7f01e7e01e7d01d7a01d7801d72ec57001d6a01d6201b7f07b7d01b7b01b7901b7701b7501b7305b7101b6f01b6b01b6701b630db5d05b5101a7f01a7e06a7d01a6f01a6e01a6b01a6901a6301a6203a6106a5d03a5106a3f03a3b06a3703a33049260187f0187d0187b01879018770187501873018710186f0186b01867018630185d018510183f0183b01837018330182f0182b0182701823018150fc6f0ac6e0fc6b01c6a0fc6701c660fc630ac6205b6f05b6b05b6705b6303b4303b4106a6f03a6b06a6703a6306a4f06a4d03a3b05a3703a33049260986f0886b09867088630984f0284d0884b01849098470284508843018410583f0583b05837058330382f0682b06827038230481501e7a0ae7205c7f05c7b05c7705c7305c6d05c6105b7f0ab7e05b7b01b7a05b7701b7605b7305b7205b6dea36c05b6105b6003b4f03b4e03b4d06a7f03a7b06a7703a7306a6d06a6c03a6103a6003a4b05a4a03a4905a4705a4603a4303a4105a3705a3606a35049260987f0887b09877088730286d018610584f0584b05847058430583f0283d0583b01839058370283505833018310382f0682b06827038230481507c6f05c6b07c6705c630db6f0ab6e0fb6b01b6a0fb6701b660db630ab6203b4b03b4a06a6f03a6b06a6703a6305a4f05a4e03a4b03a4305a4205a3f05a3d049260986f0886b09867088630584f0784b07847058430983f0283d0883b01839098370283508833018310382f0682b06827038230481501e7a0ae7206c7f06c7e06c7b01c7a06c7701c7606c730ac7206c6d06c6c06c61e846007b7f05b7b07b7705b7307b6d05b6103b4f03b4e03b4d06a7f03a7b06a7703a7306a6d03a6105a4f05a4e05a4d05a3f05a3e03a3b03a3903a3305a3203a31049260987f0887b09877088730286d018610684f0284d0684b01849068470284506843018410583f0783b07837058330382f0682b06827038230481501d6a0ad62f536ff436bf2367f0363ef35d05b51ed26f0ba6beb2670ba6306a5d03a51e923f0ba3be72370ba33049260986f0986b09867098630285d018510983f0983b09837098330982f0982b09827098230481501d7f01d7e05d7d01d7701d7501d7301d7201c7701c7601c7501c5f05c5e01c5d01b7f01b7b01b7701b7305b5f05b5b05b5705b5301b4f01b4d01b4b03b4901b4706b4501b4301b410197e019760595e0595c059560d9540194e0194c019460d9440393e069360187f0187b01877018730185f0185b01857018530184f0184d0184b01849018470184501843018410183f0183b0183701833018190181505c6f05c6d01c6b01c6a01c6701c6605c6507b6f07b6e01b4f01b4e0aa6f01a6b01a670aa6305a4f05a4b05a4705a430ba3f06a3d0ba3b03a390ba3706a350ba3303a310186f0186b01867018630584f0184b05847018430983f0283d0183b01839098370283501833018310982f0182b098270182305d7f05d7d01d7b01d7a01d7701d7605d7505c7f07c7e05c7d01c5f01c5e01c5d0ab7f01b7b01b770ab7305b5f05b5b05b5705b5305b4f05b4d05b4b03b4905b4706b4505b4303b410a97e019760595e059560594e0594c05946e41440393e069360187f0187b01877018730585f0185b05857018530584f0284d0184b01849058470284501843018410983f0183b0983701833018190281507c6f07c6e07c6b01c6a07c6701c6607c630ac6207b6f05b6b0db6a07b6707b6605b630ba6f0ba6b0ba670ba6307a4f06a4d07a4b03a4907a4706a4507a4303a4105a3f07a3b07a3705a330986f0d86b098670d8630784f0284d0784b01849078470284507843018410583f0783b07837058330982f0b82b098270b82307c6fe546b07c67e34630bb6f0bb6b0bb670bb630bb4f07b4b07b470bb430a96e019660594ee21460393e069360986f0e86b098670e8630984f0784b078470e8430983f0b83b098370b833018190281501c6301c6201b6b01b6701b6301b4f01b4d01a6f01a6b01a6701a630fa4f06a4d0ba4b03a490fa4706a450ba4303a4105a3f05a3b05a3705a330186f0186b01867018630184f0184d0184b01849018470184501843018410183f0183b01837018330182f0182b018270182301e7201d6d01c7f01c7b01c7701c7301c5f01c5d01c5b05c5901c5705c5501c5301c5101b7f01b7e01b7b01b7a01b7701b7601b7301b7201b5f01b5e01b5d01b5c01b5b01b5a04b5904b5801b5701b5604b55e035401b5301b5201b5101b5001a7f01a7b01a7701a7301a5f01a5d01a5b03a5901a5706a5501a5301a5105a4f05a4b05a4705a4304a3f04a3d04a3b03a3904a3706a3504a3303a310197e019560495404946049360187f0187b01877018730185f0185d0185b01859018570185501853018510184f0184b01847018430183f0183d0183b01839018370183501833018310182f0182b0182701823 18 262143 7 127 11 2047 20 1048575
def cc_60_8 : Nat → List (Nat × Nat) := unpackCursorV4 0x8245af8785e615b9ddd6ec9ece3ed89e52fab25d540b0f3956d627de04d0568d5990fd59efe03929a633e4b2a7928f9209903a6d86ecc0d19818046286f4411f863bd0887e096f40ad00002b 0x1d6f00eb6812dbc096da05b5f00dad816d4c254de06a6d05d3580e9a4254ce06a6505d3180e984154be01a5b00d2b82a94c0b47e05a3b02d1b8168cc032ac0493e04c3780a1b4030d60186904c3380a194030c60186100c2f80616c030ae0185302c1f8060ec0b06e0183304c178060ac1304e0182302e3f8071ec038ee05c73026378131b4098d605c6902633817194098c604c6102e2e816dfc156fc05b7d055be006dec036f401b7700dbb016dd4036e805b7302db9012dbc096dc04b6d025b6012dac096d405b6902db4012d9c096cc05b658f1b2012d8c096c404b61025b0016d74154fe01a7b00d3b82a9cc094de04a6d0253580e9a4094ce06a650253180e9840b49e05a4b02d2381690c0b47e05a3d02d1d80e8e40b46e06a3502d1980e8c4032ec01966024a70061fc030f60187700c398121bc050da0186b00c3481219c050ca0186300c3081613c030960584700c218160fc0507a0183b00c1c8160dc0506a0183300c188260bc030560982700c118075bc03ada07b6f03db683edac0b6d207b6703db283ed8c0b6c207b5f00dad806d5c156a603a6301d3081a97c034ae03a530351f80e8ec0d46e03a3304c3780a1b4030d60186904c3380a194030c60186100c2f80616c030ae0185304c1f8060ec0f06e0183301c178060ac0d04e018230363f82b1f8038f601c7a00e3b8071d80d8e606c72026378131b8098da04c6c026358131a80d8d206c68026338131980d8cb1c46402631813188098c204c6001e2e81edfc036f601b77055b9812dbc096da04b6b02db4812d9c0f6ca04b63025b081ad3c0d69a06b4b02da481ad1c1b68a06b4302da081a9fc034f601a7701d398129bc094da03a6b01d3481299c0d4ca03a6301d3080e9440d47e03a3b0351b80e8cc032ec019660249f0061fc030f60187700c398121bc050da0186b00c3481219c050ca0186300c3081a13c0509a0184b00c2481a11c0508a0184300c208260fc030760783700c1980e0bc030560682700c118075bc03ada01d6700eb281758c1f8d607c6907e3181f184038b60ac53025b7812db4076d603b69025b3812d94096c603b6102daf806d6c036ae05b5302da7816d0c094de04a6d01d3580e9a40d4ce06a6501d3180e9840d4be01a5b00d2b80e94c0d49e03a430251f80e8ec0b46e03a33024b78065b4032ce01965024af80655c0927e0493e0249b8164c80725e0492704c3780a1b4030d60186904c3380a194030c60186100c2f80616c030ae0185304c2780610c0b07e0183b02c1b8060cc0705e0182b0341380608c030360481700ebd82b5cc09ad607d69026b18135840b8fe01c7b00e3b8171cc098de04c6d026358171a4098ce05c65026318131840b8be05c5302dbf82adf8036f601b7a00dbb806dd80b6e605b72025b7812db8096da04b6c025b5812da80b6d205b68025b3812d980b6cb1a364025b1812d88096c204b6002daf832d780b6a605b5201da780ed380769a06a7f00d3d8069dc074e604a6f0253680e9ac074d204a670353280e98c074c206a5f01d2980e92c0b49403a4902d238169180748603a4102d1b8168d80d46a0197a00cbb8065d8032ce0196600cb281253c0929c0494702ca10124fc0927a049370249a80e4bc0924e0187f00c3d8061dc030e60486f014368061ac030d2048670143280618c030c20985f00c2981613c030960584700c218160fc0507a0183b00c1c8160dc0506a0183300c1880e0bc030560682700c1180606c0902e01c6b0563181316c198b204c530262882adbc036d601b67055b1812d7c096ba04b5b02dac812d5e3e6aa04b53025a8836d3e3a6860aa6f00d3580699c154c604a5f0252e81296c074b204a570352a81294c074a31b24f05d21c648fc174760da3705d198065a8032ce0196600cab806558032aa0493f0249f0124dd9e2640492f024938061bc030d60186700c3181217c050ba0185b00c2c81215c050aa0185300c2882613c030860983f00c1d8260dc030660982f00c1582609c030460181b0240b8071bc038dc01c6b00e3500719c038cc01c6300e31006dbc036d601b6a00db3806d98036c601a6f00d3580699c034c607a4f0352681e92c0749207a470352281e90c0748205a3f03d1d81e8dc0b4660186f00c3580619c030c60184f00c2680612c030920184700c2280610c030820183f00c1d8060dc030660182f00c1580609c0304601c6f00e3580719c038c601b6f00db5806d9c036c60bb4f05da582ed1c1768601a6e00cb301653a2e28c0393e0349b0061bc030d60186700c3180613c030960184700c218060fc030760183700c198060640302a01d6f00eb700759c03ac601d6200e3580718c0f8b607c5903e2981f144036de01b6b00db5006d9c036cc01b6300dab806d58036aa07b4f03da7016d0c0f68401a6f00d3580699c034c607a5f0352e81e96c074b207a570352a81e94c074a207a4f03d218168fc0f47607a3702d198065bc032ce0495f024ae81255c092aa0493f0249e8124dc0926a0492f024938061bc030d60186700c3180617c030ba0185b00c2c80615c030aa0185300c2880613c030860183f00c1d8060dc030660182f00c1580609c030460181b00c0b8075bc03adc01b6f00db5806d9c036b601b5900d378069ac034ce01a630952f81a974174b603a590952b81a954174a603a5102d1f81e8ec0f46e05a3300cb70061bc030d60186700c3180617c030ba0185b00c2c80615c030aa0185300c288060fc030760183700c198060bc030560182700c118071fc038fc0cc7d8a23e0071ec038f401c7900e3c0071dc038ec01c7500e3a0071cc038e407c7103e380071bc038dc01c6b00e3500719c038cc01c6300e31017174036fe01b7e03dbe81edf0036f601b7900dbb806dd4036e601b7202db8816dc0036de01b6b00db3806d8c0b6a201a7f0353e8069ec034f201a7700d3a8069cc074e201a6f00d3580699c034c607a4f0352682e92c074920ca470352281e90c0748205a3f03d1d81e8dc0b4660197e00cb70061fc030fa0187b00c3c8061dc030ea0187300c388061bc030d60186700c3180613c0309a0184b00c2480611c0308a0184300c208060fc030760183700c198060bc030560182700c118075bc03adc01b6b00db3806d8c036ae01b5500d378069ac034ce01a630952f81a974174b603a590952b81a954174a603a5102d1f8168ec0b46e05a3300c378061ac030ce0186300c2f806174030b60185900c2b806154030a60185100c1f8060ec0306e0183300c178060ac0304e0182300e3f8071f80b8fa07c7c00e3d8071e4038ee01c7500e398071c80b8e205c7000e378071ac038ce01c6302e2e806dfc036fc05b7d891be006dec036f401b7900dbc006ddc036ec01b7500dba006dcc036e405b7102db8006dbc036dc05b6d055b6006dac036d401b6700db3006d94036c801b6300db1016d74034fe06a7d00d3d8069e4034ee01a7500d3980e9c4034de01a6b00d3380698c0b49e05a4b02d2381690c0b47e05a3d02d1d80e8e40b46e06a3502d1980e8c4032fc0196e0249b0124d0030fe0187d00c3d8061e4030ee0187500c398061c4030de0186b00c3380618c0309e0184b00c2380610c0307e0183d00c1d8060e40306e0183500c198060c40305e0182b00c1380608c03ade01d6e00db7806dac036ce01b6303daf81ed741f6b605b5903dab81ed541f6a605b5100d378069ac034ce01a5b00d2c81a8fc0747606a3701d198061bc030d60186700c3180617c030ba0185b00c2c80615c030aa0185300c288060fc030760183700c198060bc030560182700c118071fc038fc06c7d8823e0071ec038f401c7900e3c0071dc038ec01c7500e3a0071cc038e406c71036380071bc038dc01c6b00e3500719c038cc01c6300e3100f174036fe07b7d00dbd806de4036ee01b7500db9816dc4036de01b6b00db3806d8c0d69e06b4d035a5816d240d68e0db45035a1816d04034fe01a7e0353e81a9f0034f601a7900d3b8069d4034e601a7201d3880e9c0034de01a6b00d3380698c074a206a3f01d1d81a8dc074660197e00cb70061fc030fa0187b00c3c8061dc030ea0187300c388061bc030d60186700c3180613c0309a0184b00c2480611c0308a0184300c208060fc030760183700c198060bc030560182700c118075bc03adc01d6700eb1807588038d601c6307e2d81f1641f8a607c5100db7806dac036ce01b6300daf806d74036b601b5900dab806d54076a603b5102da7816d0c034de01a6b00d3380698c0d4be06a5d00d2d806964034ae01a5500d298069440d49e03a4300d1f80e8ec0b46e03a3300cb780659c092be0495d024ab8125540927e0493701c9781249c030de0186b00c3380618c030be0185d00c2d806164030ae0185500c298061440309e0184300c1f8060ec0306e0183300c178060ac0304e0182300c0d80605c03af601d7900eb981f5c403ad601d6300e3f8171f4038f601c7900e3b8071d4038e605c7100e378071ac038ce01c6302e2f81714c036fe01b7e02dbec38df0036f601b7a00dbc806de0036ee01b7600dba806dd0036e601b7202db8816dc0036de01b6e00db5806da8036ce01b6600db1806d880b6be0cb5e02da9816d480769e03b4e01da68069fc0d4fa01a7b00d3c8069dc034ea01a7301d388069bc034d601a6700d3181a97c074a603a4b02d2500e9240b48e05a4601d2180e9040b46e05a360351a8065fc032fc0497d00cb78065b8032c40494f024a38124fc0927a049370249a80e4bc0924e0187f00c3e8061ec030f20187700c3a8061cc030e20186f00c3580619c030c60185f00c2980613c030960184700c218060fc0307a0183b00c1c8060dc0306a0183300c188060bc030560182700c1180606c0302e01d6b00eb18071bc038d601c6700e3181f17c0b8a601b6f00db7006d9c036c601b6203daf81ed780f6a607b5200da7806d380769603b4a00da3806d180368601b4200d378069ac034ce01a630352f80e94c0b49e03a4b00d2380e90c0b47e05a3d00d1d8068e40346e01a3500d198068c4032de0196e00cb38065880929e049470249f8124f40926e0493501c9781249c030de0186b00c3380618c030be0185300c2780612c0308e0184300c1f8060f4030760183900c1b8060d4030660183100c178060ac0304e0182300c0d80605c03af601d7900eb981f5c403ad601d6300e3f8071f80d8fa06c7c00e3d8071e8038f201c7800e3b8071d8038ea01c7400e398071c80d8e30c47000e378071b8038d601c6a00e33807198038c601c620362f81b1780d8a60cc5200dbf81edf4036f601b7900dbb806dd4036e605b7100db7806dac036ce01b6303daf816d4c0769e03b4e01da68069fc0d4fa01a7b00d3c8069dc034ea01a7301d388069bc034d601a6700d3181a97c074a605a4f02d270169340b47e05a3e01d1d80e8e40746605a3201d188065fc032fc0497d00cb78065b8032c40494f024a681251c0928a0493f0249b80e4bc0924e0187f00c3e8061ec030f20187700c3a8061cc030e20186f00c3580619c030c60185f00c2980613c0309a0184b00c2480611c0308a0184300c208060fc030760183700c198060bc030560182700c1180606c0302e01c6b00e3480718c198c201c5b00e29806dbe2a6da01b6b00db4806d9c036ca01b6302db0806d7c036b601b5700da9c4cd3e2268601a6f035368069ac034d201a6700d3280698c074c201a5f00d2d80695c034a70f24f05d21c348fc174770b23705d198065bc032dc0496d00caf806578032a40493f0249b8124bc0924e0186f00c368061ac030d20186700c3280618c030c20185f00c2d80615c030a60184f00c218060fc030760183700c198060bc030560182700c1180606c0302e04c6f026370071ac038d401c6700e3301f18c098c407b6f03db7006dac036ce05b63055b102a9bc034d601a670553181e93c0d49a07a4b01d2481e91c0d48a07a4301d208168fc1747a07a3b03d1b81e8d40b4660594e02c9f0061bc030d60186700c3181e13c0509a0184b00c2481e11c0508a0184300c208160fc030760783700c198260bc030560982700c11806d7c036b601b5700da980697c034b601a5700d298228fc1147608a370451980617c030b60185700c298060fc030760183700c198060bc030560182700c1182ad7c036b601b57055a982a97c034b601a570552982e8fc174760ba3705d1980a17c030b6018570142980a0fc05076028370141980a0bc05056028270141182b1bc038d601c670563182adbc036d601b67055b182ed3c176960bb4705da1806999aa49c0496e02ca74245180727c0693600c378061ac030ce0186304c2780612c1308e0184304c1f8060ec1306e0183300c0cc200600502b0701400ebd0075c8038fe01c7e02e3e8071dc038ea01c7300e39013174098a201b7700dbb006dd4036ba04b5c00da8806d400369e05b4e00da68069fc034f601a7700d39812974074a205a4f02d2581691c0b48601a3f00d1e8068ec0747201a370351a8068cc034620187f00c3d8061dc030e60185d00c2880613c030960184700c218060fc0307a0183b00c1c8060dc0306a0183300c188060bc030560182700c118075e809ae405c7f02e3e8071ec038f401c7700e3b0171d4098ba04c5102dbf81edf80b6fa05b6d03db6012d74096b804b51025a8006d3c0369c01b4d0553f8069ec034ee0aa730252e80e9440b49e05a4b02d2381690c0b47e05a3d02d1d80e8e40b46e06a3502d1980e8c4030fe0187b00c3b8061cc050ba0185102c2780612c0b08e0184302c1f80a0f4030760183902c1b80a0d4030660183104c178060ac1304e0182301f3f80f9f807cfa01c7a026390131a8098d004c620263001edfc036f601b77055b981adbc0d6da06b6b02db481ad9c0f6ca06b6302db0812d340968201a7b00d3d00e9e4034ee01a7601d3980e9c4034ce01a6600d328129340748206a3f01d1d81a8dc074660187f00c3d8061dc030e60686f014368061ac030d2068670143280618c030c20284d00c208260fc030760783700c1980e0bc030560682700c118079fc03cfc01e7d00e3d0071e0038e404c7000e35007188036fe07b7d00dbd806de4036ee01b7500db9816dc4036de01b6b00db3806d8c0969a04b4100d3f8069f80d4fa01a6f00d370069ac034d201a6300d3100e9840949a03a410351f80e8ec0d46e03a3300cbf0125f0030fe0187d00c3d8061e4030ee0187500c398061c4030de0186b00c3380618c0309a0184100c1f8060ec0306e0183300c178060ac0304e0182300ebd0135c80b8fe05c7b02e3b8171cc098ba04c5102dbf82adf80b6f601b7a02dbb806dd80b6e605b72025ae812d70096a204b5001da780ed380769a06a7f01d3d81a9dc074e604a5d01d2880e92c0b49403a4902d238169180748603a4102d1b8168d80d46a0987f0443d8261dc110e60285d00c2881613c0b0960584702c218160fc0507a0583b00c1c8160dc0506a0583300c1880e0bc0d0560682701c118071a8098c407b6f829b581ed9e086c604b4d025a0c0c9bc174d70226705d31812934074830123f03d1d81e8dc174660986f04c3582619c130c60284d00c208260fc0f0760783704c198260bc130560982704c118175bc0badc01b6b00db3816d8c036ae01b55055378069ac034ce0aa6305d2f81a974174b603a5905d2b81a954174a603a5102d1f81e8ec0f46e05a3300c378061ac030ce0186304c2f80a174030b60185904c2b80a154030a60185102c1f8060ec0f06e0183304c178060ac1304e01823 19 524287 7 127 11 2047 21 2097151
def cc_60_9 : Nat → List (Nat × Nat) := unpackCursorV4 0x91e31193561d2ac22307f898f9aade41eba1cd6caf2d3ab5979fb0dc35cc9ea9ff53bb0a60ad4827e84384fc581da3d353c264eb0b9a094ccd21df83e0b471558bf4712ba6165e4147080051 0xf6bf4035b03dabcfcd4c074be03a5b01d2b80e94c0747e03a3b01d1b80e8cc110be0885b0442b82214c1107e0783b03c1b8220cc0705e0382b01c1380e08c03ad601d6300e378071b80b8da01c6700e3280718c038c405c5f02e29806d9c036cc01b6500daf81ed78036a601b5200da7816d380369a01a6f00d3580699c034c603a5f00d2980e93c0749603a4701d218068fc0347a01a3b01d1c8068dc0746a01a3300d188065bc032d60196700cb181257c092a60494f024a581251c092860193f00c9e8064ec09272019370249a8064cc032620392701c918061bc030d60186700c3180617c030a60184f00c2580611c030860183f00c1e8060ec030720183700c1a8060cc030620182f00c1580609c030460181f00c0d80605c0302601d6b03eb18171bc0b8da01c6b00e3500719c038cc05c6502e2f81714c0b6de07b6e02db6816d7c0f6bc05b5302da9006d3c0369c01b4d01d378069ac034ce03a6301d2f80e94c0749e03a4b01d2380e90c0747e03a3d01d1d80e8e40746e03a3501d1980e8c4092de0196b00cb381258c092be04953024a781252c0928e049430249f8124f409276049390249b8124d4092660493101c9380e48c030de0186b00c3380618c0f0be0185302c2780612c0b08e0184302c1f80a0f4030760183902c1b80a0d4030660183101c178060ac0704e018230240f80606c0902e0181303e2d81f14c0f6bf3d35b03dabcf0d4c0f69e07b4301d2f80e96c074ae03a5301d2780e90c0747e03a3b01d1b80e8cc092be0495b024ab81254c0929e049430249f8124ec0926e0493301c9380e48c110be0885b0442b82214c0f09e078430441f81e0ec0f06e0883301c1780e0ac0704e038230240f81206c0902e0481303eb581f58c0f8df4446b03e33d0918c0f8be07c5301db780edac076ce03b6301daf80ed74076aa03b4f01da580ed1c0768603a6f0553700e9ac034d403a6700d3300e98c074c403a5f0352f00e9740749e05a4e01d2580e9280748f4124601d2180e908172de0b96705ca781e51c0727e0393701c9780e4b4072553e12801c9380e4980924b3b124044378221ac110ce0886303c2f81e14c1109e0784b03c2382210c0707e0383b01c1b80e0cc0705e0282d01c158060a40704e0282501c11806084110360881703eb781f5b803ad601d6a00eb38075980bac605d6202db7806dac036ce05b6301dad80ed640d4de01a6b00d3380e98c0d4ae06a5501d1d8168dc074660186f00c3580619c030c60f85f0142e80616c030b20f8570142a80614c030a20583f00c1d8160dc030660382f00c1581a09c0304607e7e00ebd0171fc038f601c7702e398171a40b8ca05b7f055bf006dec036f401b7700dbb016dcc0b6e405b6902db4016d96726c803b4f01da700ed340d4fe01a7b00d3b80e9cc074d206a6501d258169280749205a4702d2300e90c0748205a3702d1b01a8d4030fe0187b00c3b8061cc030d20286502c2780612c0b08e0184302c1f80a0f4030760183902c1b80a0d4030660183101c178060ac0d04e0182300eb580758c038de01c6e00e3580718c038c407c5f03e2f01714c0b8a401b6f00db5806d9c036c605b5f02da9806d3c0369a03b4b01da4806d1c0368a01b4300da08069bc034d601a6700d3181a97c074a601a4f00d2680692c0349206a470352280690c0348201a3f01d1d8168dc074660196f00cb383e53c0929a0f947024a28164fc0b26e0392f034938061bc030d60186700c3180617c030a60184f00c2680612c030920184700c2280610c030820183f00c1d8060dc030660182f00c1580609c030460181b00c0b8079f803ce601e7200eb781f5b803ada01c7f00e3d8071dc038e605c6f02e3180717c038ba01c5b02e2c80715c0b8aa01c5300e28806dfc036fc01b7b00dbd006ddc036ec01b7300db9016dbc0f6dc05b6302db1006d7c036bc01b5d00dae006d6c036b405b5902dac006d5c036ac05b559b9aa006d4c036a401b5100da800ed3c0769c03b4d00d3f8069ec034ee01a730353780e98c034be01a5d00d2d80e964034ae06a5500d298069440749605a4a01d2481691c0b48c03a4301d208168dc0b46c06a3500cbf8065dc032be0195d00cab8125540b29e0594702c9f8124f40b26e0493501c9781a49c030fe0187b00c3b8061cc030de0186300c2f806174030b60185900c2b806154030a60185100c2780612c0308e0184300c1f8060f4030760183900c1b8060d4030660183100c178060ac0304e0182300c0d80605c03ade01d6d00eb58075a403ace01d6500eb1807584076c603b6100daf806d6c036ae01b530353781a9b4034be01a5b00d2b80694c0747603a3902d1b80e8cc074620186f00c368061ac030d20186700c3280618c030c20185f00c2d80615c030a60183f00c1d8060dc030660182f00c1580609c0304601e7d00eb10171f40b8e201c6f00e3580719c038c605b7d9a9be016dc40b6e001b6f00db7006dac036d401b6700db3006d8c036c403b4f01da700ed340d4fa06a7c01d3880e9c0034de01a6b00d3380698c0749605a4a01d2481691c0b48c03a4301d208168dc0b46c06a3500c3e8061c4030de0186b00c3380618c0309e0184b00c2380610c0307e0183d00c1d8060e40306e0183500c198060c40305e0182b00c1380608c03ad605d6300e3580719c0b8c601c5f02e29816dbc156dc01b6b00db3816d8c0b6c405b5f03daf016d4c0b6a405b4f03da7016d340d4de01a6b00d3380e98c0d4be03a530352780e92c0749206a4701d2180e9040b46e05a360351a82a5bc032ce0794f03ca38164fc0927a059370249a80e4bc0d24e0186f00c3580619c030c60785f00c2981e13c030960784700c218160fc0507a0183b02c1b80a0d4030660382f00c1581a09c030460181b07c0b8075ac0bac601c6b00e3500719c038cc05c6300e2f8071780b8a601c5202db7806dac036ce05b6302daf816d4c0b69e05b4d01da580ed240b68e05b4502da180ed040d4de01a6b00d3380e98c0d4be03a530352781a9340749603a490352381a9140748603a4102d1f80e8ec0b47405a3702d1b00e8cc152de0196707ca78125341f28e0494502c9f8164dc0725e0692700c378061ac030ce0186303c2f80614c1f09e0284d00c258061241f08e0284500c218061040b07e0183b02c1b8060cc0705e0182b0341380608c030360f81700f3d8079e803cec01d6f00eb70075b40b8fe01c7b00e3b8171cc0b8de05c6302e2f8171740b8b605c5a02e2c8171600b8ae07c5602e2accd1500b8a605c5102dbf82adf8036f601b7a00dbb806dd80b6e605b7202db781edb80b6c605b6202daf81ed780b6ba07b5c02dad816d680b6b205b5802dab81ed580b6ab3235402da9816d480b6a205b5001da780ed380769a06a7f00d3d8069dc074e606a6f01d3181a97c0d4ba03a5b01d2c81a95c0d4aa03a5301d2880e92c0b49403a4902d238169180748603a4102d1b8168d80d46a0a97f00cbb81e57c092ba07957024aa81653c0b28e0593f0249e8164dc0926a0392f034938061fc030f60187700c3981e1bc030c60785f0142e80616c030b2078570142a80614c030a20584f00c2581611c030860583f0141e8060ec03072058370141a8060cc030620382f00c1581a09c030460181b07c0bce15be6cad73456798ab18171bc0b8d605c6702e3181717c0b8b605c5702e29816dbc156dc05b6b00db5016d9c036cc05b6302db1016d7c196bc05b5b02dab816d4c0b6a403b4f01da700ed340d4de03a6b0353380e98c0d4be03a5b0352b80e94c0749605a4a01d2481691c0b48c03a4301d208168dc0b46c06a358c8b782e5ae1a2ce0b963808af82e56dd22ae0b95302ca781652c0b28e0594302c9f8124f40b276059370249a8164cc0725e0692b0349380e48d2e0de0886b3f83382218ce00be0885b3202b82214c0b09e0584b02c2381610c0b07e0283d02c1d8060e40b06e0283502c198060c40705e0682b0341380e08c1703e0881b0200b82204c03ade01d6d00eb58075a403ace01d6500eb18075840d6de06b6d00daf806d6c036ae01b5301d3180e984034be01a5b00d2b80694c0747e05a3e01d1b80e8cc074640186f00c368061ac030d20186700c3280618c030c20185f00c2d80615c030a60183f00c1d8060dc030660182f00c1580609c0304601e7d00eb101f1f40f8f805c7102e380071bc038d601c6700e3180edf4076e201b6f00db5806d9c036c603b4f02da700ed340768e03b4501da180ed08074fb2f27c01d3880e9c0034de01a6e00d358069a8034ce01a6600d318069880748e06a4601d2280e8fc0747c03a3d00c3e8061c4030de0186b00c3380618c0309e0184b00c2380610c0307e0183b00c1b8060cc0305e0182d00c158060a40304e0182500c118060841bade07d6b972b381f58c0f8de05c6b03e3381718c0f8be05c5b03e2b81714c076de03b6b01db380ed8c076be03b5b01dab80ed4c0769e05b4e01da680ed1c0768a03b4301da100e9bc154dc03a6b00d3500e99c034cc03a6301d3100e97c194bc03a5b01d2b80e94c074a403a470352300e9140747e03a3e01d1e82e5bc172d60b96705cb181e57c172b60b95703ca981653c0f2960794702ca180e4fc072760393701c9980e4bc0725a0392b01c93812494072460886f0443582219c110c60785f0442d82215c0f0a60584f03c2581e11c0b0860383f01c1d80e0dc070660382f0141680e0ac03052038270141280e08c030420881f0440d82205c1102601d6200e378071ac038ce01c6300db7806db8036d601b6a00db3806d98036c601b6201da580ed28034de01a6b00d3380698c0b49e05a4e01d2580e9240748605a4201d208168fc0b47a0186f00c3580619c030c60184f00c2580611c030860183f00c1e8060ec030720183700c1a8060cc030620182f00c1580609c0304601e7d00eb101b1f40d8f806c71962380071bc038dc01c6b00e3500719c038cc01c6300e3101edf40b6e201b6f00db5806d9c036c603b4f01da700ed340d4fa03a7100d378069ac034ce01a6302d278169380b49a05a3f02d1f00e8ec0747203a3302d1900e8c4030fa0187100c378061ac030ce0186300c27806134030960184900c23806114030860184100c1f8060ec0306e0183300c178060ac0304e0182306eb781f5ae56ace07d630363781b1b80d8d601c6a036338071980d8c60ac620362f81b1780d8b606c57036298331480f6de05b6b03db3816d8c0f6be05b5b03dab816d4c0769e03b4e01da681a9bc074d606a6701d3181a97c074b606a5701d2981693c0b49c05a4d02d1f8168f80747603a3901d198168c8074620d96f05cb5c2c59c172c60795f05cadb9c55c0f2a60694f024a681a52c0d28e04945034a18164fc0f2760793702c9980e4bc0d2560692701c918361bc110d67d0670443181e17c110b66205703c2981a13c0509a0684b00c2481a11c0508a0684300c208160fc0f0760783702c1980e0bc0d0560682701c1182e07c11036030170440981f5bc0fadc01d6b00eb500759c03acc03d6301eb10071a80b6de01b6b00db3816d8c0b6b605b5901d378069ac034ce03a6301d2d80e9640747e03a3b01d1b8061bc030d60186700c3182217c050ba0185b00c2c82215c050aa0185300c288160fc030760583700c1980e0bc030560382700c1181f9f803af405c7f00e3d8071dc0b8e605c6902e3280edfc036f601b7701db980eda4076ca03b4f01da680ed2c0769403b4702da300ed14074fe0aa7e01d3e82a9f0034f601a7a00d3b8069d8074ea01a7401d3980e9c8074d203a6801d32ca49900749e05a4e01d2680e8fc0747c03a3d00c3f8061ec030ee0187300c3480a1940b09e0184b02c2380610c0707e0183b01c1b8060cc0705e0282d00c158060a40704e0282500c1180608403ad601d6300e378071b8038d601c6300e3101f17c0f8bc03c5301e29006dbc036d601b6700db1816d7c0b6a601b4f00da6816d2c0b69201b4700da2806d0c0368201a6f00d3580699c034c603a5f01d2980693c0349a03a4b01d2480691c0348a01a4300d2080e8fc0747603a3700d198065bc032ce0b94f024a682e51c0928a0593f02c9b80e4bc0724e0186f00c3580619c030c60185f00c2980613c0309a0184b00c2480611c0308a0184300c208060fc030760183700c198060bc030560182700c1180606c0302e01e7e00f398079c803ade07d6e00eb68071fc038f601c7700e398171bc0b8c601c5f00e2e80716c0b8b201c5702e2a80714c038a201b7f00dbd806ddc036e603b6f01db1806d7c036ba01b5b01dac806d5c076aa01b5300da880ed3c0769a03b4b01da500ed1c0b68c03b4500d3f8069f8034f601a7a00d3b8069d8034e601a7201d3781e9b8074da07a6c01d3280e98c074c401a5f00d2f006974034b801a5b00d2d00e964074b001a5700d2b00e9564e4a801a5300d29006944034a003a4f02d2700e9340747e03a3e01d1e8065fc032ee0195f00cae80655c092aa0594f02ca380e4fc0726e0392f01c9680e49c0924a0187f00c3d8061dc030e60186f00c3180617c030ba0185b00c2c80615c030aa0185300c2880613c030960184700c218060fc030760183700c198060bc0305a0182b00c1480609c0304a0182300c1080606c0302e01d6f00eb580759c03ac603b6f03db700edb4076ce03b6501db180ed88036be01b5b00dab806d4c074ce07a6601d3280697c034b601a5a00d2b806958034a603a3f01d1f00e8f4030de0186b00c3380618c030be0185b00c2b80614c0307e0183b00c1b8060cc0305e0182b00c1480609c030460182100eb78075b403ad601d6900eb380759403ac601d6102db1816d84036be01b5b00dab806d4c074c603a6100d2f80696c034ae01a5301d1f80e8ec0746e0186f00c368061ac030d20186700c3280618c030c20185f00c2d80615c030a60183f00c1d8060dc030660182f00c1580609c0304601e7d00eb10171f64a8f805c7102e380071bc038d601c6700e3180edf40d6f803b7101db8006dbc036d601b6700db180ed3c0769a03b4b01da500ed1c0b68c03b4501d3ec909f0074e203a7000d378069b8074da0aa6c00d358069a8034ce01a6600d32806990034c601a6201d2e8329700749e05a4e01d2680e8fc0747c03a3d00c3e8061c4030de0186b00c3380618c0309e0184b00c2380610c0307e0183b00c1b8060cc0305e0182d00c158060a40304e0182500c1180608403ad601d6a00eb300f58c038d601c6a00e33807198078c601c5f00e2f00f14c038a405b6f00db5806d9c0b6c605b5f02da9816d3c0b69a05b4b02da4816d1c0b68a05b4302da080e9bc034d601a6701d3180e97c074a603a4f01d2680e92c0749203a4701d2280e90c0748203a3f01d1e80e8ec0747403a3702d1b00e8d4074660a96f00cb382e53c0929a0b947024a28164fc0b26e0392f01c938061bc030d60186700c3181e17c030a60884f0142680612c03092088470142280610c030820583f00c1d8160dc030660382f00c1580e09c030460181b0440b8079ec03cf401e7600eb78075b803ada05c7f00e3d8071dc0b8e605c6f02e3181717c0b8ba05c5b02e2c81715c0b8aa05c5302e2880edfc036f601b7701db980edbc076c603b5f01dae80ed6c076b203b5701daa80ed4c076a203b4f01da680ed2c0769403b4702da300ed14074fe0aa7e00d3d8069e8034ee01a7601d3980e9c8074de07a6e01d3180e988074be07a5e01d2e81e970074b603a5a01d2c80e960074ae07a5601d2ac88950074a603a5201d2880e9400749e05a4e01d2680e8fc0747c03a3d054bf8065dc0f2be0495d03cab8125540b29e0594701c9f80e4dc0725e0392d01c93812494030fe0187b00c3b8061cc0f0de0186303c2f80a174030b60185903c2b80a154030a60185102c2780612c0b08e0184301c1f8060ec0706e0183301c1780a0b4030560182901c1380a094030460182100c0d82205e50adf2656b91ab3c8558c0b8de05c6b02e3381718c0b8be05c5b02e2b81714c076de03b6b01db380ed8c076be03b5b01dab80ed4c0769e03b4d01da580ed280768e05b4601da280e9bc154dc03a6b00d3500e99c034cc03a6301d3100e97c194bc03a5b01d2b80e94c074a403a4f02d2700e9340747e03a3e01d1e82e5bc172d60b96705cb182e57c172b60b95705ca981653c0b2960594702ca180e4fc072760393701c9980e4bc0725a0392b01c93812494072460886f0443582219c110c60885f0442d82215c110a60584f02c2581611c0b0860383f01c1d80e0dc070660382f0141680e0ac03052038270141280e08c030420881f0440d82205c1102601d6f00eb680759c03aca07d6303e3581f1a40f8c607c6100e2d81f14c096de04b6e025b681ed7c0f6bc01b5b00dab816d4c156a407b4f02da181e9bc0d4da07a6b01d3481e99c0d4ca07a6301d3082a97c034b601a570552981e93c0f48605a3f03d1d81e8dc0b4660496f024b70065b4032d80196700cb2816588092be019570249f8124f80927a049370249a8164c80925e0492703c3780a1b4030d60186903c3380a194030c60186100c2f80616c030ae0185303c2780610c0b07e0183b03c1b8060cc1305e0182b04c1380608c0303604817 19 524287 7 127 11 2047 21 2097151
def cc_60_10 : Nat → List (Nat × Nat) := unpackCursorV4 0x7df65766797194d69d7c6514c609485de2b5a13d5643d5392b50e2b4cd414a12c4604142e3240e203e12d3a23f3633f333303082b2c93f29e2b2574722334203201828112f530b27d062500313100031 0x56b78075ac03ace0ad63056378071ac038ce0ac6306e2fda116c1b8af6645301db780edb4036d601b6a00db3806d98076ca03b5f01dad80ed5c076a603b4f01da580ed1c0768603a6f0353700e9b4074be0ca5e01d2d80e95c074a603a5201d278169380749603a4a01d23d949180748603a4200d1f8068f80347a0a96f00cb580659c152c60b95f05cad82e55c172a60b94f05ca582e51c172860393f01c9d80e4dc072660392f01c9680e4ac0724e0492501c918061bc030d60186700c3182217c030b60885700c2982213c030960884700c2180e0fc030760383700c1980e0bc0505a0182b01c150060a6c40500382701c1300a096be0480182300c1082207c030360881700c098079ec03ce601d7f00ebf0075ec03af401d7700ebb0075cc03ae403d6f01eb700f5b4038fe01c7e02e3e8071dc038ea01c7300e390171bc0b8c605c5f02e2e81716c0b8b205c5702e2a81714c0b8a201b7700dbb006dd4036de07b6e00db1806d88036be06b5e00dae81ad70036b601b5a00dac806d60036ae06b5600daa836d50036a601b5200da8806d400369e05b4e00da68069fc034f601a7700d3980e9a4074c603a6102d2780e92c0b48e03a4300d1f8068f40347603a3900d1b81a8d40346601a3100cbf8065dc0d2be0495d034ab8125540b29e0594700c9f8064f40326e0493501c9781a49c030fe0187b00c3b8061cc030de0186300c2f806174030b60185900c2b806154030a60185100c2780612c0308e0184300c1f8060f4030760183900c1b8060d4030660183100c178060ac0304e0182300c0d80605c0fade07d6e00eb58075a803ace01d66036b181b588038d607c6301e2d80f1640b8a603c5102db7806dac036ce05b6302daf816d74036b601b5902dab816d540b6a601b5102da7816d0c0d4de01a6b00d3380e98c0b4be03a5b01d2c80e94c074a205a4f01d218168fc0747605a3701d1982a5bc032ce0f95f024ae83e55c092aa0593f02c9b80e4bc0d24e0186f00c3580619c030c60f85f0142e80616c030b20f8570142a80614c030a20784f00c218160fc030760583700c1980e0bc030560682700c1180606c1f02e01e7b03f3981b5fc15afc01d7b00ebd0075dc03aec06d73036b900f5bc07adc03d6d02e3f8171f4038f601c7a00e3b8071d80b8ea05c6f02e3181717c0b8ba05c5b02e2c81715c0b8aa05c5302e28816dfc0f6fc05b7d02db781edb80b6da07b6c02db2816d8c0b6c405b5f035af016d740d6b805b5b02dad016d640b6b005b57035ab016d56b86a805b5302da9016d440b6a001b4f00da7006d340d4fe01a7b00d3b80e9cc074d203a6301d3081693c0749605a4701d218168fc0b47a03a3b01d1c8168dc0d46a03a3301d1882a5fc032ee0695f024ae81a55c092aa0594f02ca38164fc0927a059370249a80e4bc0d24e0187f00c3d8061dc030e60786f00c3181a17c050ba0185b00c2c81a15c050aa0185300c2881613c030960584700c218160fc0507a0183b00c1c8160dc0506a0183300c1880e0bc030560682700c1180606c1f02e07d6f03eb701f5ac03ad407d6700eb301f58c15ac407c6b03e3180f16c078b207c5301e2881edbc0b6d607b6702db181ad7c0d6bc06b5d03da781ed380b68607b420353780e9ac0d4ce03a630352f80e96c074b203a5301d2881a93c0748605a3f0351e80e8ec0d46e06a3501d198365bc1b2ce0795f024ae81e55c092aa0593f03c9b80e4bc0d24e0d86f0443583619c110c60785f0142e81e16c030b2078570142a81e14c030a20784f03c218160fc0f0760783702c1980e0bc0d0560682701c1182206c2902e07d6b03eb181b1bc158dc06c6b00e3501b19c038cc06c630363100f17c078bc03c5d03db7d74dac0f6cf5b36303daf81ed4c0d69e06b4d035a5816d240d68f5a345035a1816d040d4de03a6b0353380e98c074b203a5301d2881a8fc0747606a3701d19c6c5be1e2ce0694f024a681a51c0928ad613f03c9b80e4bc0d24e9906f04435a0c19c110c60785f03c2981a13c0509a0684b00c2481a11c0508a0684300c209500fc0f076078370441980e0bc0d0560682701c1182206c0a02e05d6f02eb7006dac036ce05b6300dab806d54074de01a6b00d3380e98c074be03a5d01d2d80e964074ae03a5501d2980e9440747e03a3b01d1b80e8cc030de0186b00c3380618c110be0285d00c2d806164110ae0285500c298061440b07e0183b03c1b8060cc0705e0182b01c1380608c0bcfe05e7e02f3e8071ec038f405c7900e3b8071d80b8e605c7100e33807198038ca03b7f00dbd806ddc076e603b6f01db680edac076d203b6701db280ed8c076c203b5d01da780ed2c0768e03b430553f0069d80f4dc07a6c03d335609900b49c07a4601d1f0061fc030f60187700c3981e1bc050da0186b00c3481e19c050ca0186300c3081613c030960784700c2180e0fc030760383700c198060a40504a01d7f00ebf0175f403aee01d7500eb98075c8038ee01c7600e3a80717c0b8bc01c5d00dbf806dec036ee01b7301db680ed7c076b603b5701da9806d3c0369a01b4b01da4806d1c0768a01b4300da08069f8034ec05a5e02d2b0069380349801a4606d2200e8f8030fe0187b00c3b8061cc030be0185b00c2b80614c0309e0184d00c258061240308e0184500c218061040307e0183b00c1b8060cc030520182500eb78075b40f6de07b6d00daf806d6c036a601a6f00d368069ac034d201a6700d3280e98c074c201a5f00d2d80695c034a603a3f01d1d80e8dc074660186f00c368061ac030d20186700c3280618c030c20185f00c2d80615c030a60183f00c1d8060dc030660182f00c1580609c0304601d6f025b7806d7c036b601b5301d3780e9ac074ce03a6300d2f80696c034ae01a5301d2680e8fc0747603a3701d198125b8092cc0195e00cab0164f80f26c0392e00c378061ac030ce0186300c2f80616c030ae0185300c1f8060ec0306e0183300c178060ac0304e0182300c0c80605403cfe01e7e00f3e8075c819ae001c7f00e3f01f1f4038de01c6e00e358071a4038c601c6202e30806dfc076fa01b7b00dbc806ddc036ea01b7301db8806dbc036d601b6700db180ed740769e03b4b01da380ed0c034fd5527c00d3b0069d0034dc01a6602d2701e9180747c0197eaa0be0061fc030fa0187b00c3c8061dc030ea0187300c388061bc030d60186700c3180613c030960184700c218060fc030760183700c198060a40304a05c6f00e3580719c0f6de07b6e00da7806d38074de01a6b00d3380e98c074ba03a4f01d2580e91c0748603a3f01d1e80e8ec0747203a3701d1a80e8cc074620186f00c3580619c030c60584f00c2581611c030860883f0141e8060ec03072088370141a8060cc030620382f00c1580e09c0304605d7f02ebe8075ec03af401d7700ebb0175d40b8fe07c7e02e3e80717c038bc01c5d01dbf806dec036ee03b7301db680ed7c076b603b5701da980ed3c0769a03b4b01da500ed240769003b4702da300ed140d68803b4301da082a9f8034ec05a5e02d2b0169380b49805a46a912200e8f8030fe0187b00c3b8061cc0b0be0185b02c2b80614c0b09e0284d00c258061240b08e0284500c218061040707e0183b01c1b8060cc030520282503e3781f1b80f8d601c6a03e338071980f8c60ac6203db7816dac0f6ce05b6301d3780e9ac074ce03a6301d2780e9340749603a4901d2380e9140748603a4101d1f80e8ec0747203a3701d1980e8c4110de0886b0443382218c0f09e0284d03c258061240f08e0284503c218061040b07e0783b03c1b8160cc0705e0382b01c1380e08eae8df5646ba9a33d4518c076de03b6b01db380ed8c076ba03b4f01da580ed1c076860aa6e00d3301693aa048c03a3e044378221ac110ce088630442782212c1108e0884301c1f80e0ec0706e0383300c1480a0940b8c605c6200db5816da4036ce05b6302db0806d3c0369a06a6f00d3580699c074c606a4f0352680e92c0749206a470352280e90c0748205a3f01d1d81a8dc074660186f00c3580619c030c60f84f0142680612c030920f8470142280610c030820583f00c1d81e0dc030660382f00c1581a09c0304605e7f02f3f0179f403af40ad7203eb55395a00fac407d6000dbd806de80b6f201b7700dbb016dcc0b6e201b6700db3006d940f6ba07b5c02da8816d400d4fe01a7b00d3b80e9cc0d4de06a6d01d3580e9a40d4ce06a6501d3180e9840d4ba03a4102d1f80e8ec0d46e03a3300c3f8061ec030ee0187303c3780a1b4030d60186903c3380a194030c6018610142e8061440b07e0183b03c1b8060cc0705e0182b0341380608c03cf401e7800f3902b9c0038fe01c7e02e3e8071dc038ea01c7300e390171b40b8c201b7700dbb006dd4036da0db6c00db0806d800369e05b4e00da68069fc034f601a7700d3981a9b4074a205a4f01d2581691c0748601a3f00d1e8068ec0747201a370351a8068cc034620187f00c3d8061dc030e60186d00c3080613c030960184700c218060fc0307a0183b00c1c8060dc0306a0183300c188060bc030560182700c118071ac038d401b6f00db7006dac036d201b6300db1016d840f69e07b4d00d378069ac034ce01a6301d2881a93c0d49a01a4b00d2480691c0348a01a4300d208168fc0747606a3701d198061bc030d60186700c3180613c0309a0184b00c2480611c0308a0184300c208060fc030760183700c198060bc030560182700c118075bc098d404c6200e2d007148094de01a5f00d2d80694c0f49a05a41024b780e5ac092ce0396300caf80656c032ae01953034a680e4c40b25e0392b0349380e48c030de0186b00c3380618c030be0185b00c2b80614c0309a0184100c178060ac0304e0182300c0f80606c0302e0181300f3f8079f803cfa01d7a00ebc0075ca96ae001d6a00eb1006dfc036fc07b7d00db7806db8036d601b6900db1806d880b6c207b5d02da88069fc0d4fa01a7b00d3c8069dc034ea01a7301d388069bc034d601a6700d3181a9740748205a3f01d1d81a8dc074660197ea50be0061fc030fa0187b00c3c8061dc030ea0187300c388061bc030d60186700c31806174030a20183f00c1d8060dc030660182f00c1580609c0304607c6303e31016dbc036d601b6700da1806d040d4de01a6b00d3380e98c0d49e06a4d01d2580e9240b48e05a4501d2180e9040b47e03a3b02d1b80e8cc030de0186b00c3380618c1f09e0284d00c258061241f08e0284500c218061040b07e0183b02c1b8060cc0705e0182b0341380608c03cf401e780573902b9c00b8fe05c7d00e3d8071e8038ee01c7602e3a8171b41b8d805c6102e30016dfc0f6fc05b7d02db6d20db00b6c205b6002dae832d700369e01b4e00da681a9fc034f601a7701d3981a9b4074a205a4f01d2581691c0748605a3f02d1e80e8ec0b47403a3901d1c0168dc0b46c06a350351a00e8cc074620187f00c3d8061dc030e60286d00c3081613c030960584700c218160fc0507a0183b00c1c8160dc0506a0183300c1880e0bc030560682700c1181f1bc158dc07c6b00e3501f19c038cc07c6303e3101edbc0f6dc05b6b03db3816d8c1b6c406a6f01d3581a99c074c606a4f0352680e92c0749206a470352280e90c0748205a3f0351e80e8ec0d46e06a3501d198361bc110d60d8670443181e13c0509a0784b00c2481e11c0508a0784300c208160fc0f0760783702c1980e0bc0d0560682701c118075a815ac54d36fa61b5d24d9e8e6c74635d02da881a9bc074d606a6701d3181a9740748206a3f01d1d81a8dc074669806f04435a0419c110c60285d00c289480fc110764d0370441980e0bc0d0560682701c118079ec03ce601d7f00ebf0175f403aee01d7500eb98075c80bade05d6300e3b8071d8038ea01c6f03e3700718c038c401c5f02e2f007174036fe01b7b00dbb806dcc076de03b6d01db280ed7c076b603b5701da9806d3c0369a01b4b01da4806d1c0768a01b4300da08069fc034fc01a7b00d3d0069dc034ec01a7300d3900e9bc0d4dc03a6d01d2f816978074ba05a5c01d2d80e968074ae05a5601d2a836950074a603a5200d278069380349a01a4c00d258069280749203a4800d238069180748a0da4400d218069080348201a4000cbf8065dc0b2be0595700ca78065340328e0494501c9f80e4dc0725e0392d01c955004a00724e0392602492cf4490030fe0187b00c3b8061cc030de0186300c2f80616c030ae0185300c27806134030960184900c23806114030860184100c1f8060ec0306e0183300c178060b4030560182900c13806094030460182100c0d80605c03ad607d6302e378171b4038d601c6a00e338071980b8ca03c6302e2f81714c0f6de07b6e00db5806da8036ce01b6601db180ed880d6be06b5e02da9816d480369e01b4e01da580ed280768e03b4601da1806d08074de01a6b00d3380e98c074be03a5d01d2a80e94c0749e03a4b01d2380e90c0747e03a3d01d1b80e8d4074660a96f00cb381653c0b28e0b93f0249e82e4dc0926a0392f01c938061bc030d60186700c3181e17c030a60584f00c2581611c030860883f0141e8060ec03072088370141a8060cc030620382f00c1580e09c030460181b0440b8079ec0fce605d7f02ebe8075ec03af401d7700ebb0175d40bade05d6302e3f81f1f80b8fa05c6f03e3701718c0b8c401c5f00e2f007174076fe01b7b00dbb80edcc076de03b6d01db280ed7c076b603b5701da980ed3c0769a03b4b01da480ed1c0768a03b4301da080e9fc154fc01a7b00d3d0069dc034ec03a7301d3900e9bc0d4dc03a6d01d2f816978074b603a5a01d2b816958074a603a5201d278169380749a05a4c01d2580e9280749203a4801d238169180748b4324401d2180e9080748203a40054bf8065dc0b2be0595702ca78125340b28e0494501c9f80e4dc0725e0392d01c954fc4a00724e0392602492cf0490030fe0187b00c3b8061cc0f0de0186302c2f80616c0b0ae0185302c2780a134030960184902c2380a114030860184101c1f8060ec0706e0183301c1780a0b4030560182901c1380a094030460182100c0d82205c0fad607d6303e3781f1b80f8d601c6a03e338071980f8c60ac620362f81b1780f8a606c5203db7816dac1b6d407b6703db3016d8c0f6be07b5e02da981ed480769e03b4e01da680e9bc074d603a6701d3180e97c074a603a4f01d2680e91c0748a03a4301d1f80e8ec0747203a3701d1980e8c4172de0b96703ca78125340f28e0494502c9f81e4dc0725e03927044378221ac110ce0886303c2f81e14c0f09e0284d03c258061240f08e0284503c218061040b07e0883d03c1d81e0dc0f06a0583301c1780e0ac0704e038230440d82205c038de01c6e02e3680719c038ca01c6300e31006d9c036cc01b6500da7816d380369a01a6f00d3580699c034c603a4f01d2580e91c0748601a3f00d1e8068ec0747201a3701d1a8068cc034620186f00c3580619c030c60184f00c2580611c030860183f00c1e8060ec030720183700c1a8060cc030620182f00c1580609c0304605c6f02e368071ac038d401c6700e330171940b6de07b6e02db6806d3c0369c01b4d01d378069ac034ce03a6301d2780e92c0748e03a4301d1f80e8f40747603a3901d1b80e8d40746603a3100c378061ac030ce0186302c2780612c0b08e0184302c1f80a0f4030760183902c1b80a0d4030660183101c178060ac0704e01823 20 1048575 8 255 11 2047 21 2097151
def cc_60_11 : Nat → List (Nat × Nat) := unpackCursorV4 0x9a77d946618f94d880798433d8162d7e5317a4417554f6d87d67167610615a7695584f4db7d49c3f46c3043b313fc3f3af4d327882c6612814522e531b17d1466b1271f0df480a33c0841f03c480003c 0x1f3f80f9f807cfa01d7b03eb981b5ac0fad206d63036b08171fc038f601c7702e398171bc0b8da05c6b02e3481719c0b8ca05c6302e3081717c0b8ba05c5502dbf82adf80b6fa0ab7c00dbd806de8036ee01b7602dba806dd00b6e605b7202db781adb80b6da06b6c02db5816da80b6d205b6802db381ad980b6cb7f36402db1816d880b6c205b6002daf832d780b6ba01a7b00d3d00e9e4034ee01a7601d3980e9c4034ce01a6600d3281a97c074a605a4f01d2581691c0748605a3f02d1e80e8ec0747205a370351a80e8cc074620a97f00cbb81a5bc092da06967024b281653c0b28e0593f0249e8164dc0926a0392f034938061fc030f60187700c3981a1bc050da0186b00c3481a19c050ca0186300c3081e17c030a60584f00c2581611c030860583f0141e8060ec03072058370141a8060cc030620382f00c1581a09c030460181b0840b80f5bc07adc03d6d056378071ac038ce0ac630362f81b16c198b206c570362981b144156de01b6b00db382ad8c0d6be06b5d035ad816d640d6af81355035a9816d441b69f8034b06da3df8d0c034d601a6a01d3480699c034cc03a6301d3080695c034ac01a550352780e92c0d48e03a430351f80e8ec0d46e03a33054b78065ac032ce0a963034af8125740d2b606957024aa81a54e0629e0b94b768a382e50db427e0b93b06c9b82e4cc0725e0692b0349380e48c030de0186b00c3380618c0d0be0285d00c2d8061640d0ae0285500c29806144e409e0184b3302380610cac07e0183b06c1b8060cc0705e0182b0341380608c1703e0181b0300b80604c03ad601d6300e378071b8038d601c6a00e33807198038c601c6202e2f817178038a601c5200db7806dac036ce01b6300daf816d4c0369e01b4b00da4806d0c0368201a6f00d3580699c034c603a5f01d2980e93c0749a03a4b01d2480e91c0748a03a4301d2080e8fc0747603a3701d198065bc032ce0b94f024a682e51c0928a0593f03c9b80e4bc0724e0186f00c3580619c030c60185f00c2980613c0309a0184b00c2480611c0308a0184300c208060fc030760183700c198060bc030560182700c1180606c0302e01e7b00f398075fc03afc01d7b00ebd0075dc03aec01d7300eb90175bc0badc05d6d00e3f8071ec038ee01c7302e3481718c0b8c201b7f00dbf00edf4036ee01b7500db9806dc8076de03b6301daf80ed74076b603b5901dab80ed54076a603b5101da780ed2c0768e03b4300d3b8069d8034ea01a6f03d3700698c034c401a5f03d2f0069740f4b801a5b00d2d006964034b001a570652b006956f84a801a5300d29006944034a001a4f02d2700692c0349401a4703d2300690c0348401a3f01d1f0068f4032fe0197703caf812574172ae0495502ca781e51c0727e0393700c978064b40324e0492500c3f8061ec030ee0187300c3780618c030be0185d00c2d806164030ae0185500c298061440309e0184b00c2380610c0307e0183b00c1b8060cc0305e0182d00c158060a40304e0182500c11806084030360181700ebf8075ec03aee01d7302eb68071f8038ec05c5e00dbf806df8076fa01b7700dba806dcc036e403b5f01dad80ed5c076a603b4901da28069dc034ec01a7500d2f816978034b601a5a00d2b816958034a601a5200d248069200348a07a4400d1f80e8f80347a0187f00c3d8061dc030e60185f00c2d80615c030a60184900c228060fc030760183700c198060bc0305a0182b00c1480609c0304a0182300c108075ac03ad401b6f00db5806d9c036c607b5f03dae806d6c036b201b5700daa806d4c036a201a6f00d3700699c034c601a6201d2980e9440747e03a3b01d1b80e8cc030de0186b00c3380618c030be0185d00c2d806164030ae0185500c298061440307e0183b00c1b8060cc0305e0182b00c1380608c03ade01d6b00eb380758c036de01b6b00db3806d8c056be01b5b00dab806d4c034de01a6e01d3680699c034ca01a6300d3100a97c054b602a570152980e8fc0747603a3701d1980659c032cc0196500caf80a578032b60195a00cab80a558032a60195200c9f8164f8032760193a00c9b81e4d8032660193200c9780e4b80325a01e7a00f3c0079c815ce001c7f00e3d8071dc038e60cc6d02e28806dfc036fc03b7d00dbb806dd4036e601b7201db680ed840769e03b4b01da380ed0c034ee01a7600d3a8069b6f24d801a6100d3000693c0b49c01a4b00d2500691c0f48c01a4300d210068fc0747c01a3d00c3f8061ec030ee0187300c36de01b0030c20186000c2780612c0308e0184300c1f8060ec0306e0183300c178060b4030560182900c13806094030460182100eb580758c038de01c6b00e3380718c0b8be01c5300db7806db8036d601b6a00db3806d98036c601b6203daf81ed78036a601b5200da5806d280368e01b4600da18069bc074da01a6b00d33806994034c603a5f01d2980e93c0749603a4701d2180e8fc0747a03a3b01d1c80e8dc0746a03a3301d188065bc032ce0594f02ca382e4fc0927a0b9370249a80e4bc0724e0186f00c3580619c030c60185f00c2980613c030960184700c218060fc0307a0183b00c1c8060dc0306a0183300c188060bc030560182700c1180606c0302e01e7b00f398075fc03af601d7700eb98175bc0bada05d6500e3f8071f8038f601c7a00e3b8071d8038e601c7202e378331b80b8da01b7f00dbf00edf4036ee01b7500db9806dc8076de03b6301daf80ed6c076ae03b5301da780ed340769603b4a01da480ed200768e05b4601da281ad100768603b4100d3b8069d8034ea01a6f03d3700698c034c401a5f02d2f00696c034b401a5702d2b00694c034a401a4f02d270069340b49801a4b00d250069240349001a4702d23006916ec48801a4300d210069040348001a3f01d1f0068f4032fe0197702caf81655c0b29e0494d02ca38125140727e0393700c978064b40324e0492500c3f8061ec030ee0187300c3780618c030be0185b00c2b80614c0309e0184d00c258061240308e0184500c218061040307e0183b00c1b8060cc0305e0182d00c158060a40304e0182500c11806084030360181700eb78075ac03ace01d6300e378071b8038d601c6a00e33807198038c601c6203e2f81f1780f8b607c5703e2981f148036de01b6b00db5006d9c036cc01b6303daf816d6c0f6ae05b5300da7806d380369a01a6f00d3580699c034c603a5f01d2d80e95c074a603a4f01d2680e92c0749203a4701d2280e90c0748203a3f01d1d80e8e40746e03a3301d188065bc032d60196700cb181e57c0f2b60795703ca981e53c0929a0794b03ca38125140f2860593f03c9d81e4dc0b2660392f01c9580e49c072460186f00c3580619c030c60185f00c2d80615c030a60184f00c2680612c030920184700c2280610c030820183f00c1d8060dc030660182f00c1580609c030460181f00c0d80605c0302601d6f00eb580759c03ac601c6f00e3580719c038c77b45fbd22dddd15eea8a601b6f00db700edb4036ce01b6500db1806d88076be03b5b01dab80ed4c0769e03b4b01da380ed0c034ce01a6600d3280697c194bc01a5b00d2b80694c034a401a4f02d2700692c0349401a47ba12300690c0348401a3f01d1f0068f4032de0196b00cb380658c172be0b95b05cab82e54c1729e0b94b05ca382e50c0727e0393b01c9b80e4cc0325e0192d00c9580649c0924a0192300c378061ac030ce0186300c2f80616c030ae0185300c2780612c0308e0184300c1f8060ec0306e0183300c178060b4030560182900c13806094030460182100c0f80606c0302e0181300eb78075b803ad601d6a00eb380759803ac601d6200e378071ac038ce01c6303e2f81f16c0f8b207c5703e2981f144036de01b6b00db5006d9c036cc01b6300dab806d58036aa07b4f03da7016d2c0f68e05b4303da10069bc034d601a6700d3181a97c0d4ba03a5b01d2c81a95c0d4aa03a5301d2881a93c0749606a4701d218168fc0d47a03a3b0351b81a8d4074660196f00cb580659c032c60795f024ae81e56c0f2ae0495503ca981e53c0f2960794703ca18164fc0f2760793702c9980e4bc0d2560692701c918061bc030d60186700c3180617c030ba0185b00c2c80615c030aa0185300c2880613c030960184700c218060fc030760183700c198060bc030560182700c1180607c030360181700c098075bc03adc01d6b00eb500759c03acc01d6300eb10071ac038c601c5b00e2c81714c0b8a201b6f00db5806d9c036c601b5b00dac806d5c036a601b5100da7816d240b68605b4100d378069ac034ce01a630352f81a974074b603a590352b81a954074a603a510352780e90c0b47e03a3b0351b80e8cc032de01967084af812574212ae0495502c9f81e4dc0725e0692700c378061ac030ce0186300c2f806174030b60185900c2b806154030a60185100c2780610c0307e0183b00c1b8060cc0305e0182b00c1380608c030360181700f3f8079f803cfa01d7b00ebc8075cc0fae201d6b00eb18071fc038fc0cc7db8a3e0071ec038f401c7900e3c0071dc038ec01c7500e3a0071cc038e407c7103e380071bc038dc01c6b00e3500719c038cc01c6300e3101717c0b8bc05c5d00dbf806df80f6fa07b7c00dbd806de4036ee01b7500db9806dc80b6e205b7000db7806dac036ce01b6302dac816d4c0b6a201a7f00d3f01a9f4034de01a6e00d358069a4034c601a6201d3081a97c074a606a4f0352680e92c0749206a470352280e90c0748205a3f01d1d81a8dc074660197f024be8065dc032ea0196f00cb381e53c0929a0c947024a28164fc0f26e0392f034938061fc030fa0187b00c3c8061dc030ea0187300c388061bc030d60186700c3180617c030a60184f00c2680612c030920184700c2280610c030820183f00c1d8060dc030660182f00c1580609c030460181b00c0b8079fc03cfc01e7d00eb901f5c0038fe05c7d00e3d8071e4038ee01c7500e398171c4038de01c6b00e3380718c0b8ba01b7e03dbe006dd8036e801b6e00db3016d38034fe01a7e0353e8069bc034dc01a6b00d3480698c034c403a6102d2780e92c0b48e03a4301d1c81a8d4030fe0187d00c3d8061e4030ee0187500c398061c4030de0186b00c3380618c0309e0184b00c2380610c030720183500c178060ac0304e0182300e358071a8036de01b6b00db3806d8c0b6a207b4f03da6806d2c0369201b4700da2806d0c0368201a6f00d370069ac034d201a6300d3100e9840d49e06a4d02d1f80e8ec0d46e03a3300c378061ac030ce0186300c27806134030960184900c23806114030860184100c1f8060ec0306e0183300c178060ac0304e0182300eb78075b803ada01c6f016368071ac038d201c6700e3280718c058c201c5f00e2d80715c038a601a6f03d368069ac034d201a6700d3280698c0b4c201a5f00d2d80695c034a602a4f00d2580691c034860196f00cb701a5b4032be0195e00cad806564032a60195201ca880a53c0529602947014a18164bc072560692701c918079fc03cfc01e7d00ebd0075e003ae56e57000eb5007588036fe07b7d00dbd806de4036ee01b7500db9816dc4036de01b6b00db3806d8c196ba05b4100d3f8069f80d4fa01a6f00d370069ac034d201a6300d3100e9840d4ba03a5102d1f80e8ec0d46e03a3300c3f8061f4030f60187900c3b8061d4030e60187100c378061ac030ce0186300c2edb4170030a20185000c1f8060ec0306e0183300c178060ac0304e0182300eb78075b803ad601d6a00eb380759803ac601d6200e3580718c038b601c5903e2981f144036de01b6b00db3806d8c036be01b5d00dad806d5c036aa05b4f00da18069bc034d601a6700d3181a97c0d4ba03a5b01d2c81695c0b4aa03a5301d2881a93c0748605a3f01d1d8168dc074660196f00cb384257c092ba10957024aa8164fc0b26e0392f034938061bc030d60186700c3180617c030ba0185b00c2c80615c030aa0185300c2880613c030860183f00c1d8060dc030660182f00c1580609c030460181b00c0b8079fc03cfc01e7d00ebf0075ec03af201d7300eb901f5c40fae001d6b00eb18071fc038fc05c7d03e3e0071ec038f201c7700e3a8071cc038e405c7102e380071bc038d601c6700e3181717c0b8ba05c5500dbf806df80b6fb6b37c00dbd806de8036f201b7800dbb806dd8036ea01b7400db9806dc80b6e205b7000db7806db80b6da0ab6c00db5806da8036ce01b6600db2806d90036c601b6202daf832d780b6ba01a7f00d3f01a9f4034de01a6e00d358069a4034c601a6201d3081a97c074a605a4f01d2581691c0748605a3f02d1e80e8ec0b47403a3901d1c0168dc0b46c06a350351a00e8cc074620197f024be8065dc032ea0196f00cb381653c0b28e0593f0249e8164dc0926a0392f034938061fc030fa0187b00c3c8061dc030ea0187300c388061bc030d60186700c3180617c030a60184f00c2580611c030860183f00c1e8060ec030720183700c1a8060cc030620182f00c1580609c030460181b00c0b8075bc03adc01d6d00e378071ac038d201c6700e31833184038be01c5b00e2b80714c036df7236d00db5806da4036ce01b6500db1816d84036be01b5b00dab806d4ee069f6f34bb61a3da8d0c034de01a6e0353680697c034bc01a5b00d2c80694c034a403a510352780e92c0d48e03a430351f80e8ec0d46e03a3300cb78125b4032d60196700cb280658c032be0195b00cab80654e0429e0b94b758a382e50db027e0b93b6889b82e4cc0725e0692b0349380e48c030de0186d00c358061a4030ce0186500c31806184030be0185b00c2b80614c0309e0184b00c2380610c0307e0183b00c1b8060cc0305e0182b00c1380608c0303e0181b00c0b80604c0bafe01d7b00ebb8175cc0bada0ac7e00e3b017178076fe03b7d00dbd806de8036ee01b7601dba80ed7c076b603b5701da980ed240768a03a7f0353f00e9f4074be05a5e01d2e816970074b603a5a01d2b816958074aa07a5401d2980e9480749203a4801d2281e9100347e01a3e00d1e8061fc030f60187700c3981617c030b60585700c298061240508a0383f00c1d80e0dc030660382f014168060ac0705401829b201400e09c0704c02825b081200608c0304201d6b03eb18171bc038d601c6702e3181717c0b8ba05c5501e2981adbc0d6dc01b6b00db5006d9c036cc05b6302db101ed7c0f6bc03b5301da900ed2c0769403b4701da300ed0c074de03a6d00d358069a8034ce01a6601d3280e98c074be03a5301d2780e92c0748e03a4301d1f80e8f40347601a3901d1b80e8d40746601a31054b780659c0b29e0594705c9f8124f41726e0493501c9780e49c030de0186b00c3380618c0f0be0185302c2780612c0b08e018430441f80a0f403076018390441b80a0d4030660183101c178060ac0704e0182300c0d82205c03cf607e7302ebf8075ec03aee05d7302eb78175b40baca05c7f0563f0071ec038f401c7700e3b0171cc0b8e405c6f066370171b4076fe03b7d00dbd806de8036ee01b7601dba80edbc076c603b5f01dad80ed5c076a603b4f01da680ed2c0769203b4701da280ed0c0768203a7f0353f00e9f4074de07a6e01d3180e988074be05a5e01d2d80e968074ae05a5601d2980e9480749e05a4e01d268169300749603a4a01d2480e9200748e05a4601d22d9c9100748603a4201d2080e9000347e01a3e00d1e82a5fc032ee0595f02cab81653c0929a05947024a280e4fc0726e0392f01c9680e49c0924a0187f00c3d8061dc030e60786f00c3181617c030b60585700c2981613c0509a0184b00c2481611c0508a0184300c2080e0fc030760383700c1980e0bc0505a0182b01c150060a6c60500382701c1300a096c00480182300c1080606c1102e07d6f00eb580759c0fac606c6f036370071ac038d401c6700e3301f18c0d8c407c5f03e2f01f16c0f8ae07c5303e2901edbc0f6dc01b6b00db3816d8c156c407b5f02dad81ed680f6ae07b5602da980ed3c0769c03b4d01d378069ac034ce03a6301d2f80e96c074ae03a5301d2780e9340349601a4901d2380e9140748601a4101d1f80e8ec0747203a3701d1980e8c4152de0196b00cb382a58c0f2be0795b03cab81e54c0f29e0494d03ca581e51c0928a0794302c9f82e4f40f2760793703c9a8164cc0725e0392b01c9380e48c030de0186b00c3380618c0f0be0185b03c2b80614c0f09e0284d00c258061240f08e0284500c218061040b07e0183b03c1b8060cc0705e0182b01c1380608c1103e0181b0440b80604c038de01c6b00e3380718c0b8ba01b6e00db3016d38034de01a6b00d3380e93c0749603a4701d2180e8e40746a0186f00c3580619c030c60184f00c2580611c030860183900c1a8060bc030560182700c118075ac03ac601c6f00e3580719c038c605c5f02e2e817154036de01b6e00db5806da8036ce01b6600db1806d880b6be0cb5e02dae8069bc034d601a6700d3180e97c074a603a4f01d2580e91c0748603a3f01d1e80e8ec0747203a3701d1a80e8cc074620196f00cb381653c0b28e0593f0249e8164dc0926a0392f01c938061bc030d60186700c3180617c030a60184f00c2580611c030860183f00c1e8060ec030720183700c1a8060cc030620182f00c1580609c030460181b00c0b80717c038b601c5700e29806d7c036b601b5700da9836d3ec86960db47b19a180697c034b601a5700d2980e93c0749603a4701d2180e8fc0747603a3701d1980657c032b60195700ca982e53c172960b94705ca182e4fc172760b93705c9980e4bc072560392701c9180617c030b60185700c2980613c030960184700c218060fc030760183700c198060bc030560182700c1180607c030360181700c098171bc038d601c6702e31817174156dc01b6602da700e9bc034d601a6701d2780e92c0748e03a4301d1c80e8d4052de0196b00cb380a58c0529e0294b014a380a50c052720293500c978064ac0524e0292300eb581f58c0b8de01c6b00e3381718c0b8be05c5d02e2a816dbc156dc01b6b00db5006d9c036cc05b6302db1016d7c196bc05b5d01d378069ac034ce03a6301d2f80e94c0749e03a4b01d2380e90c0747e03a3d01d1d80e8e40746e03a3501d1980e8c4052de0196b00cb380a58c052be02953014a780a52c0528e029430149f80a4f405276029390149b80a4d4052660293100c978064ac0524e0292304c3780619c0b09e0584702c1f8120f40b06e0483501c1780e09c0503e028170562f80716c038ae0ac53055af806d6c036ae0ab5306da7d84d2c1b68f6034301d2f80696c034ae03a5301d2780e92c0748e03a4301d1f80e8ec0746e03a33014af80656c032ae02953014a780a52c0528e029430149f80a4ec0526e0293300c978064ac0524e0292304c2f80616c030ae0985304c2782612c1308e0984304c1f8260ec1306e0983301c1780e0ac0704e038230140f80a06c0502e02813 20 1048575 8 255 11 2047 21 2097151
def cc_60_12 : Nat → List (Nat × Nat) := unpackCursorV4 0x2bab2aaa8284cc9832245b68d6820cd27a321b86161f8569bc576612b653eb84d6c831a80ba982ba609da21e720466709ef4004f 0x1f5bc0fadc01d6b00eb500759c03acc07d63056b101edbc0f6dc01b6b00db3816d8c156c40aa6f00d3580699c154c607a5f0352e81e96c074b207a570352a81e94c074a205a3f03d1d81e8dc0b4660186f00c3580619c030c60785f0142e80616c030b2078570142a80614c030a20583f00c1d81e0dc030661182f00c1584609c030460ad6e00e3502adbc036d601b67055b1816d672a6aa0aa6f00d3580699c154c603a590352ace08fc1b4760da37941198061bc030d60186700c31806164050aa5b03f00c1d8360dc030664802f00c158a409c0304601d6b00eb18071bc038dc01c6b00e318071880f8be07c5e03e2981f148036de01b6b00db5006d9c036cc01b6303daf81ed780b6a607b5200da7806d380369a01a6f00d3580699c034c607a5f03d2981e93c0d49a07a4b01d2481e91c0d48a07a4301d208168fc0f47607a3702d198065bc032ce0794f024a681e51c0928a0593f03c9b8464bc2b24e0186f00c3580619c030c60185f00c2980613c0309a0184b00c2480611c0308a0184300c208060fc030760183700c198060bc030560182700c1180606c0302e01d6e00eb1807588038be0ac5e00e2e806dbc036d601b6700db181ed7c0f6a601b4f00da6806d2c0b69201b47c99a2806d0c0368201a6f00d3580699c034c607a5f03d2980693c0349a01a4b01d2480691c0d48a01a4300d20cd88fc0f47607a37931198065bc032ce0194f00ca680651c0928adf13f03c9bb304bd5a24e0186f00c3580619c030c60185f00c2980613c0309a0184b00c2480611c0308a0184300c208060fc030760183700c198060bc030560182700c1180606c0302e01d6f00eb68075ac03ad201d6700eb280758c03ac201b5f00dad806d68036ae01b5600da981e9bc0d4da07a6b01d3481e99c0d4ca07a6301d3080697c034b601a5700d298168fc0f47607a3903d1b8168ce4a4620186f00c368061ac030d20186700c3280618c030c20185f00c2d80615c030a60183f00c1d8060e40306e0183300c188060bc030560182700c118075b4038a59136d02db0806d7c036b601b5700da981a9b4074c201a5f00d2d80695c034a73423f9711dcac8de464660186d00c3080617c030b60185700c298060fc030760183700c198060bc030560182700c118075ac0fac601c6b00e3500719c038cc07c6300e2f8071780f8a601c5203db781edb8036d601b6702db182ad880f6be07b5e02da981ed480f69e07b4e03da682a9bc034d601a670553181e97c0f4a607a4f0352681e92c0749207a470352281e90c0748205a3f9991e81e8ec0f46e07a3502d1982a5bc032ce0794f024a681e51c0928a0593f6f09e81e4dc0f26a1192f0ac938061bc030d60186700c3181e17c030a60784f0142680612c03092078470142280610c030820583f2d01e8060ec0f06e0783500c198460bc030561182700c1180606c2902e01d6b00eb5007598038be01c5e00e2e81edbc036d601b67055b181ed7c0f6a607b4f055a681ed2c0b69207b47c79a281ed0c0b6820aa6f00d3580699c154c607a5f03d2981e93c0d49a0aa4b01d2482a91c0d48a07a4301d20cc48fc0f47607a379091982a5bc032ce0794f024a682a51c0928adc13f03c9bb284bd5824e0186f00c3580619c030c60785f00c2981e13c0509a0184b00c2482a11c0508a0184300c209600fc030760783700c199180bc030562802700c1180606c1602e05d6f02eb70175b4158de01c6b00e3381f18c0f8be07c5b0662c81f15c0f8a60ac5100db5806da80b6d201b6700db3016d8c0b6c201b5700dab006d540f69e05b4b03da3816d0c154de01a6b00d3382a98c0f4be06a5d0552d80e964154ae06a5503d2980e9440f49f5724ba692381e90c0b47e07a3b03d1b8168cc152de0196b00cb382a58c0f2be0495d054ad82a55c092aa0795303ca7bf852dea28e0794302c9f81e4ec0f26e0593364097aec4ad5624ea312300c378061ac030ce0186303c2f80a174030b6018590542b80a154030a60185103c2780612cd608e0184302c1f8060ec0f06e01833220178060ac4e04e018230b00f80606c1402e0181300eb78075ac03ace01d6300e378071b80b8da01c6700e3280718c038c405c5f02e2d81715c0b8a601b6700db3006d94036be0cb5e00dad806d5c036a601b5200da7816d380369a01a6f00d3580699c034c75d25fab12dd3095e884a605a4f02d2581691c0b48601a3f00d1e8068ec0747201a370351a8068cc034620196f00cb580659c032c70515f7e8adbd055dca2a60594f02ca581651c0b2860193f00c9e8064ec0326e0493500c99b1c4bd74256aa127510918061bc030d60186700c3180617c030b60185700c2980613c030960184700c218060fc0307a0183b00c1c8060dc0306a0183300c188060bc030560182700c1180607c030360181700c0980717c038b601c5700e29812d7c096b604b57025a9806d3c0369601b4700da181297c094b604a570252980693c0349601a4700d2181e8fc0b47607a3702d1981257c092b604957024a980653c032960194700ca181e4fea82774a13703c998164bc0f2560792702c9180617c030b60185700c2980613c030960184700c218060fc030760183700c198060bc030560182700c1180607c030360181700c09806d7c036b601b5700da980697c034b601a5700d298168fc0f47607a3702d1980617c030b60185700c298060fc030760183700c198060bc030560182700c118075bc03adc01d6d00e378071ac038d201c6700e31833184038be01c5b00e2b80714c036de01b6e055b6806d7c036bc01b5b00dac806d4c036a405b5103da7816d2c0f68e05b4300d3781a9b4034d601a6900d33806994034c603a6100d2f80696c034ae01a5303d27d4c92e9248e07a4302d1f81e8ec0f46e05a3300cb78065b8092db8b16c00cb580659c032ca0196300cb1628580032be0195b00cab80654c0f29efb14b790a381e50c0b27e0793b03c9b8164cd8a25eb812b54893a8048c030de0186d00c358061a4030ce0186500c31806184030be0185b00c2b80614c0309e0184b00c2380610c0307e0183b00c1b8060cc0305e0182b00c1380608c0303e0181b00c0b80604c15ade01d6b00eb382b58c0b8de05c6d00e358071a8038ce01c6602e3281717c0b8b605c5702e29816dbc156dc05b6d02daf832d780b6b605b5702da9816d480369e01b4e00da682a9bc034d601a6705531d6c97ea24b747257a112981693c0b49605a4702d218168fc0b47a05a3b01d1c8168dc0d46a05a3301d1882a5bc032d601967054b1c1057df22b6f0157718a981653c0b2960594702ca18164fc0927a0593b02c9b8124d40b266c312f5b095aa049d3c2460186f00c3580619c030c67505f00c2d9a415c030a60584f00c2581611c030860583f0141e8060ec03072058370141a8060cc030624202f00c1589809c030461401f00c0d82405c0302607d6b03eb18331bc158dc07c6b00e3503319c038cc07c630563101717c0b8bc05c5d03db7816dac0f6ce05b6302dac816d4c0b6a20da6fbd935dc099c1b4c607a5f03d2981e93c0d49a0ca4b01d2483291c0d48a07a4301d208168fc0f47607a3702d198365be262ce0794f024a683251c0928a0593f03c9bb044bd4e24e0d86f4a035a2819c1b0c60785f03c2981e13c0509a0c84b00c2483211c0508a0784300c208160fc0f0760783702c199000bc6e056250270f81184006c1002e05c6f02e3581719c0b8c605c5d055b7006d980b69d8026fbd135dbc99ed04c605a4f02d2581691c0b48603a390351aa6c1bd260d6890673d83181613c0b0960584702c218060e40506a3f02f1b01589009c3c04602c5f0162d80b15c058a607a5f02d2d81e95c0b4a602a4f0152580a91c054860d95fbc0addb455c1b2a60294f014a580a51c052860592f03c9581e49c0b24601b5f00dad806d5c036a601a5f00d2d80695c034a605a3f03d1d81e8dc0b4660185f00c2d80615c030a60183f00c1d8060dc030660182f00c1580609c0304601d6a056b101edbc0b6d607b6702db1832d740b6820da6fbb935db099c1b4c606a5d01d288168fc0f47607a3702d198361bd220d68706706c3180a1770a0b801851c20280160fc0f0760783702c198f40bc68056230270e01181f5ac0fac605c6f02e3581719c0b8c605c5f02e2e8171540b6de0ab6e02db5806da80b6ce01b6602db1816d880b6be0cb5e02daedf89beea4d76a267b313181e97c0f4a605a4f02d2581691c0b48605a3f02d1e8168ec0747205a370351a8168cc074631d16f888b381653c0b28e0593f0249e8164dc0926abf12f53093a681bd1e0d6850673c83181e17c0f0a60584f02c2581611c0b0860583f0141e8160ec03072058370141a8160cc030623b02f1901588809c340460e01b0380b8075bc03ada03d6b01eb480759c03aca07d6301eb081f1bc0f8d607c6903e3381f18c0f8c207c5f00e2d80715c0f8a606b6f035b701adb40f6be07b5e00dad806d5c0b6a60ab5203da7816d2c0f68e05b43035378069b4074d603a6900d33806994074c603a610352f80696c034ae03a530352780e92c0d48e03a4302d1f81a8f40747606a370351a80e8cc0f2de0496d03cb581e59c092ca07963054af80656c032ae0a95303ca781e52c0f28e0794302c9f81e4ec0f26e0593301c9781a4ac0d24e0392303c3780a1b4030d60186903c3380a194030c60186100c2f80616c030ae0185303c2780612c0f08e0184302c1f8060ec0f06e0183301c178060ac0d04e0182305c0f80606c2902e0181301f3f80f9f807cfa05c7f00e3d8071dc0b8e605c6f02e368171ac0b8d205c6702e3281718c0b8c205c5d055bf006dd80d6dc06b6c035b301ed900b69c01a7b00d3d00e9e4034ee01a7601d3980e9c4034ce01a6600d3281693c0749605a4701d2180e8e40d46a0187f00c3d8061dc030e60686f014368061ac030d2068670143280618c030c20584f00c2581611c03086018390141a80e0bc030560682700c118075bc03ada03d6b01eb480759c03aca05d6301eb081f1ac0f8d206c630363080716c0f8a605b6f02db6816d9c0b6ca05b6302daf806d6c036ae05b5302da7816d0c0b4de01a6d01d3580e9a4034ce01a6501d3180e9840b4be01a5b00d2d00695c034ac03a530352780e90c0b47e03a3b02d1b80e8cc212de0496d084b3812594152be0195702c9f8164dc0725e069270843780a1b4030d6018690843380a194030c60186100c2f80616c030ae0185303c2780610c0b07e0183b02c1b8060cc0705e0182b0341380608c0303610817 18 262143 7 127 11 2047 21 2097151
def cur_60 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_60_12 (Nat.sub p 384)) (cc_60_11 (Nat.sub p 352)) (Nat.blt p 384)) (Bool.rec (cc_60_10 (Nat.sub p 320)) (cc_60_9 (Nat.sub p 288)) (Nat.blt p 320)) (Nat.blt p 352)) (Bool.rec (Bool.rec (cc_60_8 (Nat.sub p 256)) (cc_60_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_60_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (cc_60_5 (Nat.sub p 160)) (cc_60_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_60_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_60_2 (Nat.sub p 64)) (cc_60_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_60_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def f_60 : Nat → Nat × Nat := unpackForestF 0xcab5500c5fc9b4500c5bc8b6d00c57c7b4500c5300b5f00b5bc516cc516000b5700b5300b4f00b4bc205cc205000b4700b43bf355bf34bbfb64bf34300a5fbe254ba45fba45bbc26cbc06cba457bb244ba453ba24600a5bb536db8c7cb534fb534bb6d70b685cb5347b5b7cb534300a57afc5bb3a44afc53afa46b1b4bb1b43af828b034bb0343af82400a53ad36bae354ad363ad34500a4fac264a846fa846baa27caa17ca8467a9244a8463a824600a4ba7568a336fa336ba5570a517ca3367a436ca3363a335d00a479dc6ba1a449dc639da469fb5b9fb539d9289e35b9e3539d92400a439cb6498d6f9bb5498d6b9ab7c98d67994549935498d6300a3f97a7c9756700a3b9647095d6700a3794a6490d6f93a5490d6b9247c9227c90d679125490d6300a338cb558f3648cb438e4648ca4f8d3648ca3f0095f8b9460095b85b6d8a47c85b4f8937c85b438847c85a4f8737c85a3f8647085a37009578394683818838140095380b6b80b6380a6f80a6780a3f0094f7f9647c46f7c46b7e17c7c4677d1447c4637c1460094b7b56873b6f73b6b79d7073b6778b6c73b6373b5d7756873a6f7657073a677536c73a3f7446073a37009477146b72144714637114600943703546ad6b6ec546eb546ad636db646aa6f6cb7c6aa676bb546aa5f6a9620093f0093b6947068a670093767a6e0093366a545f56b65a545f56364a645f46f5f46b6327c5f467622445f463612545f45f602445f4535f2460092f5e16457c6f57c6b5c97c57c675b94457c6357946578185835f5835b5835758353578140092b5356b535635346f5346b53467534635345f5345300927521644ec6f4ec6b5097c4ec674f9444ec634e946009234bb4b4bb434ba4f4ba474ba3f0085f4a8544745f4745b4906c474574804447453470460085b3eb6d45c7c3eb4f3eb4b445703eb474337c3eb434247c3ea4f415703ea474037c3ea3f3f4703ea37008573c45b3d0443c4533c046008533b354383633834539c643826f38b543823f0084f370460084b365683136f3536c313633135d33d683126f32b6c3123f31c6031237008472f0462f02c2f024008432e36428d6f2cc542cb5428d632bb6428a6f2ab5428a5f29b6c28a57288520083f0083b2746026a57008372595e0083324a641d56f23a541d56322a641d46f21a441d46320a541d45f1d45b1f26c1d4571e2441d4531d2460082f1c05415c5f15c5b1a86c15c571984415c53158461582c1634f1634b1634716343158240082b1156f115631146f114631145f1145b114571145300827100540cc5f0cc5b0e86c0cc570d8440cc530c846008230b96409c6f0a94409c63099460081f0885406c5f0784406c53068460081b01d6301c6f01c6301c5f01c5301b6f01b5f01b4f01b4700817008130003f 9 11
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsV4 fullMask g_60 ep_60 406 bds_60 (dagTraceF fullMask rootStock 11 f_60) (cur_60 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_0 : treeBlockF 0 32 (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 406 (dagTraceF fullMask rootStock 11 f_60) cur_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_1 : treeBlockF 32 64 (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 406 (dagTraceF fullMask rootStock 11 f_60) cur_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_2 : treeBlockF 64 96 (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 406 (dagTraceF fullMask rootStock 11 f_60) cur_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_3 : treeBlockF 96 128 (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 406 (dagTraceF fullMask rootStock 11 f_60) cur_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_4 : treeBlockF 128 160 (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 406 (dagTraceF fullMask rootStock 11 f_60) cur_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_5 : treeBlockF 160 192 (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 406 (dagTraceF fullMask rootStock 11 f_60) cur_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_6 : treeBlockF 192 224 (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 406 (dagTraceF fullMask rootStock 11 f_60) cur_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_7 : treeBlockF 224 256 (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 406 (dagTraceF fullMask rootStock 11 f_60) cur_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_8 : treeBlockF 256 288 (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 406 (dagTraceF fullMask rootStock 11 f_60) cur_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_9 : treeBlockF 288 320 (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 406 (dagTraceF fullMask rootStock 11 f_60) cur_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_10 : treeBlockF 320 352 (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 406 (dagTraceF fullMask rootStock 11 f_60) cur_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_11 : treeBlockF 352 384 (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 406 (dagTraceF fullMask rootStock 11 f_60) cur_60) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_12 : treeBlockF 384 406 (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 406 (dagTraceF fullMask rootStock 11 f_60) cur_60) = true := by decide +kernel
theorem nj_60_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 406 (dagTraceF fullMask rootStock 11 f_60) cur_60) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_60_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_60_1 h1 h2)
theorem nj_60_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 406 (dagTraceF fullMask rootStock 11 f_60) cur_60) i = true := block_join nj_60_1 (fun _ h1 h2 => treeBlockF_at nb_60_2 h1 h2)
theorem nj_60_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 406 (dagTraceF fullMask rootStock 11 f_60) cur_60) i = true := block_join nj_60_2 (fun _ h1 h2 => treeBlockF_at nb_60_3 h1 h2)
theorem nj_60_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 406 (dagTraceF fullMask rootStock 11 f_60) cur_60) i = true := block_join nj_60_3 (fun _ h1 h2 => treeBlockF_at nb_60_4 h1 h2)
theorem nj_60_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 406 (dagTraceF fullMask rootStock 11 f_60) cur_60) i = true := block_join nj_60_4 (fun _ h1 h2 => treeBlockF_at nb_60_5 h1 h2)
theorem nj_60_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 406 (dagTraceF fullMask rootStock 11 f_60) cur_60) i = true := block_join nj_60_5 (fun _ h1 h2 => treeBlockF_at nb_60_6 h1 h2)
theorem nj_60_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 406 (dagTraceF fullMask rootStock 11 f_60) cur_60) i = true := block_join nj_60_6 (fun _ h1 h2 => treeBlockF_at nb_60_7 h1 h2)
theorem nj_60_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 406 (dagTraceF fullMask rootStock 11 f_60) cur_60) i = true := block_join nj_60_7 (fun _ h1 h2 => treeBlockF_at nb_60_8 h1 h2)
theorem nj_60_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 406 (dagTraceF fullMask rootStock 11 f_60) cur_60) i = true := block_join nj_60_8 (fun _ h1 h2 => treeBlockF_at nb_60_9 h1 h2)
theorem nj_60_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 406 (dagTraceF fullMask rootStock 11 f_60) cur_60) i = true := block_join nj_60_9 (fun _ h1 h2 => treeBlockF_at nb_60_10 h1 h2)
theorem nj_60_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 406 (dagTraceF fullMask rootStock 11 f_60) cur_60) i = true := block_join nj_60_10 (fun _ h1 h2 => treeBlockF_at nb_60_11 h1 h2)
theorem nj_60_12 : ∀ i, 0 ≤ i → i < 406 → (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 406 (dagTraceF fullMask rootStock 11 f_60) cur_60) i = true := block_join nj_60_11 (fun _ h1 h2 => treeBlockF_at nb_60_12 h1 h2)
theorem nc_60 : ∀ i, 0 ≤ i → i < 406 → (dagCheckNodeV4 fullMask g_60 ep_60 bds_60 406 (dagTraceF fullMask rootStock 11 f_60) cur_60) i = true := nj_60_12
theorem lb_60 : LowerBin fullMask rootStock g_60 12 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_60 kn_60 sub_60 gl_60 rc_60 nc_60

def wg : List Gate := [⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.and, [5, 7]⟩, ⟨GateOp.or, [6, 12]⟩, ⟨GateOp.and, [2, 13]⟩, ⟨GateOp.or, [2, 13]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [14, 16]⟩, ⟨GateOp.and, [15, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 3905480832) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276676776 * 2 ^ 32 + 3905480832)) (13 - 1) := by
  rw [show canon fullMask (4276676776 * 2 ^ 32 + 3905480832) = g_60 by decide]
  exact lb_60

end PEqualNP.Outside.L_meta_49369

theorem PEqualNP.Outside.L_meta_49369 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676776 * 2 ^ 32 + 3905480832) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 3905480832) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_49369.table2_from_lowerBin (4276676776 * 2 ^ 32 + 3905480832) 13 PEqualNP.Outside.L_meta_49369.root_lb PEqualNP.Outside.L_meta_49369.wg 18 rfl PEqualNP.Outside.L_meta_49369.wfits PEqualNP.Outside.L_meta_49369.weval
