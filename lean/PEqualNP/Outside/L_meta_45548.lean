import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_45548

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

def m_0 : Nat := 0x2020202020202020
def s_0 : List Nat := [0x20002000200020, 0x202000002020, 0x20202020]
def g_0 : Nat := 0x2000202020
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

def m_1 : Nat := 0x202020202020202
def s_1 : List Nat := [0x2000200020002, 0x20200000202, 0x2020202]
def g_1 : Nat := 0x200020202
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

def m_2 : Nat := 0xa0a00000a0a
def s_2 : List Nat := [0x20200000202, 0xa0000000a, 0xa0a]
def g_2 : Nat := 0x20000020a
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

def m_3 : Nat := 0xcc000000cc0000
def s_3 : List Nat := [0x44000000440000, 0xc0000000c0000, 0xcc0000]
def g_3 : Nat := 0x40000004c0000
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

def m_4 : Nat := 0xcc000000cc
def s_4 : List Nat := [0x4400000044, 0xc0000000c, 0xcc]
def g_4 : Nat := 0x40000004c
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

def m_5 : Nat := 0xf0000000f00000
def s_5 : List Nat := [0x50000000500000, 0x30000000300000, 0xf00000]
def g_5 : Nat := 0x10000000700000
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

def m_6 : Nat := 0x3030303000000000
def s_6 : List Nat := [0x1010101000000000, 0x30003000000000, 0x303000000000]
def g_6 : Nat := 0x10103000000000
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

def m_7 : Nat := 0x5500550000000000
def s_7 : List Nat := [0x1100110000000000, 0x500050000000000, 0x550000000000]
def g_7 : Nat := 0x100150000000000
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

def m_8 : Nat := 0x55005500
def s_8 : List Nat := [0x11001100, 0x5000500, 0x5500]
def g_8 : Nat := 0x1001500
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

def m_9 : Nat := 0xf000f00
def s_9 : List Nat := [0x5000500, 0x3000300, 0xf00]
def g_9 : Nat := 0x1000700
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

def m_11 : Nat := 0xcccc
def s_11 : List Nat := [0x4444, 0xc0c, 0xcc]
def g_11 : Nat := 0x44c
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

def m_12 : Nat := 0xa0a0a0a0a0a0a0a0
def s_12 : List Nat := [0x2020202020202020, 0xa000a000a000a0, 0xa0a00000a0a0, 0xa0a0a0a0]
def g_12 : Nat := 0x2000202020
def bds_12 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_12 : KnownBin bds_12 := by
  intro b hb; simp only [bds_12, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_12 : ∀ b ∈ bds_12, m_12 &&& b.1 = b.1 := by intro b hb; simp only [bds_12, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_12 : ∀ b ∈ bds_12, canon b.1 g_12 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_12, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_12 : Nat → Nat × Nat := fun _ => (0, 0)
def l_12 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_12 : dagCheckRootsF m_12 g_12 bds_12 (dagRefF 0 (dagTraceF m_12 s_12 4 f_12) l_12 0) s_12 4 = true := by decide +kernel
theorem nc_12 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_12 g_12 bds_12 0 (dagTraceF m_12 s_12 4 f_12) l_12 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_12 : LowerBin m_12 s_12 g_12 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_12 sub_12 gl_12 rc_12 nc_12

def m_13 : Nat := 0xa0a0a0a0a0a0a0a
def s_13 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_13 : Nat := 0x2000a020a
def bds_13 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_13 : KnownBin bds_13 := by
  intro b hb; simp only [bds_13, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_13 : ∀ b ∈ bds_13, m_13 &&& b.1 = b.1 := by intro b hb; simp only [bds_13, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_13 : ∀ b ∈ bds_13, canon b.1 g_13 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_13, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_13 : Nat → Nat × Nat := fun _ => (0, 0)
def l_13 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_13 : dagCheckRootsF m_13 g_13 bds_13 (dagRefF 0 (dagTraceF m_13 s_13 4 f_13) l_13 0) s_13 4 = true := by decide +kernel
theorem nc_13 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_13 g_13 bds_13 0 (dagTraceF m_13 s_13 4 f_13) l_13 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_13 : LowerBin m_13 s_13 g_13 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_13 sub_13 gl_13 rc_13 nc_13

def m_14 : Nat := 0x3030303030303030
def s_14 : List Nat := [0x1010101010101010, 0x30003000300030, 0x303000003030, 0x30303030]
def g_14 : Nat := 0x10103000303030
def bds_14 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_14 : KnownBin bds_14 := by
  intro b hb; simp only [bds_14, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_14 : ∀ b ∈ bds_14, m_14 &&& b.1 = b.1 := by intro b hb; simp only [bds_14, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_14 : ∀ b ∈ bds_14, canon b.1 g_14 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_14, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_14 : Nat → Nat × Nat := fun _ => (0, 0)
def l_14 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_14 : dagCheckRootsF m_14 g_14 bds_14 (dagRefF 0 (dagTraceF m_14 s_14 4 f_14) l_14 0) s_14 4 = true := by decide +kernel
theorem nc_14 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_14 g_14 bds_14 0 (dagTraceF m_14 s_14 4 f_14) l_14 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_14 : LowerBin m_14 s_14 g_14 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_14 sub_14 gl_14 rc_14 nc_14

def m_15 : Nat := 0x303030303030303
def s_15 : List Nat := [0x101010101010101, 0x3000300030003, 0x30300000303, 0x3030303]
def g_15 : Nat := 0x101010301030303
def bds_15 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_15 : KnownBin bds_15 := by
  intro b hb; simp only [bds_15, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_15 : ∀ b ∈ bds_15, m_15 &&& b.1 = b.1 := by intro b hb; simp only [bds_15, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_15 : ∀ b ∈ bds_15, canon b.1 g_15 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_15, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_15 : Nat → Nat × Nat := fun _ => (0, 0)
def l_15 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_15 : dagCheckRootsF m_15 g_15 bds_15 (dagRefF 0 (dagTraceF m_15 s_15 4 f_15) l_15 0) s_15 4 = true := by decide +kernel
theorem nc_15 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_15 g_15 bds_15 0 (dagTraceF m_15 s_15 4 f_15) l_15 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_15 : LowerBin m_15 s_15 g_15 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_15 sub_15 gl_15 rc_15 nc_15

def m_16 : Nat := 0xf000f000f000f00
def s_16 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_16 : Nat := 0x100050001000700
def bds_16 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_16 : KnownBin bds_16 := by
  intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_16 : ∀ b ∈ bds_16, m_16 &&& b.1 = b.1 := by intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_16 : ∀ b ∈ bds_16, canon b.1 g_16 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_16, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_16 : Nat → Nat × Nat := fun _ => (0, 0)
def l_16 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsF m_16 g_16 bds_16 (dagRefF 0 (dagTraceF m_16 s_16 4 f_16) l_16 0) s_16 4 = true := by decide +kernel
theorem nc_16 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_16 g_16 bds_16 0 (dagTraceF m_16 s_16 4 f_16) l_16 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_16 : LowerBin m_16 s_16 g_16 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_16 sub_16 gl_16 rc_16 nc_16

def m_17 : Nat := 0xf000f000f000f0
def s_17 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_17 : Nat := 0x10003000700070
def bds_17 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
theorem kn_17 : KnownBin bds_17 := by
  intro b hb; simp only [bds_17, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_5
theorem sub_17 : ∀ b ∈ bds_17, m_17 &&& b.1 = b.1 := by intro b hb; simp only [bds_17, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_17 : ∀ b ∈ bds_17, canon b.1 g_17 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_17, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_17 : Nat → Nat × Nat := fun _ => (0, 0)
def l_17 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsF m_17 g_17 bds_17 (dagRefF 0 (dagTraceF m_17 s_17 4 f_17) l_17 0) s_17 4 = true := by decide +kernel
theorem nc_17 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_17 g_17 bds_17 0 (dagTraceF m_17 s_17 4 f_17) l_17 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_17 : LowerBin m_17 s_17 g_17 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_17 sub_17 gl_17 rc_17 nc_17

def m_18 : Nat := 0x5555000055550000
def s_18 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_18 : Nat := 0x115000001550000
def bds_18 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
theorem kn_18 : KnownBin bds_18 := by
  intro b hb; simp only [bds_18, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_10
theorem sub_18 : ∀ b ∈ bds_18, m_18 &&& b.1 = b.1 := by intro b hb; simp only [bds_18, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_18 : ∀ b ∈ bds_18, canon b.1 g_18 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_18, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_18 : Nat → Nat × Nat := fun _ => (0, 0)
def l_18 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsF m_18 g_18 bds_18 (dagRefF 0 (dagTraceF m_18 s_18 4 f_18) l_18 0) s_18 4 = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_18 g_18 bds_18 0 (dagTraceF m_18 s_18 4 f_18) l_18 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_18 : LowerBin m_18 s_18 g_18 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_18 sub_18 gl_18 rc_18 nc_18

def m_19 : Nat := 0xaaaa0000aaaa
def s_19 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_19 : Nat := 0x220000222a
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

def m_20 : Nat := 0xcccc0000cccc0000
def s_20 : List Nat := [0x4444000044440000, 0xc0c00000c0c0000, 0xcc000000cc0000, 0xcccc0000]
def g_20 : Nat := 0x40000004c0000
def bds_20 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_20 : KnownBin bds_20 := by
  intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_20 : ∀ b ∈ bds_20, m_20 &&& b.1 = b.1 := by intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_20 : ∀ b ∈ bds_20, canon b.1 g_20 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_20, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_20 : Nat → Nat × Nat := fun _ => (0, 0)
def l_20 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsF m_20 g_20 bds_20 (dagRefF 0 (dagTraceF m_20 s_20 4 f_20) l_20 0) s_20 4 = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_20 g_20 bds_20 0 (dagTraceF m_20 s_20 4 f_20) l_20 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_20 : LowerBin m_20 s_20 g_20 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_20 sub_20 gl_20 rc_20 nc_20

def m_21 : Nat := 0xcccc0000cccc
def s_21 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_21 : Nat := 0x4040000044c
def bds_21 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
theorem kn_21 : KnownBin bds_21 := by
  intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_4
theorem sub_21 : ∀ b ∈ bds_21, m_21 &&& b.1 = b.1 := by intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_21 : ∀ b ∈ bds_21, canon b.1 g_21 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_21 : Nat → Nat × Nat := fun _ => (0, 0)
def l_21 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsF m_21 g_21 bds_21 (dagRefF 0 (dagTraceF m_21 s_21 4 f_21) l_21 0) s_21 4 = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_21 g_21 bds_21 0 (dagTraceF m_21 s_21 4 f_21) l_21 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_21 : LowerBin m_21 s_21 g_21 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_21 sub_21 gl_21 rc_21 nc_21

def m_22 : Nat := 0xf0f00000f0f00000
def s_22 : List Nat := [0x5050000050500000, 0x3030000030300000, 0xf0000000f00000, 0xf0f00000]
def g_22 : Nat := 0x10000000700000
def bds_22 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
theorem kn_22 : KnownBin bds_22 := by
  intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_5
theorem sub_22 : ∀ b ∈ bds_22, m_22 &&& b.1 = b.1 := by intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_22 : ∀ b ∈ bds_22, canon b.1 g_22 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_22 : Nat → Nat × Nat := fun _ => (0, 0)
def l_22 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsF m_22 g_22 bds_22 (dagRefF 0 (dagTraceF m_22 s_22 4 f_22) l_22 0) s_22 4 = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_22 g_22 bds_22 0 (dagTraceF m_22 s_22 4 f_22) l_22 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_22 : LowerBin m_22 s_22 g_22 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_22 sub_22 gl_22 rc_22 nc_22

def m_23 : Nat := 0xf0f00000f0f0
def s_23 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_23 : Nat := 0x103000003070
def bds_23 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_23 : KnownBin bds_23 := by intro b hb; simp [bds_23] at hb
theorem sub_23 : ∀ b ∈ bds_23, m_23 &&& b.1 = b.1 := by intro b hb; simp [bds_23] at hb
theorem gl_23 : ∀ b ∈ bds_23, canon b.1 g_23 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_23] at hb
def f_23 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c838c834053fbc18bc14053b0537b2440533052f052b97489740943c94300527814c814480188014052375387534043f682c6824043b04375d440433042f042b43484340413c413004272c4c2c442c2c2c240423214c2144041f144c1444041b041709240413000f 6 10
def l_23 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607227207206e26c16c06a16a06a06a06a06a06a06246206206206205a45a05a05625605605225015004e14e04e04e04e04e04e04644604604604603e43e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424cc38c834c018bc14b130b244a3489f40983c94308d4c894484188014793875346c2c68245c305d444f484b40453c4130384c3444302c2c24254c2144184c144408100924fe3ffa3be637d233c53fb93bb537ad33a92fa52b91277d23703f643b60375833542f502b3c2728231c1f101b0c170413000f 12 5 10 6 6
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

def m_24 : Nat := 0xf0f00000f0f
def s_24 : List Nat := [0x50500000505, 0x30300000303, 0xf0000000f, 0xf0f]
def g_24 : Nat := 0x5070000070f
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_24 : KnownBin bds_24 := by
  intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_24 : ∀ b ∈ bds_24, m_24 &&& b.1 = b.1 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_24 : ∀ b ∈ bds_24, canon b.1 g_24 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_24 : Nat → Nat × Nat := fun _ => (0, 0)
def l_24 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsF m_24 g_24 bds_24 (dagRefF 0 (dagTraceF m_24 s_24 4 f_24) l_24 0) s_24 4 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_24 g_24 bds_24 0 (dagTraceF m_24 s_24 4 f_24) l_24 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_24 sub_24 gl_24 rc_24 nc_24

def m_25 : Nat := 0xff000000ff0000
def s_25 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_25 : Nat := 0x150000007f0000
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_25 : KnownBin bds_25 := by
  intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_25 : ∀ b ∈ bds_25, m_25 &&& b.1 = b.1 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_25 : ∀ b ∈ bds_25, canon b.1 g_25 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_25 : Nat → Nat × Nat := fun _ => (0, 0)
def l_25 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsF m_25 g_25 bds_25 (dagRefF 0 (dagTraceF m_25 s_25 4 f_25) l_25 0) s_25 4 = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_25 g_25 bds_25 0 (dagTraceF m_25 s_25 4 f_25) l_25 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_25 : LowerBin m_25 s_25 g_25 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_25 sub_25 gl_25 rc_25 nc_25

def m_26 : Nat := 0xff000000ff
def s_26 : List Nat := [0x5500000055, 0x3300000033, 0xf0000000f, 0xff]
def g_26 : Nat := 0x370000007f
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
theorem kn_26 : KnownBin bds_26 := by
  intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_4
theorem sub_26 : ∀ b ∈ bds_26, m_26 &&& b.1 = b.1 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_26 : ∀ b ∈ bds_26, canon b.1 g_26 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_26 : Nat → Nat × Nat := fun _ => (0, 0)
def l_26 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsF m_26 g_26 bds_26 (dagRefF 0 (dagTraceF m_26 s_26 4 f_26) l_26 0) s_26 4 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_26 g_26 bds_26 0 (dagTraceF m_26 s_26 4 f_26) l_26 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_26 : LowerBin m_26 s_26 g_26 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_26 sub_26 gl_26 rc_26 nc_26

def m_27 : Nat := 0x5555555500000000
def s_27 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_27 : Nat := 0x115151500000000
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
theorem kn_27 : KnownBin bds_27 := by
  intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_7
theorem sub_27 : ∀ b ∈ bds_27, m_27 &&& b.1 = b.1 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_27 : ∀ b ∈ bds_27, canon b.1 g_27 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_27 : Nat → Nat × Nat := fun _ => (0, 0)
def l_27 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsF m_27 g_27 bds_27 (dagRefF 0 (dagTraceF m_27 s_27 4 f_27) l_27 0) s_27 4 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_27 g_27 bds_27 0 (dagTraceF m_27 s_27 4 f_27) l_27 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_27 sub_27 gl_27 rc_27 nc_27

def m_28 : Nat := 0x55555555
def s_28 : List Nat := [0x11111111, 0x5050505, 0x550055, 0x5555]
def g_28 : Nat := 0x1551555
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
theorem kn_28 : KnownBin bds_28 := by
  intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_8
theorem sub_28 : ∀ b ∈ bds_28, m_28 &&& b.1 = b.1 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_28 : ∀ b ∈ bds_28, canon b.1 g_28 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_28 : Nat → Nat × Nat := fun _ => (0, 0)
def l_28 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsF m_28 g_28 bds_28 (dagRefF 0 (dagTraceF m_28 s_28 4 f_28) l_28 0) s_28 4 = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_28 g_28 bds_28 0 (dagTraceF m_28 s_28 4 f_28) l_28 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_28 : LowerBin m_28 s_28 g_28 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_28 sub_28 gl_28 rc_28 nc_28

def m_29 : Nat := 0x3333333300000000
def s_29 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_29 : Nat := 0x111113300000000
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
theorem kn_29 : KnownBin bds_29 := by
  intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_6
theorem sub_29 : ∀ b ∈ bds_29, m_29 &&& b.1 = b.1 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_29 : ∀ b ∈ bds_29, canon b.1 g_29 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_29 : Nat → Nat × Nat := fun _ => (0, 0)
def l_29 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsF m_29 g_29 bds_29 (dagRefF 0 (dagTraceF m_29 s_29 4 f_29) l_29 0) s_29 4 = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_29 g_29 bds_29 0 (dagTraceF m_29 s_29 4 f_29) l_29 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_29 : LowerBin m_29 s_29 g_29 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_29 sub_29 gl_29 rc_29 nc_29

def m_30 : Nat := 0xcccccccc
def s_30 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_30 : Nat := 0x4c044c
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
theorem kn_30 : KnownBin bds_30 := by
  intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_11
theorem sub_30 : ∀ b ∈ bds_30, m_30 &&& b.1 = b.1 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_30 : ∀ b ∈ bds_30, canon b.1 g_30 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_30 : Nat → Nat × Nat := fun _ => (0, 0)
def l_30 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsF m_30 g_30 bds_30 (dagRefF 0 (dagTraceF m_30 s_30 4 f_30) l_30 0) s_30 4 = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_30 g_30 bds_30 0 (dagTraceF m_30 s_30 4 f_30) l_30 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_30 : LowerBin m_30 s_30 g_30 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_30 sub_30 gl_30 rc_30 nc_30

def m_31 : Nat := 0xf0f0f0f000000000
def s_31 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_31 : Nat := 0x10103000000000
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
theorem kn_31 : KnownBin bds_31 := by
  intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_6
theorem sub_31 : ∀ b ∈ bds_31, m_31 &&& b.1 = b.1 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_31 : ∀ b ∈ bds_31, canon b.1 g_31 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_31 : Nat → Nat × Nat := fun _ => (0, 0)
def l_31 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsF m_31 g_31 bds_31 (dagRefF 0 (dagTraceF m_31 s_31 4 f_31) l_31 0) s_31 4 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_31 g_31 bds_31 0 (dagTraceF m_31 s_31 4 f_31) l_31 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_31 sub_31 gl_31 rc_31 nc_31

def m_32 : Nat := 0xf0f0f0f00000000
def s_32 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_32 : Nat := 0x105050700000000
def bds_32 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_32 : KnownBin bds_32 := by intro b hb; simp [bds_32] at hb
theorem sub_32 : ∀ b ∈ bds_32, m_32 &&& b.1 = b.1 := by intro b hb; simp [bds_32] at hb
theorem gl_32 : ∀ b ∈ bds_32, canon b.1 g_32 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_32] at hb
def f_32 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_32 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsF m_32 g_32 bds_32 (dagRefF 64 (dagTraceF m_32 s_32 5 f_32) l_32 0) s_32 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32_0 : treeBlockF 0 32 (dagCheckNodeF m_32 g_32 bds_32 64 (dagTraceF m_32 s_32 5 f_32) l_32) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32_1 : treeBlockF 32 64 (dagCheckNodeF m_32 g_32 bds_32 64 (dagTraceF m_32 s_32 5 f_32) l_32) = true := by decide +kernel
theorem nj_32_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_32 g_32 bds_32 64 (dagTraceF m_32 s_32 5 f_32) l_32) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_32_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_32_1 h1 h2)
theorem nc_32 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_32 g_32 bds_32 64 (dagTraceF m_32 s_32 5 f_32) l_32) i = true := nj_32_1
theorem lb_32 : LowerBin m_32 s_32 g_32 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_32 sub_32 gl_32 rc_32 nc_32

def m_33 : Nat := 0xf0f0f0f
def s_33 : List Nat := [0x5050505, 0x3030303, 0xf000f, 0xf0f]
def g_33 : Nat := 0x10f070f
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_33 : KnownBin bds_33 := by
  intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_33 : ∀ b ∈ bds_33, m_33 &&& b.1 = b.1 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_33 : ∀ b ∈ bds_33, canon b.1 g_33 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
def l_33 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsF m_33 g_33 bds_33 (dagRefF 0 (dagTraceF m_33 s_33 4 f_33) l_33 0) s_33 4 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_33 g_33 bds_33 0 (dagTraceF m_33 s_33 4 f_33) l_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_33 sub_33 gl_33 rc_33 nc_33

def m_34 : Nat := 0xff00ff0000000000
def s_34 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_34 : Nat := 0x100150000000000
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

def m_35 : Nat := 0xff00ff00
def s_35 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_35 : Nat := 0x1003700
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
theorem kn_35 : KnownBin bds_35 := by
  intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_8
theorem sub_35 : ∀ b ∈ bds_35, m_35 &&& b.1 = b.1 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_35 : ∀ b ∈ bds_35, canon b.1 g_35 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_35 : Nat → Nat × Nat := fun _ => (0, 0)
def l_35 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsF m_35 g_35 bds_35 (dagRefF 0 (dagTraceF m_35 s_35 4 f_35) l_35 0) s_35 4 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_35 g_35 bds_35 0 (dagTraceF m_35 s_35 4 f_35) l_35 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_35 : LowerBin m_35 s_35 g_35 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_35 sub_35 gl_35 rc_35 nc_35

def m_36 : Nat := 0xffff000000000000
def s_36 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_36 : Nat := 0x115000000000000
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
theorem kn_36 : KnownBin bds_36 := by
  intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_10
theorem sub_36 : ∀ b ∈ bds_36, m_36 &&& b.1 = b.1 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_36 : ∀ b ∈ bds_36, canon b.1 g_36 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
def l_36 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsF m_36 g_36 bds_36 (dagRefF 0 (dagTraceF m_36 s_36 4 f_36) l_36 0) s_36 4 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_36 g_36 bds_36 0 (dagTraceF m_36 s_36 4 f_36) l_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_36 sub_36 gl_36 rc_36 nc_36

def m_37 : Nat := 0xffff0000
def s_37 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_37 : Nat := 0x17f0000
def bds_37 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_37 : KnownBin bds_37 := by intro b hb; simp [bds_37] at hb
theorem sub_37 : ∀ b ∈ bds_37, m_37 &&& b.1 = b.1 := by intro b hb; simp [bds_37] at hb
theorem gl_37 : ∀ b ∈ bds_37, canon b.1 g_37 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_37] at hb
def f_37 : Nat → Nat × Nat := unpackForestF 0xf938f934063fed28ed24063b0637e3440633d638d634053fc93cc934053b0537be440533b24cb244052fa54ca544052b05279a340523043f043b7e4c7e407d4c7d400437683c6834682c68240433042f042b4f484f404d3c4d300427384c3844382c38240423041f041b1e481e401e381e300417084c0844083c08340413000f 6 10
def l_37 : Nat → Nat → Option Nat := unpackLinksF 0x8608608228208207e27c17c07a17a07a07627607607227017006e16e06e06a26a06a06626416406216206206206206206205a45a05a05a05a05245205205205205205204a44a04a04a04a04244204204204204204203a43a03a03a03a0324038001 0xfd38f934f128ed24e230e344da38d634cd3cc934bd30be44b64cb244a94ca54499209a348a4c8640814c7d40743c70346c2c68245b485740513c4d30444c40443c2c38242a48264022381e30144c10440c3c0834f63fea3be637de33d13fc53bc137b933ad2fa12b9d279523903f8c3b78376433602f5c2b48273423301f2c1b18170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsF m_37 g_37 bds_37 (dagRefF 64 (dagTraceF m_37 s_37 5 f_37) l_37 0) s_37 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_37_0 : treeBlockF 0 32 (dagCheckNodeF m_37 g_37 bds_37 64 (dagTraceF m_37 s_37 5 f_37) l_37) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_37_1 : treeBlockF 32 64 (dagCheckNodeF m_37 g_37 bds_37 64 (dagTraceF m_37 s_37 5 f_37) l_37) = true := by decide +kernel
theorem nj_37_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_37 g_37 bds_37 64 (dagTraceF m_37 s_37 5 f_37) l_37) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_37_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_37_1 h1 h2)
theorem nc_37 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_37 g_37 bds_37 64 (dagTraceF m_37 s_37 5 f_37) l_37) i = true := nj_37_1
theorem lb_37 : LowerBin m_37 s_37 g_37 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_37 sub_37 gl_37 rc_37 nc_37

def m_38 : Nat := 0xffff
def s_38 : List Nat := [0x5555, 0x3333, 0xf0f, 0xff]
def g_38 : Nat := 0x377f
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
theorem kn_38 : KnownBin bds_38 := by
  intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_11
theorem sub_38 : ∀ b ∈ bds_38, m_38 &&& b.1 = b.1 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_38 : ∀ b ∈ bds_38, canon b.1 g_38 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
def l_38 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsF m_38 g_38 bds_38 (dagRefF 0 (dagTraceF m_38 s_38 4 f_38) l_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_38 g_38 bds_38 0 (dagTraceF m_38 s_38 4 f_38) l_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_38 sub_38 gl_38 rc_38 nc_38

def m_39 : Nat := 0xaaaaaaaaaaaaaaaa
def s_39 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_39 : Nat := 0x22002a222a
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 5, g_12), (m_13, s_13, 5, g_13), (m_19, s_19, 5, g_19), (m_0, s_0, 4, g_0)]
theorem kn_39 : KnownBin bds_39 := by
  intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_12
  · exact lb_13
  · exact lb_19
  · exact lb_0
theorem sub_39 : ∀ b ∈ bds_39, m_39 &&& b.1 = b.1 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_39 : ∀ b ∈ bds_39, canon b.1 g_39 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def f_39 : Nat → Nat × Nat := unpackForestF 0x10bc857f50e98109e48112049a20b084601f 3 10
def l_39 : Nat → Nat → Option Nat := unpackLinksF 0xe1c34e1972243a70a8601 0x50c10208d41d3030816404480d3420b282f90ad827108c01f 7 3 10 4 4
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsF m_39 g_39 bds_39 (dagRefF 11 (dagTraceF m_39 s_39 6 f_39) l_39 0) s_39 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_39_0 : treeBlockF 0 11 (dagCheckNodeF m_39 g_39 bds_39 11 (dagTraceF m_39 s_39 6 f_39) l_39) = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 11 → (dagCheckNodeF m_39 g_39 bds_39 11 (dagTraceF m_39 s_39 6 f_39) l_39) i = true := fun _ h1 h2 => treeBlockF_at nb_39_0 h1 h2
theorem lb_39 : LowerBin m_39 s_39 g_39 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_39 sub_39 gl_39 rc_39 nc_39

def m_40 : Nat := 0x5555555555555555
def s_40 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_40 : Nat := 0x115151501551555
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 5, g_18), (m_27, s_27, 5, g_27), (m_28, s_28, 5, g_28), (m_7, s_7, 4, g_7)]
theorem kn_40 : KnownBin bds_40 := by
  intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_18
  · exact lb_27
  · exact lb_28
  · exact lb_7
theorem sub_40 : ∀ b ∈ bds_40, m_40 &&& b.1 = b.1 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_40 : ∀ b ∈ bds_40, canon b.1 g_40 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def f_40 : Nat → Nat × Nat := unpackForestF 0x2d3c5a5c15c168e51515a21234368844d05a1801f 4 11
def l_40 : Nat → Nat → Option Nat := unpackLinksF 0xe1c3862a5424c882ac601 0x19a0415c546864d15a21b4468a888d089a534f9696ed1c5a1801f 7 3 11 4 4
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsF m_40 g_40 bds_40 (dagRefF 11 (dagTraceF m_40 s_40 6 f_40) l_40 0) s_40 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_0 : treeBlockF 0 11 (dagCheckNodeF m_40 g_40 bds_40 11 (dagTraceF m_40 s_40 6 f_40) l_40) = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 11 → (dagCheckNodeF m_40 g_40 bds_40 11 (dagTraceF m_40 s_40 6 f_40) l_40) i = true := fun _ h1 h2 => treeBlockF_at nb_40_0 h1 h2
theorem lb_40 : LowerBin m_40 s_40 g_40 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_40 sub_40 gl_40 rc_40 nc_40

def m_41 : Nat := 0xcccccccccccccccc
def s_41 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_41 : Nat := 0x40404004c044c
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_20, s_20, 5, g_20), (m_21, s_21, 5, g_21), (m_30, s_30, 5, g_30), (m_3, s_3, 4, g_3)]
theorem kn_41 : KnownBin bds_41 := by
  intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_20
  · exact lb_21
  · exact lb_30
  · exact lb_3
theorem sub_41 : ∀ b ∈ bds_41, m_41 &&& b.1 = b.1 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_41 : ∀ b ∈ bds_41, canon b.1 g_41 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def f_41 : Nat → Nat × Nat := unpackForestF 0xb4f2d2fa50e140b47890204051510382d0c01f 3 11
def l_41 : Nat → Nat → Option Nat := unpackLinksF 0xe1c34e1972243a70a8601 0x15a0234036810941c282a404080715081c534f9696cd1c5a1801f 7 3 11 4 4
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsF m_41 g_41 bds_41 (dagRefF 11 (dagTraceF m_41 s_41 6 f_41) l_41 0) s_41 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_0 : treeBlockF 0 11 (dagCheckNodeF m_41 g_41 bds_41 11 (dagTraceF m_41 s_41 6 f_41) l_41) = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 11 → (dagCheckNodeF m_41 g_41 bds_41 11 (dagTraceF m_41 s_41 6 f_41) l_41) i = true := fun _ h1 h2 => treeBlockF_at nb_41_0 h1 h2
theorem lb_41 : LowerBin m_41 s_41 g_41 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_41 sub_41 gl_41 rc_41 nc_41

def m_42 : Nat := 0x3333333333333333
def s_42 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_42 : Nat := 0x111113301333333
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 5, g_14), (m_15, s_15, 5, g_15), (m_29, s_29, 5, g_29), (m_0, s_0, 4, g_0)]
theorem kn_42 : KnownBin bds_42 := by
  intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_14
  · exact lb_15
  · exact lb_29
  · exact lb_0
theorem sub_42 : ∀ b ∈ bds_42, m_42 &&& b.1 = b.1 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_42 : ∀ b ∈ bds_42, canon b.1 g_42 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def f_42 : Nat → Nat × Nat := unpackForestF 0x52f14ae03c149ca3454909543490814148c01f 4 10
def l_42 : Nat → Nat → Option Nat := unpackLinksF 0xe1c3862a5424c882ac601 0x648203c5510c145490d2468d1154205292f94add27148c01f 7 3 10 4 4
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsF m_42 g_42 bds_42 (dagRefF 11 (dagTraceF m_42 s_42 6 f_42) l_42 0) s_42 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_0 : treeBlockF 0 11 (dagCheckNodeF m_42 g_42 bds_42 11 (dagTraceF m_42 s_42 6 f_42) l_42) = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 11 → (dagCheckNodeF m_42 g_42 bds_42 11 (dagTraceF m_42 s_42 6 f_42) l_42) i = true := fun _ h1 h2 => treeBlockF_at nb_42_0 h1 h2
theorem lb_42 : LowerBin m_42 s_42 g_42 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_42 sub_42 gl_42 rc_42 nc_42

def m_43 : Nat := 0xf0f0f0f0f0f0f0f0
def s_43 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_43 : Nat := 0x10103000703070
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_23, s_23, 6, g_23), (m_12, s_12, 5, g_12), (m_14, s_14, 5, g_14), (m_17, s_17, 5, g_17), (m_22, s_22, 5, g_22), (m_31, s_31, 5, g_31), (m_0, s_0, 4, g_0), (m_5, s_5, 4, g_5), (m_6, s_6, 4, g_6)]
theorem kn_43 : KnownBin bds_43 := by
  intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_23
  · exact lb_12
  · exact lb_14
  · exact lb_17
  · exact lb_22
  · exact lb_31
  · exact lb_0
  · exact lb_5
  · exact lb_6
theorem sub_43 : ∀ b ∈ bds_43, m_43 &&& b.1 = b.1 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_43 : ∀ b ∈ bds_43, canon b.1 g_43 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_43 : Nat → Nat × Nat := unpackForestF 0x25049328148005a7802d2e454b922a5192495c945524924722a50914a848a172450a000b4790c12c648e632071202318c81ac664be332571db408ec1846649e384611c0208d91a46c062332471982b8cc11c640d001687170488b822c5c1100149f0c45989d22c4e1162847d1423289c2243114625ad10c24f88c1ac3093a184870c02f87c9e4300ae1804f0e24286012c340b2192690c02300525c2c0d6136a30a35984c2e80291e0f47d0792883c1280290e0d0bb0535682dad4140d40147f03a3e81c940028ee018b100c50804a04021320108000a377c5adbfc971f14b6fda4d7ec12be2969f14aefb45e7d924bec175f14acf882f7c413be4969f104a00a337bc1abd8539ed284f6015004a5bd405401286f401578ca5bcc175e328ef193f78c998024f9e12580093b77c2ebb8559dd2b4ee01500499bb4095ce496e723973919ba692dd348ee982f74c13b9c8c5d10bae714773d2d39c05c01264e61546d22fb6916dc66c0e316c7183638c181b48aee114470824384111b48a6de3516f1a4b7c0d1bc682de05d6d0ab370d69b86acdc0356d0a736a569b5284da01500495b64551958becac5b6b1b03585b1ac0d8d60606562bb50511a8090d404465629b4c0d1a06a2d034d68928344141a068ad005d654ab334d699d0b8cd35666dac3340d59529ccb15a65caa32c5099502a0092364d2ab169658b492c796463caa3164ad8c2a8c601462c9180213d89268bd35b61cb62f4d5d85248bd25b608923040917a476bfa645fc122f48cd7a0acbdb5a5edab2f40f8010968c35b461a9aec8e5186a28c25f5cdb623096d706c0b81604612bad8d416c4b8b61505a9b22d44a1184a6b2a4e594952cc9016524c8c251589b02c409118496ae451571af2b8d495c054ae02646124ab2941590d88c2475592f2ac8f918482a836c541b22a0d51504c0a80344611fa8d181466c0a326c5193228c98149480a325451d2828c091184668c15b460a9a8405118296a01344f8a8a7c5251827c9bc604dcb6274941372c89b9544dc0a2304cd246a49a239491a8264491244a29845049124a58d412c4b89625049118a48575294a09215549da0248515256a0920164609923cd811e2d88f164478aa23c051182568cb60464b6234d41192c88c12300423a2c090f34768926444892224090f34667d24f43c121f492d0b6a08595042c2e1f491d0868084140419aa20c4a0fa486820143e8a59f450d010287d12b3f4ae1fcd00fd2a87d1233ec9c9f4138f32a87aa4e3d5211ea538f52847a0543cc1f00210cf069a78239381ad1d91a0ec498760243812d9d2d80e90d870257398a61cc050e02b67194c38c0a1c04ace1298701230041f9bc090d84766d92436c121b08ccd807c6c02c0041d983160c18a060a4c305209a04acd10286812330520182500caad065560329a8194570c12566156830ab0184d40c22b861c5030d20184050c1246008372f89a17c0d0926b65d4602e8b61741b0926ae5b9242dc1212496cb42485a0242491d964090924665792b2bc91924170a94a254a492ad20152914a9292490562592794c0909649651350288a81441709648e4fb4027ca013ad509d2504b24326c0a12c52c962864c0142589592c48c920a849a5a24d2b1240f80106621c5b2352411a9108d08821c5310dad886d4c4368621a5f219b610c090434b640a4e2051e9044f08104c21a5a10d2b8f1178786a23c3491ec1a0f0d04784923c24110d2b0ec970746c83a02410d2988693c6f6b437b561bd208869386d04821a431a12d0d09586849a3402610d210ca568652ac2194e18d260c2968614ac21942179ac0bc990430be2e02610c2d0b0d80594802c25410c2b89ad444d4bc26a521352489a9044d29a269451341f09cd404d06421856129ad0945344309c220561192708c908440a82202610c210020bc3f0b81f8560fc2a0020ac278b61d3480ec98074110278a61ac590dc2206b1443549c13b5a0c629062968314ac13b420bd2d04e5382b6d015b580ad2c04e17c286b01426009c2b80209c252680ab5b08c9a02ad4c1f4920fa4107c2f02a5581b4a20da4906d2082a158174b40ba5605c2b02a0f815058008230122d8225101108802453031a8818d240d06806341010ab012d68096ac0214e01cb200817c052a8020570040f804158010260001f 10 11
def l_43 : Nat → Nat → Option Nat := unpackLinksF 0x436021b010c84854442a0214050a008500427061285094084614210a0c91064082e14150a0a03038681a0c0c060583028180c2406020301010280804010e000300007ee4bed29f680fb407da03ea0df404fa007d003e801f400f9827c61be301f084f8407ba23db09eb88f5817a61bd00de800f10c78803c305df88ea1775003a50dd280e70972843910dc880e34470e338701c206e1007021b7c15be00df006f21b7901bc80de406f2037901ba0adc826e4036f0db780dbc06d6236909b480da406d2036415b086d7c26be035a15a61cd300694134a01a20ccf8667c033d059e80ce836740339059c80ce406624331019802cc0065a1b2d019506c9c364e03240d9200c9006480324019200c90063e2b1f018e06c7006321b11218880c40161c130e018700c38061c030a118500c2806120b05118280c14060a0304058200bf085f802fc017e00be045f002f8017810b84f5c202df096f02b7415ba02dd016e02b5c55ae02d7016b80b5035a802d3056980b4c05a602d1096880b24859202c9016402b20058e0ac3116180b0c05840aba21559eaac055212a5115280a94054612a3015180a8425324299014a88a5405241a92014882a440522028f094780a3c051a1289114480a24050a227d213e029e824f20a7121360a9ac14cc2a6409310496c74b40a5a012c8295444a80a4e192700938049c024d051ea08f014760a380d1b828dc046e0237011b808b4a45a022d0114888a404520225111280894044a02250112808805440021d0d0e0287004360a1b010d0286804320a102506868301418020b05058082814140206110300818040c020505028081404002a000100007e863f401f70cfb807d813ec01f600fb007cc33e601f300f9027c803e209f100f802794b3ca01e500f28079403ca01df18ef8077813ba09db08eb886e5e37009b608da826d0136801b010d7046b8035a09ac04d5826ac034e21a700d380694234a01a110d080680134001a000cf8267c033e019e04ce046700334119028c8006400320019000c60862c130e218700c3806085304018200c1005f842fc017e00be045f002f8017a08bd005e802f0117800bb825bc82de016e04b7005b802d8116c00b6005a042cc116408b20058822c4016200b08257c22be015f00af8057c02be015b10ad8056812b2095900ac8056402ae115214a5105241292014510a28051012880140109f824fc0278193b049d804dc426e01340c9a004d0026411310498024c0025c112d04938c498124c012504920248c1246011f108f8047c023a111d008d0646802320919008c804601230010f24878043c021a1103287f883fc01fe00fe047d083d841e420f00876863b011d800e810738239421ca00e4046d1435c31ac08d6006b0035801aa08d5006a80324c19200c8046400310418410c2006100308017c20be005e042f0017800bc005e002e0417000b8005a862d4016808b40058862c4016200ad1056802ac215408aa005482298314a08a5005280294014a00a5005280294014a00a4044d1426801340098084c0026001300096084b0024c30f8b87c003e001f000f21877083b801dc00ea10711038801c400e0087000339219c00ce006700320619000c6086300318018c00c0186000300017040a840540028081400098204c002600130009020480024001200088204400220011000821841001d8c0e420720038041a860d4006a0035001a020b8605c002e0016040b00056082b001502090604800230400c40001 0x2514932814872c95b6248e2c4b2fd23172895b6048cef07a4802f0f41382607dc9272d7931928aa4964ae49246e381b6b409b8c4adac24726a5c93128c90942472a0e292b6ac91c8c172450a04782d90c12b864ada92461d8348a92c91e8e6404624682e0e81302207a292b03d9548e490470480376b11e3408dc904760c2394611c0208a12c46e8d2360300685489ca4c7c4be3d2571d1278d491c680ae33046e101b6a009c4c96642472e092b69c91c820e23f06b190342301787209c1003f180488bc22c5c112254ba7704d8a51f4508ca2b48b1504589c2244b5a1fc4a0fe34d7f9209da0f62306afe35c7dd320f2991634990f8382041a4340915d2c90f93c0b01a2b8190810590c8203b527438909e829ced1426242d2c4158ec09c5f8422181f04a0c88105c0c82d868164324d01c0c8be04c0641e459166268a2ffb4389127c4493a21486fd24279ca73b2509920bac405b5842bab6154eb09e5e84322c1f8480ce2005e4002d87815c3a09e1b04b0c0232f0209d40f61606a0cc5d0622ac28d64ea6a2f313e61c252b2118e907c5d8328462ec2ad45e527d0985d61825ab011ce807e5c8335582a8320b42c04a0ca3e075190e80f82306508a3e840942aa1548a07e1103383c12c1a175530aaa904582dad2a6d59500ad06356821a73c85394f0af050358211f3b05020725102c588122840650202099008407f9ae3ee991f86c8ff25c758a83f0955fc49a3582d7ec12bf0961d5280fc45e7dd24bec1754b0aaa40451bd2e3a854068068e99501a0163e49694b4aca30561b41f0d00b9ff6b6fea5b7e92d3f295df54acf194e75ca13a4501450ae4483f7d0178ce0b5f304ef882539c1ebde0d4e729cf69426142d284158e609c5c0427b8a730816d410ae7284f2d821bd8055ea02a9f0551980ebd0055e60baf0a3e79ca5bca51de427ef19334f4238c807c2e02ef092c77c2ea721553808aee95a4e4ab26e159de2ac9b0577700aa5e1546205aed02575925baa91d2b08eea02f74c13ba2175280aa9304573d2d250959240aceca4b7611cbae8cdd2462e814748c238c00bdce02ee61546fcb2374531c96c0e416c71c3638c181be0a8de964710a2386121c2088df0346e9acb80d45bf692deb416f02ea401559009a8f8456e9ad372d58e407adc0356d8ad240558e429cda94260c2d23c158e309c5a84272e2fb9516dc58aee0c536ecab36e5398e0bec085b4742ba2a14ce209e6e84b3242396610db402ad21646c8aa33c531a32a8d11546bdb035c5b1a12a8d686c6b030354511a9090d40446981a346941a20a0cf359695a8b48d35a168ad005d4642ab0012514082ce85c66dac33cd699c6ac7083d6681ab2e551982b48c956384a732c5098c0bc8985237025184119b18bed845b6ae2bb4f14d9f2accc94e62c2fafc16d180ae88853380279b412cc108e588436540ab26955560aa2f83d0ac1a8320b42c04ac816463caa31a5518c028c925964524b1c4ad8b246be8451741785409c0603ec4934558322f813019078c396c060362f60f185248c1924608123009917f0480ca5907528aac9241705cbe35a5edab032968184acc435b619abb0896d81476bf23316c9f2fa1597a07c78c603c63426a5013428078b4d5812ca9c90576472a52314f0a0a665005605c0ec6c5cd342be961100a02a82c5b5222e6db0836c02c254438282c40916e4a0868405b12821810019ad814c6c5c5b02d6941702c0ac86c4282021210108080b73505b52e2d8541070808304020db42d6d915e6b0b5128414280a80f166480b1b5a569ab2a2d394d684b424e529210328f88347a9f94e4c4a12444e51c262b392a594930b40f42806a41034209282c6d80194d0b10244c0a81dd165608a2afb5e579a927c5392f2842983e084192ba0a95c04c0cd6c55a362b4941590d8aba5e5591f0a40f820064aa36c54db22a4d51514c0a80345252a25c50147048969304b0a0292901474a0a7460535b02989b06b4d0a5a64529302909512b280a3024014aa20614142028810505080a2804d0662b29f9514f8a489e0793a4a09e4604ecb6272591382a89b8144c124a688e52c462939451381724a0592e680962404c8922611412e6a096a5c4b1282529412768092b504d5a9266d40624b298a514bd24a568c52a2ba94155498a289a0b92402c91360484b62405911f2a8800504780a1fe140fe0808d3503f420238d811b2d88c9643f0282f0d6cef6b2bbb535d5a8ae897d724b6402595bd2bad294d644a2b0a4b56d24ab091d55482a7a3f51519a8856d432a6a094b4f49f26c4cd232648e92b460919f21005705e2602e09c1383c0880403e80854400b222c090fd2a87e954451321f859113248890243d8221f00b10f04884a404212021ad41074808615042c2e212d010828083b54418941ee0f0f5058820144040a1fcd00ff2b87e9543ec9c9ea4c51049e8724b42923a0a90d0329681143400959f848cfa09c7a02e3e1271ee908f629c7a9423d02a22a8ed114667c9543cc1f1e2d34ee4b2782391ad188960b8ee8d076a4c1ad201d8090ea6c07486c39ca61cc050e429871814384a61ded68eb4b67425719d189ca56ce225670123124171bc090dc2486d8243751d9b48ccd907c6c02c3349599048ccc2566392332c9c98c4c4d10286912b3409199b5a0ccac065b50328ae188050c30286245030d201915a0c7ac063350314ae184050d68b06ac50351261a6904cf480671403249598248ca60a85f9342b0321280f0be068510442f2301765b0ba0d85505426c2a170490a90c85b8242602a16a490b00d84b8642d01215e1b0960c8590242c09595e48cab6a8530242ad201441709b0284a2592b528958924aa48a549491201708e0b0a60485024027d20148d409e480519502882e140d009f2804f3542749408c0f09b0284c01429d2794a92ca148e4e243268a593250c972564b12311417128968934ac5eb5b2e5ab96c96cb347658a3310c9f15c170a80ac4a8542481f0f89907149835a4012c260f65507a4c847a482392211a110796c80ca3014c3210c090786c80ca3c148320e80906f6b83682421d34030950510c83b25421db60fcd905a4984302418ca00b2d50820684113c0612b0fc9548449c35a420751f1068f46629c31142204130580947e4b03aa501402a0b28f07b0683f45e0662e8e2d647d6a23e3491e9a08f2924784823293e184990bc1345808a3b25c1d5b20be930194783a0241a528094170716b4383561a5a68de904696b8368241ad2d0d49586949a34026198ad0ca5584f0ac31a4c1892d0c29584d0ac2fb5817932032960170a80b856170130b2d50594802d360065340b09504e0802735012dac8acd44554bc2a25214d248a49045129a2814513c1f09a0c84b6b42514d11d2708c908480ac228541101312116c8c8a645b5b229a9912d0c884be42a5b2012d0fe95c774ac39a531c9278dc9386c48633a42190a70c05085d0be2d85a15c2b8981584909c218421042e0801583f0a81c3680c9a006e9603b2601b3680cda8078d203a0881b8440e22c86d1443549c192420bca705a174290aa0c82d0b012867148324b418a560bd2d05ada02c6b015a58065b4052d60284c00b83c0f62d87314c346b4183420b8a705417c270ae0b03d084b204a4d01c0c80c83c080b20464d01b0c80e834085248409041f0bc0b82e0652c83a9441c4920da410652d030958170ac1235b089a983c5581a0ac0b03e0541601c5900a29806854030b20245101108806834029ac81ed440e6920634101c2680a1140a6b404b5601cb200a550138b60845302cab010538060be020570082b49ed3e4e697223478c5a1c5a93e174970924783921c128fe06477002377c119bd652de9286f113e7809dbb64cdcd264d992b65091b1413d790968b8473c8219be0fcd707660037244198840bc3e056130270501180607c010260001f 17 6 11 10 7
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsF m_43 g_43 bds_43 (dagRefF 594 (dagTraceF m_43 s_43 8 f_43) l_43 0) s_43 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_0 : treeBlockF 0 32 (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_1 : treeBlockF 32 64 (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_2 : treeBlockF 64 96 (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_3 : treeBlockF 96 128 (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_4 : treeBlockF 128 160 (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_5 : treeBlockF 160 192 (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_6 : treeBlockF 192 224 (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_7 : treeBlockF 224 256 (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_8 : treeBlockF 256 288 (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_9 : treeBlockF 288 320 (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_10 : treeBlockF 320 352 (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_11 : treeBlockF 352 384 (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_12 : treeBlockF 384 416 (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_13 : treeBlockF 416 448 (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_14 : treeBlockF 448 480 (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_15 : treeBlockF 480 512 (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_16 : treeBlockF 512 544 (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_17 : treeBlockF 544 576 (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_18 : treeBlockF 576 594 (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
theorem nj_43_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_43_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_43_1 h1 h2)
theorem nj_43_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_1 (fun _ h1 h2 => treeBlockF_at nb_43_2 h1 h2)
theorem nj_43_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_2 (fun _ h1 h2 => treeBlockF_at nb_43_3 h1 h2)
theorem nj_43_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_3 (fun _ h1 h2 => treeBlockF_at nb_43_4 h1 h2)
theorem nj_43_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_4 (fun _ h1 h2 => treeBlockF_at nb_43_5 h1 h2)
theorem nj_43_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_5 (fun _ h1 h2 => treeBlockF_at nb_43_6 h1 h2)
theorem nj_43_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_6 (fun _ h1 h2 => treeBlockF_at nb_43_7 h1 h2)
theorem nj_43_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_7 (fun _ h1 h2 => treeBlockF_at nb_43_8 h1 h2)
theorem nj_43_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_8 (fun _ h1 h2 => treeBlockF_at nb_43_9 h1 h2)
theorem nj_43_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_9 (fun _ h1 h2 => treeBlockF_at nb_43_10 h1 h2)
theorem nj_43_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_10 (fun _ h1 h2 => treeBlockF_at nb_43_11 h1 h2)
theorem nj_43_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_11 (fun _ h1 h2 => treeBlockF_at nb_43_12 h1 h2)
theorem nj_43_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_12 (fun _ h1 h2 => treeBlockF_at nb_43_13 h1 h2)
theorem nj_43_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_13 (fun _ h1 h2 => treeBlockF_at nb_43_14 h1 h2)
theorem nj_43_15 : ∀ i, 0 ≤ i → i < 512 → (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_14 (fun _ h1 h2 => treeBlockF_at nb_43_15 h1 h2)
theorem nj_43_16 : ∀ i, 0 ≤ i → i < 544 → (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_15 (fun _ h1 h2 => treeBlockF_at nb_43_16 h1 h2)
theorem nj_43_17 : ∀ i, 0 ≤ i → i < 576 → (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_16 (fun _ h1 h2 => treeBlockF_at nb_43_17 h1 h2)
theorem nj_43_18 : ∀ i, 0 ≤ i → i < 594 → (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_17 (fun _ h1 h2 => treeBlockF_at nb_43_18 h1 h2)
theorem nc_43 : ∀ i, 0 ≤ i → i < 594 → (dagCheckNodeF m_43 g_43 bds_43 594 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := nj_43_18
theorem lb_43 : LowerBin m_43 s_43 g_43 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_43 sub_43 gl_43 rc_43 nc_43

def m_44 : Nat := 0xf0f0f0f0f0f0f0f
def s_44 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_44 : Nat := 0x1050507010f070f
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_32, s_32, 6, g_32), (m_13, s_13, 5, g_13), (m_15, s_15, 5, g_15), (m_16, s_16, 5, g_16), (m_24, s_24, 5, g_24), (m_33, s_33, 5, g_33), (m_1, s_1, 4, g_1), (m_2, s_2, 4, g_2), (m_9, s_9, 4, g_9)]
theorem kn_44 : KnownBin bds_44 := by
  intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_32
  · exact lb_13
  · exact lb_15
  · exact lb_16
  · exact lb_24
  · exact lb_33
  · exact lb_1
  · exact lb_2
  · exact lb_9
theorem sub_44 : ∀ b ∈ bds_44, m_44 &&& b.1 = b.1 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_44 : ∀ b ∈ bds_44, canon b.1 g_44 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_44 : Nat → Nat × Nat := unpackForestF 0x25048b28044005a7802d2e4d2b31e25d8f0ae4944da3c2a31e92f8f495c8c0f23d24f2023490c9248055241249200148f491c7a07e3d02f1e150005a3c648e23246b1b02f8dda046c09e32469191388c89a4640d0016871804400527c5495a2d2731524e8aca74544a40149710b5b885a9c4c4e6216a31095b884a9c4453a212a200a4786d264369121b2510d92486c1200290dfe8b50a35d850a8c2a4b61524b0a1507fa2b3fcd6e1069b081397f9ad41d161fe6af05c5e82ca8bfcd5a088c1043547f92bbfc4fe05498ff13b80cab3fc4e5fe26f0013c7fd223fc4cc0147efd1297e8943f449001476fb9417dc260028ddf52a2f8a567c5273e4559f125200a337b922bdc1100129ef5a487aca43ced3de8470f413879da180252dc76b8f223571da8bae8fdd7476f004c75d1bbb4d11dd468ed25476d1a3b4091d7466eb83f75c1bb8ed41d5692e3a5d73e3039edb1cf6c0e835073c9c38e8fdcd688e446072136390951c96a0e412871d1980251dbd298de9446f49e37a4d9bf05ee01306fc13b7a4d1bd028009436ec9c36a93db9250daa436d91f36c8c9b546a0093f6cca3360d35b026cd812e0049db5c9340126ed4b5c6a51c3524e1a9268ae35b69230348981a42d8d2160571abab8d3da0494d0246571a6b3c5355c68ace35c571a1b308f59946acc13d571222b856d9469aca136570ad2b855d8e8bcc725d63922b1c8f55c2acc4c5c629a6314931894a8ae13f61ca6308d5184498c213c5709dafad7180698c024c5f52a2fc5117d098ae1375c5ad2e2d59714b4bbb505dca82e29597149cb8a425c41f2e415171064ae1365bca62c4d516c488b613c589222d091169268b4134588b22c44f163488b213458c9a2c40515c266b014c57daa2b807d5d6a8ae01700499ab093958498ac24400497a2716d534c0a996c54cb022715d136ae89b4f44da3a26969496a2a5a3a52d1b292d41492ba89a5651c9aa269391349689a434f9a6a7cd153e2b49f1564f89ea7c4d5134849e13c44cada725393925a8995a4dd2c22655d338bc99b514cd22a26559314a08994f49e2d25c541278ac93b5a49dab24e9352748a9394949ca0a26539234b89194448c9e22652d214808994747ca62389511c2888e13c44ca1a28569142ac8a14d45ca62284d5152688a12d44ca10024ad0568487b5043ca420a93d0b6a085b4042ca820a91d0749a83a4541c9ea0a50905078009273ae2da048d1004c08016c3ae2b9fc910eb4967e2443ad219f2d44f968a759563c22d1ec540f08ac7835a3c1ab1e0524f0282781393aca71d8908ec29c761423ac9700248c0109e6c24b361239cc4e4d847e72129361199c0d34e107870136360999b8908dc29c6e142360959b4538d82466c046004251ac4e4cc6a26a14e330a899b180cd4c06696c33c9a19a580cd2a866133004239940a4a54865293d2949b98692cc34866184b30c2194a4d4c10525292f2fc1f14a10cac6a45e05c2b1229588f4ac2a45605e2dc12158148ac08a58a322c4a69624b4b1064560442b52815a910ad2885602629411954110a62645303e29c2214c0c8a50360084628ca8928d58942b64fc6027db612855c9429e4a1432552d134d40954ac4aa4e2552112a568952ac4a1390041f9245040106e482541622f8b116c8b4d84596c22cb00b115c8668843244218a410c510588a641b5120ca88b09587c8b4401501f22b0f8d687c6ac3e139161270f4950582be2c15b1d6360eb180754d82c1571c0ae0e05507028838134160a98dc9105829e35b5c1ac9a0b052c694b82c14718dae0cc930634a83194418c9a0b050c594b4303501652b0b2938594842c95a164ab0b2538592842c129004178acd60158be0ac5b145b00a25b0512c00ac57131a40989104c29026144056298944e04749c2414c11c9482ad683e8bc21b4410ca207d1483e4b4201500f92b07c4a4156841e358054af82a56c378d81bc600ddb002a55c322b8191540c8a60644d0152a617b500bda402a53c2d2980a94b0a9a8054d001528e12a5409ca204a530252680a9430592f042910214680b2520592502c918162b40e350058ab02c538174880c13405caa02c50815262008270122d822980112d8024570112580890c0d6a2021560162d014540058ac02b5a015ab00a524052820214e0040f8049080102e0001f 10 11
def l_44 : Nat → Nat → Option Nat := unpackLinksF 0x436021b010c84854442a021405098284a0c1f1a0f03074183a041a0e0c05060082e0c17020b0304848220c11020412ff8a7fc03fc09fe00ff007f60bf909fb84fd427ea03ed21f680fa837d403ea01f386f9c07c81bdf15ee06f6827b403d515e906f4027a003cb15de9cef4077a03bd01de80ef407702bb609db00ed8076c03b601da04ec4375e13af01d780eac475603a909d480ea4074a23a501d280e8c273e239e05cd86e6c071e638c0dc600e2c170e23705db800dc006e0036d0db488da406c6336301b006d7436ba035425a610d300698034811a400d200688234401a200d0826744338099b82cc466600b2f059780cb03654132a019482ca406500b24119182c8c06344b1a018c04c5c162e0317018b80c5816242312018804c4006200310018782c2c460252ff097e84bf405f612fb017d80be815f012f8017810bc005d822ec017486ba405d202e5116e90b7405b612d7116988b2c85940ac6116300b18058c02c601608ab00157e0abe055f00ad495641ab2015900aa0a55002a4115200a804538229c014d04a40a51e0a8f014780a2855101288014382a1c050c0a7e213f009f804fc027c093b8a9dc04ec0a75053a029bc54de026f0137809ac44d6026a05320c99004c60a6301318098c04c01a5f052f8097c04be025e0527209380494224809240091044860a430121029002480023f051f808f8147812351d1a808d014621a31011802849e424021201090083c3416220a050500828040c22040900087f043f411fa00fd007e803f011f800fa867d403e611ef10f6067b003d801ec00f5827ac03d601e128f08077c23be01df00ed8876c03b211d900ec8076403aa21d500e90674803a401d104e88074403a201d100e880740138861c304e18070c037e21bf00de066f0037609ba04dd006d8436c01b504da026d0036411b200d88269ca320b98c10c6006300310218800c4006200308218400c2006100300218000bd0c5e022f0017608bb005c842e4016f0cb7805ac42d6016b00b4065a002d0016704b38059c02ce016700b38057892bc015e00af0056c32a6415204a90054802a4014f0ca780538129c014e00a6825244292014900a480518328c014504a2804f4827a013a0c9d004dc326e0137009b804dc026c093600988a4b8325c012b0c95804ac0256012b0095804ac024c292600918648c0240191f048f804703236091a048d0046802320919008c804640232011900898c44c02260113008806414b20a0104048200410020609000c7c103e001ec10f40879823cc01e018ef0477023b801dc00ed0476803b401da00ed00738c38461c200e004700037c11ba10dd006e8037011b020d8006c0036001b000d4106a0035001a020d000680033c119e00cf00678031c818e00c6046204310018608c3005f882fc017e00bf005f802ec417600b9085c802e4016e10b6045a042d0016800b30459802cc015a30ad0056802b0115800ac0056002b0015800ac005210254f12a00930849022480124009200478623c011c088e0046822205110008704438021811042082004100208010010800040001fc10fe0077203b801d420e80874003a001d000e218710038021c000de086a1435001a800d0106800330419800ca0861102f8417c00bc085e002d0816800b4005a002c0416000ae0857002b8015810ac0055042a8015010a4104a201d9e0e420700838001a860d0106608330018840c4006200300418000c00060003000150c090604800230400c40001 0x25148b2804423c178aa09e1949b07a3d64c98aac4ad032464702f1501382607e4d2b2a99512300f8a405d022410bb4d5551d2028c9532752513604816c2cd312e2990aa4c9109048c0f2432892081490c9248249244469211543d8a64800500a2990a23d92097c8e4ae4524f1f92322c178a209e3e03f1e8179312ec268f64b2b9249518f0a82a44acff2464502f1401382007c8905a270258dda04700be3604e4382f1341390c07c4c02f1d2388e51ac6a8d234271199348c81a10a0bc4b04f172453202a460111ac283169396a898b5690a2b29cd51428b92b458939a8287151293a02d423182086a8630548463418a1521169b04a4d69ca0c4c4e5a42629ca604ccaa188151394d061854699212788ea2229cd21424e496c50d6e0f6b313b53895a8c0e8fe242b69c15988ca9c42545a3266a892b39c2518e118c20890fa4c8792243a4a21c2490d82483a2ab2a4c61625b0a925861aec2e546142a106464825ae418d561169b0813946898c1d1620c6b10645e82122bd65660b2a304c60821aa220d70ec698dba34814a44004d1a14a102a4c451203d8969cf4acdda4e611212388e90f46cf595a80cab1d84b91425a7305a3042b1e0d31a02a0ff9308009e228921ff4889515c5d49a43316a138ad0935b83dad41ad5e0a6ad03a577a8adb9c55dba29ed9149688a1b3e5060627f0213b8089cc024ddfe2668993154095a1c49ce50b4600567f094bf64a1fa24891a3a42d1b1d84e90d26cf9a4d7e0a0b3a4c54f256851277dc263d0565f52a2e5145670a09e04e4ec262f4a5a7212b37293966484f415a7c8ab1da538ec2847205a7d12b3e6939e72b6e39576e0a7b3650df12527185a7bd22bdc1107905e1d8277b12432a541eb2908d1407a51c3d04e1ea69ef3b435391d326509382745084f1e01f8740dc7705e1c827735203a6935cc482e8a3d7911aa9a4a8a009ae81385309c3bc8c14b250f004c775223b6091dd468eda34779a23b8951c9250ed0242689c3c48fde1476efa3776519a944a9d807eeb8371d81787009dd5692e8b41740a43a0d41d38c0e936c745b039e4e1cd688e4928725a8399181cb4d8e5254720943cad71e36a2eb3507512eb9c8fdc7466a412a2781f8e80bc3604e3982f0d4138e40bc3404e3882d0c812b804c1c105edf827714a6388511c3278e11366f89a0de0fc3106ede8146722e1d8d21b7488dd9386d9a21da911b9250763493b5a0b6e8f9b6464d834e6e927b7090db546aa312a274278da0bc2e04ed9946670971d84e4f0262921293f890b38d34ee4747613a4349b364d35454767ea336c49b3604b86a07e1603703c17b34501ae49acb9301a01785209dac6b8d5a385e4a23544e1a9268bc1345dc9a178111a78c0d3260694b62345a17a2c8d216063caa2ec4d0bb0a8c22483b0a02ea4d1a1494d024650d1d2128d9952b4c71566309eb044d4e20b45d056671a6a848e90846ccf14d671ae2cc8e174288761386049eb144d58b25ac01256051eb328d59a47acc13d62497b0c4ad7f24eb71231941785009d5f03eae8176453232ad3541474c89554689d3284d9912b05a8542cc2a164111918bcc825d5e92ab1e9158e47aa012a334229601118b698c524c6322e3129513f490c29484349a30e5316c2688a934619aa30a931164889395c6109e302d3180498b69205f81e2fc511826b8bfa544f91c22c4e16b260be84c2b8222f0d41772a0568444549c2e41517b6b4bd3565e52d2ec9597549cba2424591f1d88f51d2527e1213802d1581597307cb88321901684a0956d468b51545bca62ca05169288b20145b5222d05516c278b18145a4922d24d16a488b4134590922c84d165488b19345b9aa2d6911672c87895c5989e1d84b162028b014c57daa00a57097278aeb546a1adb46d5da269ecfb4d675a2b36d0d97488a223b4f51d20c8d8fb466cb15b64cad32455d8d2acc413f60c9da264e97c26eb8136584999be168cc0ae55856270278c40fc2406e0702f5780fab805d5a49caca4c561222829012f2b89614c468a025c931554c0aa16c54cb025a5313c4c09995450d282389212a2b87614048d28284900ec2a09494c4dd2aa825094c474a5a36535a8a94d41492ba7734e51c9aa50971242887713c3b09624e9711d288761202a822286d354268a98a4d48522a82569402ac9f93d4f89a9bc168a90ac9aa644f09e26a5553a29c8d1424e496a6e961352b09ac5e4b1aca68d453348a98a50494ac2305412e2a08b9344be2d25b1592c6b495b563b1a7230d352a49a94a454a0a4a4e504dd0b45405647ca224a971242889193c3b096242900ed2b88f14047ca622e531184b88f254474a22384f0a70888b93445ca622a4b1152688d15a464ab1da5391829a869364589a9e04b91425a6e05a2982b2ad16d528aea8b57541a7a9ed1d4e4b4a42565192728a92d444869ea424ecada70569362ae991564c0a7a4c539222969014746ca1a26508db0b452856441a6a18d14ec47486a36441a81d8d01092a087948435a8218d010b2a08414042526a10914ee47a8393d445a121c93d0a48e75a3d418a120a0f0f72b87a14c4091a1ec531014c08016c3e4aa1ea530fe4887915c3c0921f8910f12b87713c3b0961e8d64fa6a27cb453d8a81ef168f58ac7a35a3cdab1e4524f1282781393b0989b4168ee4847694e3b0a120716cff8ae7ea4b3ed219f0558ef29c7592e3642d1b0110e228273139370989c84a4e10787134d3791d1b84e8e026c6f242374a71b8508da29c7424b39d239ca8fce34666f93336c959b248cd808c691413589c99c4c4d14846a14e338a119e4d0d28c068a60340b619c580cd2a86ab5134ca89984ccbd062650292d81098c92cc54866204b30c2197608cba06260829298109724c8bf07c5b0322d022178170ae0a8568242c822162110b70485a2322cca695c514b225a588322a80d15e940ae488569442f5a9176914ba47a5c9522a495170178b60a45a8452c02214c0a8ac04c5504429c221524c8a807c53032325219904f4c726e611353009797c10cab0465281b258ac9465449b4904b148268a41411809f6d84c938260a412e9209a6a04da5a2652b130938974844b15a254ab144d58a12b64f157274a793850c94272491412412a1029707e4984024c235360fe9308c2d845960225a211091087290431441f9ac908d445c2b241951200a81031687f8ac3f35a1f5ab0d8524672823e139164988f4950614702e138180940ef1b0768c03aa6c17c940e6570722a8389441c09a0dc9105e2503635c1ac9a0cc500694b832940199260ced70654a82ea38190a20b24e063268303501852d0be9585e49c2ea42170ad0b65585a29c2c94223e2f91d16c8a8ae42c532092b0f6938792be3c15b1d0ab8de54c6d29e3514b1a0a38c450c582522b358115a0082d00536c02916c144b0088900434802135013da409c9104d290261441289c0905304949c20a4211c9483a4844468821944100a808b178428a420a5a0fd2b0605342a28a1f12905890878d60232600e9400e636071180376c01113008490040900352b81a1540cca60644d0306a017b4807d2005a5301924015b500a9a00505001e2601393c0649804e510284a81314c058a004a4d02248810a3406498038d40182880c1340652202e550234bc1025207d2503c9181d2b40d956068a702c508558be2a45b1422b89714c466b41eb420ecaf87456c362ae189530b8a785852c2928e1214305498816570082980524c049300225b0092980325c0152e010d640d6a20515002e2d013158086b403b56018a480a504138b60845703d2581c90c0c2ac0214e0092149ed3e4e6971db478c5a1c5e93e294971024786921bfa8fdf9476fb2377c119bda53de6296e31476f0a1b684fdaf276d693756c99aae4bd12256821273a8919d213cd709465847290231260fc9106e2b82f0501380607c0102e0001f 17 6 11 10 7
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsF m_44 g_44 bds_44 (dagRefF 594 (dagTraceF m_44 s_44 8 f_44) l_44 0) s_44 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_0 : treeBlockF 0 32 (dagCheckNodeF m_44 g_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_1 : treeBlockF 32 64 (dagCheckNodeF m_44 g_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_2 : treeBlockF 64 96 (dagCheckNodeF m_44 g_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_3 : treeBlockF 96 128 (dagCheckNodeF m_44 g_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_4 : treeBlockF 128 160 (dagCheckNodeF m_44 g_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_5 : treeBlockF 160 192 (dagCheckNodeF m_44 g_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_6 : treeBlockF 192 224 (dagCheckNodeF m_44 g_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_7 : treeBlockF 224 256 (dagCheckNodeF m_44 g_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_8 : treeBlockF 256 288 (dagCheckNodeF m_44 g_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_9 : treeBlockF 288 320 (dagCheckNodeF m_44 g_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_10 : treeBlockF 320 352 (dagCheckNodeF m_44 g_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_11 : treeBlockF 352 384 (dagCheckNodeF m_44 g_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_12 : treeBlockF 384 416 (dagCheckNodeF m_44 g_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_13 : treeBlockF 416 448 (dagCheckNodeF m_44 g_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_14 : treeBlockF 448 480 (dagCheckNodeF m_44 g_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_15 : treeBlockF 480 512 (dagCheckNodeF m_44 g_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_16 : treeBlockF 512 544 (dagCheckNodeF m_44 g_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_17 : treeBlockF 544 576 (dagCheckNodeF m_44 g_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_18 : treeBlockF 576 594 (dagCheckNodeF m_44 g_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) l_44) = true := by decide +kernel
theorem nj_44_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_44 g_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_44_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_44_1 h1 h2)
theorem nj_44_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_44 g_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_1 (fun _ h1 h2 => treeBlockF_at nb_44_2 h1 h2)
theorem nj_44_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_44 g_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_2 (fun _ h1 h2 => treeBlockF_at nb_44_3 h1 h2)
theorem nj_44_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_44 g_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_3 (fun _ h1 h2 => treeBlockF_at nb_44_4 h1 h2)
theorem nj_44_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_44 g_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_4 (fun _ h1 h2 => treeBlockF_at nb_44_5 h1 h2)
theorem nj_44_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_44 g_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_5 (fun _ h1 h2 => treeBlockF_at nb_44_6 h1 h2)
theorem nj_44_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_44 g_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_6 (fun _ h1 h2 => treeBlockF_at nb_44_7 h1 h2)
theorem nj_44_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_44 g_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_7 (fun _ h1 h2 => treeBlockF_at nb_44_8 h1 h2)
theorem nj_44_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_44 g_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_8 (fun _ h1 h2 => treeBlockF_at nb_44_9 h1 h2)
theorem nj_44_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeF m_44 g_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_9 (fun _ h1 h2 => treeBlockF_at nb_44_10 h1 h2)
theorem nj_44_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeF m_44 g_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_10 (fun _ h1 h2 => treeBlockF_at nb_44_11 h1 h2)
theorem nj_44_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeF m_44 g_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_11 (fun _ h1 h2 => treeBlockF_at nb_44_12 h1 h2)
theorem nj_44_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeF m_44 g_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_12 (fun _ h1 h2 => treeBlockF_at nb_44_13 h1 h2)
theorem nj_44_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeF m_44 g_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_13 (fun _ h1 h2 => treeBlockF_at nb_44_14 h1 h2)
theorem nj_44_15 : ∀ i, 0 ≤ i → i < 512 → (dagCheckNodeF m_44 g_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_14 (fun _ h1 h2 => treeBlockF_at nb_44_15 h1 h2)
theorem nj_44_16 : ∀ i, 0 ≤ i → i < 544 → (dagCheckNodeF m_44 g_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_15 (fun _ h1 h2 => treeBlockF_at nb_44_16 h1 h2)
theorem nj_44_17 : ∀ i, 0 ≤ i → i < 576 → (dagCheckNodeF m_44 g_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_16 (fun _ h1 h2 => treeBlockF_at nb_44_17 h1 h2)
theorem nj_44_18 : ∀ i, 0 ≤ i → i < 594 → (dagCheckNodeF m_44 g_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := block_join nj_44_17 (fun _ h1 h2 => treeBlockF_at nb_44_18 h1 h2)
theorem nc_44 : ∀ i, 0 ≤ i → i < 594 → (dagCheckNodeF m_44 g_44 bds_44 594 (dagTraceF m_44 s_44 8 f_44) l_44) i = true := nj_44_18
theorem lb_44 : LowerBin m_44 s_44 g_44 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_44 sub_44 gl_44 rc_44 nc_44

def m_45 : Nat := 0xff00ff00ff00ff00
def s_45 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_45 : Nat := 0x100150001003700
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 5, g_16), (m_34, s_34, 5, g_34), (m_35, s_35, 5, g_35), (m_7, s_7, 4, g_7)]
theorem kn_45 : KnownBin bds_45 := by
  intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_16
  · exact lb_34
  · exact lb_35
  · exact lb_7
theorem sub_45 : ∀ b ∈ bds_45, m_45 &&& b.1 = b.1 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_45 : ∀ b ∈ bds_45, canon b.1 g_45 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def f_45 : Nat → Nat × Nat := unpackForestF 0x93f24efc50e9009378d02230491113c24cc01f 3 11
def l_45 : Nat → Nat → Option Nat := unpackLinksF 0xe1c34e1972243a70a8601 0x14a0213088a0e900c982b404460691089e513f9276c4dc499801f 7 3 11 4 4
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsF m_45 g_45 bds_45 (dagRefF 11 (dagTraceF m_45 s_45 6 f_45) l_45 0) s_45 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_0 : treeBlockF 0 11 (dagCheckNodeF m_45 g_45 bds_45 11 (dagTraceF m_45 s_45 6 f_45) l_45) = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 11 → (dagCheckNodeF m_45 g_45 bds_45 11 (dagTraceF m_45 s_45 6 f_45) l_45) i = true := fun _ h1 h2 => treeBlockF_at nb_45_0 h1 h2
theorem lb_45 : LowerBin m_45 s_45 g_45 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_45 sub_45 gl_45 rc_45 nc_45

def m_46 : Nat := 0xff00ff00ff00ff
def s_46 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_46 : Nat := 0x150037007f007f
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 5, g_17), (m_25, s_25, 5, g_25), (m_26, s_26, 5, g_26), (m_3, s_3, 4, g_3)]
theorem kn_46 : KnownBin bds_46 := by
  intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_17
  · exact lb_25
  · exact lb_26
  · exact lb_3
theorem sub_46 : ∀ b ∈ bds_46, m_46 &&& b.1 = b.1 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_46 : ∀ b ∈ bds_46, canon b.1 g_46 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def f_46 : Nat → Nat × Nat := unpackForestF 0x44f112e25c111c95451108443110834110c01f 4 10
def l_46 : Nat → Nat → Option Nat := unpackLinksF 0xe1c3862a5424c882ac601 0x897184050d0c245110c44655104420d284f912dc47110c01f 7 3 10 4 4
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsF m_46 g_46 bds_46 (dagRefF 11 (dagTraceF m_46 s_46 6 f_46) l_46 0) s_46 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_0 : treeBlockF 0 11 (dagCheckNodeF m_46 g_46 bds_46 11 (dagTraceF m_46 s_46 6 f_46) l_46) = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 11 → (dagCheckNodeF m_46 g_46 bds_46 11 (dagTraceF m_46 s_46 6 f_46) l_46) i = true := fun _ h1 h2 => treeBlockF_at nb_46_0 h1 h2
theorem lb_46 : LowerBin m_46 s_46 g_46 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_46 sub_46 gl_46 rc_46 nc_46

def m_47 : Nat := 0xffff0000ffff0000
def s_47 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_47 : Nat := 0x1150000017f0000
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_37, s_37, 6, g_37), (m_18, s_18, 5, g_18), (m_20, s_20, 5, g_20), (m_22, s_22, 5, g_22), (m_25, s_25, 5, g_25), (m_36, s_36, 5, g_36), (m_3, s_3, 4, g_3), (m_5, s_5, 4, g_5), (m_10, s_10, 4, g_10)]
theorem kn_47 : KnownBin bds_47 := by
  intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_37
  · exact lb_18
  · exact lb_20
  · exact lb_22
  · exact lb_25
  · exact lb_36
  · exact lb_3
  · exact lb_5
  · exact lb_10
theorem sub_47 : ∀ b ∈ bds_47, m_47 &&& b.1 = b.1 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_47 : ∀ b ∈ bds_47, canon b.1 g_47 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_47 : Nat → Nat × Nat := unpackForestF 0x24549f2835c91525c8a91e4d28322a4592d26494d52454872294b91c9b48a5264528600b4f9051c4828d64146800b4b8fcacc789763d26d1e151005a3c70d7a3846b1c038005a1c48d7e246a71a244891a7c6517224697123478b5a745ad0a2d2a3123458adae4531522946912343890a5c4c51a242931214300527c409322048d1024400525c3c5261b6bb0e14686ca880291e196a908c5f85da242314e114bd09b5e84da942291a1105000a4383da340f17a076bd05c5482db640e97e088d90435c81d2b8028fe056a8fe45f80db63f915e0148cfe35e7f9aebfcd55fc4bcfe2460051db6f17df568cfab457d5233ea915f5292dbc5e7cab63e4d71b78b6f79607bc3036f15deb6b8f59507ac283d3591e9070dbc5378daebc64e5e3074f203078c1b36f149df8c0f035077d2a36ed7dda6b2ed351769253b4919b76bcebc5075d3636ed5dd46bcea34e6dda93a1181d1680e83546dd2fb92d65c96a2e4a5e72529392929c948cdba5e7163638b141c56d8dba57701af380d49c04bce024e6dd2936e52db7286dd45e6e9af374579b7282db84b6dc218028ddb5488d2b4f695a5b60971b02a0d8050695a3b5a501ad080d5c546ac1c34ad0da949cd2a3e69c1a34a0eda5066cf34468124b40905a0472d023167d1a33c97801466ce048004a7b33581992b8c834765926b2c8d59028cc934a649a33249199026cc812e004a5b14d718a6a0c525c629283141400128eb8c5f5c5afb07581834a0c195c60ca82e2d1d81278b894b5c4a3af6d797b49abe4505ed1aae251979278b893b5c49bae4d297268cb925e5ce282e49197126c009435b9af2dc0e00127eb624a5862f2d3151692b0b0b5f59a362cc581616aeb11455889b2c44b5612a40093b55e2c2af1495b076ae05456c19aaf14157498aba4055c200024dd5528c98c5e54a2a2a4551316bea746c5393029c5b1316aea62454c4af2624f1448bca235e511a928897945480a22564c49b264d39416889924f4fe2e26492d3b6b89d9504ec2826491d358b89b9404dc2026ad5135050992434c815a6408d31268009334b92f25c0a00125e95b544acac23717d286d89416046e2ba4c9291b6bc911464889aa444b51b2a48e45e471af2385791c2a48e12d46ca50024ad116b088b5245415a2c1111504688b50445a4222d011106000927439aa21c550eb8be8536c429302145b0eb8ae841463adaf20cd14eb2bc7594c3fa2f1fd148fe6bc803403f9ab1fc978eb28c7e2443b1a79d8d2cf74b87b9503dc281d8d1cf42807a0403ca2a1e40e0ec68677a493bd209d8938ec076760333aca200248ce908858b4f39c1a162d2ce4ac07205c2c5a39c1150e1688700342c5a19bc110b149e58a4b362b01b0d70d86a06c05c2c5239a8930d44886a0242c5219a40d0b147e58a3b33230199160cc8a06604c2c51b990970c84a8640242c519980934c047a60235300a09804e4c1268601312c42316ed28b768c5ba4a2dd2316e4c4b72525c1442dc909620d8b2294591462c89d1644d8b105c0084b2bc220dcd3cad0683734b2aab01541706e68e5404c29a2a14c0d06e686520441b9278dc92c9eac04f35c279a813c1706e48e4d24c269221340906e4864c0341b91f8dc8ec928c04945824a281241306e46e4725c2392a11c0906e4664224d2111c9088c489268421412109e90b14085480421351b8230ecd28812803b3461d9270fc4c07d6883b2421eca20ec4c47625a3bb501dda00ec4946e06c3794a1cd260de5186f274383481bc9b0dc0b8010862eb4b175a38ba8ec684a834024175198c29286148c30931184948c4510612422e8361789d0bc4d85d05c0083b16c1b0020cc4a69e25347129258aa91055048252431391e89c8d44e2822713913c9a09c4c44a08c2594a12ca30940b801056240460041188c9143769e2225d0dda3884d143749e2035d0dd238751783d0681d4520e9af0749783746e1b94b0dca1802078350380081b0c9280641702968e17a4d0bd1a8521182a694164500a9a30549182906c0081309d22804d3c2568a0124f08ca4031178210680c452061af030978182840d34e06927034538182800c04d0091b8045380228609450048a60245000d46e0693b0349b81a4ac0d24e01142025268145000946a0103700da500d1400368c0214000d2300409c010240001f 10 11
def l_47 : Nat → Nat → Option Nat := unpackLinksF 0x4321218830b838561c2b020f9907c083c0c1a120c050600828241209fdaefec07f603fb01fc06fe007de4bef01f606f9087c21bdd11ee80f5c67a623cf11e780f2c47940bc70de206f10078803c401dc18ee0076e0bb701d988ec4276203ad11d584e517728039401ca00e443722038825c400e1436fa437d01bc88de406ea23720db900dc806dc236e01b40cda006cc136211b100d8806bc235e01af00d6c36a6435301a788d3c06981b4c01a504d280694034611a108ce8866a2b34059a00ccc16660332059414c9c164e0322159004c78262e3b17018b02c541622231005850cc2026100308018400c1c15ee82f6057b00bd415e41af2017900bc805e402e8297400ba005c822e4017200b8045be0adf016f02b6c35b602db016d80b6c05b602db016894b4405a202d1016688b34059a02cd016680b2445900ac6096282b1015860abb215c06adc1532f299014c02a58252c0295054a02a4045200290014704a380514228a014404a20050e0a87013e949f404fa027d013e809e444f00a74113a009c434e2027101360a9b004d802690d34809a404d202660d330098454c2026101308098404c2025c152d0496024aa1a55012a0294c14944a4a012386914248a0245012280910147e2a3f011e068e82474023a011d008e804720a3415131c898044c022211110088024400220010e088700438021a090d00868043402161107108380418120c01060082c1412120709028481403fa41fd00fd067e413f201f510fa027d003e801f010f8007b823d811ec00f6007ac13d409ea00f40478863c011e000ef8277c03bc09de00ee8277013b021d800ec0076003ac11d600e98674813a401c924df946fc037e01bb10dd806ec036e21b700db806d4236a01b308d9806cc036601af10d7806bc035e01af00d7806a8534441a200d0046800340019f04ce8466c2332119900c8906401320018c10c58262c0316018710c3806103308018208c00460002fe097e04bf005f022f8017618bb005d412e8097400b9825c812dc216e00b7005b022d801690cb4805a402ce116604b30057492a6515300a884544029e114f00a7805246290094800a382514228a014404a1045080284014200a1004f8427c013d049e804e442720138049b044d8026c0136009b004c8426401310498804b4425a012d0096804b4025a012d009602490824801240092004900248012400920048c1236411b008d8046c0236011710841e420020c1106008204410020608ff107f803f421fa00f9107c803dc21ec08f5047a803d011e800ef1477803bc01de00ec0c76003a821d208e804740039c11ce00e214710038801c400df0c6f8037c01bc08de006e8237401ba00dd006d8434c81a600d204680434001a000cf046702338019a08cd006680334019610c320618030c018408c2006100304117a20ae3c56822b0115410a9045480298314c00a6005300298014c00a5044f8c27c013e009d084b8c25c012c0895044a0224821220891004706238011c008e004700238011a088718438021c010a107f183f801f810fc007b0c3d801e810f400770c3b801d810ec0076003a821d400ea00711038801c400d240690034021a000d0006314318018c00c0186000300017c10be005c0c2c8616400ac185600298614c00a40852002786138109a084d002680134009a00471823800f0b078003c001e000f0007800390c1c800e400720039001a0a0d0006800330418060c00060002f0417800b8105618232000c40001 0x1e18d917b449412c3ee9524b4892835c76da23ec951f7499252407691a46897a194a4fba4e71d26c0a8e9df46c95949934a0a584a50f2422301e09c094969324a6a8ffa6c71d2e428911624a0b6248605292564ea4726cb112d5892c2fc512364bf0c25394527be89364f4972724793122c9290e0e47b0223b7791bbb28d5882a72414b918a4c8a50d61282b593955098a544ad0d2462281e098094868e24246b20a3471daebf0d5603474eba368fcaca5054529252861211100f2168c9282751e9368e9aec7c97602476eb2378f0a8a4e4ad092462181e71d26bec915d546ae3b5e7c9a945297a174a51d35e8d52fc2c94dd348b1ca358e01c38f1422f6a91a2447311a45d151c76b8e5a448a51a3a51b2326b0fcb548d122456d12328b8fc354729223f2d322a680e4a347e5af38ed762f69d173428311eba08d5692b3169515a89caa64c44203c128128adae4551520b6d8e3b5c8a51a24494126470bca525a4a544c5192225a912585d09a46cd7e356a719b4f7d1a6c62d2e3068f163458a1a1c148fe00474e7a377211b30e54e2729712949890a1a4250568276a893349494a0e4844103c120128892644291a20488e3a4d7d922c128f5c546b0f149598a0ace4e5502622001e53d212cc52a1c28d0eb5d8552ec0e8fdc446f0d9515949da9a4cc3f03d0cb5470da238e97214488e135485da2426951f2488e3b4d7e1a2b828d9c78bcf9452851af426d4a188bf0b4536fda342a97a1248d0882883da33aa8d60b4bb0425571d26bec9160c8a905b6c71dae3828d2098d8fb36c821ae41d17a0d6bd0525f81d2bbf88d4e80b65705316415c0ad51ff4d8e3a5c75522406db1f84d8ff25c805233828d9ff6baff35571da6bf0d15c78bcf9452755af38297a048bf01457801af3fa979fc48c7305b2b0298d812df38d0f3c60741aa3be951b4460e8b4c781ae046081f28bcf3c5d7e5a33f0d15f748cfb2457d4a4a3a5043e03c110127b5aa3e75b1dd8d8f935c73936366901ec8a0d8a307ae283608c1c78d8f5450715b63ae9b1af460f81607bc3035c901ad480f6b5c6b1203d8541eb0a0d5a3079eb63d5591dc8d8e6a6c6a9203d20e1d18a8f0254790183c3175d88aae3b5e79daeba4975c64aacd159618a8bcc4e583262728592ac28bca0e9e306c1e01e080093c0951e06a0f0c6071e2e3be951dd6b2ee3517312f386949db494ed2464809cb784c43b03c0f81271e363b1141d56d8eba6c755af3a8d39cb4bce12527462a3a2d01d28c0e3c5c741aa39cd65cd6a2e625e72d29394929c948c8f9396ec988740781e024e3c6c71a2838adb1c14d8e1b5e709a9382979c049c8e2504712c03a0801c0400d82006808379179bb6bcc2a526e8af3065491c25a198210641034cd005208832834695a03f517df48bcf8c5b7ba2bbd114de28a4ef35f765af3acd5dd36a4e7a5f7212f38895dbf4a4d2230660adb0454dbe2968d9496f4a1b72504e30b6548536e025b6e10c6b0762c02b0e40f06204c17024daa4468d2e3428d1ae680d6b406b1a0364971b12a0d80506b8a035a101ac8a8d125c6811e3560e1a949cd024269c1a368d3db3696d7b476a9a1b3e939a847c7104b29c21b4c0eda5066d1a4968920b428e5a0462cfa34691a233c978df0b6528536422f33812016020cd560664ae32655196288c913465d26b269159646aca34a64da33249199868eca9466449b3204b83805cc735c635a83189718b4a0c50506052c2fc511794b0ba1345f0aa2e64d014040098100481030d581854a0c215c474ac2ea551832a0bd9445c89a022081644a8c093c040182c85200f040be4505f9af2c8d397d49abaa455ed1aa46911792780703048c9c01a081738a0bb34a5d5a32e89797248c91a3e6222fb0ed7d8268ec014b584a52fe51d7a28cbc13b4849d2ee4dd7126c1b82e054110180816f6bc6e85b28c29adc0e16c4949013a5aa2a2d25611d2a08f93859e362cc5816428a8e93a58c9b2c44b56b8bcb435f595abac25491b2746e05b288298ae0ecdb0b2508515702a2ba0ed5b0666d04b280219b212c9f086afc5857a292b514159498ac24035c2d93a14d57080aa9465249b2844d141268a9c54520ae2a4551462689e9345423629e9814e2d8a213452126a98914d60964e043515aa282d113d6b8a2a405262f290d79476a4a325e5112b0ac0a53f4929ca41505a227f171384809ba404f5ae26c9013c2a09d8504e0a026e101398b89b3544d41409e1114269ca024f4f925a7491d344866a84b26c21a660ad32046aa45e545afa9ad5d4b2bca513c50c9b2624d0d30b64c8531501da5e978d10b64b8534b814258d512b2b08e950480a4252db1282c09324a47c9d23a5292428c9193548896a411791f6bc8f15e474a92384b52a8be93c57495af2425491b2946805b258298d412ccf0b24a8514582222e0ad150466704b2502199a12c930868cb58461a9228d41136908934032c2d92214d110607e13443daa2065710e2a8809443e49a218db10b4c08516c3fca2210518fe26c7713440da6a0cd14ca096480434022a1f8911006807ca5c40e2f205149016bc7fb563f92f0d20e4fc4887825c3d5a01e8d00f36807ca5c3e0a81ee140f52807a0403ce2a1de970f2070782493bd208c40d0fb69e7d34b3d9a39e2d0cee49c6484b23c219da0ecec06686c5f4262ba0ed79052bc8214c3f4a31d6510c70b64685319c2598a150e90885e04439c1a1cb580e26807205c2f42a188110bb06870834385a21c5150e00686f0443082a16a0b0dbac06d35c365a81b0170c10886b24c35522180150d4048690342e4221660b0cf8c06745833628198130b80686525c3252a16e110c8048609343192697a914c547a622352d4a4986504c2272601312e0a217cd28bd68c5e24a2ed231664e4ba2625c9292dc9096a528b428c5993a2c89b1d0d3ce669671b4737da19ba93cdc4966ba4734d219a28fcd047665a3731d1997e118b606c5882e2bc220fe0d08b0a8568342a118157580a76805505c2002a1501307d08853c542282a0f8110a606843854290220e80b0860a842844286b0140d709f6a04f05c210221389309b4884d0241e4221300d0710583c0441dc2212b180948b049c50248260ec0d0904b847a54238120fad108926843450215201189348048a45a39229188e8524882824393d2109a8fc8c07d460409401f8980fad107b2883c3501dda0104d288068c3fa4e1f1210e24e47a2623c92d1d8928e6930706903a14a1c8a30e24e86f26c5734f2b1a5952d1ca568651a4f2892593a91c994864ba3f2591d9228dc8d466418461d41b0dc0b8660883283418c220be0b06206834a54184220d0090622883324a195230be4e46426231929184908be4e85e26c3634b1ada38d48ec6746630036174170b60d8530a8290441402a0980b04f0882b2441382a0aa0904f26829a3d1491a8985245128228139138988985284b28c2cb4f161a38ae92c5448626846128170901183e49a232450ed1a8889743e69a213450e91b080d743d0681f45e0f229076d783a4bc22b4f10da388293c3f48e1ca370e0a586e50c3503c1a81c0cd280641702b0a8178440a81a0609342b48a17a350b22805ad282b68c152460c5a385c1182906c1124d09d2283e8d42269a12b450791b046520142a0091300841a0384c01b2600e34e06d27034538122840503501012845178208a40fb5e0792f0225481d2840c9400602680a1140906a01825052280265301228008a370409d81e4dc0e25606927028a00169340548a04a3501a280085000769402b4600d2304cd3c2449e0ba37058a702a50c0c2840403700813c88d3e406971db478dda1c4693e1f4970d24784121c0c8fdfb476db23767519b3653d8f296c49475c0a1ada4fd60276ab1374c099a5a4bd1a256881273a89196012c6d0862e03b168198920ac470461b01e0d00d85004c010240001f 17 6 11 10 7
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsF m_47 g_47 bds_47 (dagRefF 594 (dagTraceF m_47 s_47 8 f_47) l_47 0) s_47 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_0 : treeBlockF 0 32 (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_1 : treeBlockF 32 64 (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_2 : treeBlockF 64 96 (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_3 : treeBlockF 96 128 (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_4 : treeBlockF 128 160 (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_5 : treeBlockF 160 192 (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_6 : treeBlockF 192 224 (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_7 : treeBlockF 224 256 (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_8 : treeBlockF 256 288 (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_9 : treeBlockF 288 320 (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_10 : treeBlockF 320 352 (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_11 : treeBlockF 352 384 (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_12 : treeBlockF 384 416 (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_13 : treeBlockF 416 448 (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_14 : treeBlockF 448 480 (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_15 : treeBlockF 480 512 (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_16 : treeBlockF 512 544 (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_17 : treeBlockF 544 576 (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_18 : treeBlockF 576 594 (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
theorem nj_47_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_47_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_47_1 h1 h2)
theorem nj_47_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_1 (fun _ h1 h2 => treeBlockF_at nb_47_2 h1 h2)
theorem nj_47_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_2 (fun _ h1 h2 => treeBlockF_at nb_47_3 h1 h2)
theorem nj_47_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_3 (fun _ h1 h2 => treeBlockF_at nb_47_4 h1 h2)
theorem nj_47_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_4 (fun _ h1 h2 => treeBlockF_at nb_47_5 h1 h2)
theorem nj_47_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_5 (fun _ h1 h2 => treeBlockF_at nb_47_6 h1 h2)
theorem nj_47_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_6 (fun _ h1 h2 => treeBlockF_at nb_47_7 h1 h2)
theorem nj_47_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_7 (fun _ h1 h2 => treeBlockF_at nb_47_8 h1 h2)
theorem nj_47_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_8 (fun _ h1 h2 => treeBlockF_at nb_47_9 h1 h2)
theorem nj_47_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_9 (fun _ h1 h2 => treeBlockF_at nb_47_10 h1 h2)
theorem nj_47_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_10 (fun _ h1 h2 => treeBlockF_at nb_47_11 h1 h2)
theorem nj_47_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_11 (fun _ h1 h2 => treeBlockF_at nb_47_12 h1 h2)
theorem nj_47_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_12 (fun _ h1 h2 => treeBlockF_at nb_47_13 h1 h2)
theorem nj_47_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_13 (fun _ h1 h2 => treeBlockF_at nb_47_14 h1 h2)
theorem nj_47_15 : ∀ i, 0 ≤ i → i < 512 → (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_14 (fun _ h1 h2 => treeBlockF_at nb_47_15 h1 h2)
theorem nj_47_16 : ∀ i, 0 ≤ i → i < 544 → (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_15 (fun _ h1 h2 => treeBlockF_at nb_47_16 h1 h2)
theorem nj_47_17 : ∀ i, 0 ≤ i → i < 576 → (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_16 (fun _ h1 h2 => treeBlockF_at nb_47_17 h1 h2)
theorem nj_47_18 : ∀ i, 0 ≤ i → i < 594 → (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_17 (fun _ h1 h2 => treeBlockF_at nb_47_18 h1 h2)
theorem nc_47 : ∀ i, 0 ≤ i → i < 594 → (dagCheckNodeF m_47 g_47 bds_47 594 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := nj_47_18
theorem lb_47 : LowerBin m_47 s_47 g_47 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_47 sub_47 gl_47 rc_47 nc_47

def m_48 : Nat := 0xffff0000ffff
def s_48 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_48 : Nat := 0x15370000377f
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_23, s_23, 6, g_23), (m_19, s_19, 5, g_19), (m_21, s_21, 5, g_21), (m_24, s_24, 5, g_24), (m_26, s_26, 5, g_26), (m_38, s_38, 5, g_38), (m_2, s_2, 4, g_2), (m_4, s_4, 4, g_4), (m_11, s_11, 4, g_11)]
theorem kn_48 : KnownBin bds_48 := by
  intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_23
  · exact lb_19
  · exact lb_21
  · exact lb_24
  · exact lb_26
  · exact lb_38
  · exact lb_2
  · exact lb_4
  · exact lb_11
theorem sub_48 : ∀ b ∈ bds_48, m_48 &&& b.1 = b.1 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_48 : ∀ b ∈ bds_48, canon b.1 g_48 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_48 : Nat → Nat × Nat := unpackForestF 0x2510332714993c1749c1240169f25b5692d1a002d2e422b72115391c0cc84546420b72105390c174841440168f1e2348f09c4784d23c0711e034005a1c72546390a3193458d8a346c06632293198468cc174641240149f180188b4a4c5c0b22d0931235d8ac2045251a290331215189ca044a11a2505d12051005238028fe1f69f0fb4787d1b0028ea1d0330d14186c174341040146f0724a83923c2652e132870984b84c21c1c91a110330713383c1741c0cc0146d05049828244141100129efac577d5a53ead1a05278fa94b7d4a3c02d5a01082fa9467d40fbfc4b1f5036fd34a7e9a33f4119f5032fa8177dc0e3ec491f50260094b7c92e3e41440128ef534a7bc20bd4519ea25cf5b4a7ac233d406401286f135679daa3c497de46d8f21607892bbc48d00127eefa5877cac3acd7ddd2c0eb35776ca2bac969d728aeb92d75c0cbac56801276ea0396ce2d3a3161d12b0d9a5f73e3036695dcd29ad995a728a7b9451db3098e3a5a71c2b366105c5290da24f6d123b68529c12b0da04f6d025b7a971bd290da0476dcaa374111b7088dc0446dc1a36810db4056da0276cc200024ddb12a8ce35f6b93035c5b19c6aece15c6a526b54541a948ace15669527b4c541a548ece1546709a34293da148ece01867527b3c5419d48ece01400499b341059728ccc04665c0c8024ad9506200927644a4b22521912880084f5b62badad296d68cb6a5b5b52bada92d872a0c385c61c282da91d85058b684b5b423b02d5981282b68465b417aecd297668cbb25a5d92b2ec92979080bb2465d8a52ec5196d05cb993c5cc162da0ad6d04eb802c5b89a2dc0b16d0460084b5912e2c8545684c0b4018590a5aca541650c0b214700423aa4d2952496b0054578a82bc1715248ead94156c9aaa411954694aa24a55c202a891954294aa146548172a407801086a535653daa29497d4c6d8a60605292ba948d00107ea395851c2c26ad7d450c09ab57508942840a1354b69f9284fc1426a94d3c2509e0284d51da74115352b49b0454d81726c075350b40083b4cc9ca01169308b0980584012fa5d181004ae9595c4ac0c20056d272b89394449c0c20054d2429e92147400a623c9691e4a48f15a47ca023c559002828e04843127a1891d0c29e8c018430a5a2c9710c28e87a5444ca221e511112888793443c0c21850d0c25686127400a020e941072b88414041c0c2004ad012828194d40ca2a025010109a8005a0041b9fc150e96be7d9603ec361d2d5ce90b87b24d3dc281ec914e90ac7924f3cc281e491ce90a8748343b9279dc91ce90587524f3ac281d491ce904800833371259ca540e50b86e24738ca09b8118dd49470040375231ba528dd28c6e02e004159b44c40104e6b95435c2c190d7cd44c06a16c321ab9a4060c84b6680183212999c060c84766594932ca0990558c902a6405a0040f98a960c50a85ab5f308b01841b0b56ae600262d52d17c0f0b52b65e03c2d4a99740f0b52765b8492dc2096a158b503c0081b2cd2c15ad7caf4c0579602bc3015ad5cad4b4008172a12c150560a80b05405400a2f946980a32c05186c28c3000515c9e4b04f1582782c13c150026be4d06c26c22134180026ae0134a24d28126540930b84a05424c28004d1c910b845b5622d211165088b09c4605422c21004d18024b642b4a215a310a4a88524c0125a20c2e80495881478012530091d80456c786943c3461e12d0f09587825a3c125008ad0e85287428c3a05d008ab0e44b0022a60113b1bca40ce93c6b0b8360341ac280ce91c672943414619c0e804490614d030968188ac0c4520612480105f17c160b68d05b2d82d83c16c1600416c5169428b461442b0ac8d05108c2882e144168a20785103a0105a125b6092960492b02525c128ac09452049248010570ca2f064d743269a2195010c28064d14324bc202340c9290649343248a1e25c0c91d072d4039488192360dc0c064524322821a02c0c824864104020ac1802c0851a05a4902d0b8109640a492054050290a8108540949204c050250a8108440841e0420b02103801053008258369681b2b40d85a06c2b004128196880104702a2d0151580a6ac0534e0291a81e9280f48c0793203c190148d00d4680515a02d1a0141680208c0402c0151a00a0f0050580103b00c920040dc010260001f 10 11
def l_48 : Nat → Nat → Option Nat := unpackLinksF 0x4360219870cc08601c2b1615810ac08501c250e118508c083c2c1b0e0c8506408282c063a0301018080c04060203010045802040101fe88ff407fa03f521fa80fd407da43de3def00f7417ba03dc05ec08f6007ae0bd701e790f3c079c0bce01e310edcf76c0bb601db00ed8075c43ae01d586eac07501ba50dd280e94074a03a501d280e9407402ba001ce86e7407341b9221c900e480724038f0dc684e28370e1b8701c284e0c2706038301bf88dec46f40b770dbb80ddc06ee036b31b406da006ce0b6311a62ed300690234219a082d04067c1b3b0d9d80cec06644b2a219500ca806520b29019480c9c264e0323119180c8c06421321019002c80063c131e018f00c7806342312218900c402620030f058588c2c06101b08018286c14060a0303098180c0815f832fc017d82bec05f212f9017c02bdc15ee02f7017a06bc825e402f1057880bc015d822eb057580b8895b052d8016a08b4825a402cd156680b34059a02cc056504b28059402c9056384b1c058e02c7016284b14058a02c4056104ae8857402b8095c00ac8655832ac015582aac055602ab015406a9825461aa00d4e08a6045282293054980a4c051e228f014684a2c2516028b014388a1035080284014200a1005080284014182a0c05060277313b029d804e4226f0d37809b814dc026a1129ae94c049e224f01278092c4496024b01238890464800a3e091f008f024780238111c008e0046a1a35011a808d404680a34011a008ac94501a20211000880043e0a1f010f80874243a0219110c80864042e1217010b02858042c021211090084804201210010800838241c020c0906008300418020811001080003fc11fe00fe827e443f201f60cfb007d413e221f100f8807c013d821ec00f6007a823d209e708f38079c03cc09e018f00077c13be01de04ef0077413ba01da0cec0476003ae09d700eb0275803a421d104e880720938e09c700e380718138619c300e18070c038211c100df066d0a36801b010d7046b8035229a900d4806a4035009a608d300698034a09a308d18068c034601a108d0806840340099e08cb106502326099300c806640031c118e00c700634131a018d00c38c6046302018004c00060002fc117e00bf005f022f8017810bc005d432ea017404ba005d002e0217000b70459882cc016600b20459002c8016208b10058022c0015c10ae0056432b2015804ac0056002a8215010a41051c128a114500a20250c127e213e049d084e80274013a009d004d4526809330499024c8025249290094804a402520123189102484123e111b108b8845c022e0117008b80458122229110087064341218090c00860042c120058fd0c7e803f011f800fc0079143c801dc20ee0075083a411cc18e600728239401ca00e500728036ca1b600db006d8035c41ae00d310690234801a208d1006880340119c10ca106500320217c50be005f002f8017c00bc085b8a2dc016c08b5045a022cc115c28ae0056822b4015a00ac0456002ac115600aa04501427c113e009f004f8027c013e009b104a8c24c2126009300498024c0120189000480023c111e008f004780238111c008e00458622c0114088a00450022411120079403c801d440e610730037881b810dc006d0435841a810d4006904338419c00ce006700300e17c10be005f002f8017c00b4285a002c0415c10ac0856002b0015800ac0056002b0015800a0305000278213c009c0846202300114108a0045002106108008208237800c40001 0xab043288192a40895448a4f05c54822931a2c428ea502932704929c09c98d5a1848925a34859a23b0982022890ab447613440a969d825a5302191c0c946046146889b16060822426d11362d0c295a294914860b8a30449b01d8811d42e8da124692495b758acc9054e462a30414b9142da6a166440a72105163c2594404e404691f9388f89a47a0e23c068ef9598e8a8a8e166390a2f024a745233be52a3728c6302928410c6c0649f022a414a4c0a31ae4b8a0244a384a8d0234660b89f0451c3458d4a4bcc4fdde276e81376c099c641254e07ea303b4bc1b9fa0ccd603e6201b2c80b93a04e300311702c8bca4bba5062d092a28418ac203c8939af484ee94a8a8a31aa0b4b004b1481926808c4e5014c29c7e14230c9515e49945095130468941713408a2c6bb1415178c9fbb84edce26ed693389028a960fd44076968373e8199a607cc10365701726409c3e8d22169f1034787d1b40e52df0286c704b5882193004c970430e81924c0892c48a1b05c49822870a0c34104920270b14b854a1c2812e130864801323c10c220648b0224712283c1711608a184950ba478492340c52e10266c684b8381991404e0c093058488282240a98202288440217f00c8b204487042fd81916008bb295205278eda48764a4404d59d969ca104980420998591692781092c7f8143ee05086260ff12c144903f8d29fb68cb715a5a0ab2865292b28c6912e16c91284129fa08c1081e1440e8a44b085060fb0107dc0e0a24a1f62481b0645f01e41115e07695033467692539891a04296eb14a80ca3c005198c0b6b385750425a5411cd105e5f82922411908085ff03efe81b7e40cbf005df5026280115ccad2ca558210b42b8567b62ebe6971f20a2c584b59023904045ec0329f8497bc20a500d4810422901908408bd8d294029493946340970444893f094f584615017042089f0694f71467b49727c12d2608e6782f20011bd4065e76a8f2b6c790b03d0d59e64bef1a577891a3c0961df2b0ee96076ca283c085d928aec12d75c0c838045de6beee3577692d3ac5698a0b6b085339c1d834045d4072c3831714203a5161d12b0e584c7102039f181ca098e1840734a6b90105c2080e594f728a3ac0101c84b4c495a57ca91cc4e9870b4e3856714a4382135bd08ae09585e41637c971bd290dd8406e81a370091ba088dc0446ecaa372111b7068ab82c3801638893dc348ee114a70027b7e12dbc08edb0436d415b6809dd38b4e825f7392bb98569860b6ae8537242638c105b30807202b6acb2362551a2030cf8146a8aa33c051af4c0d716c6a4aa3420619d028d51506ad26b52915a62a0d3a4f69523b4493da148ecf15067d27b3a91db06bed6b576b0ae350559a42a8d19346800c3380513c092cd0414f4a520e518ce25c029224f0253301199928c9d84b4182399a0bc7f046cb81965418b2652592290c8944614b03041107d244bf02e164110f84897d05c2c0221ec982dc4a17c078108205ccb00f4480210c0bd82c074902f40f1770580e0205e496312541880b8c38505e016270551850589d1484e024304d593869cbb949604a08f24c174070298305e4202fcd297d68cbe25a5ed2b2f49297848cbb94a5d8a30424b85325a5f02917010ae0091742785c0645cc16042070782402a03c5bc102e00b053278b79340cc322dc0b18f8aec734a635a331896d8b4aec524b61923a725290028c6412e2f4958fc48c77244c204b4d42530611d8008cbf82f5d4172e40ad7104eb6823140112d2969664ac1095a15cab2d2980212c03b0205a00c0af581662a0b28601d4082a51756b4b8b515159ca5ac851c73024ac82e5601e2aa0b157258b005457ca82bc1715b088ab02c554a4ab85055b26aab840565a52b09295648caa94a550a31780a42304229019084088e44885405c10822589a52c292d5d48e5d92b1c491ab41195305ca901e53daa29adb14c0c0a83565392fa9695d4a468a415851c2c28a181432500f03050814038081402509f8284f4942780a01d2449d0454e022a6e0b81c0449b01d519afa88d5d414b69f2534ed1da72569350b40d0224cc9ca404c51c28098c58494a6236501300b097460490a623450118280912504b0ae2405412b03087940485282525712828893818494a7a4851d180508f95443c1423e501224b490a524291d2405691e2ac8285a47024208161180308b25c450a0206121132688892444ca2222511144a8891444409a21e061080308da4f46923a3253d172968a947438a1a1a4ad0c24e8104a420142105010a4a08495c41c0c2085350328a82941408a0202135328b497a5f4b52ba5456d262a69194c474a0a16501062568005a3e0321fc150ef058760243dc2a1d6090fc2c07d86c3d82a1dc0b0ea0487b8503e1269ec914f30a07a24f3c9239de93cee48e758503b1279d491cfd6be7d3573e42e1ea158f10a8780343b4161d2090e10786f02c380961cc540e50b86f82c378a49c6504e008070a4a37d231bc528dd28c5d029018109ce92ce448e5c92b1c0919c4118dc05c6d131360aa1ae160d54c06a16c331321028f0212506901832d320a8490d003067018084ac8a8544cc292659411c897192054d66be69b573452d99e94ccd476651562d497190168c64b06285430cb01841b0c004c4081e2e0b20e44b0be078108182dcb21780f0520285d03c0842c8a4144b80925b8412052d0e4568210b42b856311af982d5cbf4b45e95b2eca99724ecb60ac5a81e1bc101669606e020358101ac08162980b02c0578601a8080d2080b26be573572b52d0cc040ab4b05515811432152160a80a82205410c2a1228d09068853260294b01481b01c0d00b06428c300841501508850a58280ac0dc4903e0c84f8582782a0da0506c0283592426c220d44909c0d84d0600f42a1109687d2b42c85a0ec2b128150974a04b1502542e126140130884885c0442a07211010068078342302a120d58874b447a421f0ad11c508580b41c056234271161081906a0703416c9406c1902104006834221a510ed187b2b43b1562189510a498650ba2705507825018118818ba3d14a1d4a310617481478111280d4320420a0052502e13c0cc320420400b0683eb4a1f1a30f69687a4ac3c92d1e0928c81744d0aa0e84a028230e5174762943a9461d02e8464f072258190640840c00c4f06f290360341b42e0d61406309a2504512c0e8c40544b294341461b9278d491c692943084f1782589211c2f0860382b00c138ce074632b031148195340c85a0612482e86815c2a0be0b02d0a81a0540dc2a0bc8d05d2d8239641701e0b60b0560682b2340d02a06e150596942c34615c2b08e1541c0942a846150170a60b45203c2881d130920989704b2b0251480b82009edb04e4b0269581249208e1602c0a01a02c0dc0e0728d0442a0218501011a0789703a6a008a540e52206e0603405823c5e0862e88cd74166aa22b4d109a28829783f4a41f24d0f5228768e83846c1b1490d4a086612432082171540ac2204e0d030058150340981205c4902d0b8148440941a0541102a028159240a42a04c11026028139240942a05e8d02c2c814054090220460f0220581081c050aa03c9681d2b40e05a06c2b028114196880a048049220228d01249408a46034a50204c80b094078320351a0168d0178b40b456055ab028d381346a07234030ad0141680805803a340181e00a0b00324853c5f28a2b93ad7c996ae4c34a249a3914d18894b64225a2092b10094c7f4763f15b1dcad0e6558712a63813b198920c017c5a0b62805a1202b862158200a60f84b0682503011c0908c0203b0081bc9ad3e4a69720b478eda1c6293e2348f1123f8791d4328de0d46d0494f7d0a5be251de9286f093f7549db644dd9b266cb12b65093b2013d6c096b184754421a920fd340767f8373a0199b60acd904e6381f2d00d95805c010260001f 17 6 11 10 7
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsF m_48 g_48 bds_48 (dagRefF 594 (dagTraceF m_48 s_48 8 f_48) l_48 0) s_48 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_0 : treeBlockF 0 32 (dagCheckNodeF m_48 g_48 bds_48 594 (dagTraceF m_48 s_48 8 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_1 : treeBlockF 32 64 (dagCheckNodeF m_48 g_48 bds_48 594 (dagTraceF m_48 s_48 8 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_2 : treeBlockF 64 96 (dagCheckNodeF m_48 g_48 bds_48 594 (dagTraceF m_48 s_48 8 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_3 : treeBlockF 96 128 (dagCheckNodeF m_48 g_48 bds_48 594 (dagTraceF m_48 s_48 8 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_4 : treeBlockF 128 160 (dagCheckNodeF m_48 g_48 bds_48 594 (dagTraceF m_48 s_48 8 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_5 : treeBlockF 160 192 (dagCheckNodeF m_48 g_48 bds_48 594 (dagTraceF m_48 s_48 8 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_6 : treeBlockF 192 224 (dagCheckNodeF m_48 g_48 bds_48 594 (dagTraceF m_48 s_48 8 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_7 : treeBlockF 224 256 (dagCheckNodeF m_48 g_48 bds_48 594 (dagTraceF m_48 s_48 8 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_8 : treeBlockF 256 288 (dagCheckNodeF m_48 g_48 bds_48 594 (dagTraceF m_48 s_48 8 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_9 : treeBlockF 288 320 (dagCheckNodeF m_48 g_48 bds_48 594 (dagTraceF m_48 s_48 8 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_10 : treeBlockF 320 352 (dagCheckNodeF m_48 g_48 bds_48 594 (dagTraceF m_48 s_48 8 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_11 : treeBlockF 352 384 (dagCheckNodeF m_48 g_48 bds_48 594 (dagTraceF m_48 s_48 8 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_12 : treeBlockF 384 416 (dagCheckNodeF m_48 g_48 bds_48 594 (dagTraceF m_48 s_48 8 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_13 : treeBlockF 416 448 (dagCheckNodeF m_48 g_48 bds_48 594 (dagTraceF m_48 s_48 8 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_14 : treeBlockF 448 480 (dagCheckNodeF m_48 g_48 bds_48 594 (dagTraceF m_48 s_48 8 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_15 : treeBlockF 480 512 (dagCheckNodeF m_48 g_48 bds_48 594 (dagTraceF m_48 s_48 8 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_16 : treeBlockF 512 544 (dagCheckNodeF m_48 g_48 bds_48 594 (dagTraceF m_48 s_48 8 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_17 : treeBlockF 544 576 (dagCheckNodeF m_48 g_48 bds_48 594 (dagTraceF m_48 s_48 8 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_18 : treeBlockF 576 594 (dagCheckNodeF m_48 g_48 bds_48 594 (dagTraceF m_48 s_48 8 f_48) l_48) = true := by decide +kernel
theorem nj_48_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_48 g_48 bds_48 594 (dagTraceF m_48 s_48 8 f_48) l_48) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_48_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_48_1 h1 h2)
theorem nj_48_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_48 g_48 bds_48 594 (dagTraceF m_48 s_48 8 f_48) l_48) i = true := block_join nj_48_1 (fun _ h1 h2 => treeBlockF_at nb_48_2 h1 h2)
theorem nj_48_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_48 g_48 bds_48 594 (dagTraceF m_48 s_48 8 f_48) l_48) i = true := block_join nj_48_2 (fun _ h1 h2 => treeBlockF_at nb_48_3 h1 h2)
theorem nj_48_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_48 g_48 bds_48 594 (dagTraceF m_48 s_48 8 f_48) l_48) i = true := block_join nj_48_3 (fun _ h1 h2 => treeBlockF_at nb_48_4 h1 h2)
theorem nj_48_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_48 g_48 bds_48 594 (dagTraceF m_48 s_48 8 f_48) l_48) i = true := block_join nj_48_4 (fun _ h1 h2 => treeBlockF_at nb_48_5 h1 h2)
theorem nj_48_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_48 g_48 bds_48 594 (dagTraceF m_48 s_48 8 f_48) l_48) i = true := block_join nj_48_5 (fun _ h1 h2 => treeBlockF_at nb_48_6 h1 h2)
theorem nj_48_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_48 g_48 bds_48 594 (dagTraceF m_48 s_48 8 f_48) l_48) i = true := block_join nj_48_6 (fun _ h1 h2 => treeBlockF_at nb_48_7 h1 h2)
theorem nj_48_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_48 g_48 bds_48 594 (dagTraceF m_48 s_48 8 f_48) l_48) i = true := block_join nj_48_7 (fun _ h1 h2 => treeBlockF_at nb_48_8 h1 h2)
theorem nj_48_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_48 g_48 bds_48 594 (dagTraceF m_48 s_48 8 f_48) l_48) i = true := block_join nj_48_8 (fun _ h1 h2 => treeBlockF_at nb_48_9 h1 h2)
theorem nj_48_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeF m_48 g_48 bds_48 594 (dagTraceF m_48 s_48 8 f_48) l_48) i = true := block_join nj_48_9 (fun _ h1 h2 => treeBlockF_at nb_48_10 h1 h2)
theorem nj_48_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeF m_48 g_48 bds_48 594 (dagTraceF m_48 s_48 8 f_48) l_48) i = true := block_join nj_48_10 (fun _ h1 h2 => treeBlockF_at nb_48_11 h1 h2)
theorem nj_48_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeF m_48 g_48 bds_48 594 (dagTraceF m_48 s_48 8 f_48) l_48) i = true := block_join nj_48_11 (fun _ h1 h2 => treeBlockF_at nb_48_12 h1 h2)
theorem nj_48_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeF m_48 g_48 bds_48 594 (dagTraceF m_48 s_48 8 f_48) l_48) i = true := block_join nj_48_12 (fun _ h1 h2 => treeBlockF_at nb_48_13 h1 h2)
theorem nj_48_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeF m_48 g_48 bds_48 594 (dagTraceF m_48 s_48 8 f_48) l_48) i = true := block_join nj_48_13 (fun _ h1 h2 => treeBlockF_at nb_48_14 h1 h2)
theorem nj_48_15 : ∀ i, 0 ≤ i → i < 512 → (dagCheckNodeF m_48 g_48 bds_48 594 (dagTraceF m_48 s_48 8 f_48) l_48) i = true := block_join nj_48_14 (fun _ h1 h2 => treeBlockF_at nb_48_15 h1 h2)
theorem nj_48_16 : ∀ i, 0 ≤ i → i < 544 → (dagCheckNodeF m_48 g_48 bds_48 594 (dagTraceF m_48 s_48 8 f_48) l_48) i = true := block_join nj_48_15 (fun _ h1 h2 => treeBlockF_at nb_48_16 h1 h2)
theorem nj_48_17 : ∀ i, 0 ≤ i → i < 576 → (dagCheckNodeF m_48 g_48 bds_48 594 (dagTraceF m_48 s_48 8 f_48) l_48) i = true := block_join nj_48_16 (fun _ h1 h2 => treeBlockF_at nb_48_17 h1 h2)
theorem nj_48_18 : ∀ i, 0 ≤ i → i < 594 → (dagCheckNodeF m_48 g_48 bds_48 594 (dagTraceF m_48 s_48 8 f_48) l_48) i = true := block_join nj_48_17 (fun _ h1 h2 => treeBlockF_at nb_48_18 h1 h2)
theorem nc_48 : ∀ i, 0 ≤ i → i < 594 → (dagCheckNodeF m_48 g_48 bds_48 594 (dagTraceF m_48 s_48 8 f_48) l_48) i = true := nj_48_18
theorem lb_48 : LowerBin m_48 s_48 g_48 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_48 sub_48 gl_48 rc_48 nc_48

def m_49 : Nat := 0xffffffff00000000
def s_49 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_49 : Nat := 0x115153700000000
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_32, s_32, 6, g_32), (m_27, s_27, 5, g_27), (m_29, s_29, 5, g_29), (m_31, s_31, 5, g_31), (m_34, s_34, 5, g_34), (m_36, s_36, 5, g_36), (m_6, s_6, 4, g_6), (m_7, s_7, 4, g_7), (m_10, s_10, 4, g_10)]
theorem kn_49 : KnownBin bds_49 := by
  intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_32
  · exact lb_27
  · exact lb_29
  · exact lb_31
  · exact lb_34
  · exact lb_36
  · exact lb_6
  · exact lb_7
  · exact lb_10
theorem sub_49 : ∀ b ∈ bds_49, m_49 &&& b.1 = b.1 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_49 : ∀ b ∈ bds_49, canon b.1 g_49 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_49 : Nat → Nat × Nat := unpackForestF 0x25109b2714593ca6c9c1140169f25b4e92d1c002d2e454a12295c914a848a172450a000b478f09fc784de4107b1e1358f01fc780de3d27b1e035005a1c7293e3948600a4e8dd1e00292e3505b191258cc96c640940148713349899a1c564fe2b26f1583f8ac1bc4cd062907b1312789c9ec4c09c014851194588c22c3897a204a51002d87092c3a94a1d25b0e0250051dc341321728b0c14c85c22c1c97a1504909a5284c16c1c4961124907a5283c96c1c0940146705a5c82c924108ee094b904233004a7c0c4d20069701a3480c9a400d0e0029d0013c004a5bd2d71e96a2fd23b7ec923f48cde96a0f4a507da303ec9b1e9476f8c607c5363e4d41f1248f4a337b895bdc48de90b8f523b7ac923d48cde90a0009477991a3cc4d1cc696f2134731a1bc40d5cc29cefa3b77d19b98061dd284e601576c9239a8edcd466e683f7341dbab141d5480e6837749a03a48c1d0288e803c73419b9a0bdcd046e6014004a1b5714dab6bee3b5171c22b56d79c5268d5b53705aeb824d9c106ad5b526ad2f356949bd4bad595e6dc9b36e055b8072dc0316dc0a356549ab07eda14c6ac1db560ddaf6a4d7a5e6bd293560d5ad078d61446ac198024fda7030d381569c0a0024eda506ad04526812f343179a14bcd004d0049bb385399c278ce01500499b34115974bccc25265c128024bd9502a009236492e32409186476c825c61919b1ad718d068c313f62a283141318626ec3a5c61c1230c4bc0109ec20345f9a5b024d181068bf3435f8272fc0f001096b3b5c59da8af08ed79048bc23359da82ce941748c0ba26c59d1dadf1816f4d8b83505bc122ce8cd6c256b612359cae2d08ed69048b423359ca800211d64268b20344e1a5ac40d138686af94457c2227093d5bac0ad95c56c2e27091d58268ac0344e11faac4d53809ca9a3b54d19a700b14c49ca6242530a729c4c14c28ca613e4e013294091394769ca3351c1a2724fd39276a1450509202841313926e9fb404fd1827a9113d2789c9334ec122724bd392469c02400421a1114d086be99b514cca2a10d7931068843534b5aea5a4d52d06c843524212f210949082be9314c498a224c051082a68414f420a1a440d10827e9024c4209da104dd158bc8ac524552f22a949152bc8c014454a922a4f9152648413544ca6222911110288413343d2ea101790906c848164281ca140c509028840520041fa080b10404c820240041da044d4f38a479a5e3ccaf9f7580fb2b87e0303ec0a1e654cf46bc7a3523d12f1e8578f50287a1523cca68020dcf128874a4f3bc921d290ce909c7483c3a8a71d4508e904c0083339ca29b8978dc2be7193438c0a1b854cdd6bc6eb52374af1bc050dd2a46e125004179b4098010466ba3435c9a190d2cd42686a034321a19a44d8c849c6414e3392219c570c809e65a5c32ca619011cc94686403f0040f98a4d0c50685ab4b3091a1840d0b5686601442d52797c570b548e5e1342d51f9740d8b529c5b94d2dca296a138b504c0081b2c12c160950b02a85805409e2f956920ab488559442ac2204f14c276bc5223829d201488d0a42685203409da99449209c8a24e23a27da01388d89c26c4e03609da912e8e0974684b93425c1a04ed2c934704a25024d1a04ed0c274be4834909d2f11d180274a642c51215a89128d88906c42b50214ae90c9408529c13a5209d278f4d787a6a43d25e1fdae0f49487a26c3d1351e81b0f40d42749c3bb5c1dc9e04e92c74ac03a35009d238e1140706803814c1b9aa0dc530274862dc5e1a9220d41105b8a43414416daf0cb140652682db5216da48b6d045b2bc3035016ca90b65345b27a2e35016c9a84e9082747e13a33155280ac500550881394f12d2f0969484b2bc2825012ca90965244b2822583a12c1b04e538484802405c09ca388a5384525c1394210c1a04e4fc3f4a0201300fca204e13c334bc19a520ccaf074940332a4199490cca0866138330841983a0cc1b04e1382f4b817a400bcae04e11c2a29c151420a8270540b8270841413409c1f80205c250680134b0851a0424d0210680134307c120128ec1b2500e14006c920128cc190680493f0249d829140144800a04c0249b822d001146007a4403c9e0124cc0d0480492f024918140f80903c011240101c8080c4040520202100c0a004138010260001f 10 11
def l_49 : Nat → Nat → Option Nat := unpackLinksF 0x4360219870cc08601c2b1615810ac08501c280214010a00850042802118b080383c141e020c8b0583828141402078b004e802040101fc90fe407f00bf801fa86fd407e41bef0df780fbc07de03ef01f780fbc07d42bea01f386f9c07c81bdc21ee00f7007b023d801ec00f4087a003d001e410ee4f77203b805dc00edc176623b301d902ec8075443aa01d482ea4074243923dc900e480720139001c782e1c870e038605c300e180708138401c200e004700037e09bf00df806fa0b7b09bd80dec06f6037711bb02dd806ec037409b78adbc06de036d09b680db406d80b6a09b110d8416c2035d11ae80d6836b4035809ac00d6006ac135505a78cd3c069c0b4e01a682d3016960b4a05a308d18068c034409a200d0436800b40019b92cb4a6561329099480ca4064a2325019184c8c06460323018f88c7036321b19018b84c5c062e0317018b80c5426241b0e118682c28360e1b07018380c1c05f662fb017d02bd845bebadf016f80b7c05b81adc016c86b6015b002d8016792b1c85881ac4016008ae8657402b8095c00ac8655832ac015582aac055602a9095480aa0155002a8015208a90054802a2095100a8805401298214c00a5c152e0297014a84a54052a0291114880a3c251e028f014702a302518028c014600a20450e0a87014380a1425002a800140009f824fc027e013e829ec24e642720539009b844dc026b0d35029a804cc226601328299404c2226005300097434ba025b092d8096c04b21259012c0295c14ae0255092a02938649c024d05268093404980a4b0525029241492024511228091404861243012006900047e0a3f011b128b0a45412280914008a00448222401110488804440222010f0886c34301a14110a0085004260a0f11058881c440e02031101027fc33f819fc00fe007f003f801fc00fe007ec13f601fb00f7987bc03dc09ee00f5087a803d011e800f4007a003d001e608f186731739801cc00e600724339201c60ce28270c238601c300e180704237a21bd00de806f4037a01bd00de026cc935641ab00d38869c034621a00cd0006800340019c10cb0c6580328119208c900644131c198e00c700638031c018d04c38c6046302018004c00060002fc117e00bf005f022f8017a08bb085d802ec017210b9005c802de196f00b70259882cc016600b20459002c8016208b10057842bc015b0cad8056812b4015808ac0056002a8215010a4105200290014800a40050c5284094200a082500126e49331099804cc026409320099004b4525a012a0c95004a802520928049382470b238011c008e00470022c3115048a02448221c210d04868042052100106088300418020c010600800c400020000ff047b903c851e208f10078803c401e008ef0477803b811dc00e428718238c01bc28dc086d0434c71a408d1046880334419808c6186300318018c00c30c6180308118400c2005f862fc017e00bf005f802f8117810bc005e002ec115680a80c5382298114c00a5045106288014208a1005080280114000a0005000280012c5096004b0024841240092004708238011a088c04460022c1110188800438221c010e0086044300218010c008600430021800f8507c003e001f000f02078003c001e000f00074103a001cc10aaf05404290414410a008500026081300096084b00258012810901048002382114208808430421800fc407e003f001e840f400722039001c020e0007000360816140b00058002c0016000a0404e08231000c40001 0x25109a590452c40ac9e534b228a580169322f47497a5028b270452bc0bc98d3a304a125a3892528490572472a12305c91428390db22e4c0e11448b5303844f1c529ce113e9041e95a0d4ac02a9a36c8b13025a1122b4c09683c8f49e95a4d53109c9683e2ac0b47297a2f4a515250728a7c864fdc027b211379009aa6c13e3f07e9603d8f81bc780d4aa02f1bb4e8e927c7290dbf25ed19274ac17a0009ca902f1ba3c8d41694c094a502b1992d2989294805a3424b1902528c0bc5c4fe2d26f1603f8ac1b94205e2907a4f0352740ac4e4f49e26a4e0168c1a4c5ed0e2a682df13f8a093a540fe2604e4d817830a6c485159309b118458312f44294a0b2bcf395288016932094d803a4c01564d2f43c94a1d25a4c9256482f2ca148c60344b8168892f41457e052b6fa957794a9c3e495910bec185b5cc2bac614e1c04a6b01f3100d92c05c240270d04c860a64125361928ac804d85c22c2a092094bd0a252810ad3e255a1305a4982530c0c84604611248c825e8412941e4b49324ac105a5bc2b1a8078220250b25e820afc0456df02aef195384892b1e17d800b6b705758429c1c094d303e6081b2480b84004e0c4b9059248252e380d060a477042336f09f11e1352907e7f83739417c0c4d20446901934815a5c04d0e0129d0013c7dd24be8905fb248fe23b7e919bef181f64d8f786c7b0303e4491f26a0f58507d2303e69b1f1248f706c7a8303de4adee246f59247b11dbd48cdfe6b8feb517e5a83f0941f5476f82337b42e3d2141db028f3a347989a3c0061da028f213477c0c3b20512807af10357811dbbe8ccfc088dd24e4a0a73ba5092609c7d84638c1f3b649118268dca4c74c203a40c1d68a0eaa403d4a63a20c1d3680e92306e1263a2511d00786f1247691dbb28cdb727cec03f75c1dba80ddcf066e702f73411bcad2de3686db24e784a724a13cfa08e7103f7780c3b8055cc028e446c7149a386d81bd2d8e1c5d721a8b1c135c708ae1c6c7149a386d75c226c4083d7041a9000b5b004a298151f81eb5e0d45202adea5d14426b720e5b8062dd9366e80ab6e050576b88b1346d0240f6111ad068da14c130920f41107b078d603012c0a31cd79b16a4d825e6bd2931a179600a49104e3c4210f60f83107a6001a1540b35a0f1ac2885c05c0c4261d6091ca8a6e4b5f719af388d4dc06a4dfa5e6f929378579b62a4c605f57829a4813cf0086da83f1e41eb660edb206ed70356ac199a2074bf0362a0171280ab52061a802ad381457428b160f5a506ad083d68a2f317149a14bc1894d1f0a2b141795c0a45f01a1200b349149a34bccf14d6242fab414da009a5e81b11c0b8620f47a06a230150c4a70ee5091109c77842678a733a4f12309e7704311012b380558809acd0456212f330949870bcac8522f00d086059994bcc305f55c29b2e094bb036210176540ab2697192048c825c639ae102d40512b8c683462e28314131884b8c38244b1a0b228ed8f4664794d6309fb124dd8625e8703e6101a3044d181068c1b4b601a1afe1397e078baa495c920af20917a476bc2335d6302e89b16d2d8b51605c0122e0d41690a0b94605c5362d85b1682c0b78245b495ad848d69048b523b5a119af8d717b6a2bbb505d9282e68ed6e466b595c59ca829405165268b20345501629209162068a982c5201228e05160288a884c57c2229e09142028aed60570ae2b61714d0489d8145649a2b00d14c048a893d5589aaa88ed53466a724451c1a29c4c1420989d824545272a09094f29ca69465309f2181394a048a383442c262805013f260a245050d2027c4c142098a03404fd1827c9113d2788504c4ec122928ed48466a313f5149da824dd3c2669d12f4e491a120f963696b0b4357927ab491d5747e8414e554272a40b14b04c9c0244d2362620d12f6c08786c4be2ea68d451d29a999454be362620d12f6ba4093d4b89aa5a0d88025a8d9250f40b0fc4f51a26a1e016475ae102d41192681d85c4609a22e91128298939444980a062d0116288910340d80a22a910312981a8244440a082d71202903e9444881a2264d1204983e1440d0120fa4f112260198144600a23b1791c8a48da5e46929232579172a43e94e0c4a6a2c4f9152646781d0fc0aa26531124886715c0c4a62220510f4ba1d84d42c1ca140c50d06c860164240a26d14d356be9935e4c1a9a58d492b4bc952524a4afa4a54d2429e919434849f8f24f51f2768f1374509aa204cd0e0bc840523340f9720683e02e190164181620a099040487f1513e09ea044d4f727a7c4503d8a61ea530fc0607f5603d12e1fa570fb0287a8143e5af1f0d48f74bc7b15e3d0a90620f47a06a6601d0bc0aa03149004bc7f95f3e8a99e6534ed09a6501f0b80b9e25102d2481884c3ac120584d0ef248750341dc120624f47c26a158160c5270ee908eb29c751423c1279dc90c2924c7684e3b01e1d2098e129a739453852e1be490de2486ea343909a1c6050de02870b5e381a91be578dd2a46481d0a00a9cc978e52be711533709299007c2702e6d0263611a1ae4d0d52686a0343489b08c054ce09a658450c41e8f40d4cf4886715c0c4a6056050cc4b83d15c32ca61928d0d669669b43345271a0538cd09e650473201f96a054c62686283430d1a1840d0c02885c05c0c42608c090be2b83e05c2dc261784d0ba06c158162e0a696e5143127a3e1350c5270ee9084629c1584e311a5982d0cbf49e5ea472ed1f972538b609c5a8262cd2c1649506c480589542c02a144d406b28035140285b0118980694a040a4c2b92415a9105f480561442ac221008f8674642993e0f41f14e9008b4c0542382991a14a4d0a406833250289240c09009f68045150224a81431448e4a2442501f9270c8908a04744f236148a713a4d83c09c4e03618d281348e0994684c13425c1a03c0401d0400e01025128036040624a04aa3824d1a034040874c043c5d241a4902d045127c1d83e23a3010edb05049c45236218a70c05083a09c44836219281191448b6a24435013d2710e5748529c2f9420e4270f09605e4a01f944154220300407f4a03fb5c1011e0ac930826bc40b521dda70bcd34804bc3f2521f49b0f84d47b06c3d0351c0a20f0d704e4b83b93c0e02e02e080724a00b0101c52002a04075ac03a3500c52e0de9002f2b82405c04c0802408011040394501c5a00e05301004007810179ae0ded504d4b83714c0dc2e01c080666a035a441a8220d0510668a0301501949a0c0d40404882b044171a80d9178698a433b5e191a90c6d24626822ba4d125228c25785f2a41894e178a68ba4f45b26a2084d0c0228504d0430680601002c100ac110562802ba500c5260aa110502a02825014d2f0a4948512bc27952138a489a5043609c168421301d0960d8314b824a40118ae0901704629c2292e0d427058108430682024410098082940314981f9440e8a80749403d4bc1e2520ecaf072548382921b9410d82706a10834074198360c52e0609002f2b81585c0b4a70585082b09c1502e0a09a15f17caa8a654b5e28da9936d4896696493432452f91e9788d4a64225220d278f29387649639a471b5218b49085947e2c233150a78945384728e221421089f87c13c3209c170470a42104e0fc080200f8140789204a0d01b2480d92408d1a0444d01a2481083407c120385001d2500d9240641a00e13005028091400449802d140154800813005026024d00114600824403c9e00c13004038068240281f0080c81e4760d2330609f82e4ec1326e071330309781648c0307c0481e01c1c80c0c4050520202100c0a048d2c20686041240082749ad3e4a697223478eda1c7093a3649718a43895214368ee0d4670394f7fca5bd051dcb286d513f6989db3e4dd9b266cb12f65091b0a13d7d096b30474dc21a0e0fd03076790373a0199b60bcd90466381f2d00d84c05c010260001f 17 6 11 10 7
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsF m_49 g_49 bds_49 (dagRefF 594 (dagTraceF m_49 s_49 8 f_49) l_49 0) s_49 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_0 : treeBlockF 0 32 (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_1 : treeBlockF 32 64 (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_2 : treeBlockF 64 96 (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_3 : treeBlockF 96 128 (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_4 : treeBlockF 128 160 (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_5 : treeBlockF 160 192 (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_6 : treeBlockF 192 224 (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_7 : treeBlockF 224 256 (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_8 : treeBlockF 256 288 (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_9 : treeBlockF 288 320 (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_10 : treeBlockF 320 352 (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_11 : treeBlockF 352 384 (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_12 : treeBlockF 384 416 (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_13 : treeBlockF 416 448 (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_14 : treeBlockF 448 480 (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_15 : treeBlockF 480 512 (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_16 : treeBlockF 512 544 (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_17 : treeBlockF 544 576 (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49_18 : treeBlockF 576 594 (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) = true := by decide +kernel
theorem nj_49_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_49_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_49_1 h1 h2)
theorem nj_49_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_1 (fun _ h1 h2 => treeBlockF_at nb_49_2 h1 h2)
theorem nj_49_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_2 (fun _ h1 h2 => treeBlockF_at nb_49_3 h1 h2)
theorem nj_49_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_3 (fun _ h1 h2 => treeBlockF_at nb_49_4 h1 h2)
theorem nj_49_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_4 (fun _ h1 h2 => treeBlockF_at nb_49_5 h1 h2)
theorem nj_49_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_5 (fun _ h1 h2 => treeBlockF_at nb_49_6 h1 h2)
theorem nj_49_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_6 (fun _ h1 h2 => treeBlockF_at nb_49_7 h1 h2)
theorem nj_49_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_7 (fun _ h1 h2 => treeBlockF_at nb_49_8 h1 h2)
theorem nj_49_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_8 (fun _ h1 h2 => treeBlockF_at nb_49_9 h1 h2)
theorem nj_49_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_9 (fun _ h1 h2 => treeBlockF_at nb_49_10 h1 h2)
theorem nj_49_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_10 (fun _ h1 h2 => treeBlockF_at nb_49_11 h1 h2)
theorem nj_49_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_11 (fun _ h1 h2 => treeBlockF_at nb_49_12 h1 h2)
theorem nj_49_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_12 (fun _ h1 h2 => treeBlockF_at nb_49_13 h1 h2)
theorem nj_49_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_13 (fun _ h1 h2 => treeBlockF_at nb_49_14 h1 h2)
theorem nj_49_15 : ∀ i, 0 ≤ i → i < 512 → (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_14 (fun _ h1 h2 => treeBlockF_at nb_49_15 h1 h2)
theorem nj_49_16 : ∀ i, 0 ≤ i → i < 544 → (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_15 (fun _ h1 h2 => treeBlockF_at nb_49_16 h1 h2)
theorem nj_49_17 : ∀ i, 0 ≤ i → i < 576 → (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_16 (fun _ h1 h2 => treeBlockF_at nb_49_17 h1 h2)
theorem nj_49_18 : ∀ i, 0 ≤ i → i < 594 → (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := block_join nj_49_17 (fun _ h1 h2 => treeBlockF_at nb_49_18 h1 h2)
theorem nc_49 : ∀ i, 0 ≤ i → i < 594 → (dagCheckNodeF m_49 g_49 bds_49 594 (dagTraceF m_49 s_49 8 f_49) l_49) i = true := nj_49_18
theorem lb_49 : LowerBin m_49 s_49 g_49 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_49 sub_49 gl_49 rc_49 nc_49

def m_50 : Nat := 0xffffffff
def s_50 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_50 : Nat := 0x17f377f
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_37, s_37, 6, g_37), (m_28, s_28, 5, g_28), (m_30, s_30, 5, g_30), (m_33, s_33, 5, g_33), (m_35, s_35, 5, g_35), (m_38, s_38, 5, g_38), (m_8, s_8, 4, g_8), (m_9, s_9, 4, g_9), (m_11, s_11, 4, g_11)]
theorem kn_50 : KnownBin bds_50 := by
  intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_37
  · exact lb_28
  · exact lb_30
  · exact lb_33
  · exact lb_35
  · exact lb_38
  · exact lb_8
  · exact lb_9
  · exact lb_11
theorem sub_50 : ∀ b ∈ bds_50, m_50 &&& b.1 = b.1 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_50 : ∀ b ∈ bds_50, canon b.1 g_50 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_50 : Nat → Nat × Nat := unpackForestF 0x24549f2835c91525c9c4964549322a4792d26494d52454872294f914a3c8c9064528a00b4f9051cc828e24146800b4b8f928c7c1700168f1c35e8ec92c708e6394631c135005a1c6c922306bf1a2388c1a9c62d3a316851834500527c5c95a2b8bb15a468ad1f00292e296ba00a477ae2fc4ad6a256acf5c5d88d2ebd7156218d8f5c53875a6c3cd161d49af5b54862b6433172196b90c3647ad27c2c972138c909b5c84d263d692e0c8d907c5c83dae418d920d4a90605c7ad23c0ad7a056a50294d8142740c05205084f5a4680d2e3ed192006a90024c7d9aa3ec931fb6a8fe2447ed223ec491f76a8fc2447dd223ec091eb486f592f7ac93be3175f1494f59257bd2e3dd191eb05ef64647ac1380290de76bcf3b5c79daa0028fdbc8bede45778d22b78d79bc6b6de35376e2ebb7155db49aeda4576c92b78d49d96c0de25f74daeba6d55d34b2e9a5174ca2b78979cf6d8e7a5473d2637896dcd6a0de25772d2e390d91c84a8e424c6f129b82975c54b8e0a4570d223828f5c124ade2526f097b7849dbd4a4de1250051db5d149b88c0dc2586b9afb69181b48a0da2606b9abb60d75b06aad824d6b92935c1300146ed6354679adb54d519e6a6d2a5969528b4a925a528acf25e685a9342979a14a4cf23e67d2933c49401466ce146655aeb329b1994b8caa3b6593632c971954660094f648a332405001296c82495b1aeb1d1756c69ab625c62a2eb149196c4a2bd34d61e2e2f48fd7a476c1b5c60c262f48dd7d688c02345f4922fc8d17d048bd2335e817af409d6c4a0ba3605d1362e8981754a0ba25c5b11dae4d116d6c0b6a6c5bd282da9716d248b6233004a3ac45316228cb303f59e282cc0dd62288b113c5889a2c405001286b024955daf2b91b15c4a8ae24455d29ab0d49584bcac25255d1c8024fd5428caa0140049da6f17d50492a81464de2f26f14d4c6baa62394de29293181492a89bb5f50ab0284971424a8a235050922284491374a69ba4b4dd21a7cd113b6a49da5e4ed2926e905386a09c1244dd1d8024dd312b8989544c49e2624d131028009334b9ac25c9611e8be95b484ad2423d14d2924c8f34a4922ea48d292448c921264792923e9791f4a48fa3d47c9323c9280125e8d94646c0a0024ad186b08c2583d62fa28d21144908a1443d6299ead610e8ba8745143da821c918f56a47fa4f42d261fe92d090b87fa47409aa204931054888112440d22204090ff4867f82f3fc139ead40fc4bc7e2523d5a51ecd48f849a7c2453d9a81ec8f4f5494009273acae1d6550eb298759463b41f9dc900ed06e759443ac0a00248cda4be6d253395af1cad48e524a6d24938d289b4514e06b070258368979b6d80db6b06e35036d2c1b449c0109e6c251004239aa924d528a4f35e34daa13c97cd08d8682442792d99cdb09e4ae6446c32dae190d90c84a86424427929984d78c26a46125e309291844949e4726036c278af97c5109e2b65c36c2e1ae1709b0b96b85c260278ab966550b32885993c2cc9a13c54caf8bc57c522bd2093c4d4ac69056248278979545109e25652368291b0148d20a56a0522482789393e5b09f2c84f95427ca213c48c0107e4d23926d181344d45b8a44bc6025e2c0b697c954b82da5b24a301251405b4ae46b6423d2a11a9708d4882da5320dad106d58834bc4335421d2210c490834a44225020c928b69045b2be3fd601fcae0b656c7b8c03da6c1ed300b655c73ac03995c1dda80e6510732783a4501cc9a0b654c7149036b5e1b5a90dc9706d4722d94d1ad280b64bc686a03415c16c958c8da0646c03235016c938b8d405c2d830240170b20b85705d4602e14416c918020dc4a6b6253531552c8aa9445528a2525e14d3609457c4e6c02726c13d2809c9704a2ae25b5e12da90944940105e243520041380207c454921ab4f10d1c86ad0c3f8ba2004c0fd2306a90c3b6a41da5e0ed2906a8ec394bc1aa330d49f86a4dc3502c0081a0c91c0644d0296a617b510bc9f0529482a6a41515e0aca2054548294640081709d24804d3c1e8ba121400792303c4a41e04c0fb4d07c9d03c090024860e024061a9030978190480c2520091d82c4d0146a20a03e008a18244d00e6a40705e03c2201c148022460103a0081b806d3c036860314c018a200c4d0032860193b00c998040d80102c0001f 10 11
def l_50 : Nat → Nat → Option Nat := unpackLinksF 0x4321218830b8385c0422320f8707c083c0c1a120c05058282c041211fdaefec07f603fb01fc06fd047e803ee19f586fac07c44be201ef86f5c87ae03d311e980f4037a003d001e608f10878803c209df08ee8476443b105d688ea8375403aa01d014e800738239c01cc08e504728039209c414e200710038801c304e045702038005bf82df816f22b7901bc80de406ea237501ba02db866da0b6d01b680db406da036c05ae20d7006b0235609ab00d4846a4035105a880d40169c134d05a680d30169413431da102d00267e0b3e059b10cd8066a0b320d9900cc41626f313018980c4c06201b0c118408c20060c1302117f86bfc05fe02ff017f80bf815e852f4017886bc405e202f1017802bc005c862e3057180b8c05be22df016e06b7005b60ada056d00b5845aa0ad5016984b4c05a40ad1056394b14258612c3015f88aa1754822a4015200a80454002a0015000a704538029c014e00a6045300292194900a3c351e028b114580a2c0516028b014112a0805040282013f869fc04f81a74213a009c824e402720137089b804dc026c09321099004c8026011300097824bc025b0d2c8496404b00a52192804940049e0a4e05270093804961a490924809201490024705218890814840239251c028e004700238011b828cc446602310918808c404600a30011608888a4440220091000880043e0a1d090d8486424320211210880838341c020e0107008245412020901048081834022a010100807f833f619fb00fd807dc43ea11f500fa807c053e001f000f7047b413d809eb04f5807a033d001df24ee0676823b401d904ec8076403a829d400ea00748238871c400e200710038801c400df8a6fc037e01bb10dd806ec037211b900db846dc036e01b700db806c8536401b200d9006c8035c21a620d300698034421a200d082674433a019c04ce00660432c119504c98464c0324098c18c58262c0314098a00c386614230a018500c2026100306097f10bf025f802ea497500ba805cc22e6017300b9805c422e2016e0cb21458822c0116000af0457802bc015d04ad8456c02a6415204a88254402a2015100a58c52c0292114900a48051c228c094600a3005141284193c189e004ec1276013b0099904cc026211310098804bc225c092c0896004b00256092b009580494624a0125009280494024a011d208e8046c2236011a048d0046412320119008c0245042280114008a00450022021100088004400218210c008600428221401090484804201210010800838240c4206010300818040c01fe20f03c78003c001de08e720738039c01ca10e500718438c01c408de106e0437001b608db006b8835c01ac08d6006a8235401a808d2086900344119240c8046400320018c10c6006300318018618c1086080304018008c00060002fc117428ba005c822e4017200b8045a082d0016608b30059802c4216200b10058802b8315810ac0056002ac115600ab005502294512c7895044a022500128009400470c2380118108b04458022c011408870c438021c010a107f183f801f810fa087d003d061e800f20879003c801e010e82074003a001d000e218710038021c000e000700034101a000d0006314318018c00c0186000300018000be085c0c2c8616400ac1855042a8014830a40052002900148009830412c208010010800040001f820f03078003b041d800e030700037041b800dc006c08330c19800cc006600330019800cc006600300c18000c0005628232000c40001 0x1b98d8d0c5c8c9a24a09624b48913360941ae384d42366bd09b52721a5370d19a147ce123d4bc9ea304d52e25b271251140d04e059a68b912a6092920496931c26b12535475d364149114a8d8a8154670b62a05312e49323241540a72924da354bf16a5989d29c489465149f27a4b93524c9891e49486e02417951db6e8dd9b2bac6955920a7a9e5364728f229455209ba5a4bd1724e2201a0980b4868e64247120a3473da5368d19a1494db2468f1aec7e94622482f223b6cd1bc7c172214a2d324968520c68d79fe6a4d125e685292584f51526a9592d8ec928860692b4731ca3145093478d7a334bf102538e91cc704d52a25e899271080d4435b1a18b1193548d924463151a26a91a2386862cb451463269d18b428ae2f46ad7e336a7183457891d1d217cd207e4b0378b92b4428f9a1492d32417411cb588c6218bad1b4a6852536c91a2d8baf0b4b6ada1c5891a2b47c6784f250238b20fe1f4a114b5d8712019a0fc9106f09b5868528414912266b512b5677da5364d1a1b49b08a4549c96be449441034128168862ebbcd29b168d11a5d886363fcd22094a8d0a4884126c329161a47b07a35841a6c3cd161f69b0ea4d8611fc2a8ee0e46f012333281f9200ddee05ef602786a2e432d721bad90c364775ac428961b64890b25c80122386912158c90a35c711aa3a89b2134990845c83dae4028c20d09906a548463641cd91dc690e22487fd20418171c349103014829af412d49c469cd0b4d7251cb548c60829aa29455749ea864d60709d028423241e91a0d43f03411816805a2406971fd248fc8247f0923f0092016a90024c7ec923ee091fc468fe2447f5aa3f6911f8468fc2447e5aa3ee912028c8ffb5469d363fc931a1478fd1247d8122484d124258108140800a03e051f28baedb4a7c52528a9194228c9212e0c80a83c051ef4b8f7464159361cc931ec8c913c5f8922ec45156208a70e354781a5bb4d29af68cd4b4385d27c2492dc049505a47811233ea90d5b29ea09477d097a464b5f324ef81253a02f98e13c8c08e2c03f7b417bd609c3e034188170740b3d2d79e86b8f3b5477db0390d61d74d8d0a5073db03bcd41a14c0eb25c68e2f3c6915d56d8e825468d263428f1d46d8e4a5468518038051df8baef455765aeb9ad55dd49aee24549896bb64943d0340d816765b03a29a1c64c0e2a446862f38d175d76baeb3557552cba89459a2baba155664a6ba65143c0340d01672d2a3a2db1d04a8e7a4c6851e39ad41a24d8e525072d2e38a971c66d8e53647252a390931c5488e2a5c70d1e38691019028d125e7192eb6c919c448ad323e7091ea424b5c124a1d81a0600b2729311f2689494c47c96332979bd4a49c14647c973cb17de48aef135e785adbc0d4dda6a4ec25f7492f39c96dcc4aee3a537012933057d732ae9b9474a09e9ea4d5bf25e8f12d6f893b784943a0340b8166e62eb6b155a1694db3466e630343141b24c0dc2586da3036b141b44c0d8a506c9aeb62d55a369ad824d6ea2936ed7db36aed034d6bd2935c131ac6a8d426c6991a354d51a74d8d1a4c6851e350965a74a2d324968520b2e5756e2aacb14d694a2872069a36a4d125e6852932c9799f4a4b69566adadb52d4da44bcd023e654afad855d9e24a1c01a49d28b38519266a0cd26c6652e242941974d8cb25c66daea9ed3523482cc23b6551997e0fc8106e2902f64ca317a13c7e08ec901464124aec9058e8bac5a51621281740bc7c04eb923062e2eaf0d2971684bb24a629230a20f58747ac223561e2e2ea971846b8c0a3060c263004917e048c02345f91a302d116f4b8bf9245f41209e9718869ac323f6151db048dd7c4665c03f1ec1baf60bd7a04ebab5c5d5282f0d81774d8bb2605d12e2e4d116f4b8b7a505c5b02e09b16e4b8b692463daeb1ad358c4b8c4a515e5282e68ed6c4665b83f1e81b89a0bcb607a3b03559e282d00fd6606e5a03f1d41b9660fc7306eb514c5a4a32ca51164278b19342c8278e411d62028af25158124ab09055e8d8ad3485752a2b09215c488ad3525652f2b09495f6bcada5355d1caaa4d437034aa946030122a80514d8c0a49540280a29b1755149290a41540a329b5b009028a545d535aea8e9454c4729da3152a30292551444a80401401c0a288d413e4600301451eb027ad41464b890a585152a27694143488a11240140a240d413824802014481ac0060513e6889eb524e5a52789793b4a49023d4e5a8270491528bea7c5e53a29a97149486bea0a5350125a3c9253f4869d2414dd1d86c0680b02c010144d4ae26855133278991344c40a25ed61274c09725848528258d212b490933524a49324f1752669490a4a49523248499224bc90a524811ea3e4992d8be954534a1a52469491e4946f85f2ac278d411d1c28c5484f19c23a360510b6a088b60465ac1f8d41184b083350441b022cd21154908a1442a0278cc11d0b6b08334843d2a21ed41118ba884513e9a51f89290e48c6f05d3e5ac216930f869083a404242e20a4910304882a4440d2220ed510649882124408121b8930f76948624f42925a1091d014865384f19423a000bcff04e7ea5e3f1291f2934f848a7d3523dda81ec8f5178be89c53449ac21ad48fe6a07db4a3d5251b417ca309e318472881f8c20dca107e2f8372801e8b80d4ee4807783f3b41b9e6570f22a87894c3c0a31d85109e09e2d8473ac0a1ce960e66b073b5e399a91c24f4db26a7012d394929c0964e34a270b583812c1b8d60dc6a06f360375ac1b6960e94be74253391249c4514df25e6d127361289a2964cc4a26b24930d20980574bb2aa5894d354a29a6d50c647068c6c34122196940ce6d86525032dae1991b0ca6c862b483252a186920c84886335e315a9188978c34a45693d2909a9584b4c224a6036c2c5ae17c510b94a05cb5c2f1b6176d70ba4d85c2602d8aa16a510b4278599342c62f161148ac49257a412b5a4158920aa28852b48295a8150da0a76c053348291241445b0a12c85015427ca21a8d78d24be67a5b3352b98e94cc14725f95f2f4ad96e55cb22a6571352ac979524aca324e4f12326d18130974924aa4e23921518900564792a23793d2689a931180978b045b502552e1108c0938c049450241281149008f4984424023d2a120d908e4b842a50235221109008724843a44221aa10c490844a045b5a229ab112978854a434939188988d64b48324a37c50202b00fe5707d8c03e26c1ed300ee550742683bb501d2280f3580782b83b1441d49e0e64d0714903725c1c1af0ded486d47235a311ad280d2d40682b833368195b00c8d40602a82e944181200ba8c0626a03096c17cb20bc5705c2884cc522592f92896c914ae462532092090257c7e2b63d1571c8a98d85346a25e3392b18c938b648c576d82b36c15d2c8ac944532ba27155130a68aa514534d82625c13dae09e940516c02826c1392e098d784b6a42cb5b161a98a8978522be2695712892890d483502820a5111524876904434722004c1062e87ad283b4941fa460f5a90789783b4a41ca5e111a7884d0c3e4861d23b0e11986e4fc3626e1a8160c13005a90033470152300c89a060d442f27c151320aca205ad482c2bc151520c5a985c9482946412a5109d24830904200481214001c2200c0d02069a0e23a07c9d00e4d816082090210962e836d281849411a46054a88224c42225207121014230420981e0480e02406412036d481a4bc0c2520589a02ad441407c070320489a01e110116a40805e038290105300728803134029a7812d0c052860213b00c9984cd3c1d4860ba3b04ca181a48c0c074058370081b488d3e406971eb478dda1c5e93e2a497142477a921bcc8fdbb476d6a3767519b2853d91296b5947584a1aac4fd532769b1374c099a3a4bd1a2567a1273a8919b213cd708e4e83f1681b8920bc4704e2301f0d00d05005c0102c0001f 17 6 11 10 7
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

def g_51 : Nat := 0x1151537017f377f
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_49, s_49, 9, g_49), (m_48, s_48, 9, g_48), (m_47, s_47, 9, g_47), (m_44, s_44, 9, g_44), (m_43, s_43, 9, g_43), (m_50, s_50, 9, g_50), (m_46, s_46, 7, g_46), (m_45, s_45, 7, g_45), (m_42, s_42, 7, g_42), (m_41, s_41, 7, g_41), (m_40, s_40, 7, g_40), (m_39, s_39, 7, g_39), (m_17, s_17, 5, g_17), (m_18, s_18, 5, g_18), (m_19, s_19, 5, g_19), (m_29, s_29, 5, g_29), (m_30, s_30, 5, g_30), (m_16, s_16, 5, g_16), (m_8, s_8, 4, g_8), (m_4, s_4, 4, g_4), (m_1, s_1, 4, g_1)]
theorem kn_51 : KnownBin bds_51 := by
  intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_49
  · exact lb_48
  · exact lb_47
  · exact lb_44
  · exact lb_43
  · exact lb_50
  · exact lb_46
  · exact lb_45
  · exact lb_42
  · exact lb_41
  · exact lb_40
  · exact lb_39
  · exact lb_17
  · exact lb_18
  · exact lb_19
  · exact lb_29
  · exact lb_30
  · exact lb_16
  · exact lb_8
  · exact lb_4
  · exact lb_1
theorem sub_51 : ∀ b ∈ bds_51, fullMask &&& b.1 = b.1 := by intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_51 : ∀ b ∈ bds_51, canon b.1 g_51 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_51 : Nat → Nat × Nat := unpackForestF 0x3852df0a59e34b3c295f852a80c5fd1adfa35bb46b6e8c66d18bda2d2b45a36bc58d78a9a292f4524e9b48d3689a291f452280c5bc48bd891671137e226dc44c78898720b6e4161c42dd8a9b71530e2162018af831f30538d5567bf4bf7d1b2aab35e253bb8d955596aa375546daa8bd55176a925d5249aa48f649c2c6b3d5245ae4935c916a82555939ab26b541180629cec6b9d8cf3b16e762ccec579d8ab43166862ace85a9e6933cd16742b00a5f90adf2158e41b7c836e906db2099a412fc825e934bd2095e412b4823e014b6ff1bdfe36bfc637f8c3155f1fe2fc447c7f8a70adb615b0bfb6e828db05185fdb13fa5e7f4b20295df52a30d6b7b4f8c359de2b8bc27c616ceecd4dd53630b66738bee49b185b2b0a6e614dac297d852f30a576b8e0d499d852b30a3e6147aca979952b3092a622bcc4559849300a5354adea959d5237aa46e548d4b51b95233aa466548c4ad9fd5135aa2630149e7d5acfab19f36f3e6ce7cd7cf9af1f35d3e4de7c9b8f9351f2673e4cc7c988f92b1f23e424dc84998f8951f96e3f2cc7c498052593d6e27ad64f5a89eb313d6327ac46d1b09e359a46c278c6649b09d359826c274c64e9389d2495d6a2bac44e178a2b514562270a40291c95320156f234f80559c85320136f1f4f804d9c73390e26c026ae3516c652e01356178a62c97009aa8126f024dc049a8093387d700fac01c91c093301262024bc049742137042660249a0a9b81533012450247c048f405218003f 8 11
def l_51 : Nat → Nat → Option Nat := unpackLinksF 0x3402d003400cf0b3c0c5cf141c487101c403100c30b082c203080c10b040c103040c00b000b5d6d60b582d22b482ce2b306cc0b302c82b202c80b10a9b5a682962a40e900a3868c1a3028a1a206880a202880a202842a102802a0027c29e867a09e827629d827609c8a4959186441900a4008f0a3c08f023c08e0a3808e0234282d606281060218005fe17f81fa27e81fa07d89f607d81d137309cc07209c617181c417101c217081c206f89be06f81ba26e81ba0645590063858e06305882620182360818015f857e05f057a15e817a05d897605c897205b896c15b016c05b016c05a096805a016424ed53624d053024c013004c012c24b012c04b0128249850133f84fc13e84f813d84f413c84ee23b80ee03a88ea03a80ea03a80ea03a80e623980e603888b952e00b422d00b402c08ae12b80ac12b00aa12a80a812a00a612980a602980a602888a2028809e21d547401c847201c047001b846e01b046821a00623188060117845e017045a115885601580522148052013884c113004c013004c013004821200480110844011001b500b0001 0x38db2f1a65e3addc69676eb75c56ddf8d7bd1ab7634e7c66b88c39f15b722acda6b894ce78977952df2259e24afc29551928afa4f2448785192fa2a5dc64d8493a89175d1ce9a35d88b1af15351a469b44dfadfbd5bb76b6e7565b6ac5b919b3a32edc5eb68bbb4d2b65a35426f7c4c6a496cd52bada4dd6497aa9274923e8a4512483925f318b86417cc52e18358f24b6e4161c64db8a9873ab75bd6dcf8dd731b73e2f67459c08a77b14aea28e6a6fcc4da929a4e532e5a63ca4c34e97de929af24f224878e5bb10b159354104a9851f30538d8a45bf4bf7d1b2f129ddc6caf0b158152b82455844108e1649c2c6b3d7a49ae48b584e6ac9adc56db6ad58159ef6b35d565b98dd711b6de2f5b45d9a4d70e99d452d99a575749b6a92ed124d9a47b048a18906b425550467b8c8fb5f288344f864a10b13c1528a2cd0c559f6933cd1642b737d6da88d74f19cf22ed345ba58b34915e8e2aabc51994d7309aa5d34c02666f4c30095a592aa824b204874016a742b2b35f884c914951e1323aa54724c92699a4d2b49a6e934bd375be6ab1ccb6f986dd2edb5fdb2b3b62556be62d5e59333fa65954bf28979252d49257914ac2494a411f33a3d866f906dc215be41370794c7155f2223e4336d856c3071b60a30bfd6e68adb1d1be3636adc69398cb1918e2e30c4c5f878a708dba05b14026e704db00979fd2cbba53744a4e29453d258f2437d4a8f69f1ad320825479ae2f09f1a92b3b353754d8e717dc9363312863248ca4a18892085706b8e0d499d992f32a56632bcc4559f2b5bd5676f6daceda9ddb3ba366716caa8d7cbdabb826e6f4dadc97db52f2325a6c4aed295831293423e6747ac84a9849311c64564f64b1f16a3b2d4665a8fcb51b95b3f98254324a8bf5bd7ab3aec6f5c8dcb71a96633ac466578c4891782a2eaaa6b544c69c96d352d262592e4ac14944b92322a45344a86c9507d3210a7c1c4a832910592a2192840248844a0fc9221a6e424cc805b8fcb32956b51ac6a0dbd3db3a735f4d6bc98d74b5aa813524b4de949b9253524267474cc8c989152b16a554447c048f504951f1262c0d852180ac36140601d4a66d1b0d2361926c304d8595a8aeb114d6a28ac4795b8eeb59d56a39acc7158cdeb11ac6b338c65b1780e2e98a6b2f4c65c9782d2e9724e2d4923690c61210aa412a0bc4e148953211a7c214c83e9f03d3a082541dce41c9d871360d45b194b82f14c592e04a4c06488109301522085700fac01c91c253704266064dc0a99892b791567206de3cd9c29ae8135a1b6ae30d5855aa8a26f134dc249a8453386a660c4c416978292e83a4d0448a068f8091ef045fd08b78715ea629ce25f8f4b6fc95d8129a9a4f3d4964c91c05218003f 14 5 11 8 6
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsF fullMask g_51 bds_51 (dagRefF 230 (dagTraceF fullMask rootStock 11 f_51) l_51 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_0 : treeBlockF 0 32 (dagCheckNodeF fullMask g_51 bds_51 230 (dagTraceF fullMask rootStock 11 f_51) l_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_1 : treeBlockF 32 64 (dagCheckNodeF fullMask g_51 bds_51 230 (dagTraceF fullMask rootStock 11 f_51) l_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_2 : treeBlockF 64 96 (dagCheckNodeF fullMask g_51 bds_51 230 (dagTraceF fullMask rootStock 11 f_51) l_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_3 : treeBlockF 96 128 (dagCheckNodeF fullMask g_51 bds_51 230 (dagTraceF fullMask rootStock 11 f_51) l_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_4 : treeBlockF 128 160 (dagCheckNodeF fullMask g_51 bds_51 230 (dagTraceF fullMask rootStock 11 f_51) l_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_5 : treeBlockF 160 192 (dagCheckNodeF fullMask g_51 bds_51 230 (dagTraceF fullMask rootStock 11 f_51) l_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_6 : treeBlockF 192 224 (dagCheckNodeF fullMask g_51 bds_51 230 (dagTraceF fullMask rootStock 11 f_51) l_51) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51_7 : treeBlockF 224 230 (dagCheckNodeF fullMask g_51 bds_51 230 (dagTraceF fullMask rootStock 11 f_51) l_51) = true := by decide +kernel
theorem nj_51_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF fullMask g_51 bds_51 230 (dagTraceF fullMask rootStock 11 f_51) l_51) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_51_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_51_1 h1 h2)
theorem nj_51_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF fullMask g_51 bds_51 230 (dagTraceF fullMask rootStock 11 f_51) l_51) i = true := block_join nj_51_1 (fun _ h1 h2 => treeBlockF_at nb_51_2 h1 h2)
theorem nj_51_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF fullMask g_51 bds_51 230 (dagTraceF fullMask rootStock 11 f_51) l_51) i = true := block_join nj_51_2 (fun _ h1 h2 => treeBlockF_at nb_51_3 h1 h2)
theorem nj_51_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF fullMask g_51 bds_51 230 (dagTraceF fullMask rootStock 11 f_51) l_51) i = true := block_join nj_51_3 (fun _ h1 h2 => treeBlockF_at nb_51_4 h1 h2)
theorem nj_51_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF fullMask g_51 bds_51 230 (dagTraceF fullMask rootStock 11 f_51) l_51) i = true := block_join nj_51_4 (fun _ h1 h2 => treeBlockF_at nb_51_5 h1 h2)
theorem nj_51_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF fullMask g_51 bds_51 230 (dagTraceF fullMask rootStock 11 f_51) l_51) i = true := block_join nj_51_5 (fun _ h1 h2 => treeBlockF_at nb_51_6 h1 h2)
theorem nj_51_7 : ∀ i, 0 ≤ i → i < 230 → (dagCheckNodeF fullMask g_51 bds_51 230 (dagTraceF fullMask rootStock 11 f_51) l_51) i = true := block_join nj_51_6 (fun _ h1 h2 => treeBlockF_at nb_51_7 h1 h2)
theorem nc_51 : ∀ i, 0 ≤ i → i < 230 → (dagCheckNodeF fullMask g_51 bds_51 230 (dagTraceF fullMask rootStock 11 f_51) l_51) i = true := nj_51_7
theorem lb_51 : LowerBin fullMask rootStock g_51 12 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_51 sub_51 gl_51 rc_51 nc_51

def wg : List Gate := [⟨GateOp.and, [5, 3]⟩, ⟨GateOp.or, [5, 3]⟩, ⟨GateOp.and, [4, 3]⟩, ⟨GateOp.and, [1, 0]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [6, 4]⟩, ⟨GateOp.and, [11, 0]⟩, ⟨GateOp.and, [10, 2]⟩, ⟨GateOp.or, [10, 2]⟩, ⟨GateOp.and, [14, 1]⟩, ⟨GateOp.or, [15, 12]⟩, ⟨GateOp.and, [7, 16]⟩, ⟨GateOp.or, [13, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 4269852800) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276808392 * 2 ^ 32 + 4269852800)) (13 - 1) := by
  rw [show canon fullMask (4276808392 * 2 ^ 32 + 4269852800) = g_51 by decide]
  exact lb_51

end PEqualNP.Outside.L_meta_45548

theorem PEqualNP.Outside.L_meta_45548 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 4269852800) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 4269852800) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_45548.table2_from_lowerBin (4276808392 * 2 ^ 32 + 4269852800) 13 PEqualNP.Outside.L_meta_45548.root_lb PEqualNP.Outside.L_meta_45548.wg 18 rfl PEqualNP.Outside.L_meta_45548.wfits PEqualNP.Outside.L_meta_45548.weval
