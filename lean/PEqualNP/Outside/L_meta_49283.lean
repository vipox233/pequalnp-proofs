import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_49283

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

def m_5 : Nat := 0x4444444400000000
def s_5 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_5 : Nat := 0x4044400000000
def ep_5 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
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

def m_6 : Nat := 0xcc00cc00000000
def s_6 : List Nat := [0x44004400000000, 0xc000c00000000, 0xcc00000000]
def g_6 : Nat := 0x4004c00000000
def ep_6 : Nat := 0x48000000000000000000000000000400080000000000000000000000000004004000000000
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

def m_7 : Nat := 0xf0f0
def s_7 : List Nat := [0x5050, 0x3030, 0xf0]
def g_7 : Nat := 0x1070
def ep_7 : Nat := 0x60000000000000000000000000000010200000000000001040
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

def m_8 : Nat := 0xa0a0a0a00000000
def s_8 : List Nat := [0x202020200000000, 0xa000a00000000, 0xa0a00000000]
def g_8 : Nat := 0x2020a00000000
def ep_8 : Nat := 0x208000000000002000800000000000000000000000000020200000000000000000000000000
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

def m_10 : Nat := 0xc000c000c000c00
def s_10 : List Nat := [0x400040004000400, 0xc0000000c00, 0xc000c00]
def g_10 : Nat := 0x40004000c00
def ep_10 : Nat := 0x400080000000400000008000000000000000000000000000000000000000000000000000000040004000000
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

def m_11 : Nat := 0xa000a000a000a00
def s_11 : List Nat := [0x200020002000200, 0xa0000000a00, 0xa000a00]
def g_11 : Nat := 0x20002000a00
def ep_11 : Nat := 0x200080000000200000008000000000000000000000000000000000000000200020000000000000000000000
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

def m_12 : Nat := 0x808080808080808
def s_12 : List Nat := [0x8000800080008, 0x80800000808, 0x8080808]
def g_12 : Nat := 0x800080808
def ep_12 : Nat := 0x8080000000008000008000000000800080000000000000000000000000000000000000000000000000000
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

def m_15 : Nat := 0xff0000000000
def s_15 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_15 : Nat := 0x170000000000
def ep_15 : Nat := 0x6000000000000001200000000000000140000000000
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

def m_16 : Nat := 0x4444000044440000
def s_16 : List Nat := [0x404000004040000, 0x44000000440000, 0x44440000]
def g_16 : Nat := 0x4000004440000
def ep_16 : Nat := 0x440000000000000000000000004000000400000000400000400000000000000000000000000000000000000
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

def m_17 : Nat := 0xa0a00000a0a0000
def s_17 : List Nat := [0x202000002020000, 0xa0000000a0000, 0xa0a0000]
def g_17 : Nat := 0x20000020a0000
def ep_17 : Nat := 0x208000000000000000000000002000000080000000000000000000000020000020000000000000000000000
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

def m_18 : Nat := 0xc0c00000c0c0000
def s_18 : List Nat := [0x404000004040000, 0xc0000000c0000, 0xc0c0000]
def g_18 : Nat := 0x40000040c0000
def ep_18 : Nat := 0x408000000000000000000000004000000080000000000000000000000000000000000000004000004000000
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

def m_20 : Nat := 0xff000000ff0
def s_20 : List Nat := [0x55000000550, 0x33000000330, 0xf0000000f0, 0xff0]
def g_20 : Nat := 0x75000000f70
def ep_20 : Nat := 0x82000000000000000000000000000000000000000000000000000000200000000200000045000000040
theorem epk_20 : ep_20 = edgePack m_20 g_20 := by decide +kernel
def bds_20 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_20 : KnownBin bds_20 := by intro b hb; simp [bds_20] at hb
theorem sub_20 : ∀ b ∈ bds_20, m_20 &&& b.1 = b.1 := by intro b hb; simp [bds_20] at hb
theorem gl_20 : ∀ b ∈ bds_20, canon b.1 g_20 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_20] at hb
def cur_20 : Nat → List (Nat × Nat) := unpackCursorV4 0x1a2d58952244890e8701 0x39283048e8d081a1924205128ea11b313a526c80e841b000f 7 127 3 7 10 1023 15 32767
def f_20 : Nat → Nat × Nat := unpackForestF 0xc74636f1a14e8a6c43a49220a086c00f 3 10
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV4 m_20 g_20 ep_20 10 bds_20 (dagTraceF m_20 s_20 4 f_20) (cur_20 0) s_20 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_20 : treeBlockF 0 10 (dagCheckNodeV4 m_20 g_20 ep_20 bds_20 10 (dagTraceF m_20 s_20 4 f_20) cur_20) = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 10 → (dagCheckNodeV4 m_20 g_20 ep_20 bds_20 10 (dagTraceF m_20 s_20 4 f_20) cur_20) i = true := fun _ h1 h2 => treeBlockF_at nb_20 h1 h2
theorem lb_20 : LowerBin m_20 s_20 g_20 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_20 kn_20 sub_20 gl_20 rc_20 nc_20

def m_21 : Nat := 0xff00ff0
def s_21 : List Nat := [0x5500550, 0x3300330, 0xf000f0, 0xff0]
def g_21 : Nat := 0x7500f70
def ep_21 : Nat := 0x8200000000000000000000000000000000000000000020000200000000004500040
theorem epk_21 : ep_21 = edgePack m_21 g_21 := by decide +kernel
def bds_21 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_21 : KnownBin bds_21 := by intro b hb; simp [bds_21] at hb
theorem sub_21 : ∀ b ∈ bds_21, m_21 &&& b.1 = b.1 := by intro b hb; simp [bds_21] at hb
theorem gl_21 : ∀ b ∈ bds_21, canon b.1 g_21 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_21] at hb
def cur_21 : Nat → List (Nat × Nat) := unpackCursorV4 0x1a2d58952244890e8701 0x39283048e8d081a1924205128ea11b313a526c80e841b000f 7 127 3 7 10 1023 15 32767
def f_21 : Nat → Nat × Nat := unpackForestF 0xc74636f1a14e8a6c43a49220a086c00f 3 10
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV4 m_21 g_21 ep_21 10 bds_21 (dagTraceF m_21 s_21 4 f_21) (cur_21 0) s_21 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21 : treeBlockF 0 10 (dagCheckNodeV4 m_21 g_21 ep_21 bds_21 10 (dagTraceF m_21 s_21 4 f_21) cur_21) = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 10 → (dagCheckNodeV4 m_21 g_21 ep_21 bds_21 10 (dagTraceF m_21 s_21 4 f_21) cur_21) i = true := fun _ h1 h2 => treeBlockF_at nb_21 h1 h2
theorem lb_21 : LowerBin m_21 s_21 g_21 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_21 kn_21 sub_21 gl_21 rc_21 nc_21

def m_22 : Nat := 0xffff00000000
def s_22 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_22 : Nat := 0x175f00000000
def ep_22 : Nat := 0x48000000000000060a0000000000001200000000000000145000000000
theorem epk_22 : ep_22 = edgePack m_22 g_22 := by decide +kernel
def bds_22 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_22 : KnownBin bds_22 := by
  intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_22 : ∀ b ∈ bds_22, m_22 &&& b.1 = b.1 := by intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_22 : ∀ b ∈ bds_22, canon b.1 g_22 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_22, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_22 : Nat → List (Nat × Nat) := fun _ => []
def f_22 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV4 m_22 g_22 ep_22 0 bds_22 (dagTraceF m_22 s_22 4 f_22) (cur_22 0) s_22 4 = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_22 g_22 ep_22 bds_22 0 (dagTraceF m_22 s_22 4 f_22) cur_22 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_22 : LowerBin m_22 s_22 g_22 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_22 kn_22 sub_22 gl_22 rc_22 nc_22

def m_23 : Nat := 0xaa00aa00aa00aa
def s_23 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_23 : Nat := 0x2000a000a002a
def ep_23 : Nat := 0x80020000000080000002000000000000000000002000a000a000800020000000000200000000000000000
theorem epk_23 : ep_23 = edgePack m_23 g_23 := by decide +kernel
def bds_23 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_23 : KnownBin bds_23 := by intro b hb; simp [bds_23] at hb
theorem sub_23 : ∀ b ∈ bds_23, m_23 &&& b.1 = b.1 := by intro b hb; simp [bds_23] at hb
theorem gl_23 : ∀ b ∈ bds_23, canon b.1 g_23 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_23] at hb
def cc_23_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xb41682b1560ac148a80d009c3382704e09c1382704648c1182304607c8f81f03a2740e81b1341680c841c001 0xf138749a360b1a048b8305ca226d212680893c40981c130d088602c2c12125308288304c1422040402249fa3ff91df28df4467893fb89dda4deb267512fa495c849df246e03f641db00dd6066a82f50159e09ca046381f100d8605c1026000f 11 2047 5 31 10 1023 17 131071
def cc_23_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb0b0b0b0b0949090909074707062606052494841404040404040242020202004 0x3d299e140ec26741038251b924d8146a09330719034c00c5e052c2616244a1a44ed02607928308ca64451210310014 8 255 3 7 10 1023 17 131071
def cur_23 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_23_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_23_0 p) (Nat.blt p 32)
def f_23 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c838c834053fbc18bc14053b0537b2440533052f052b97489740943c94300527814c814480188014052375387534043f682c6824043b04375d440433042f042b43484340413c413004272c4c2c442c2c2c240423214c2144041f144c1444041b041709240413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV4 m_23 g_23 ep_23 64 bds_23 (dagTraceF m_23 s_23 5 f_23) (cur_23 0) s_23 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_23_0 : treeBlockF 0 32 (dagCheckNodeV4 m_23 g_23 ep_23 bds_23 64 (dagTraceF m_23 s_23 5 f_23) cur_23) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_23_1 : treeBlockF 32 64 (dagCheckNodeV4 m_23 g_23 ep_23 bds_23 64 (dagTraceF m_23 s_23 5 f_23) cur_23) = true := by decide +kernel
theorem nj_23_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_23 g_23 ep_23 bds_23 64 (dagTraceF m_23 s_23 5 f_23) cur_23) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_23_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_23_1 h1 h2)
theorem nc_23 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_23 g_23 ep_23 bds_23 64 (dagTraceF m_23 s_23 5 f_23) cur_23) i = true := nj_23_1
theorem lb_23 : LowerBin m_23 s_23 g_23 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_23 kn_23 sub_23 gl_23 rc_23 nc_23

def m_24 : Nat := 0xff00ff0000000000
def s_24 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_24 : Nat := 0x1100170000000000
def ep_24 : Nat := 0x600000000000000000000000000000006000000000011001200000000001100140000000000
theorem epk_24 : ep_24 = edgePack m_24 g_24 := by decide +kernel
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_24 : KnownBin bds_24 := by
  intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_24 : ∀ b ∈ bds_24, m_24 &&& b.1 = b.1 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_24 : ∀ b ∈ bds_24, canon b.1 g_24 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_24 : Nat → List (Nat × Nat) := fun _ => []
def f_24 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV4 m_24 g_24 ep_24 0 bds_24 (dagTraceF m_24 s_24 4 f_24) (cur_24 0) s_24 4 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_24 g_24 ep_24 bds_24 0 (dagTraceF m_24 s_24 4 f_24) cur_24 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_24 kn_24 sub_24 gl_24 rc_24 nc_24

def m_25 : Nat := 0xff00ff00000000
def s_25 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_25 : Nat := 0x17005f00000000
def ep_25 : Nat := 0x480000000000000000000000000006000a0000000000120000000000000014005000000000
theorem epk_25 : ep_25 = edgePack m_25 g_25 := by decide +kernel
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
theorem kn_25 : KnownBin bds_25 := by
  intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_6
theorem sub_25 : ∀ b ∈ bds_25, m_25 &&& b.1 = b.1 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_25 : ∀ b ∈ bds_25, canon b.1 g_25 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_25 : Nat → List (Nat × Nat) := fun _ => []
def f_25 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV4 m_25 g_25 ep_25 0 bds_25 (dagTraceF m_25 s_25 4 f_25) (cur_25 0) s_25 4 = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_25 g_25 ep_25 bds_25 0 (dagTraceF m_25 s_25 4 f_25) cur_25 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_25 : LowerBin m_25 s_25 g_25 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_25 kn_25 sub_25 gl_25 rc_25 nc_25

def m_26 : Nat := 0xf0f0f0f00000000
def s_26 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_26 : Nat := 0x107070f00000000
def ep_26 : Nat := 0x608000000000006000800000000000000000000000001020200000000000104040000000000
theorem epk_26 : ep_26 = edgePack m_26 g_26 := by decide +kernel
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3), (m_14, s_14, 4, g_14), (m_4, s_4, 4, g_4), (m_8, s_8, 4, g_8)]
theorem kn_26 : KnownBin bds_26 := by
  intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_3
  · exact lb_14
  · exact lb_4
  · exact lb_8
theorem sub_26 : ∀ b ∈ bds_26, m_26 &&& b.1 = b.1 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_26 : ∀ b ∈ bds_26, canon b.1 g_26 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_26_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8724381de0ee07323981c44b575a02d01642aa4550298940698435b9a80d406623301980c445a429214049844a123109c0064001 0x59003c6015407c9a07d3a36950b460fa10592a048cf1460a9f054b9d07a0c39201a830c4285a8825180a83d002c600c4040120310050280f4e07a6b69342c92a2450b20878f5a46ac94d2ca2874f5826a1c4e0626870f818720c320618830c018547826060d0805952980e400f180310100680c300c0a038c01a6015200b20078c02a8081340fa72cd29468c1f420b25269181c7c0e3d489e904d42a5a892506251e118287c0c3d0a17030a418440c21061003068202c624c0b2012d203e800d400e980310050680d300a90030c030480c300e980a0d0184015200c1207938d4945a460f21058f8a47442360b190e518626c0d2e06250811818741036060c878fc2c7742370b19874fe426e152f7093870fc1876b8370619850bc1856702706118306c102e000f 13 8191 5 31 10 1023 17 131071
def cc_26_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb817017bae0544a80580a014018811001 0x2e9c174d0f27059343c7c16390b19058c42c61514d84a2874f6626a152d8092d21341892a0450620870f5a06a142d4c12858c1f2493a4d0b24c29142c821e3d991a875383a7cf126942683124b08a0c410e1eb00d4702b104c0620078c1f2681520 11 2047 5 31 10 1023 17 131071
def cur_26 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_26_1 (Nat.sub p 32)) (cc_26_0 p) (Nat.blt p 32)
def f_26 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
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

def m_27 : Nat := 0xcccccccc00000000
def s_27 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_27 : Nat := 0x4044c00000000
def ep_27 : Nat := 0x448000000000004004800000000000404080000000000000000000000000004044000000000
theorem epk_27 : ep_27 = edgePack m_27 g_27 := by decide +kernel
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6), (m_0, s_0, 4, g_0), (m_5, s_5, 4, g_5), (m_4, s_4, 4, g_4)]
theorem kn_27 : KnownBin bds_27 := by
  intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_6
  · exact lb_0
  · exact lb_5
  · exact lb_4
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

def m_28 : Nat := 0xaaaaaaaa00000000
def s_28 : List Nat := [0x2222222200000000, 0xa0a0a0a00000000, 0xaa00aa00000000, 0xaaaa00000000]
def g_28 : Nat := 0x2020a00000000
def ep_28 : Nat := 0x2080000000000020008000000000002020a0000000000020200000000000000000000000000
theorem epk_28 : ep_28 = edgePack m_28 g_28 := by decide +kernel
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
theorem kn_28 : KnownBin bds_28 := by
  intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_8
theorem sub_28 : ∀ b ∈ bds_28, m_28 &&& b.1 = b.1 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_28 : ∀ b ∈ bds_28, canon b.1 g_28 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_28 : Nat → List (Nat × Nat) := fun _ => []
def f_28 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV4 m_28 g_28 ep_28 0 bds_28 (dagTraceF m_28 s_28 4 f_28) (cur_28 0) s_28 4 = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_28 g_28 ep_28 bds_28 0 (dagTraceF m_28 s_28 4 f_28) cur_28 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_28 : LowerBin m_28 s_28 g_28 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_28 kn_28 sub_28 gl_28 rc_28 nc_28

def m_29 : Nat := 0x66006600660066
def s_29 : List Nat := [0x22002200220022, 0x6000600060006, 0x6600000066, 0x660066]
def g_29 : Nat := 0x6004600460066
def ep_29 : Nat := 0x40002000000040000000200000000000000000000600020002000000000000000000000000000000000000
theorem epk_29 : ep_29 = edgePack m_29 g_29 := by decide +kernel
def bds_29 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_29 : KnownBin bds_29 := by intro b hb; simp [bds_29] at hb
theorem sub_29 : ∀ b ∈ bds_29, m_29 &&& b.1 = b.1 := by intro b hb; simp [bds_29] at hb
theorem gl_29 : ∀ b ∈ bds_29, canon b.1 g_29 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_29] at hb
def cur_29 : Nat → List (Nat × Nat) := unpackCursorV4 0x16ac58b12a44890e8701 0x31243048c4f080a193c202928f611ab92a524c80a8413000f 7 127 3 7 10 1023 15 32767
def f_29 : Nat → Nat × Nat := unpackForestF 0xc7a63529564f0a4c42a49e205084c00f 3 10
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV4 m_29 g_29 ep_29 10 bds_29 (dagTraceF m_29 s_29 4 f_29) (cur_29 0) s_29 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29 : treeBlockF 0 10 (dagCheckNodeV4 m_29 g_29 ep_29 bds_29 10 (dagTraceF m_29 s_29 4 f_29) cur_29) = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 10 → (dagCheckNodeV4 m_29 g_29 ep_29 bds_29 10 (dagTraceF m_29 s_29 4 f_29) cur_29) i = true := fun _ h1 h2 => treeBlockF_at nb_29 h1 h2
theorem lb_29 : LowerBin m_29 s_29 g_29 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_29 kn_29 sub_29 gl_29 rc_29 nc_29

def m_30 : Nat := 0xcccc0000cccc0000
def s_30 : List Nat := [0x4444000044440000, 0xc0c00000c0c0000, 0xcc000000cc0000, 0xcccc0000]
def g_30 : Nat := 0x40000044c0000
def ep_30 : Nat := 0x448000000000000000000000004000000480000000400000408000000000000000000000004000004400000
theorem epk_30 : ep_30 = edgePack m_30 g_30 := by decide +kernel
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_19, s_19, 4, g_19), (m_9, s_9, 4, g_9), (m_16, s_16, 4, g_16), (m_18, s_18, 4, g_18)]
theorem kn_30 : KnownBin bds_30 := by
  intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_19
  · exact lb_9
  · exact lb_16
  · exact lb_18
theorem sub_30 : ∀ b ∈ bds_30, m_30 &&& b.1 = b.1 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_30 : ∀ b ∈ bds_30, canon b.1 g_30 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_30_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8714381de0e647113881c40b575622a094469a44d0268130298035b9890b485812a114849c44e027012889404a023109c0064001 0xf818060a07d3a36850a420f1d405382a94154678a1074b43872a831301083075d0320c150808a85001a681c44061a164c01a4817496da085925a4820d4d0aa5035181a8a0d44069f264c81a5c5122062703135907c1c3a0e1b200c9805c2822060f0507542800d340a22030d092600d24069a030d02828a3400e9a051102828882c0fa72cd083c72aa3106a7265081a7a1d3a069b034d41a680d2e209124138289414464021030f8187a782e081103078383a5940069205110184849300692070d018480c242d200511018484a300e1a0c0f03868184c0a221a908c4640d4e28a1034f882640d2d1c2705128288c2842101f070e8386c10320616878fc2c761637a119854ee42661d2b7091830fc28760c375c19830bc38560c2738118307c1026000f 13 8191 5 31 10 1023 17 131071
def cc_30_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xc018019bae25c0b80780a210201000000 0xfa685d282e8c17450ba2059383c9a163e0b1e8552672821d398c98d44a5e24214496c20870e560620c2da41483095004312400ea205d267682164a85194c4f83a741d367899054b42892d04134108307650320c151408c49002a88152489a0078d02a881524 11 2047 5 31 10 1023 17 131071
def cur_30 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_30_1 (Nat.sub p 32)) (cc_30_0 p) (Nat.blt p 32)
def f_30 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
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

def m_31 : Nat := 0x5555000055550000
def s_31 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_31 : Nat := 0x1115000015550000
def ep_31 : Nat := 0x440000000000000000000000004000000400000000400000400000011100000100000000000000000000000
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

def m_32 : Nat := 0xff000000ff00
def s_32 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_32 : Nat := 0x170000001f00
def ep_32 : Nat := 0x800000000000000000000000000000000000000060000000e0000001200000010000000140000001000
theorem epk_32 : ep_32 = edgePack m_32 g_32 := by decide +kernel
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
theorem kn_32 : KnownBin bds_32 := by
  intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_15
theorem sub_32 : ∀ b ∈ bds_32, m_32 &&& b.1 = b.1 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_32 : ∀ b ∈ bds_32, canon b.1 g_32 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_32 : Nat → List (Nat × Nat) := fun _ => []
def f_32 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV4 m_32 g_32 ep_32 0 bds_32 (dagTraceF m_32 s_32 4 f_32) (cur_32 0) s_32 4 = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_32 g_32 ep_32 bds_32 0 (dagTraceF m_32 s_32 4 f_32) cur_32 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_32 : LowerBin m_32 s_32 g_32 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_32 kn_32 sub_32 gl_32 rc_32 nc_32

def m_33 : Nat := 0xf0f00000f0f0
def s_33 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_33 : Nat := 0x105000001070
def ep_33 : Nat := 0x2000000000000000000000004000000060000000000000000000001000000010200000105000001040
theorem epk_33 : ep_33 = edgePack m_33 g_33 := by decide +kernel
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
theorem kn_33 : KnownBin bds_33 := by
  intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_7
theorem sub_33 : ∀ b ∈ bds_33, m_33 &&& b.1 = b.1 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_33 : ∀ b ∈ bds_33, canon b.1 g_33 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_33 : Nat → List (Nat × Nat) := fun _ => []
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV4 m_33 g_33 ep_33 0 bds_33 (dagTraceF m_33 s_33 4 f_33) (cur_33 0) s_33 4 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_33 g_33 ep_33 bds_33 0 (dagTraceF m_33 s_33 4 f_33) cur_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_33 kn_33 sub_33 gl_33 rc_33 nc_33

def m_34 : Nat := 0xf0f00000f0f0000
def s_34 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_34 : Nat := 0x1070000070f0000
def ep_34 : Nat := 0x608000000000000000000000006000000080000000000000000000001020000020000000104000004000000
theorem epk_34 : ep_34 = edgePack m_34 g_34 := by decide +kernel
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1), (m_14, s_14, 4, g_14), (m_18, s_18, 4, g_18), (m_17, s_17, 4, g_17)]
theorem kn_34 : KnownBin bds_34 := by
  intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_1
  · exact lb_14
  · exact lb_18
  · exact lb_17
theorem sub_34 : ∀ b ∈ bds_34, m_34 &&& b.1 = b.1 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_34 : ∀ b ∈ bds_34, canon b.1 g_34 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_34_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8724381de0ee07323981c44b575a02d01642aa4550298940698435b9a80d406623301980c445a429214049844a123109c0064001 0x59003c6015407c9a07d3a36950b460fa10592a048cf1460a9f054b9d07a0c39201a830c4285a8825180a83d002c600c4040120310050280f4e07a6b69342c92a2450b20878f5a46ac94d2ca2874f5826a1c4e0626870f818720c320618830c018547826060d0805952980e400f180310100680c300c0a038c01a6015200b20078c02a8081340fa72cd29468c1f420b25269181c7c0e3d489e904d42a5a892506251e118287c0c3d0a17030a418440c21061003068202c624c0b2012d203e800d400e980310050680d300a90030c030480c300e980a0d0184015200c1207938d4945a460f21058f8a47442360b190e518626c0d2e06250811818741036060c878fc2c7742370b19874fe426e152f7093870fc1876b8370619850bc1856702706118306c102e000f 13 8191 5 31 10 1023 17 131071
def cc_34_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb817017bae0544a80580a014018811001 0x2e9c174d0f27059343c7c16390b19058c42c61514d84a2874f6626a152d8092d21341892a0450620870f5a06a142d4c12858c1f2493a4d0b24c29142c821e3d991a875383a7cf126942683124b08a0c410e1eb00d4702b104c0620078c1f2681520 11 2047 5 31 10 1023 17 131071
def cur_34 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_34_1 (Nat.sub p 32)) (cc_34_0 p) (Nat.blt p 32)
def f_34 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
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

def m_35 : Nat := 0xcccc0000cccc
def s_35 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_35 : Nat := 0x44c00000c4c
def ep_35 : Nat := 0x800000000000000000000000048000000400000040800000c0800000000000000000000044000000040
theorem epk_35 : ep_35 = edgePack m_35 g_35 := by decide +kernel
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
theorem kn_35 : KnownBin bds_35 := by
  intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_0
theorem sub_35 : ∀ b ∈ bds_35, m_35 &&& b.1 = b.1 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_35 : ∀ b ∈ bds_35, canon b.1 g_35 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_35 : Nat → List (Nat × Nat) := fun _ => []
def f_35 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV4 m_35 g_35 ep_35 0 bds_35 (dagTraceF m_35 s_35 4 f_35) (cur_35 0) s_35 4 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_35 g_35 ep_35 bds_35 0 (dagTraceF m_35 s_35 4 f_35) cur_35 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_35 : LowerBin m_35 s_35 g_35 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_35 kn_35 sub_35 gl_35 rc_35 nc_35

def m_36 : Nat := 0xaaaa0000aaaa
def s_36 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_36 : Nat := 0x20a00000a2a
def ep_36 : Nat := 0x820000000000000000000000008000000200000020a00000a0800000200000000200000000000000000
theorem epk_36 : ep_36 = edgePack m_36 g_36 := by decide +kernel
def bds_36 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_36 : KnownBin bds_36 := by intro b hb; simp [bds_36] at hb
theorem sub_36 : ∀ b ∈ bds_36, m_36 &&& b.1 = b.1 := by intro b hb; simp [bds_36] at hb
theorem gl_36 : ∀ b ∈ bds_36, canon b.1 g_36 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_36] at hb
def cc_36_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xb41682b1560ac148a80d009c3382704e09c1382704648c1182304607c8f81f03a2740e81b1341680c841c001 0xf138749a360b1a048b8305ca226d212680893c40981c130d088602c2c12125308288304c1422040402249fa3ff91df28df4467893fb89dda4deb267512fa495c849df246e03f641db00dd6066a82f50159e09ca046381f100d8605c1026000f 11 2047 5 31 10 1023 17 131071
def cc_36_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb0b0b0b0b0949090909074707062606052494841404040404040242020202004 0x3d299e140ec26741038251b924d8146a09330719034c00c5e052c2616244a1a44ed02607928308ca64451210310014 8 255 3 7 10 1023 17 131071
def cur_36 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_36_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_36_0 p) (Nat.blt p 32)
def f_36 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c838c834053fbc18bc14053b0537b2440533052f052b97489740943c94300527814c814480188014052375387534043f682c6824043b04375d440433042f042b43484340413c413004272c4c2c442c2c2c240423214c2144041f144c1444041b041709240413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV4 m_36 g_36 ep_36 64 bds_36 (dagTraceF m_36 s_36 5 f_36) (cur_36 0) s_36 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_0 : treeBlockF 0 32 (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 64 (dagTraceF m_36 s_36 5 f_36) cur_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_1 : treeBlockF 32 64 (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 64 (dagTraceF m_36 s_36 5 f_36) cur_36) = true := by decide +kernel
theorem nj_36_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 64 (dagTraceF m_36 s_36 5 f_36) cur_36) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_36_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_36_1 h1 h2)
theorem nc_36 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_36 g_36 ep_36 bds_36 64 (dagTraceF m_36 s_36 5 f_36) cur_36) i = true := nj_36_1
theorem lb_36 : LowerBin m_36 s_36 g_36 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_36 kn_36 sub_36 gl_36 rc_36 nc_36

def m_37 : Nat := 0xcc00cc00cc00cc00
def s_37 : List Nat := [0x4400440044004400, 0xc000c000c000c00, 0xcc000000cc00, 0xcc00cc00]
def g_37 : Nat := 0x40004000c00
def ep_37 : Nat := 0x4000800000004000000080000000000000000000000040004000c0000000000000000000000040004000000
theorem epk_37 : ep_37 = edgePack m_37 g_37 := by decide +kernel
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
theorem kn_37 : KnownBin bds_37 := by
  intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_10
theorem sub_37 : ∀ b ∈ bds_37, m_37 &&& b.1 = b.1 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_37 : ∀ b ∈ bds_37, canon b.1 g_37 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_37 : Nat → List (Nat × Nat) := fun _ => []
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV4 m_37 g_37 ep_37 0 bds_37 (dagTraceF m_37 s_37 4 f_37) (cur_37 0) s_37 4 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_37 g_37 ep_37 bds_37 0 (dagTraceF m_37 s_37 4 f_37) cur_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_37 kn_37 sub_37 gl_37 rc_37 nc_37

def m_38 : Nat := 0xf000f000f000f00
def s_38 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_38 : Nat := 0x100070007000f00
def ep_38 : Nat := 0x600080000000600000008000000000000000000000000000000000001000200020000000100040004000000
theorem epk_38 : ep_38 = edgePack m_38 g_38 := by decide +kernel
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1), (m_3, s_3, 4, g_3), (m_10, s_10, 4, g_10), (m_11, s_11, 4, g_11)]
theorem kn_38 : KnownBin bds_38 := by
  intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_1
  · exact lb_3
  · exact lb_10
  · exact lb_11
theorem sub_38 : ∀ b ∈ bds_38, m_38 &&& b.1 = b.1 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_38 : ∀ b ∈ bds_38, canon b.1 g_38 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def cc_38_0 : Nat → List (Nat × Nat) := unpackCursorV4 0x8724381de0ee07323981c44b575a02d01642aa4550298940698435b9a80d406623301980c445a429214049844a123109c0064001 0x59003c6015407c9a07d3a36950b460fa10592a048cf1460a9f054b9d07a0c39201a830c4285a8825180a83d002c600c4040120310050280f4e07a6b69342c92a2450b20878f5a46ac94d2ca2874f5826a1c4e0626870f818720c320618830c018547826060d0805952980e400f180310100680c300c0a038c01a6015200b20078c02a8081340fa72cd29468c1f420b25269181c7c0e3d489e904d42a5a892506251e118287c0c3d0a17030a418440c21061003068202c624c0b2012d203e800d400e980310050680d300a90030c030480c300e980a0d0184015200c1207938d4945a460f21058f8a47442360b190e518626c0d2e06250811818741036060c878fc2c7742370b19874fe426e152f7093870fc1876b8370619850bc1856702706118306c102e000f 13 8191 5 31 10 1023 17 131071
def cc_38_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb817017bae0544a80580a014018811001 0x2e9c174d0f27059343c7c16390b19058c42c61514d84a2874f6626a152d8092d21341892a0450620870f5a06a142d4c12858c1f2493a4d0b24c29142c821e3d991a875383a7cf126942683124b08a0c410e1eb00d4702b104c0620078c1f2681520 11 2047 5 31 10 1023 17 131071
def cur_38 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_38_1 (Nat.sub p 32)) (cc_38_0 p) (Nat.blt p 32)
def f_38 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
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

def m_39 : Nat := 0xcccccccc
def s_39 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_39 : Nat := 0x44c0c4c
def ep_39 : Nat := 0x80000000000004800400000000004080c0800000000000000000000000004400040
theorem epk_39 : ep_39 = edgePack m_39 g_39 := by decide +kernel
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_39 : KnownBin bds_39 := by
  intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_39 : ∀ b ∈ bds_39, m_39 &&& b.1 = b.1 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_39 : ∀ b ∈ bds_39, canon b.1 g_39 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_39 : Nat → List (Nat × Nat) := fun _ => []
def f_39 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV4 m_39 g_39 ep_39 0 bds_39 (dagTraceF m_39 s_39 4 f_39) (cur_39 0) s_39 4 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_39 g_39 ep_39 bds_39 0 (dagTraceF m_39 s_39 4 f_39) cur_39 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_39 : LowerBin m_39 s_39 g_39 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_39 kn_39 sub_39 gl_39 rc_39 nc_39

def m_40 : Nat := 0x5555555500000000
def s_40 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_40 : Nat := 0x1115155500000000
def ep_40 : Nat := 0x440000000000004004000000000000404000000000011101000000000000000000000000000
theorem epk_40 : ep_40 = edgePack m_40 g_40 := by decide +kernel
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
theorem kn_40 : KnownBin bds_40 := by
  intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_5
theorem sub_40 : ∀ b ∈ bds_40, m_40 &&& b.1 = b.1 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_40 : ∀ b ∈ bds_40, canon b.1 g_40 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_40 : Nat → List (Nat × Nat) := fun _ => []
def f_40 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV4 m_40 g_40 ep_40 0 bds_40 (dagTraceF m_40 s_40 4 f_40) (cur_40 0) s_40 4 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_40 g_40 ep_40 bds_40 0 (dagTraceF m_40 s_40 4 f_40) cur_40 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_40 : LowerBin m_40 s_40 g_40 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_40 kn_40 sub_40 gl_40 rc_40 nc_40

def m_41 : Nat := 0xffff0000
def s_41 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_41 : Nat := 0x175f0000
def ep_41 : Nat := 0x48000000000000060a000000000000120000000000000014500000
theorem epk_41 : ep_41 = edgePack m_41 g_41 := by decide +kernel
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_41 : KnownBin bds_41 := by
  intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_41 : ∀ b ∈ bds_41, m_41 &&& b.1 = b.1 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_41 : ∀ b ∈ bds_41, canon b.1 g_41 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV4 m_41 g_41 ep_41 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_41 g_41 ep_41 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_41 kn_41 sub_41 gl_41 rc_41 nc_41

def m_42 : Nat := 0xffff
def s_42 : List Nat := [0x5555, 0x3333, 0xf0f, 0xff]
def g_42 : Nat := 0x1f7f
def ep_42 : Nat := 0x600000000000000e0800000000000010200000000000001040
theorem epk_42 : ep_42 = edgePack m_42 g_42 := by decide +kernel
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
theorem kn_42 : KnownBin bds_42 := by
  intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_7
theorem sub_42 : ∀ b ∈ bds_42, m_42 &&& b.1 = b.1 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_42 : ∀ b ∈ bds_42, canon b.1 g_42 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_42 : Nat → List (Nat × Nat) := fun _ => []
def f_42 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV4 m_42 g_42 ep_42 0 bds_42 (dagTraceF m_42 s_42 4 f_42) (cur_42 0) s_42 4 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_42 g_42 ep_42 bds_42 0 (dagTraceF m_42 s_42 4 f_42) cur_42 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_42 kn_42 sub_42 gl_42 rc_42 nc_42

def m_43 : Nat := 0xff00ff00
def s_43 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_43 : Nat := 0x17001f00
def ep_43 : Nat := 0x80000000000000000000000000006000e0000000000120010000000000014001000
theorem epk_43 : ep_43 = edgePack m_43 g_43 := by decide +kernel
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_43 : KnownBin bds_43 := by
  intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_43 : ∀ b ∈ bds_43, m_43 &&& b.1 = b.1 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_43 : ∀ b ∈ bds_43, canon b.1 g_43 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_43 : Nat → List (Nat × Nat) := fun _ => []
def f_43 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV4 m_43 g_43 ep_43 0 bds_43 (dagTraceF m_43 s_43 4 f_43) (cur_43 0) s_43 4 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_43 g_43 ep_43 bds_43 0 (dagTraceF m_43 s_43 4 f_43) cur_43 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_43 : LowerBin m_43 s_43 g_43 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_43 kn_43 sub_43 gl_43 rc_43 nc_43

def m_44 : Nat := 0xf0f0f0f0
def s_44 : List Nat := [0x50505050, 0x30303030, 0xf000f0, 0xf0f0]
def g_44 : Nat := 0x10501070
def ep_44 : Nat := 0x200000000000400060000000000000000000000000100010200000000010501040
theorem epk_44 : ep_44 = edgePack m_44 g_44 := by decide +kernel
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
theorem kn_44 : KnownBin bds_44 := by
  intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_7
theorem sub_44 : ∀ b ∈ bds_44, m_44 &&& b.1 = b.1 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_44 : ∀ b ∈ bds_44, canon b.1 g_44 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_44 : Nat → List (Nat × Nat) := fun _ => []
def f_44 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV4 m_44 g_44 ep_44 0 bds_44 (dagTraceF m_44 s_44 4 f_44) (cur_44 0) s_44 4 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_44 g_44 ep_44 bds_44 0 (dagTraceF m_44 s_44 4 f_44) cur_44 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_44 : LowerBin m_44 s_44 g_44 5 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_44 kn_44 sub_44 gl_44 rc_44 nc_44

def m_45 : Nat := 0xaaaaaaaa
def s_45 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_45 : Nat := 0x20a0a2a
def ep_45 : Nat := 0x820000000000008002000000000020a0a0800000000020000200000000000000000
theorem epk_45 : ep_45 = edgePack m_45 g_45 := by decide +kernel
def bds_45 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_45 : KnownBin bds_45 := by intro b hb; simp [bds_45] at hb
theorem sub_45 : ∀ b ∈ bds_45, m_45 &&& b.1 = b.1 := by intro b hb; simp [bds_45] at hb
theorem gl_45 : ∀ b ∈ bds_45, canon b.1 g_45 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_45] at hb
def cc_45_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xb41682b1560ac148a80d009c3382704e09c1382704648c1182304607c8f81f03a2740e81b1341680c841c001 0xf138749a360b1a048b8305ca226d212680893c40981c130d088602c2c12125308288304c1422040402249fa3ff91df28df4467893fb89dda4deb267512fa495c849df246e03f641db00dd6066a82f50159e09ca046381f100d8605c1026000f 11 2047 5 31 10 1023 17 131071
def cc_45_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb0b0b0b0b0949090909074707062606052494841404040404040242020202004 0x3d299e140ec26741038251b924d8146a09330719034c00c5e052c2616244a1a44ed02607928308ca64451210310014 8 255 3 7 10 1023 17 131071
def cur_45 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_45_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_45_0 p) (Nat.blt p 32)
def f_45 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c838c834053fbc18bc14053b0537b2440533052f052b97489740943c94300527814c814480188014052375387534043f682c6824043b04375d440433042f042b43484340413c413004272c4c2c442c2c2c240423214c2144041f144c1444041b041709240413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV4 m_45 g_45 ep_45 64 bds_45 (dagTraceF m_45 s_45 5 f_45) (cur_45 0) s_45 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_0 : treeBlockF 0 32 (dagCheckNodeV4 m_45 g_45 ep_45 bds_45 64 (dagTraceF m_45 s_45 5 f_45) cur_45) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_1 : treeBlockF 32 64 (dagCheckNodeV4 m_45 g_45 ep_45 bds_45 64 (dagTraceF m_45 s_45 5 f_45) cur_45) = true := by decide +kernel
theorem nj_45_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_45 g_45 ep_45 bds_45 64 (dagTraceF m_45 s_45 5 f_45) cur_45) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_45_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_45_1 h1 h2)
theorem nc_45 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_45 g_45 ep_45 bds_45 64 (dagTraceF m_45 s_45 5 f_45) cur_45) i = true := nj_45_1
theorem lb_45 : LowerBin m_45 s_45 g_45 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_45 kn_45 sub_45 gl_45 rc_45 nc_45

def m_46 : Nat := 0xf000f000f000f0
def s_46 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_46 : Nat := 0x10005000500070
def ep_46 : Nat := 0x40002000000040000000200000000000000000000000000000000000100000000000200010005000500040
theorem epk_46 : ep_46 = edgePack m_46 g_46 := by decide +kernel
def bds_46 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_46 : KnownBin bds_46 := by intro b hb; simp [bds_46] at hb
theorem sub_46 : ∀ b ∈ bds_46, m_46 &&& b.1 = b.1 := by intro b hb; simp [bds_46] at hb
theorem gl_46 : ∀ b ∈ bds_46, canon b.1 g_46 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_46] at hb
def cc_46_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0xe24c6d20345319280b83c581a2a0b14048912844921e0b0e04858202c9a124f08268303c141a040402249fa3ff91df28df4467993fc89dda4de8267292f8895c249df246f03f741db00dd3066802f34159809ca046381f100d8605c1026000f 11 2047 5 31 10 1023 17 131071
def cc_46_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0x3d299e140ec26741038251b924d8146a09314998240bc265c102c2795934a80c5205270513024900c4605202410234 8 255 3 7 10 1023 17 131071
def cur_46 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_46_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_46_0 p) (Nat.blt p 32)
def f_46 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV4 m_46 g_46 ep_46 64 bds_46 (dagTraceF m_46 s_46 5 f_46) (cur_46 0) s_46 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_0 : treeBlockF 0 32 (dagCheckNodeV4 m_46 g_46 ep_46 bds_46 64 (dagTraceF m_46 s_46 5 f_46) cur_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_1 : treeBlockF 32 64 (dagCheckNodeV4 m_46 g_46 ep_46 bds_46 64 (dagTraceF m_46 s_46 5 f_46) cur_46) = true := by decide +kernel
theorem nj_46_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_46 g_46 ep_46 bds_46 64 (dagTraceF m_46 s_46 5 f_46) cur_46) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_46_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_46_1 h1 h2)
theorem nc_46 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 m_46 g_46 ep_46 bds_46 64 (dagTraceF m_46 s_46 5 f_46) cur_46) i = true := nj_46_1
theorem lb_46 : LowerBin m_46 s_46 g_46 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_46 kn_46 sub_46 gl_46 rc_46 nc_46

def m_47 : Nat := 0x8888888888888888
def s_47 : List Nat := [0x808080808080808, 0x88008800880088, 0x888800008888, 0x88888888]
def g_47 : Nat := 0x800080808
def ep_47 : Nat := 0x8080000000008000008000000000800080000000000080008080800000000000000000000000000000000
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

def m_48 : Nat := 0x2222222222222222
def s_48 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_48 : Nat := 0x2020202020222
def ep_48 : Nat := 0x200002000000200000000200002000000000020000202020202020000000000000000000000000000000000
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

def m_49 : Nat := 0xc0c0c0c0c0c0c0c
def s_49 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_49 : Nat := 0x4040c040c0c0c
def ep_49 : Nat := 0x408080000000408000008000004000800080000000000000000000000000000000000000004040004000000
theorem epk_49 : ep_49 = edgePack m_49 g_49 := by decide +kernel
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4), (m_18, s_18, 4, g_18), (m_10, s_10, 4, g_10), (m_12, s_12, 4, g_12)]
theorem kn_49 : KnownBin bds_49 := by
  intro b hb; simp only [bds_49, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_4
  · exact lb_18
  · exact lb_10
  · exact lb_12
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

def m_50 : Nat := 0xa0a0a0a0a0a0a0a
def s_50 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_50 : Nat := 0x2020a020a0a0a
def ep_50 : Nat := 0x208080000000208000008000002000800080000000000000000000000020200020000000000000000000000
theorem epk_50 : ep_50 = edgePack m_50 g_50 := by decide +kernel
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8), (m_17, s_17, 4, g_17), (m_11, s_11, 4, g_11), (m_12, s_12, 4, g_12)]
theorem kn_50 : KnownBin bds_50 := by
  intro b hb; simp only [bds_50, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_8
  · exact lb_17
  · exact lb_11
  · exact lb_12
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

def m_51 : Nat := 0x3333333333333333
def s_51 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_51 : Nat := 0x1113131313131333
def ep_51 : Nat := 0x200002000000200000000200002000000000020000202020202020000000000000000001110101010101000
theorem epk_51 : ep_51 = edgePack m_51 g_51 := by decide +kernel
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_48, s_48, 6, g_48)]
theorem kn_51 : KnownBin bds_51 := by
  intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_48
theorem sub_51 : ∀ b ∈ bds_51, m_51 &&& b.1 = b.1 := by intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_51 : ∀ b ∈ bds_51, canon b.1 g_51 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_51, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_51 : Nat → List (Nat × Nat) := fun _ => []
def f_51 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV4 m_51 g_51 ep_51 0 bds_51 (dagTraceF m_51 s_51 6 f_51) (cur_51 0) s_51 6 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_51 g_51 ep_51 bds_51 0 (dagTraceF m_51 s_51 6 f_51) cur_51 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_51 : LowerBin m_51 s_51 g_51 7 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_51 kn_51 sub_51 gl_51 rc_51 nc_51

def m_52 : Nat := 0xff00ff00ff00ff00
def s_52 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_52 : Nat := 0x1100170017001f00
def ep_52 : Nat := 0x6000800000006000000080000000000000000000000060006000e0011001200120010001100140014001000
theorem epk_52 : ep_52 = edgePack m_52 g_52 := by decide +kernel
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_38, s_38, 7, g_38)]
theorem kn_52 : KnownBin bds_52 := by
  intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_38
theorem sub_52 : ∀ b ∈ bds_52, m_52 &&& b.1 = b.1 := by intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_52 : ∀ b ∈ bds_52, canon b.1 g_52 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_52, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_52 : Nat → List (Nat × Nat) := fun _ => []
def f_52 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV4 m_52 g_52 ep_52 0 bds_52 (dagTraceF m_52 s_52 7 f_52) (cur_52 0) s_52 7 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_52 g_52 ep_52 bds_52 0 (dagTraceF m_52 s_52 7 f_52) cur_52 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_52 : LowerBin m_52 s_52 g_52 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_52 kn_52 sub_52 gl_52 rc_52 nc_52

def m_53 : Nat := 0x5555555555555555
def s_53 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_53 : Nat := 0x1115155515551555
def ep_53 : Nat := 0x440000000000440000000000004004000400040000404000400040011101000100010000000000000000000
theorem epk_53 : ep_53 = edgePack m_53 g_53 := by decide +kernel
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_31, s_31, 5, g_31)]
theorem kn_53 : KnownBin bds_53 := by
  intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_31
theorem sub_53 : ∀ b ∈ bds_53, m_53 &&& b.1 = b.1 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_53 : ∀ b ∈ bds_53, canon b.1 g_53 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_53, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_53 : Nat → List (Nat × Nat) := fun _ => []
def f_53 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV4 m_53 g_53 ep_53 0 bds_53 (dagTraceF m_53 s_53 5 f_53) (cur_53 0) s_53 5 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_53 g_53 ep_53 bds_53 0 (dagTraceF m_53 s_53 5 f_53) cur_53 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_53 : LowerBin m_53 s_53 g_53 6 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_53 kn_53 sub_53 gl_53 rc_53 nc_53

def m_54 : Nat := 0xffff0000ffff
def s_54 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_54 : Nat := 0x175f00001f7f
def ep_54 : Nat := 0x820000000000000000000000048000000600000060a00000e0800001200000010200000145000001040
theorem epk_54 : ep_54 = edgePack m_54 g_54 := by decide +kernel
def bds_54 : List (Nat × List Nat × Nat × Nat) := [(m_36, s_36, 6, g_36), (m_32, s_32, 5, g_32), (m_22, s_22, 5, g_22), (m_42, s_42, 5, g_42), (m_7, s_7, 4, g_7), (m_35, s_35, 5, g_35), (m_20, s_20, 5, g_20), (m_0, s_0, 4, g_0)]
theorem kn_54 : KnownBin bds_54 := by
  intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_36
  · exact lb_32
  · exact lb_22
  · exact lb_42
  · exact lb_7
  · exact lb_35
  · exact lb_20
  · exact lb_0
theorem sub_54 : ∀ b ∈ bds_54, m_54 &&& b.1 = b.1 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_54 : ∀ b ∈ bds_54, canon b.1 g_54 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_54, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_54 : Nat → List (Nat × Nat) := unpackCursorV4 0xd00a18a009a3699680623338038001 0x4e9c9d35727264d5c7c98e53192631829a3525aa28d415a7aa4d52271c4d38985124e22bc4228825100e1e9c351e803500a200f4e1e9ac935324b6454c82b8f551aad4e1a9ab4f869c8d321a6234c06951126389a5124e229441287250c4a0c8c114c80b8c0a102f4e3694dd197a10e3e1c7a35288a3253e1a7a94b86948d221a4290f8e1e9c3c287270d5a19143128603074e0aae3f4c76e8dd319ad3f1a7684dc699a52f1a56249c6919c3f287670dca199c2f2856709ca118c1f2836705c609801f 12 4095 5 31 10 1023 15 32767
def f_54 : Nat → Nat × Nat := unpackForestF 0x214d18dd64d58d45372d28946149c01f 4 10
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV4 m_54 g_54 ep_54 9 bds_54 (dagTraceF m_54 s_54 7 f_54) (cur_54 0) s_54 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54 : treeBlockF 0 9 (dagCheckNodeV4 m_54 g_54 ep_54 bds_54 9 (dagTraceF m_54 s_54 7 f_54) cur_54) = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 9 → (dagCheckNodeV4 m_54 g_54 ep_54 bds_54 9 (dagTraceF m_54 s_54 7 f_54) cur_54) i = true := fun _ h1 h2 => treeBlockF_at nb_54 h1 h2
theorem lb_54 : LowerBin m_54 s_54 g_54 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_54 kn_54 sub_54 gl_54 rc_54 nc_54

def m_55 : Nat := 0xffffffff00000000
def s_55 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_55 : Nat := 0x1117175f00000000
def ep_55 : Nat := 0x6480000000000060048000000000006060a0000000011121200000000001114145000000000
theorem epk_55 : ep_55 = edgePack m_55 g_55 := by decide +kernel
def bds_55 : List (Nat × List Nat × Nat × Nat) := [(m_26, s_26, 7, g_26)]
theorem kn_55 : KnownBin bds_55 := by
  intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_26
theorem sub_55 : ∀ b ∈ bds_55, m_55 &&& b.1 = b.1 := by intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_55 : ∀ b ∈ bds_55, canon b.1 g_55 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_55, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_55 : Nat → List (Nat × Nat) := fun _ => []
def f_55 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV4 m_55 g_55 ep_55 0 bds_55 (dagTraceF m_55 s_55 7 f_55) (cur_55 0) s_55 7 = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_55 g_55 ep_55 bds_55 0 (dagTraceF m_55 s_55 7 f_55) cur_55 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_55 : LowerBin m_55 s_55 g_55 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_55 kn_55 sub_55 gl_55 rc_55 nc_55

def m_56 : Nat := 0xffffffff
def s_56 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_56 : Nat := 0x175f1f7f
def ep_56 : Nat := 0x820000000000048006000000000060a0e0800000000120010200000000014501040
theorem epk_56 : ep_56 = edgePack m_56 g_56 := by decide +kernel
def bds_56 : List (Nat × List Nat × Nat × Nat) := [(m_45, s_45, 6, g_45), (m_43, s_43, 5, g_43), (m_41, s_41, 5, g_41), (m_42, s_42, 5, g_42), (m_7, s_7, 4, g_7), (m_39, s_39, 5, g_39), (m_21, s_21, 5, g_21), (m_9, s_9, 4, g_9)]
theorem kn_56 : KnownBin bds_56 := by
  intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_45
  · exact lb_43
  · exact lb_41
  · exact lb_42
  · exact lb_7
  · exact lb_39
  · exact lb_21
  · exact lb_9
theorem sub_56 : ∀ b ∈ bds_56, m_56 &&& b.1 = b.1 := by intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_56 : ∀ b ∈ bds_56, canon b.1 g_56 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_56, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cur_56 : Nat → List (Nat × Nat) := unpackCursorV4 0xd00a18a009a3699680623338038001 0x4e9c9d35727264d5c7c98e53192631829a3525aa28d415a7aa4d52271c4d38985124e22bc4228825100e1e9c351e803500a200f4e1e9ac935324b6454c82b8f551aad4e1a9ab4f869c8d321a6234c06951126389a5124e229441287250c4a0c8c114c80b8c0a102f4e3694dd197a10e3e1c7a35288a3253e1a7a94b86948d221a4290f8e1e9c3c287270d5a19143128603074e0aae3f4c76e8dd319ad3f1a7684dc699a52f1a56249c6919c3f287670dca199c2f2856709ca118c1f2836705c609801f 12 4095 5 31 10 1023 15 32767
def f_56 : Nat → Nat × Nat := unpackForestF 0x214d18dd64d58d45372d28946149c01f 4 10
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV4 m_56 g_56 ep_56 9 bds_56 (dagTraceF m_56 s_56 7 f_56) (cur_56 0) s_56 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56 : treeBlockF 0 9 (dagCheckNodeV4 m_56 g_56 ep_56 bds_56 9 (dagTraceF m_56 s_56 7 f_56) cur_56) = true := by decide +kernel
theorem nc_56 : ∀ i, 0 ≤ i → i < 9 → (dagCheckNodeV4 m_56 g_56 ep_56 bds_56 9 (dagTraceF m_56 s_56 7 f_56) cur_56) i = true := fun _ h1 h2 => treeBlockF_at nb_56 h1 h2
theorem lb_56 : LowerBin m_56 s_56 g_56 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_56 kn_56 sub_56 gl_56 rc_56 nc_56

def m_57 : Nat := 0xffff0000ffff0000
def s_57 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_57 : Nat := 0x11170000175f0000
def ep_57 : Nat := 0x64800000000000000000000000600000048000000060000060a000011120000120000001114000014500000
theorem epk_57 : ep_57 = edgePack m_57 g_57 := by decide +kernel
def bds_57 : List (Nat × List Nat × Nat × Nat) := [(m_34, s_34, 7, g_34)]
theorem kn_57 : KnownBin bds_57 := by
  intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_34
theorem sub_57 : ∀ b ∈ bds_57, m_57 &&& b.1 = b.1 := by intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
theorem gl_57 : ∀ b ∈ bds_57, canon b.1 g_57 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_57, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl; decide +kernel
def cur_57 : Nat → List (Nat × Nat) := fun _ => []
def f_57 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV4 m_57 g_57 ep_57 0 bds_57 (dagTraceF m_57 s_57 7 f_57) (cur_57 0) s_57 7 = true := by decide +kernel
theorem nc_57 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV4 m_57 g_57 ep_57 bds_57 0 (dagTraceF m_57 s_57 7 f_57) cur_57 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_57 : LowerBin m_57 s_57 g_57 8 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_57 kn_57 sub_57 gl_57 rc_57 nc_57

def g_58 : Nat := 0x1117175f175f1f7f
def ep_58 : Nat := 0x6480820000006480000082000060048004800600006060a060a0e0811121200120010201114145014501040
theorem epk_58 : ep_58 = edgePack fullMask g_58 := by decide +kernel
def bds_58 : List (Nat × List Nat × Nat × Nat) := [(m_30, s_30, 7, g_30), (m_52, s_52, 8, g_52), (m_23, s_23, 6, g_23), (m_55, s_55, 8, g_55), (m_34, s_34, 7, g_34), (m_50, s_50, 7, g_50), (m_56, s_56, 8, g_56), (m_54, s_54, 8, g_54), (m_27, s_27, 7, g_27), (m_46, s_46, 6, g_46), (m_51, s_51, 7, g_51), (m_53, s_53, 6, g_53), (m_26, s_26, 7, g_26), (m_38, s_38, 7, g_38), (m_48, s_48, 6, g_48), (m_36, s_36, 6, g_36), (m_13, s_13, 4, g_13), (m_49, s_49, 7, g_49), (m_47, s_47, 5, g_47), (m_16, s_16, 4, g_16), (m_25, s_25, 5, g_25), (m_44, s_44, 5, g_44), (m_28, s_28, 5, g_28), (m_40, s_40, 5, g_40), (m_45, s_45, 6, g_45), (m_33, s_33, 5, g_33), (m_12, s_12, 4, g_12), (m_15, s_15, 4, g_15), (m_5, s_5, 4, g_5), (m_7, s_7, 4, g_7), (m_6, s_6, 4, g_6), (m_19, s_19, 4, g_19), (m_37, s_37, 5, g_37), (m_35, s_35, 5, g_35), (m_29, s_29, 5, g_29)]
theorem kn_58 : KnownBin bds_58 := by
  intro b hb; simp only [bds_58, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_30
  · exact lb_52
  · exact lb_23
  · exact lb_55
  · exact lb_34
  · exact lb_50
  · exact lb_56
  · exact lb_54
  · exact lb_27
  · exact lb_46
  · exact lb_51
  · exact lb_53
  · exact lb_26
  · exact lb_38
  · exact lb_48
  · exact lb_36
  · exact lb_13
  · exact lb_49
  · exact lb_47
  · exact lb_16
  · exact lb_25
  · exact lb_44
  · exact lb_28
  · exact lb_40
  · exact lb_45
  · exact lb_33
  · exact lb_12
  · exact lb_15
  · exact lb_5
  · exact lb_7
  · exact lb_6
  · exact lb_19
  · exact lb_37
  · exact lb_35
  · exact lb_29
theorem sub_58 : ∀ b ∈ bds_58, fullMask &&& b.1 = b.1 := by intro b hb; simp only [bds_58, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_58 : ∀ b ∈ bds_58, canon b.1 g_58 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_58, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def cc_58_0 : Nat → List (Nat × Nat) := unpackCursorV4 0xdd20da614705c6de229b72535f8ee99264ff339946b25cce2328bf84e7549cdfcad9e21aef4d5845aa10f9231f21b2b3ba7c6c0b4b91f13f33218663c8686415092360bc680f484009e00001 0x26df0036e01297c054bc02a5d0212e005d6f0f2b38131bc098d604c670263181316c098ae01b6f00db5806d9c036c601b5b00dab806d3c0369601b4700da18129bc094d404a6703d3301293c0948e01a3f00d1b8165bc052dc1096b05cb504259c172cc05963014b104256c152b410957054ab01253c0529c0494b024a501251c0928c04943014a10064fc0327c0193b00c9d0064dc0326c0193300c9900e4ac072540192700c930161bc070d60c86a0343381a198070c60385b0342b81213c070960484701c218060fc030760183700c1980e0ac0304e0181b00c0c80605c030260181102f3f8859dc09afe04d7b026bb8135cc09ad604d6700e3f8071ec038ee01c7300e3580719c038be01c5d00e2d807168038ae04c5600e2a806dfc0b6fc01b7b00dbd006ddc406ec01b7300db9006dac036d401b670f9b3006d7c096bc01b5d00da7806d380369a05a7f0153f01a9ec324f406a770353b0169cc054e406a6b0b93501a99c0d4cc04a5f0252f01296c094b404a590252c01295c094ac04a530252901a944134a001a4f00d2700692c0349406a4904d2400691c0348c01a4300d210069040348001a3f00d1f0068f40347801a3b00d1d01a8e43a47001a3700d1b01a8d40d46801a3300d190068c4034600497f024bd0125dc0f2ec0495f024ab80653c0328e0193f00c9e8064e80326e019360249a81e4d00725e0392e01c968161fc070f60c87a0343b81a1d8070e60386b0343381217c070b60485701c2980613c030960184700c218060fc0307a0183b00c1d00e0e4070700183700c1b01a0d40d0680183300c1880e06c0703203811024080175e809aec04d650163f0171e80b8ec02c720263280ad340369202b4500da08165d80d2ea0495e024ad012558092a40994e074a68265301d2940b94905ca403a5181f28a0f94404ca102e504132800193e0149d00a4d8032640587d0343a81a134070920684501c2080a064038f40bc7600e3280adf8036f40bb7600db9006d941b6bc01b5a025ab006d480d2ec0697504caf012568092ac0995200ca70065280328c0194200c9f0064f4032780193a05c9c82e4e00326c0f93507c9a0064c803262019300343e81a1d40307a038390341a8060c40503201c5d00e2d013158038aa02b7e00dbd016dd8036e401b6a075b300ad78036ba01b4e00da68129f4094ea01a3d00d1d0068d80946a07a3402cbb01a5d4152d40a966024af012568092ac0495200ca70065280328c0194200c9f0064f4032780193a05c9c82e4e00326c0f93507c9a0064c8032620193001c9500e4980b0fa0687500c1e8060e8070720383800c1b01a0d40d068018310140c80a0440bade0bd67026378171ac098ce05c630da2d81315c0b6de0bb6b05db3816d8c346b610b57085a7812d2c0968e1934302d3781e9b40f4ce07a650252781291c0f47e07a37034b381a5980d2ca0b95b054ad03e55c152ac0f94f04ca701252c0929404947024a302e50c132840f93f00c9f02e4ec052740f9370149b02e4cc032640392b01c9501e49c0724c0586f0343680e1ac0d0ce0686501c3180e16c0d0ae0684f01c2581211c070860683f01c1d81a0dc070660382b0341380e06c050320681701c0980e044038ba01c5a0262b0071540b6fc01b7a075bb006dc8096bc01b5d00da7006d340f4ec01a3603d1a00a5f8152f40e976014b901a594092bc0495a024ab0125480329c0194a00ca30065080327c0193d00c9e0064e8152720a93800c9b02a4d4432680193200c988064c0110f406876034328060f4030740383901c1c0060d80d06a0683400c188131bc1d8d604c670763183adbc1d6d60eb67075b1842d3c0969604b470b9a181e998152de0296e054b582a5a8152ce0e966054b180a5880d2aa0a94f04ca701252c0929404947024a302a50c132840a93f00c9f02a4ec052740a9370149b02a4cc032640686f01c358221a80d0ce0686601c3181a1540d09e0384b0242380e10c0d07e0383b0341b80e0cc0bafc05d6e0263f0131f4098f804c790263a8271c8098e209c7004dbe806de4136ea01b71025a4826d04252fc0997d094be0265e8132f209978054bb0265d4152e80997204cb88265c0052dc0596d014b60165a80b2cc0996505cb200a588132aa0a954024a701a5340327c0293a0149b0064c80d0fa038790343a80e1c40d09a0484501c0c8175bc13adc05d6d05e3782b1b4178ce0ac6502e2f8171740b8ae0bc55025b780adb4096d604b69025b380ad94096c604b61025af812d6c096b204b57025a9812d440969604b4704d3780a9b4134d601a6904d3380a994134c601a6102d2f8169740b4b605a5704d2a81694c1349609a470251f8128ec0946e04a33024b78125b4092ce04965024af81255c0927e049370249781249c0d0de0686d01c3580e1a4090ce0486501c3180e1840b0be0385b0242b80e14c07096068470241f80e0ec0906e038330341780e0ac0d04e0382301c0d81205c0bade15567026378131ac098ce04c630262d81315c0b6de09b6b04db3816d8c136b609b57025a7812d2c0969204b47025a1826d04094de04a67025278129340948e04a450251f8128dc0b2de0296e04cb58265a8132ce1416602cb180a588132b60995a04cab82a5580929e0494e034a68264fc0327c0993b0149d0264dc0526c0993300c9900e4ac072540492701c930161bc070d60686701c3180e16c0d0ae0484f0342680e12c0908e0484501c2181a0fc070760683701c1980e0ac0904e0381b01c0c81205c0702603811016b780b59c058de02c6b0163380b18c138b604c57015b7806dac056ce01b6300dad80ad5c0569e02b4e00da580ad1c0368609b420153780a99c0949e04a4700d1f81e8f40546e02a35014b780a5b8052d60296a014b380a598052c602962014ad80a568052ae0a956014a7826538052960294a014a381251805286029420149b80a4d80526a0292b0149500a49c0724c0286f0143580a19c050c60385b0342b81a13c070960484701c218060fc0d07a0283b0141b80a0d4030660382b0341380606c030320281701409806044098de04c6b0263381318c0b6de0fb6b07db3816d8c0969e04b4b025a3812d0c0b4de02a6e0353581a99c0b4c602a620252781292c0948e04a430351f81a8ec0d46e06a3303cb301a4b80b0de0386b07c3501a19c0d0cc038630242780e12c0908e038430341f80e0ec0d06e0383301c0c8175bc11ace04c6f02e3581319c0b8c608c5b0262b816dbc1f6d60fb6702db1822d6c116ae0cb4f025a5812d1c1968605a6f0153701a9ac0d4ce05a630153101a96c114b406a570352b01a93c0949604a470352181a8fc0d47606a37035198165bc1f2d40796703cb301253c0928e0793f03c9b80e4bc0725c0392d01c3381a198070ca0385b01c2b80e13c070960384701c2180e0fc070760383701c1980e0bc0d05c0382d01c0d80e0640702e0381107eb78d159c098de3346b0263383f18c648b604c5707db78c0dac5a6ce0fb63149ad894d5c4669e04b4b025a3870d0c0d4de05a6e035358609a80d4ce06a66035318169880d4b61625a0352b81a9580d49e06a4e025258129280948e04a460352184c9080d47e01a3e0351d8488e80d46e06a36035198068c80f2de1116a03cb381e5980929e0494703c9f81e4dc0725e0392e01c9681a1bc070d61006a0343381a198070c60385b0342b81a13c070960484701c2181a0fc070760683701c1980e06c0703203811028080075bc03adc02b6f025b5812d9c056c604b5f025ae812d6c096b204b57025aa812d4c096a201a6b0153380698c054ae02a550151f8068ec0546e01a330143780e1ac070ce028630142f80a174070b60385901c2b80a154070a60385101c1f80e0ec0706e0383300c1780a0ac0504e0182301c0a83e05003cfe01e7e00f3e80b1fc098f604c770163980b1bc098da04c6b0263481319c098ca02c6302630806dec0b6f401b79015bb816dd8036e601b71015b3816d98216ca02b4f00da580ad1c036860297f01cbd80e5dc052e60296f01cb680e5ac072d20396701cb280a58c072c20394f01ca580e51c072860193f0149d80a4dc032660392507c9200a1f80b0ec0286e014360161981c0c80484e024230060f80506c0381e016bf8135ec09aee02d7300e3f8171f8038fa01c7700e3a8071cc038e401c5f00e2d80715c038a601b77085bb006dd4036be04b5e00dad806d68036ae04b5600da9806d480369e01b4e00da680a5fc072f603977014b980e57c072b60395701ca980653c032960194700ca18064fc0327a0193b01c9c8064dc0726a0193300c9880e4940e2480287e05c3b012178090ac0184e00c230060f803078018360141a00e07803ade01d6d025b7812db4096d604b69025b3812d94096c604b61015af812d6c096ae02b530153780a9b4054be01a5b00d2980a8fc0347602a3700d1980e1bc050da0386b01c3480a19c050ca0386301c3080a17c070b6038570142980e0fc070760383701c198060bc050560282700c118079fc03cfc01e7d0263f8131f4058f604c790163b8131d4098e604c71016378131ac098ce02c63015bf816df80b6fa02b6f02db7006dac036d201b6302db1006d840569e01b4b015a3806d0c072fe0397d014bd80e5e4052ee0397501cb980e5c4052de0396b01cb380a58c0729e0394b01ca380e50c0327e0293b0149b8064cc0724a061240843f02c1f0050ec028740143702e1980909c0484600c1f00a0d80703c02c6f0263581319c058c601b6f00db5806d9c0369e01b4b00da3806d0c054de02a6e025278129380949604a4a025238129180948604a4200d1f8068f8050de0386b01c3380a18c0709e0384b01c2380e10c0307e0183b00c1b8060cc0305e0182d01c1580e0a40304e0182500c118060840702a0f814016bf8135ec09aee02d7300e3f8071f4038f601c7a00e3b8171d8038ea01c5f00e2d80715c038a601b7f02dbf006df4036be04b5e00dad806d68036ae04b5600da9806d480369e01b4e00da680a5fc072f603977014b980e57c072b60395701ca980653c032960194700ca18064fc0327a0193b01c9c8064dc0726a0193300c9880e4941f2480287e02c3b012178090ac0184e00c230060f803078018360481a00e078058de04c6b0263380b18c036de05b6e00db6806d9c036ca01b6300db1006d3c0369601b4700da180699c1f4cc01a6500d278129380349601a4a00d238129180348601a4200d1f8068f80347a0296f034b581a59c052c60494f024a581251c092860193f00c9d8064dc032660192f00c968064ac0d252019270349280648c032420b8660340f0075bc03adc01d6d025b7812db4056d604b69015b3812d94096c604b61015af812d6c096ae02b53015378169b80b4da02a5f02d2f00696c034b201a5302d290069440547e01a3b0151b8068cc0d2de0696d014b581a5a4052ce06965034b181a584052be0695b034ab80a54c0927e0493b0249b8124cc0325e0292b0149380648c170ac0681e025af812d6c096ae04b5307d2f81c96c0c4ae0fa530251f8128ec0946e04a33034af81a56c0d2ae069530249f8124ec0926e049330349781a4ac0d24e069230202b01a078094be04a5b0252b81294c0949e04a4d0252581291c0948a04a430b4af82e56c172ae1695302ca782e52c1728e05943024978124ac0924e0492302c2f81a16c0d0b2068570342981a1440b09e0684b0342481a11c0b08606841024178120ac0904e048230340f81a06c0d02e06813025b7812db4096d604b69025b3812d94096c604b61025af812d74096b604b57025aa812d4c2d4de02a6d05d358069a4174ce02a650b5318069840b4be0ba5b05d2b81694c0947e04a3b0251b8128cc070de0286d01c3580e1a4070ce0386501c3180e184070be0385b01c2c80e15c070a60385101c1f80e0ec0706e0383301c1780e0ac0704e0382301c0a810050058de02c6b0163380b18c056de02b6e015b580ada8056ce02b66015b180ad880569e02b4e015a5812d280568e02b46015a1812d08054de01a6b0153380698c0549e01a4b0252500a91c0548c01a430143780a1ac050ce0286301c2780e12c0708e0384300c1f8060f405076028390141b8060d4050660383100c1780a0ac050520282700c1180e084098de04c6b0263381318c1a6de0c36b051b3820d8c0969e04b4b025a3812d0c072de0396b01cb380e58c0729e0394b01ca380e50c0727e0393b01c9b80e4cc0724a0512402c3700c1980909c0484600c1f0080d80703d9845fcaa2de3515f068a78235fc09ade00d5efa6a77c34fbc9a5de0d1eea6877325fb712dd8c95ec24a75f24fad125d4491e9e4874b23fa511dd148de7e4673c15f9c0adc9855e442a71c14f8a8a5c3c51e0a2870313f8109dc044ddfc266f812f7b095bb449dd6246e605f6e02dad815d600a6aa04f4c825a3c11d0a0868003f3f81d9f80dcf00666902f3201594809c920464201f1d80d83c05c020260003f 19 524287 8 255 11 2047 21 2097151
def cc_58_1 : Nat → List (Nat × Nat) := unpackCursorV4 0xe3a7fb3d3b40a76374ac660988c430f02e0e10c021b74cbaba2fcf480926c31a4a9f4c03b6336caa2b9601630fa96304d6568119cea181b81c31a564b1848e0809a82124101e86017260002e 0x7ade0f5b81eb686c6f0d8ce1717c462b84b6f0d6d612d9c35b184b5f0b6b612d5c2da988b4b0968e1a9bc353586a670d4c61697c7d2d8fa570b4a62292c45238ca3f09476128dc65198696f0d2ce1657c3cab8493f0926e1e4bc3c938386f0d0dc0e1b41c2f8285e070b60e15c1c2982852070960e1281c23888460707e0e0ec1c1b838330705e0e0ac1c13838230702e1a0581c0a83d6f07adc0f5b4463788c6d118ce231942e2f88c57096de12db45db589b69096ce12d9465b189b61096be16d6c25ab85b531169612d1c7d3782a6d174d6069a45d3382a651f4c6069842d2f8ba5b174ae1694c452588a471947e128ec251b8ca330f2de1a5b434b3869650b2be1e5743cab879550927e124dc3c9787927070de0a1b41c3383865070c60e17c1c2d83859070ae0e14c1c288384b0708e0e0fc1c1d83837070660e0bc1c1583827070460e0741c0d838170702a0b5bc16b382c6f058d60b19c163188c5b098ae0adbc15b702b6b056d40ad9c15b302b63056c40ad6c45ad02b57056ac0ad3c15a702b4b096940ad1c15a302b43136840a9bc0d3582a67034c60696c452d02a57054ac0a93c0d2582a47034860a8fc151f02a3d052de0a59c24a7849470527e1a4f4149b829350325e1e4b4149382925050de0a1ac143382863070b60e15c1c278384b0708e0e10c0c1f8183d0506e060d414198182f050560a0a4141381823070420e06c1c0b88d6f11ace131bc663584c67198c62316c262b8fb6f826d6fcd9c7db188b5b116ae32d3c25a584b47196861e9bc3d3384a4f0948e1e8fc3d1b8396f072d60e5a81cb3be166072c60e56c1cab8394f072960e51c1ca18393f072760e4dc1c998392d0724e0e4941c378586e070d60e1a81c33bd066070c60e1881c2d8385a070ae221581c278c84e070960e1281c2384846070860e1081c1f8183e070760e0e81c1bbc03607066060c81c13868260704a125f024bc06974092e02762026c204c8c0d5182aa20354212a80094b02694035263a2480d488269003ca2038480d0881a5f034bc06974032e02a5500fc60ab88057081aa30554406a84215000a9f1c13c06a74054e00a8e00d1807974070f01a1d00e440ac84057181aa30554406a84255000a9200d2001a3c454701a8d00d1804c6f0b8d61319c2e3185b6f1f6d63ed9c2db190b4f0969612d1c85a187a660b2de0a5b884a78994e092961252824a3849462128626508849f8193e212760a4e8849b8293621266064c82c378386b110d41a19c34330684f070961211c1c218683f070761a0dc1c198381b07032175f82eb704c7f098fa2b1ecae3c84c77098eae51ccae3884c6f0b8d61319c2e31b737f216fa2adec0dbc8ab77216ead8dcc0db885b6f1f6d63ed9c2db1a434f0969612d1d09a186a7f0d4fc1a9f4353e06a7b154f41a9e4553c06a770d4ec1a9d4353a06a73254e41a9c5a93805a6f054dc1a9ac5d3506a670d4cc1698c153106a4f0d49c1292c252504a470948c1a90ca92106a3f0347c1a8ec151d06a370546c1a8cc0d19079660725c1a1fc343e8387b070f21a1dc343a83873070e2161bc1c358886a0d0ce1a1981c318684f070961211c1c218683f070761a0dc1c19838190bcfe179dc26bf84d7e09afa135dc26ba84d730bae4135acaeb504d6709acc131dc263b04c750b8d6571a82e3385c66098be131782e2e85b7f0b6f616ddc2db98db6b136ce12d7c25ad84b57096a616d3c85a685b4b0369216d1c2da285b4303682169fc153f05a7b0b4f4169dc2d3b05a73054e41a9ac753506a670d4cc1297c252f04a5b094b41295c252b04a53094a41693c2d2706a4d0d4981692c2d2505a490b4901691c2d2305a450b4881690c2d2106a41134801a8fc0d1f06a3b054741a8dc151b06a3303464125fc24bd049770b2ec1257c24ab8494f0929a1251c24a28493f0926e0e4bc1c970392d0b0fe0e1ec2c3d058770b0ec0e1cc1c3586867090be0e16c242b838530b09e1a1341c25838490b08e161141c21838410d07e0e0ec341b83833070360e0641c088481009afe135ecaebd04d7709aec135cc26b285c7f0b8fc271ecae3d0ec77238ec171cc2e3904c650b6fe36dec4dbb85b73096be12d6c25ab84b531369e42d344da581b491368e42d144da181b410b4fe169f8353d9b27a0d4ee1a9d82d3985a72094be12978252d84a5a094ae12958252984a520d49e1a938352686a4c0d49646928352491a480d48e1a918352286a440d48626908352089a400d47e068f8351d89a3a0d46e1a8d8351981a320f2ec0e4b82c3f8387b110f41a1dc343b03873090be0e16c242b838530d09e1a1341c25838490d08e1a1141c21838410d07e0e0ec341b83833070320b9d816bb01d6e098da0b1a4163289c61036d206d64153f02a7a054ec0a9c8153706a6d0d4d80a9a8153482a68054cc0a994153202a620d4c242980352704a4a0948c269080d1f01a3a0346c068c814bb0392e050f40a1d8343682869050ca0e1841c0c82e7f1fcee0b5fc2ebd84d7705ae6375ac26b381c7f0b8fc071f40e3b81c75038e6071c80e3581c6a038ce9d1980e2f81c5b038ae0714c0dbb8fb76036ea06dac0db501b67626cc06d7c6daf01b5b036b406d5c25ab01b53036a406d3c0da701b4d054fe0a9f8353d8ba7a0d4ee1a9d8153982a720d4d63a9a8353386a660d4be1a978252d84a5a094ae12958352989a520349e069380d2581a4a0348e069180d2181a420347e068f80d1e81a3c03476068e8351c82a380346e068d8351a82a3403466068c80d1881a30052fe3e5e83cbb87976092be1255c0ca7819470327e064f40c9b879350725e0e4b81c968287f070f63e1e8343b86876050e60e1ac34338685f070b61215c1c298184f030960611c0c218183f0307a060ec1c1c818370d06a060cc0c188381b070320e044380801e7a15aec0b598263689c69098ca271844e2c82b6d056aa0a9f85d3d06a76054e41a9b8353686a6c154d41a9a4853406a660d4ca1a990553106a61154c01a964552c06a4e09494129184d2101a3e054740a8d80d19079760f2cc1e5901c970887a0d0ec1a1b4443503869070d01a198343286864070c20e06416b78fd67058de171ac263382c63138b61315c15b781b6b056ce06d8c0dad82b570569e06d2c15a381b43054de3e9a83d3387a660949e1291c0d1f82a37052de0a5b80cb58196a0d2ce0659814b182962212b62a56884ab8a9561329e2653824a58494a0928e125184ca1899420327e064f8149d8293a0526e0a4d80c9981932072560e4a83c9383926050de0e1ac7c35068670d0cc0a18c1c2d868570d09e0e12c2423838430307e0a0ec141b81833070561a09c140d828190d02e0e04c140881e7f03cfc079f486bfaf57d05aee435d416b78fd67098fe131f4163d90c79058ee131d44e3995c71058de171ac263382c63138b61315c15bf85b7e0b6fa0adbc2db701b6b036d206d8c2db101b61036b6b0d6815ab90b560569e06d2c15a381b430d4fe1a9f8353e86a7c054f60a9e8353c82a78054ee0a9d8353a82a740d4e6429c83538ae270054de0a9b835358ba6a0d4ce1a998153182a620d4b63a968352b86a560d49e1a938252584a4a0948e12918352189a420347e068f8151d82a3a0546e0a8d80d1981a320f2fe1e5f414bb87975052de3e5a83cb3879660929e1251c0c9f829370725e0e4b81c968687f0d0fa0a1ec1c3c828770d0ea0e1cc1c388286f070d63e1a8343386866050c60e16c342b8684f070961211c1c218183f050760a0dc0c198381b070320e044300801e7e03cfa42df80dbe82b6e036c406d54353f02a7a054ec429c815370ba6a0d4cc0a988352704a4a0948c269080d1f01a3a0346c068c83cb3019360725c221a834330183a0306c0e0640f3f01e7d098fa271e4263a89c71036fa06da40db086a7e0d4fa1a9f05d3d06a79174f01a9d8353a86a741d4e41a9c4753802a6e174d41a998153106a4e09494129184d2101a3e03474068d80d19079760f2e81e5981c970687d110f40e1e41c3c068760d0ea1a1d01c388886a0d0cc0e06426378dc6b098ce3718c0db781b6b036ce06d8c0da781b4b0368e06d0c74b78296e212d62e5a884b38b9661d2c60a5886ca78994e092961252824a3849461b286265080c9b819360d0de0e1ac3433838630d09e0e12c2423838430307e060dc0c198181b03032135fc6ebd84d771bae6071fc0e3d81c7a038eeb11d80e3981c65038be0716c0e2b81c53036fe16df80dbd81b7a036eeacdd80db981b72036ca06d7c6daf01b5b036b406d5c25ab01b53036a41a9fc153f06a7b344f41a9dc353b06a73054e41a97c352f04a5b094b41295c252b06a53134a40693c0d2701a4b034940691c0d2301a4303484068fc0d1f01a3d03478068ec0d1d06a3954470068dc0d1b06a350d468068cc0d1901a31034601e5d80c9b079340725c1a1fc1c3d8887a0d0ee1a1d81c398685f070b61215c1c298184f030960611c0c218183f0307a060ec0c1d0383907070060dc0c1b068350d068060cc0c188381905aec0b5d44e3c82c71098ba0b164162a89c51056fa0add40dac82a7e054f41a9e45d3c02a76054e40a9c4153802a5e0d4ba1a970152d02a59054b00a958152a82a54054a41a9445d2806a4e09494129184d2101a3e054740a8d80d19029760725c0a1e8143b0685d050b20a1541c288381905cfc0b9c80eb702b76036ea0adb80db682a7e054f40a9d8153902a6e054d40a998153106a4e09494129184d2101a3e03474068d80d19029760725c0a1e8143b03819058de271ac263382c63056de06dac15b381b630569e06d2c15a381b43052de0a5b884b58b96a212ce2e59814b1829621329e2653824a58494a0928e125184ca1899420327e064f814378386b0d0ce0a18c34278384b0908e0e10c0c1f8283b0506e0a06c140c82e7f0bcfc0b9ed433d02e7721cec0b9cc2f3901d6e058fe271ec263b82c73098de131b4163590c69058ce131944e3195c61056fe06ded39bd02b77216ec06dcc0dac82b4f036960ad1c0da182a7f054fc1a9ec853d06a770d4ec0a9cc153906a6f0d4dc1a9b4353602a6b054d41a9a4153402a67054cc1a994153206a63214c41a985313006a4f0d49c1292c252504a470948c1a90c4d2101a3f0347c0a8ec151d02a370546c068cc0d19079760725c0a1fc1c3d8887a0d0ee1a1d814398686f0d0da0a1ac1c34828670d0ca0e18c1c308684f070961211c1c218183f050760a0dc0c19838191b9180b220564202c800571806e0035460aa880d50842a0015260da480d4880a900151c01a3005cfe919dc16bf84d7b09aee0b5cc26b584d67058fe171f8163d90c7a058ee371d8163985c72058d6431a86e338dc66038be071780e2e82b7f036f60addc0db981b6b056ce06d6c25ad01b59056ae12d580da981b510568e12d1825a282a7f054fc1a9ec853d06a770d4ec0a9cc153906a6b214d41a99c353304a5f094bc1296c252d04a57094ac1294c252902a4f0549c1a934152606a4b1b4941a9246d2406a470d48c1a914352202a43054841a904152001a3f0347c0a8ec151d06a39054700a8dc151b01a33034641a8c40d180297f092f4125dc3cbb0495f092ae0a53c24a6849470928a064fc149b8392f0725c0e4b4143f8387b190f41a1dc343b02873070d61a19c242f8385b090ae0e14c14278684d070960e124342386845050860e1040c1f8283b0506e060cc1c0d838190702212040353e10a780d4e8429c0252409a4005470068c04e4601c804471806e2055c201b800b6f84edd055b206a8c155101aa10854004a58134a00a9200d2001a3c3c4701a8d00d1807934070701a0d00f3f01e7d15afa2b5d42eb693d65058fa0b1e4263a84c71098d2131840dbe81b79036ea06dc40db481b610d4fc1a9f4353e0ba7a0d4f22e9e0353b06a750d4e84e9c8353890a70054dc169b4153605a6a0b4cc1a994353202a621d4b41a958252704a4a0948c129080d1f01a3a0346c068c824be8497a0f2ec125d43cba0496d092d41659824b2879640725c0e4b4343e8b87a070f20e1e0343b068750d0e80e1c42c368586a0b0cc1a1943432038190702212040173f0ee7a15cec0b9c856bb01d6e058d2131640db481b59054fc3a9e8353b02a720d4dc1a9b435360aa6a0d4d22a9a0353306a650d4c82a988353090a600d4aa1a950252704a4a0948c129080d1f01a3a0346c068c83cbb0392e110f41a1d83436838690d0ca0e184342a83819 19 524287 8 255 11 2047 19 524287
def cc_58_2 : Nat → List (Nat × Nat) := unpackCursorV4 0x911418a86983d6b7ff3e7d22d7834f7067d6ee186c62869b2b65b4061d3e5bc6156d4f4f27b4b0424614f3df823ae3136d41304692a1632633e2372c1f93e1d02919e3216c3214b210ce7d07d510007d 0x16bf02d7d05adc0b5882e3f04c7d098f8171e4263a89c720b8e2271c015be81b79056ea06dc415a682b45254fc269f4953e09a7a134f2269e0553b09a75154e8269c84d3889a70054dc0a9b4153602a6a054cc269945d3202a62114ba22968452b09a55154a80a938152681a3e054740a8d80d190797d0f2ea1e4b43c928687d070f21a1d41c388684d0b08a060f80c190182d07052060941c1082d6f13adc0b5b45e378ac6d118d62f19c563288c63058be0b174162d82c57178aa0b14c15b782b6d056d60ada415b382b65056c60ad8415af82b5b0b6b20ad5c15a982b510969e16d2c25a385b43054de0a9b40d3581a69054ce0a9940d3181a61054be0696c152b81a530549e0692c152381a430547e068ec151b81a33172de1e5b424b58b9670f2ca1258c14af8295d052b60a55c5caa829531129e1252c9ca3849430927e124ec249b849330325e0a4ac1493819230d0de1a1b41c35838690b0ce161941c3183861050be0a16c142b828530d09e0e12c3423838430b07e0e0ec241b838330305e0a0ac1413818230903e0e06c340b8381305ade235aef2b382d63058de171ac263382c63098be2716c262b88c53056de06dac15b381b63056be06d6c15ab81b530569e0ad340da582b470568a06d0c153782a6e134d6269a84d33dd266054c60a988452f89a5b134b42695c552b08a530549e0a938152681a3f0347c0a8ec151d02a370546c068cc0d190296f092d66659c14b18895f092b66655c24a98494f092963252424a38494313282064fc149d8293703266264bc3c968492b1324e1e49424918286f070d61a19c14318685f070b61a15c1c298684f0d09a0e12c24238684507086060fc0c1f0283b0506e060cc0c190182f0305a0e0ac1c14868270304a0e08c1c108481f070361a05c1c0982d7f05af60b5dc16b982c7f058fc0b1ec163d02c77058ec0b1cc163902c5f058bc0b16c262d02c57058ac0b14c262902b7f036f60addc0db982b5f036b60ad5c0da982b4f0569c0ad34153f02976092bc1255814a70f94c0528c0a5100c9f02936050fe0a1ec143b82873090be0e16c242b838530309e061380c268183f0307c0a0ec141c81833030640e0c43412838190d02a0b5d83eb304c6d138d2131944e3089c59056fc0ade815bb02b72056dc0adb415b60ab6a056d24eda015b302b65056c82ad8815b08ab60056b22ad6015a704b4a0568c66d08153681a69054ca06984151f02a3d0d0da0e1a43432838610307c060f40c1702829030440e08416b782d67058de0b1ac163382c63138b61315c15b781b6b056ce06d8c0dad82b570569e06d2c15a381b43054de0a9b8153382a63054c46e96c552d1ba57154ac2693c4d2704a4b094941291c252309a4313484068fc0d1f02a3b054740a8dc151b01a33034640a5bc14b38494f0928e064fc149b8292f0525a0a49c14928286f050d60a19c14318385b0d0ae1a13c1c258484707086060fc141d8283703066060bc0c168382b070521a09c0c1283823070421a0741c0d868170d02a1f5fed2be87d770faea0b5bc16b384c7f098fa1f1ec3e3c84c77098ea1f1cc4e3882c6f058d60b19c163189c5b098ae0adfc15bf02b7d056f80adec3dbd02b790f6f00addc15bb02b75056e80adcc3db902b71b26e00adbc15b702b6b056d40ad9c15b302b63056c40ad6c75ad02b57056ac0ad3c15a702b4b096940ad1c15a302b43336840a9fc153e81a7b034f20a9dc153a81a73034e20a9bc0d3582a67034c60696c152b82a4f034960a91c0d2182a3f0547c0a8f414bf8297e052fa0a5bc14b702962ae2b41e55824a7849470527e1e4f4149b829350325e0a49c343f8687d070f60e1e4343b86875070e60e1c414378286b050ce0a18c1c2d868570d09e0e12c2423838430307e060f80c1e8182f0305c0a0ac141481823030440e084340e8381b0d02e1a05415bf07b7a056ec1edc815b702b6a056cc0ad8815a704b4a0568c12d08151f02a3d0f2fc0a5b80c1f0183d0305c0a0a40c11038210d02a1a050263e84c79098ea131c415bf02b7d056f82ede815bc8bb78056ec0add415ba0eb72056e23adc015b702b6a056cc0ad8815a704b4a0568c12d08153e81a79054ea069c4151f02a3d0d0fa0e1e4343a838710307c060f40c1702829030440e084163784c6b098ce0b18c15b781b6b056ce06d8c15a781b4b0568e06d0c153782a6e214d62e9a885338ba66054c60a988252784a4e0949612928252384a460948612908151d82a3a050de0e1ac3433828630909e0e12c2423838430307e0a0ec0c198182f0305a0b5fc26bd84d7705ae60b1fc2e3f02c7b278f40b1dc363b02c730b8e40b17c262f04c5b098b40b15c262b04c53098a40adfc0dbd82b77036e60ad7c0dad82b57036a60ad3c1da703b4dae4ec0a5fab0bb0495e092ac1a53aa8a60294605288064f8149b0287f070f61a1dc14398485f070b61215c1c298184f0309c061340c1f8183e050760e0e40c1981832070620e0641c0c068150d0280b9f83f3b02c7f138f6131dc163987c69098ca0adfc2dbf02b7b276f40addc35bb02b730b6e41ada43db402b65056c80ad3c35a704b4b096940ad1c25a306b43336840a9fc0d3d82a77034e6069a4153282a4f034960a91c0d2182a3f0747c0e8f43cbb0287f070f61a1dc1439838690d0ca1a13c1c258484707086060fc0c1f0183d0305e060b814158382903046060881c1082d6f11ad78559c16b182c6f138d63319c163188c5f138b63315c462982b6f0b6dc0adaf01b502b670d6cc0ad8c2db102b5f0d6b77cd6815ab86b560d6a60ad3c35a706b4b096940ad1c25a306b43b86840a9bc0d3582a67034c60a97c0d2d82a57034a60a93c0d2582a47034860a8fc1d1f03a3d052df6c5aec0b382963112bf5056e98ab889531329e3252c64a3899430d27e1e4f4149d829370d26a1a4cc0c978292b0524e0648c14378386b0d0ce0a18c342f8385b0d0ae0e14c34278384b0d08e0e10c0c1f8183e0307a060bc0c170282b070520608c0c11038210d03e0e06c340b8381303ad6075a80eb381d6603ac60b1bc163388c5f118ba2315c462a82b6f056d60ad9c15b184b5f096ba16d6c2dac84b57096aa16d4c2da885b4b0968e069bc0d3581a67034c60697c0d2e81a5b034b20695c0d2a81a53034a20692c0d2381a3f03476068dc0d198196f052d40a59c14b30195f032ba1e55c3caa8493f0926e064bc0c938286f050d60a19c14318285f050ba0a16c142c82857050aa0a14c14288384b0708e0e0fc1c1d8383707066060bc0c1581827030460e06c1c0b82d7f05aee0b5bc16b682d6711aca0b1fc163d82c77058e60b1bc163682c6b0b8d20b19c263282c63058c21716c262b81b7f036f606ddc0db981b6f036da06dac0db481b67036ca06d8c0db081b5b036ae06d3c0da581b47036860a9e8153b82a76054ce0a9983d3284a4f0948e068fc0d1b8297f052f60a5dc14b98296f052da0a5ac1cb482967072ca0a58c14b08395b072ae0e53c2ca70394b0728e0e50c1ca10193f0327a064ec0c9d019370326c0a4d41c9583927030fe0a1f80c3d8187a030ee0a1d80c3981872030de0a1b80c368286c030d6061a80c3481868030ce0a1980c32d1064030c6061880c3081860030b6061680c2b888560309e161380c258184a0308e121180c21818420307e060f80c1e8182b030540609c3c130181f0503c0607416bf84d7b09aee0b5cc0e3f81c7b038ee071cc0e2f81c5b038ae0714c15bf07a76094bc129580d2701a46052fe0e5ec1cbb82973072be125781cad83957072a60e5480ca78194d03296065280ca3819460728a0e4d41c9483925030fe0a1f80c3d8187a030ee2e1d80c3981872030be121780c2d8185a030ae121580c29818520309e061380c26818350f068060a40c14018251f0480607c140f0181d03ad6075a40eb381d6303ac2231bc463688c67118ca0b17c462b84b6f096da32dac4db484b67096ca32d8c4db082b5f0b6b612d5c15a988b4b0968e069bc0d3681a6b034d20699c0d3281a63034c20697c0d2d81a57034a60692c0d2381a3f03476068dc0d198296f052da0659c0cb28295f032ae124fc249b8192f0324e0e1bc1c368386b050d20e19c1c3282863050c20a17c1c2d83857050a60e12c1c238383f1907c0e0ec1c1b8383307064060bc0c1581827030460e06c1c0b87d7f11afa1f5dc3eba82d6f11ace131fc263e87c7b0f8f2131dc263a87c73138e20b1bc2e3584c67058c62316c262b81b7f036fa06dec0dbc81b77036ea06dcc0db881b6f036d606d9c0db181b5b036ae06d3c0da581b47036860a9fc153f02a7d054de0a9b8153108a5a0f4ac1293c252381a3f0346e0e5fc1cbe8397b072f20e5dc1cba83973072e20a5bc1cb583967052c60e56c1cab8394f1929c0e52c1ca38394307284064fc0c9e8193b03274064dc0c9b039350725a0e4ac1c9383925030fe1e1f80c3ece07c030f6061e80c3c81878030ee1e1d80c3a87874030e6061c80c3881870030de0a1b80c358186a030ce2e1980c3181862030b6061680c2b888560309e321380c258184a0308e121180c21818420307e060f80c1e8182d03056060a80c13878260304a1e0900c0f8281e0303a0b1bc163582c67058c606dbc0db581b67036c606d3c0da581b47036860a99814b78296e032d6065a80cb381966032c60658824a78494e092961252824a38494609286125080c9f8193e050de0a1ac1433828630709e121381c2583847070860e1080c1f8183b03074060dc0c1b0281b050340a06416bf82d7b05aee0b5cc0e3f81c7b038ee071cc0e2f81c5b038ae0714c15bb02a7e094bc129580d2701a46052fe0a5ec14bb82973072be125781cad83957072a60e5480ca78194d03296065280ca3819460528a0e4a41c94039250d248061fc143f0187b030f4061dc143b01873030e40617c242f0185b030b40615c242b01853030a40613c0c270184d03052060a00c12cc0240303e0a0780c0e81d6f03adc075b4463788c6d118d62319c463288c63058be2316c462b82c530b6de12db45db589b690b6ce12d9465b189b61056be32d742dad85b57196aa0ad4c2da788b4b0b68e22d0c0d3781a6d034d6069a40d3381a65034c6069840d2f81a5b034b20695c0d2981a510349e0692c0d2381a430347e068ec0d1b81a33272de1e5b45cb58b9670f2ca4e58c14af8b95b172ae0a54c44a78894b1128e2250c649f8593b0b26e324cc0c978192b0324e0648c14378286d050d60a1a41c3383865070c60e184142f8385b070b20e15c1429838510709e0e12c1c23838430707e0e0ec1c1b838330305e060ac0c13818230703e0e06c1c0b8381311ade235ac46b388d63198de331ac66338cc63118be2316c462b88c53036de06dac0db381b63036be06d6c0dab81b530369e06d2c0da381b43a04df3c9ae6933cb263114be2296c452b88a531949e3292c65238ca430347e068ec0d1b81a33072de0e5ac1cb383963072be0e56c1cab839530729e325381ca583947072860e5080c9f8193d03276064e80c9b819360726a0e4bc1c958392707246061bc2c370186b030d40619e503301863030c40617c0c2d8185a030ae221580c298184f1909c0612c0c25018470908c0610c0c210183f0307c060f40c178182b030540609c3c13018230303e0e0780c0e82d7f09af6135dc16b981c7f0b8fc071f40e3b81c75038e6071c80e2f81c5b038ae0714c0dbb90b76036ea06d7c25af01b5b036b406d5c25ab01b53036a406d3c0da701b4d274ec0a5f85cbb0495e092ac065380ca30193e03278064d8149a0287f070f61a1dc14398485f070b61215c1c298184f030960611c0c218183f0307a060ec1c1c818370d06a060cc0c18838290d02a075bc0eb684b6f096da12dac25b484b67096ca12d8c25b082b5f096b612d5c15a982a6f054da0a97c0d2d81a530547e068ec151b81a33272ac1a1bc34368286b050d21a19c343283863050c20a17c1c2d86857050a6120fc1c1d8483707066060bc14158282703046079fc0f3f01e7d098fe131f4163d84c79058ee131d4263984c71058de131ac263382c63056fe16df82dbe82b6f0b6dc06dac0db481b630b6c406d8415a781b4b0568e06d0c9d331097e8e2f80a5d814ba0296e172cc1253824a30193e0526c1a1fc343e8287b070f20a1dc343a83873070e20a1bc1c3586867050c61213c1c258484707086060fc141d82837030660e0a4340a84b6f096d612d9c25b184b5f096b612d5c25a987a6f0f4d61e99c3d3185a5f274b64e95c2d2984a3f09476128dc25198796e052bc1a1bc1c35838690d0ce0e18c1c308585f070b61a15c1c298483f07076120dc1c198682f070561a09c1c1186815096de12db425b584b69096ce12d9425b184b61096be12d6c25ab84b53314de0a9b45d3581a69174ce0a994c53181a610b4be2e96c5d2b85a530947e128ec251b84a330d0de1a1b41c35838690d0ce1a1941c31828610b0be1a1741c2d868570d0aa0e14c241f8383b0906e0e0cc34178382b0d04e0e08c163782c6b058ce0b18c15b782b6e056d60ada815b382b66056c60ad8815a782b4e0569612d2815a382b460568612d08153781a6b054ce0698c152781a4b0548e0690c14378286b050ce0a18c24278384b0908e0e10c141f8683d05076060e4141b8283503066060c40c178682d050560a09c141281823098de131ac263384c63316df20dae31b398b630969e12d2c25a384b438a4cc165ba20b30494e0928c064fa189b0686f070d61a19c1c318484f070961211c1c218683f070761a0dc1c19838290d02a0b9fc473b82d7f0baf6135dc16b988d6b09ace071fc2e3f01c7d038ee071d40e3981c72038d6071a80e3388c66038be0716c0e2b81c53036ee3edd80dba81b6b036d406d9c45b301b5f196bc06d6c0dad01b57096ac06d4c0da901b4f0369c06d34153f87a77094be1295c0d2781a470347e068f40d1b87a35052fe0e5ec1cbd039771f2ec0a5cc1cb583967072be0e56c1cab839530329e0652c0ca3819430327e064f40c9d839390326e0e4d40c99819310725a0e49c1c928287f050fc0e1ec1c3d03877170ec0a1cc14390386b070d40e19c44330385f130bc0e16c1c2d03857090ac0e14c1c290184f0309c0612c0c25018470308c0610c0c210183f0307c060f40c1e0183b030740e0e4141c018370306c0e0d4141a0183303064060c40c18038270d04c0e0940eb781d6d05ad60b5a41eb381d6505ac60b584463788c6d118ce23194162f88c57096de12db44db589b69096ce12d944db189b61056be16d6c25ab82b531169612d1c153782a6d034d6069a4153382a65034c606984152f81a5b054ae0694c0d2588a4a0548e22918151f81a3b0546e068cc34b78696d0f2ce1a59414af879570927e124dc0c9782927070de0a1b41c3582867050ca0a17c1c2d8385a070ae3e15814298384b0708e0e0fc1c1d8383707066060bc141582827030460e06c1c0b81e7f03cfc079f446bf88d7d05aee235d416b788d67098fe131f4163d8cc79058ee131d44e398cc71058de171ac263382c63118b61315c15bf85b7e0b6fa0adbc2db701b6b036d206d8c2db101b61036b622d6815ab88b560569e06d2c15a381b430f4fe1e9f4153b87a75054de1e99c252784a470347e0a8dc1cbf8397d052f60e5e414bb83975072e60e5c414b78396b072d40e59c7cb302963072b60e55c1ca78394b0728e0e50c0c9f8293b0526e064cc1c96839270724a0e1fc843f0387d800f80a1ec143d03879050f00a1dc143b03875050e80e1cc1c3903871070e00a1bc14370386b070d40e19c5c3302863050c40e16c1c2d03857110ac0e13c4c270384b070940e11c24230384307084060fc0c1f0283b050740a0dc141b01833030640e09c341303825 20 1048575 8 255 11 2047 19 524287
def cc_58_3 : Nat → List (Nat × Nat) := unpackCursorV4 0x9ed6199e4f9148a8c54f8586d7e573782637334f72a096af7b648675f94f5b94058c2d539534ba7f49d1d4732a4442f402423be4435b6331b402cc4f24c801e567184611374d12d0a0b47904d670004d 0x2eb785d6b0bace1758c263784c6e098d6171a8263384c66098c617188262f84c5b238b41315c262b04c53096de12dac25b384b63096be12d6c25ab84b530769e0ed381da685a6f0b4d61699c2d3188a5f1b4b63695c452984a4f1b49a1292c0d2484a470948a1290c0d2084a3f09476128dc25198496f092d61259c24b18495f092b61255c24a98494f0929a1252c24a38494509286124fc249d8493709266124bc24958492709246161bc1c3585867070c61a17c1c2d86857070a61213c24270684d0907e120f81c1d8383907066120c81c188682f070561a09c1c118481f070361205c1c0983d6b05ad20f59c1eb182d61118de231b4463388c650b8be1715c25b784b6d096d612da425b384b65096c612d8425af84b5b096ae12d4c25a584b47134de0a9b46d3581a69134ce0a9946d3181a610b4be1696c2d2b85a53114962291c251f84a3b0946e128cc24b78296d072ce0a59424af83957092941e518249f849370925e1249c1c378386d070d60e1a41c3383865070c60e1841c2f8385b070ae0e14c1c25838470707e0e0ec1c1b838330705e0e0ac1c1383823070360e05c3ebf88d7d0faee1f5d42eb785d67098fe131f4263d84c79098ee131d4263984c71098de131ac263384c63098b61315c3dbf89b7d0f6f606de43dbb87b750f6e606dc42db785b6b0b6ce16d8c45ad88b570969e12d2c25a384b43094fe169f8253e84a6f0b4dc12988252d07a560949e1291c251f84a37072fe1e5f81cbe8697c072f60e5e41cbb83975072e60e5c81cb883970072de0e5ac1cb383963072b60e55c1ca78394d072960e5281ca3849460728a0e4fc6c9f0393b0726e0e4cc1c990392d072560e49c1c928387f0f0fc0e1f7e83e0387b070f40e1e41c3c038770f0ec0e1d43c3a03873070e40e1c41c380386f050dc0e1b42c360386b070d40e19c2c3303865f60c80e18c14310385b070b40e15c442b0384f0909c0e1341c1f8183e070760a0e81c1b8283607066060c81c168382b070540e09c2413038250f0480e07c1c0f0381d07ad60f5a41eb383d6307ac21f1bc463687c670f8ca2317c462b84b6f096d612da425b384b63096c212d7c25ad84b57096a612d2c25a387a6f134da1e9ac3d3387a650f4c62697c5d2d89a57174a62292c452384a3f09476128dc25198496f0b2dc125b424af8795e072ae1254824a5079460927e124dc249784927070de1e1b81c3583869070ce0e18c1c3103861070c00e17c1c2d83857070a60e12c1c238383f070760e0dc1c198382f070560e09c1c118381d070360e05c1c0a83d6f07adc0f5b4463788c6d118d62319c463288c630b8be171742e2d85c57118aa1714c25b782b6d0b6d616da425b384b650b6c616d8425af85b5b0b6b212d5c2da985b510969e16d2c25a385b43134de0a9b45d3581a69134ce0a9946d3181a610b4be169742d2d85a57134aa1694c452788a4b1148e2290c2d1f84a3b0946e168cc9cb78796d092d62e59c3cb2849630b2be1657424ad85957f62aa1254c44a78494b1128e1250c249f8493b0926e124cc6c978492b1324e1248c1c378286d070d60e1a41c3383865070c60e1841c2f8385b070b20e15c1c29838510709e0e12c1c23838430707e0e0ec1c1b838330705e0e0ac1c13838230703e0e06c1c0b8381305ade0b5ac16b382d63058de0b1ac163382c63098be2316c262b88c53056de0adb815b582b6a056ce0ad9815b182b62056be0ad6c45ad02b57056ac0ad4c15a782b4e0369606d2815a381b46056861ad08153781a6b054d40a99c153301a63054be0696c452d02a57054ac0694c152782a4e034960a91c0d2189a420547e0a8f8151e8296f052d60a59c14b18895f092b62255c24a98494f092961251c24a18293f0f27a0a4ec149b8293505266064bc6c968292b0524e0a4940c918286f050d60a19c14318385f070b60e15c1c298384f070960e11c1c218183f0307c060f4141d828390506e060d4141982832070620e0c00c178182e050560a0a4141381823030440e0841c100381f070360e05c1c0985d6f11ad62359c2eb184c6f0b8d61319c2e3184c5f118b61315c462985b6f1b6d626d9c2db188b5f116b622d5c45a989b4f0969612d1c4da185a6f094d7f099c253188a5f094b62295c252984a4f094961291c25218da3f09476268dc25198396f072d60e59c1cb18395f072b60e55c1ca98394f0729a0e52c1ca5039470928c0e5141c9f8d93e072760e4dc1c99839320725e0e4ac1c9383923070de161b81c358386a070cfe81981c3183862070be0e16c1c2d03857110ac0e14c1c278684e0709a0e0fc0c1f0383b070740e0dfc81b03833030640e0bc1c158382a0704e1e0981c118381f0703c0e0740eb581d6903ace0758c0eb082c6f058da0719c0e3282c5f038ae16dbc25b68db6b136d216d9c25b28db63136c20ad7c2dad85b57056a622d2c2da381a6f034da069ac0d3481a67034ca0698c0d3081a5f034b60695c0d2981a4b0348e068fc0d1d81a3703466425bc3cb6909670f2ca0a57c84ab8d93f0b26e064bc0c938286f050da0e1ac1c3486867050ca0e18c1c308285f070b61a15c14298384b0d08e1a0fc341f0383b0b06e0e0cc44190182f030560609c0c118381b0d02e4aa300d440aa84035001e9f00d3c13a74034e01e61016bf82d7e05afa0b5bc16b702d620b8fe131f4563d89c790b8ee131d46e3989c71058de171ac2e3382c63118b61715c0dbf81b7d036f606de40dbb81b75036e606dc40db781b6b036ce06d8c0dad81b570369e06d2c0da381b43034fe4a9f80d3ef727c034f6069e80d3c81a78034ee2a9d80d3a8aa74034e6069c80d3881a70034de0a9b80d3581a6a034ce2e9980d3181a62034b6069680d2b88a560349e369380d2581a4a0348e129180d2181a420347e068f80d1ef617f0f2fa2a5dc3cba8296f2f2ce3653c2ca38193f0326e064bc0c96819270f24a1a1fc343e8387b070f21a1dc343a83873070e20a1bc1c3586867050c60e16c342b8684f0d09c0e12c2c238384311084060ec0c1d038390306e060d80c19818310304e0609814128381b0d02e075bc0eb701d6d278de2b1b446358bc67158ca2318c162f88c5b178ae0b14c2db784b6d176d626da42db384b651b6c626d8415af85b5b0b6ae0ad4c2da78db4b0b68e22d0c0d3781a6d034d6069a40d3381a65034c6069840d2f81a5b034b20695c0d2981a510349e0692c0d2381a430347e068ec0d1b81a33212de1e5b45cb58b9670f2ca4258c14af8b95b172ae0a54c44a79094b2728e2250c6c9f8593b0b26e364cc0c978192b0324e0648c34378686d070d60e1a4143382865050c60a184142f8685d070b61a15c342a828530d09e0e12c3423838430d07e0e0ec2c1b838330305e060ac0c13818230d03e0e06c340b8381315ade0b5b856b58ed6a15ace2b59856b182d62118de2319c0e2f81c5e038ba32dbc6db58cb671b6c62ad7c25ae8ab5b136b22ad5c25aa8ab53136a222d2c45a381a6f034d60699c0d3181a5b034b20695c0d2981a5103496069240d2381a410347e068ec0d1b81a331d2de3a59c54af8795d152ae1e55444a68a9451b27e324dc0c97819270d0de0e1ac3433838630d0be1a1741c2d86857050aa1a1341c25868470d08a1a0fc1c1d8683707066060bc0c1581827030460e06c340b82d7f09af6135dc16b981c7f038f6071dc0e3981c5f038b60715c0e2981b7f056fc06dec0dbd01b77176ec06dcc0db901b5f096bc06d6c0dad01b57096ac06d4c0da901b4f0369c06d34153f07976092bc125580ca7019460327c064f00c9b0f934050fe0e1ec343b82873090be121781c2d84857070a6121480c258184a070920611c0c230184303082060dc0c1b028350d04a0e064340a8ad760facc131b44e3484c65138c22b1640db681b69036ca06d84153f01a7a174ec069c8553701a6d154d8069a80d3481a68154cc06994853201a62034c2069806d2701a4a0948c069080d1f01a3d0d0da0e1a43432838610d09c221080c1d038390306c060c40c130282503ade075b80eb381d6303ac40b1bcbe3390c5f158ba4315c562a82b6f0b6d612d9c15b184b5f096ba36d6c4dac84b57096aa36d4c4da88db4b0968e069bc0d3581a67034c60697c0d2e81a5b034b20695c0d2a81a53034a20692c0d2381a3f03476068dc0d198296f032ce0a57c14ae81957032aa425283ca30493f0926e064bc0c938286f070d61a19c14318285f050ba0e16c1c2c86857050aa0e14c1c288384b0d08e1a0fc341f0383b0906e0e0cc6c190182f030560609c0c118681d070361a05c340a87d7fe2afa1f5dc3eba82d6f2face131fc263e87c7b0f8f2131dc263a87c73138e20b1bc2e3584c67058c63716c262b81b7f036fa06dec0dbc81b77036ea06dcc0db881b6f036d606d9c0db181b5b036ae06d3c0da581b4703686069fc3d3f01a7de04f8069ec0d3d01a79034f0069dc3d3b01a750f4e8069cc0d3901a71034e0069bc153701a6b034d40699c5d3301a63034c40696c0d2d01a571d4ac0693c6d2701a4b034940691c252301a4303484068fc0d1f01a3d052fe0a5f814be8296f052dc0a58b70ad079560929e1251c0c9f819370325e064b40c93879250d0fe1a1f41c3d838790d0ee1a1d41c3983871050de0e1ac343382863070b61a15c34278684e070961211c1c218d84203076060e81c1c818370306c060cc0c18818270304c0a094340e8381b0d02e1a0543d3f01a7d214f8069e83d3b01a750f4e8069c8153701a6a174cc06988252701a4a0948c069080d1f01a3d0f2fc0a5b8242704842030740e0e40c1b018310304c0a094340a84c7d098f2131d4263881b7d036f206dd40db88ea7e034fa3a9f00d3d01a79034f02e9d80d3a8ba74034e4069c40d3802a6e034d42e9980d3104a4e03494129180d2101a3e0347a1a1f41c3c86875070e21213824210183a07072060d80c18818260504a131bc263584c67098c63adbc15b710b6b176d442d9c5db30eb63056c412d3c25a704b4b0969412d1c25a304b4309684069bc0d3581a67034c60693c0d2581a4703486068ec0d1c8686f070d61a19c1c318484f0909c0e12c242383843090841a0dc141a8182b030540609c0c130182309afe135ec26bb84d73038fe071ec0e3b81c73038be0716c0e2b81c53036fe16df80dbd81b7a036ee42dd80db981b72036be12d780dad81b5a036ae12d580da981b520369e06d380da6ee2760346c1e8d014bf6d176092bc125580ca7019460327c064f00c9b6c1340d0fe0e1ec343b83873090be121781c2d84857070a6121480c258184a070920611c0c230184303082060dc0c1b06835070321a054173f07e76098fe371ec263b8dc730f8d2131940dbf81b7b036ee06dcc0db481b650369e06d2c0da381b43034fe169f80d3d81a7a034ee4e9d80d3981a72034d2069a00d3287a64034aa2a9500d278da4e03496069280d2384a4603486069080d1f81a3e0347a1e5d80c93079240d0fe0e1ec343b83873070d21a19434278684e070961211c1c218884203076060e81c1c818370306c060cc0c18818270304c1a094c6b788d6beaace2358c66378dc6b198ce3718c462f8dc5b198ae2314c0db781b6b036ce06d8c0daf81b5b036ae06d4c0da781b4b0368e06d0c0d3785a6e034d6069a80d33f4266034c6069880d2f81a5b034b40695f992b01a530349e369380d2581a4a0348e129180d2181a420347e068f80d1e9896fe42d7bc59cc4b18895fd62b7a855c44a98d94f192963251c6ca18193f03276064dc0c998192f0325a064ac0c9387925032461a1bc1c3586867070c61a17c1c2d86857070a61a13c34270384b0d08e0e10c6c210183b030740e0e40c1b8183603066060c40c13818260d04a1a07c1c0d86817070260b5fc16bd82d7705ae60b1fc0e3d82c77038e60b17c0e2d82c57038a60adf8153b04a5e094ac0693815230297f052f60a5dc14b98395f072b60e55c1ca98194f0329c0e53414a38294503286065081c9a839290724a0a1fc143f0287b050f40a1dc143b02873050e40a17c242f0285b050b40a15c242b02853050a40a11c1423028450506a1e0d01414828280504a3e0900c0f8181e0303a0b5ac16b482d6705ac60b584463788c6d118ce23194162f82c57096de12db44db589b69096ce12d944db189b61056be0ad6c15ab82b531169612d1c153782a6d034d6069a4153382a65034c606984152f81a5b054ae0694c0d2582a470547e068ec151b81a33052de0a5b414b382965052be0a55c44a5079460927e124dc0c9782927070de0e1b41c3581869070ce0e1940c3181861050be0a16c142b82853070960e11c1c1f8383b0706e0e0cc0c178282b0504e0608c1c0d838170fafe235f43ebb87d7505ade0b59c263f84c7d0f8f61f1e4263b84c750f8e6271c4163782c6b058ce0b18c462d84c57056fe0adf40dbd81b79056ee0add40db981b71056de06dac15b381b63036b60ad5c15a781b4b0568e06d0c153f82a7e054fa0a9bc153702a62114b41e958252784a470347e0a8dc1cbf8397d072f60e5e41cbb83975072e60e5c414b78296b052ce0a58c1cad839570729e0e52c1ca3839430327e064f81c9e829370526a064cc0c990392d072560e49c1c928287f0f0fc0a1f7383e0287b050f40a1e4143c028770f0ec0a1d43c3a02873050e40a1c414380286f050dc0a1ac143502867050cc0a18c14310285b050b40a15c442b0284f1909c0a12c1425028470908c0a10c1421028370506c0a0d414168282b050540a09c3c13028250f0480607c0c0f0181d05ade0b5b816b682c6f058da0b1ac163388c65058c60b17c162d82c57058a60adbc15b682b6b136d20ad9c25b282b63056c20ad7c15ad82b57056a616d3c45a585b47116860a9bc153681a6b034d20a99c153281a63034c20a97c152e81a5b054ae0a9540d2982a4f034960a91c0d2182a3f034760a8dc0d198296f052da0a5ac14b387965052c60a57c14ad82957052a62253c44a58894711286264fc2c9d8593713266064bc149582927032460a1bc14368186b030d20a19c1c3282863030c20a17c142d83859050ae0a14c14288384f070960e11c1c218383f070760e0dc1c198182f050560a09c0c118381f070360e05c1c0982d6f11ad62359c16b182c6f138d63319c163188c5f118b62315c462982b6f036d60ad9c0db182b5f036b60ad5c0da982b4f036960ad1c0da182a6fd04d79899c153188a5f114b62295c452989a4f194963291c4d2181a3f054760a8dc0d198296f072d60e59c14b18395f072b60e55c1ca98394f072960e51c1ca18193f0327c0e4f4149b8393503266064c81c978392b0724e0e48c14378586e050d60e1a81433e5066050c60e1881c2f8285b070b40e15c442b028530709e3213814258384a0708e121181421838420506e1a0d81c1a8382f050560e0a81c1387826050460607c0c0f0181d05ade0b59c163782c6b058ce0b18c462d85c57056de06dac15b381b63036b60ad5c15a781b4b0568e06d0c153782a6e054ce0a98c153102a5b054b40a95c152b09a4f1349c1692c252505a470948c2690c4d2101a3f0347c0a8ec151d02a370546c068cc0d190296f052ce2653c2ca38193f0526e4a4bc3c96929270f24a0a1bc143582867050c60e16c342b8684f070961611c1c218183f050760a0dc0c198182f0305a0e0ac1c14868270304a0e08c1c108381b0d02e0ae3055c402b84257000adf09dbc02b740f6e01e6103c9e02d7f05afc0b5f416b782d6e05ac4171fc263e89c7b138f2171dc263a89c73138e20b1bc163582c67058c62316c2e2b82b7f056fc0adf415be02b7b156f40ade455bc02b77056ec0add415ba02b73256e40adc719b802b6f056dc0adac15b502b67056cc0ad8c15b102b5b116b40ad5c15ab02b4f0569c0ad2c25a502b470568c0ad0ef1a102a7f054fa069ec0d3c82a77054ea069cc0d3882a6f034d60a99c0d3181a5b054ae0a93c0d2582a47034860a8fc151f02a3dc42fe1e5f454bb87975052de0a59c4ca7859470527e1e4f4149b829350325e0a49c343f8687d070f60e1e4343b86875070e60e1c414378286b050ce0a18c1c2d868570d09e0e12c2c23838430307e060f80c1e8182f0305c0a0ac141481823030440e0841c0d8681705ade0b5ac16b382d63058de0b1ac163382c630b8be2716c2e2b88c53056de0adb40db582b67056ca06d8c15af81b5b056ae06d4c15a781b4b0568e06d0c153382a66054ca0a97c152d8aa5a054ae0a958152982a4f0549c0a92c252502a470548c0a90c4d2101a3f0347c0a8ec151d02a370546c068cc0d190296f052d60a59c14b18895f272b64e55c44a98994f0b2961651c4ca18193f052760a4dc0c998292f0f25a0a4ac149382925052460a1bc14368286b050ce1a19414318685f070b61a15c1c298684f070961611c1c218183f050760a0dc0c198182f0305a0a0ac1414828270304a0a08c1c108681f070361a05c1c0982d6f11ace0b1bc4e358cc67058c62316c462b82b6f036d60ad9c0db182b5d036b60ad5c15aa82b4f036960ad1c0da182a6f054dc2a9ac55350aa671d4cc0a98c153102a57054ac0a9544d2789a4e1549612928552384a461348626908151d82a3a0546e0a8d80d198296f1d2ce2653c64a38193f0526e2a4bc3c968a9270f24a0a1bc1c3586867050c61a1741c2d868570d0aa1a13c1c258684707086060fc141d8283703066060bc0c16868270304a0e08c1c0d86817 20 1048575 8 255 11 2047 19 524287
def cc_58_4 : Nat → List (Nat × Nat) := unpackCursorV4 0x9ad3f9852895e279124c8c64c87c4a7ff7d7827d7057d68a7b608825a7615485f4e3654855e43b4a40e2d3d13d3923f3672b3283f2fa2e2bd3d2893425336233201b47f1872d104830c4400616300061 0x3d6f03d6e03d6d06c6f06c6705c5f08c5705b6f06b6b05b6706b6305b5f05b5b05b5705b5308b4b05b4706a6f06a6b06a6706a6305a5f0ea5b0ea5705a5308a4b08a470ca3f05a3b05a370ca330696f069670595f0e9570c93f05937a012f9f1270386f0686e0386d0385f0285e0385b0385703853028520384706846038450383f0383b03837038330382f0382b03827038230381b0381a038170781603e7e03e7d04c7d09c7904c7509c7101b7d01b7901b7501b710ea7e01a7d0ea7c01a7a01a7901a780ba7601a750ba7401a7201a7101a7002a6e01a6a0ba6601a620ca4e01a4a04a4601a420794e01936019260287d03869038610182d03829038250182103e7e02e7d04c7d09c7904c7509c7102b7e02b7d02b7c0bb7a02b790bb7802b7602b7502b740eb7202b710eb7002b6e02b6a02b6602b6202b4e04b4a02b460cb4202a7d01a7902a7501a710193e0192e0287d03869028610383d02839028350383103d6f03d6e03d6d08c6f06c6d06c6706c6505c5f08c5d08c5708c5505b6f04b6d0bb6b09b6905b6704b650cb6309b6105b5f05b5b05b5705b5308b4b05b470ea6f02a6d0ba6b01a690ba6702a650ea6301a6105a5f0ba5b0ba5705a5308a4b08a470ca3f05a3b05a370ca330e96f0796d0b967079650595f0b9570c93f059379d12f9c1270386f0286d0386703865038630385f0385b038590385703853038510384b038470383f0383b03837038330382f0382b03827038230381b0381702d6f02d6702c6f02c6b02c6702c6308c5b08c5702b6f02b6e02b6b02b6a02b6702b6602b6302b6202b5b06b5a02b5702b5602b4f02b4e02b4b04b4a02b4702b4602b4309b4202a6f01a6b02a6701a6301a5b08a5a02a5702a5602a4f01a4b02a4701a4302a3f02a3e02a3d0296f029670994f099470293f0793d02937029350192f029270286f0286b02867028630385b038570384f0384b03847038430183f0183d0283701835028330182f0282b028290282701823038210381b0381708d6f08d670cc6f0cc6b0cc670cc6308c5b08c570eb6fa936ba73670eb6308b5b08b570cb4f0cb4b0cb470cb430ea6fa52670ca4f0ca47a323fa12370396f0396b0396a039679e166039630395d03957039550394f0394b03947039430393f0393b03937039330392b039270386f0586e0386b0386a038679b06603863038620385706856038550384f0c84e0384b0384a038470484603843038420383f0183e0383b0383a038379a03603833018320382b0382a038270782605e7f02e7e05e7b05e7a05e7705e7605e7302e7205d7f05d7703d6f03d6e03d6d04c7f05c7e04c7d04c7704c7505c7305c7204c6f04c6d05c6b05c6904c6704c6505c6305c6105c5b08c5a04c5705c5604b7704b7604b7505b6f05b6e05b6d05b6c05b6b06b6a05b6906b6805b6705b6605b6505b6405b6306b6205b6108b6005b5b08b5a05b5705b5605b4f05b4e05b4d05a7f05a7b05a7705a7306a6f02a6d06a6b01a6906a6702a6506a6301a6108a5b08a5705a4f04a4b04a4705a4305a3f15a3d05a3b01a3905a3705a3505a3301a310597f059770696f0796d06967069650494f049470593f0793d05937059350d92f099270587f0387b0587a0587705876038730385b03859038510584f0384b04847038430583f0683d0383b03839058370583503833038310682f0382b06827038230381b0681702e7f02e7e06e7b08e7a06e7706e7602e7302e7202d7f08d7703d6f03d6e03d6d02c7f05c7b05c7702c7305c6f04c6d06c6b06c6905c6704c6506c6308c6108c5b05c5701b7f05b7e01b7d01b7701b7501b7301b7201b6f01b6d01b6b01b6901b6701b6501b6301b6101b5b01b5a01b5708b5601b4f01b4b01b4701b4301a770ea7601a7501a6f06a6e01a6d02a6c01a6b01a6a01a6901a6801a6706a6601a6502a6401a6301a6201a6101a6001a5b01a5a01a5708a5601a4f0da4e01a4b01a4a01a4704a4601a4301a4201a3f01a3e01a3d0297f0e9770696f0796d06967069650d94f059470193f019370192f0192d01927079250287f0387b0887a0687706876028730385b03859038510684f0384b05847038430183f0183b01837018330182f0182d0182b03829018270682501823018210381b0681701e7f01e7e01e7d06d7f06d7e06d7d06d7c02d7b02d7a06d7902d7802d7702d7606d7502d7406d7308d7206d7108d7002d6f02d6e06d6b08d6a06d6706d6602d6302d6208c7f08c7d02c7708c7502c6f08c6703c5f03c5e03c5d05b7f04b7d02b7b15b7902b7704b7509b7315b7102b6f05b6b05b6702b6305b5f04b5d06b5b06b5905b5704b5506b5308b5108b4b05b4702a7f05a7e05a7d02a6f05a6e01a6b01a6901a6305a6201a6102a5f02a5d01a5b01a5902a5702a5501a5301a5101a4b08a4a02a4708a4602a3f01a3b02a3701a331097f0797d02977079750296f0e9670695f0795d06957069550993f059370192f029270687f0687d0287b03879028770687503873038710286f0386b0886a0686706866028630384b03849038410683f0383b05837038330182f0282b02827018230381b0681702e7f02e7e06e7b08e7a06e7706e7602e7302e7202d7f08d7703d6f03d6e03d6d02c7f05c7b04c7702c7304c6f04c6d06c6b06c6904c6704c6506c6308c6108c5b04c5702b7f05b7e02b7b15b7a02b770db7602b7305b7206b6f06b6e08b6d08b6c02b6b06b6a02b6902b6806b6706b6606b6506b6402b6306b6202b6102b6002b5b08b5a08b5708b5601b4f01b4e01b4d02a7f01a7b02a7701a7302a6f02a6d01a6b01a6902a6702a6501a6301a6101a5b02a5701a4b04a4a01a4902a4704a4601a4301a4102a3704a3604a350297f1d9770696f0796d06967069650494f049470293f0793d0d937079350192f029270287f0387b0887a0687706876028730385b03859038510684f0384b04847038430283f0683d0383b03839068370683502833038310182f0282b02827018230381b0681705e7f02e7e06e7b08e7a06e7706e7605e7302e7205d7f08d7703d6f03d6e03d6d04c7f05c7b04c7705c7304c6f04c6d06c6b06c6904c6704c6506c6308c6108c5b04c5701b7f01b7b01b7701b7301b6f01b6d01b6b01b6901b6701b6501b6301b6101b5b01b5701b4f01b4d01b4b01b4a01b4704b4601b4501a7f05a7e01a7b01a7a01a771ca7601a7301a7201a6f06a6e01a6d08a6c01a6b01a6a01a6901a6801a6706a6601a6506a6401a6301a6201a6101a6001a5d01a5b01a5a01a5708a5601a550aa5401a4f0ca4e01a4d01a3f01a3e01a3d0597f1b9770696f0796d06967069650494f049470193f019370192f0192d01927079250587f0387b0887a0687706876038730385b03859038510684f0384b04847038430183f0183b01837018330182f0182d0182b0182a03829038280182701826068250682401823018210381b0681706d7f06d7e06d7d06d7c06d7b07d7a06d7907d7806d7706d7606d7506d7406d7307d7206d7108d7005d6f02d6e06d6b08d6a06d6706d6605d6302d6203c5e04b7f04b7d07b7b07b7904b7704b7507b7315b7104b6f05b6b04b6705b6304b5f04b5d06b5b06b5904b5704b5506b5308b5107a7f1ea7d07a7b01a7907a7707a7507a7301a7105a6f0ea6b0ea6705a6306a5f02a5d06a5b01a5906a5702a5506a5301a511da3f04a3b04a371ba330597e0596e06956069540687f0687d0387b03879068770687503873038710586f0386b0886a068670686603863038490683f0383b04837038330682f0382b06827038230681505e7f05e7e06e7b08e7a06e7706e7605e7305e7203d6e04c7f04c7b04c7704c7304c6f04c6d04c6b04c6904c6704c6504c6304c6104b7f04b7e04b7b07b7a04b7704b7604b7305b7204b6f04b6e04b6d04b6c04b6b06b6a04b6906b6804b6704b6604b6504b6404b6306b6204b6107b6005a7f0da7b09a7705a7306a6f08a6d06a6b01a6906a6706a6506a6301a6104a4f04a4b04a4704a4304a3f07a3d04a3b01a3904a3704a3504a3301a3104946049360792e0587f0387b0887a068770687603873038590484f0384b04847038430483f0683d0383b03839048370483503833038310682f0382b068270382306e7f02e7e06e7b08e7a06e7706e7606e7302e7203d6e04c7f0dc7b04c770dc7304c6f04c6d06c6b06c6904c6704c6506c6308c6101b7f01b7b01b7701b7301b6f01b6d01b6b01b6901b6701b6501b6301b6101b4f01b4b01b4701b4301a7f05a7e01a7b01a7a01a771ca7601a7301a7201a6f06a6e01a6d08a6c01a6b01a6a01a6901a6801a6706a6601a6506a6401a6301a6201a6101a6001a550aa5401a4f0da4e01a4b01a4a01a4704a4601a4301a420794e01936019260687f0387b0887a068770687603873038590684f0384b04847038430183f0183b01837018330182f0182d0182b0182a038290382801827018260682506824018230182102e7f02e7e06e7b08e7a06e7706e7602e7302e7203d6e02c7f09c7b04c7702c7304c6f04c6d06c6b06c6904c6704c6506c6308c6102b7f05b7e02b7b1cb7a02b7707b7602b7305b7202b6f06b6e02b6d02b6c06b6b06b6a06b6906b6802b6706b6602b6502b6406b6306b6207b6108b6002b4f07b4e04b4b04b4a02b4704b4607b4315b4202a7f01a7b02a7701a7302a6f02a6d01a6b01a6902a6702a6501a6301a6102a4f01a4b02a4701a430193e0192e0287f0387b0887a068770687602873038590684f0384b04847038430683f0683d0283b03839028370683503833038310182f0282b028270182306d6f05d6e06d6b08d6a06d6706d6606d6305d6208c6f08c6703c5f03c5e03c5d0cb6f9836b0cb670eb6306b5f04b5d06b5b06b5906b5704b5506b5308b5108b4b08b470ea6f9726b962670ea6306a5f08a5d06a5b01a5906a5706a5506a5301a5108a4b08a479523f0ca3b0ca37942330e96f931670695f0795d06957069559213f0c9379112f901270686f0386b0886a0686706866038630384b03849038410683f0383b06837038330682f0382b06827038230381b0681701d6f01d6e02b6f05b6b05b6702b6305b5f04b5d05b5b05b5905b5704b5505b5305b5101a6b05a6a02a6705a6601a6302a5702a5502a3f01a3b02a3701a330286f0386b03867028630285f0285d0385b03859038570285503853038510383f0383b03837038330182f0282b028270182301e7f01e7e01e7d02c7f05c7b05c7702c7302c6f04c6d05c6b05c6905c6704c6502c6305c6101b7b05b7a01b7902b7705b7601b7301b7102b6705b6610b6502b4f01b4b02b4701b430297f0397b03977029730296f0396d0396b0396903967039650296303961039550394f0394b03947039430193f0293b02937019330287e058760286e0286c058668e0640584e048460183e028360381e02d7f05d7b05d7702d7301c7f05c7e01c7d01c7701c7501c7301c7201c5f01c5b01c5701c5301b7710b7601b7501b5f0cb5e01b5b01b5a01b5704b5601b5301b5201b4f01b4e01b4d0297f0397b0397702973039650395f0395b03957039530194f0194b01947019430193f0193d0193b03939019370393501933019310287e0b8760985e048560184e0184c01846028440183e0183c01836028340381e01d6f01d6d05b6f04b6d09b6b09b6905b6704b6509b6309b6102b5f05b5b05b5702b5302a6f02a6d02a5f01a5b01a5302a3f01a3b02a3701a330386f0286d0386b03869028670286503863038610285f0385b03857028530383f0383b03837038330182f0282b028270182301e7f01e7e01e7d05c7f04c7d02c7b0cc7902c7704c7509c730cc7102c6f05c6b05c6702c6302b7f05b7e05b7d02b6f05b6e01b6b01b6901b6305b6201b6102b4f01b4b02b4701b430397f0397d0297b03979029770397503973039710296f0396b0396702963039550394f0394b03947039430193f0293b02937019331087e8b07c02876028740286e0b8660984e048460183e0183c02836028340381e02c6f05c6b05c6702c6301b6f01b6b01b6a01b6705b6601b4f01b4b01b4701b4302a6f02a6e05a4f05a4e05a4b04a4a05a4704a4605a4305a4201a3f01a3e0286f0386b0386702863038550384f0384b03847038430183f0183b01837018330182f0182d0382b038290182701825018230182102d7f05d7b05d7702d7301c7f01c7d01c7b01c7a01c7705c7601c7501c5f01c5b01c5701c5301b7f05b7e01b7d01b5f05b5e01b5b01b5a01b5704b5601b5301b5201b4f01b4e01b4d0297f0397b0397702973039650395f0395b03957039530194f0194b01947019430193f0193d0193b03939019370393501933019310287e058760585e048560184e018460183e0183c01836890340381e05b6f04b6d0bb6b09b6905b6704b650cb6309b6105b5f0cb5d05b5b05b570cb5505b5312a6f02a6d0ba6b01a690ba6702a6512a6301a6105a5f0ba5b0ba5705a530ca3f05a3b05a370ca330386f0286d0386b03869038670386503863038610385f0385b038590385703853038510383f0383b03837038330382f0382b038270382302c6f02c6b02c6702c6302b6f02b6e02b6b02b6a02b6702b6602b6302b6202b4f02b4e02b4b04b4a02b4702b4602b4309b4202a6f01a6b02a6a02a6702a6601a6302a4f01a4b09a4a02a4702a4601a430286f0286b02867028630384f0384b03847038430183f0183d0283b02839028370183502833038310182f0282b028290282701823038210cc6f0cc6b0cc670cc638d36f8c36b8a367883630cb4f0cb4b0cb470cb430396f0396b0396703963039550394f0394b03947039430393f0393b03937039330586e870660c84e048460183e860360381e05d7f05d7e05d7d05d6f05d6e05d6204c7f04c7d05c7b05c7904c7704c7505c7305c7104c6f05c6b04c6705c6305c5b04c5706b7f0cb7e06b7d0cb7c06b7b06b7a06b7906b7806b770ab7606b750ab7406b7306b7206b7106b7005b6f02b6e05b6b05b6a05b6705b6605b6302b6206b5b06b5a06b5708b5603b4f03b4e03b4d09a7f09a7d0aa7b01a7909a7709a750da7301a7105a6f05a6b05a6705a6308a5b08a5705a4f04a4b04a4705a4306a3f02a3d06a3b01a3906a3702a3506a3301a311a97f0797d0a977079750596f059670494f049470693f0693d06937079350d92f099270687f0687e0687d0687c0387b038790687706875038730887203871038700586f0386b05867038630385b068570384b0484a03849048470484603843038410483704836048350682f0682e0382b0682703823088220381b0681705d7607d6604c6d04c6904c6504c6104c5902b7e05b7a05b7602b720ab6e06b6d0ab6c06b6a06b6906b680ab6606b650cb6406b6206b6106b6003b4e03b4d02a6d01a6902a6501a6102a3d01a3902a3501a310686d0386906865038610484a03849048460384104836048350682e0882207d7f8357d07d7707d7505d6f05d6704c7f04c7d04c7b04c7904c7704c7504c7304c7104c6f04c6b04c6704c6304c5b04c5706b7f07b7e06b7d0cb7c06b7b06b7a06b7906b7806b7707b7606b7507b7406b7306b7206b7106b7005b6f02b6e05b6b05b6a05b6705b6605b6302b6206b5b06b5a06b570cb5603b4f03b4e03b4d07a7f09a7d07a7b01a7907a7707a7507a7301a7105a6f05a6b05a6705a630da5b09a5704a4f04a4b04a4704a4306a3f02a3d06a3b01a3906a3702a3506a3301a310497f0597e0497d0496f0596e049620495a079560494f049470493f0493d04937049350492f049270687f0687e0687d0687c0387b038790687706875038730787203871038700586f0386b05867038630385b068570384b0484a03849048470484603843038410483704836048350682f0682e0382b06827038230c8220481d0381b048170681505e7e07e7604c7f04c7b04c7704c7304c6904c6505b7f05b7e06b7b06b7a06b770cb7605b7305b7206b6906b6806b6507b6403b4f03b4e03b4d05a7f0da7b09a7705a7301a6907a6504a4f04a4b04a4704a4306a3f06a3d06a3b01a3906a370ca3506a3301a31079760587f0387b068770387303869068650384b0484a03849048470484603843038410483704836048350682f0682e0382b06827038230882205d6f08d6b8456705d6304c6f05c6b04c6705c6304c5f09c5b04c5708c5305b6f05b6e06b6b06b6a06b670cb6605b6305b6206b5f06b5b06b5a06b570cb5606b5303b4f03b4e03b4d05a6f0da6b09a6705a6308a5f0da5b09a5708a5309a4f04a4b04a4709a4306a3f06a3d06a3b01a3906a370ca3506a3301a310596f0496b82167049630895f0495b81157049530494f0494b04947049430693f0693d0493b0693707935049330d92f0492b09927049230586f0386b06867038630685f0385b06857038530384b0484a03849048470484603843038410483704836048350682f0682e0382b06827038230c8220481f0381b068170381305d6f05d6b05d6705d6304c6f04c6b04c6704c6304c5f04c5b04c5704c5305b6f05b6b05b6705b6308b5f08b5b08b5708b5304b4f04b4b04b4704b4304a6f04a6b04a6704a6304a5f04a5b04a5704a5304a4f04a4b04a4704a4304a3f04a3b04a3704a330396f0396b03967039630395f0395b03957039530394f0494e0394d039470394503943039420393f0393b03937039330392f0392b03927039230386f0586e0386b0386a038670586603863038620385f0385b0385a0385708856038530384704846038450383f0183e0383b0383a038370d83603833018320382f0382b0382a0382704826038230381f0381e0381d 20 1048575 8 255 11 2047 20 1048575
def cc_58_5 : Nat → List (Nat × Nat) := unpackCursorV4 0x827feff8adef5fbc9aa7449ed8ff5a6d632dc05f6cab8ac5616028d6b50230988f917f2a16b23ee7e786ace11f9a73632e40563f498288f1fd1b65a2ab8449d706263099560738006cf0001b 0x3e7f03e7e03e7d06d7fc057d06d7706d7502d6f0fd6704c7f04c7d06c7b06c7904c7704c7506c7309c7102c6f05c6b04c6702c630dc5b04c5701b7f01b7d01b7b01b7901b7701b7501b7301b7101b6f01b6b01b6701b6301b5b01b5701b4f01b4b01b4701b4301a7f06a7e01a7dbf27c01a7b01a7a01a7901a7801a7706a7601a7506a7401a7301a7201a7101a7001a6f02a6e01a6b01a6a01a670ba6601a6301a6201a5b01a5a01a570ea5601a4f0da4e01a4b01a4a01a4704a4601a4301a420697f0797d06977069750296f079670494f0794e049470d9420193a01937019360192701926029250287f0287e0287d0286f0286e0386b038690286302862038610385ba005a06857068560684f0384b04847038430183f0183b01837018330182f0182d0182b03829018270682501823018210381b0781a068170681602d6b02d6a02b6f02b6b02b6702b6304b5f04b5d04b5b04b5904b5704b5504b5304b5102a6f01a6b02a6701a6302a5f02a5d01a5b01a5902a5702a5501a5301a5102a3f01a3b02a3701a330286f0286b028630285f0285d0483f0383b04837038330182f0282b028270182302e7f03e7e02e7d04c7f04c7d04c7b04c7904c7704c7504c7304c7102c6f02c6b02c6702c6302b7f02b7d01b7b01b7902b7702b7501b7301b7102b6f01b6b02b6701b6302b4f01b4b02b4701b4301a3e0697ebd17c06976069740296e029660494e04946029360287f0287e0287d0286f0286e0286b038690286302862028610484f0384b04847038430183f0283b02837018330381903818068150681402e7a02d7606d6604c6d09c6904c6509c6109c5902b7e02b7a02b7602b7202b6e02b6d02b6c0ab6a02b6913b6802b6602b6502b640ab6202b610ab6002b590ab5802b4e04b4a02b4615b4202a6d01a6902a6501a610193e0192e0286d068550683d02839028350383102d6f02d6702c6f02c6b02c6702c6309c5b04c5702b6f01b6b02b6701b6301b5b02b5702b4f01b4b02b4701b4302a6f02a6e02a6b02a6a02a6702a6602a6302a6216a5b0aa5a16a570aa5609a4f09a4e04a4b04a4a04a4704a4609a4309a4201a3f01a3e02a3701a3301a320296f029670494f049470193f029370192f0192d06927019250286f0286b02867028630385b068570684f0384b04847038430183f0283b02837018330282f0282d0282b02829028270282502823028210381b0781a068170681602e7f03e7e02e7d06d7fbb57d06d7706d7502d6f02d6704c7f04c7d06c7b06c7904c7704c7506c7309c7102c6f02c6b02c6702c6309c5b04c5702b7f02b7e02b7d02b7c02b7b06b7a02b7906b7802b7702b7602b7502b7402b7306b7202b71ba37002b6f02b6e02b6b02b6a02b6702b6602b6302b6202b5b0eb5a02b5702b5602b4f02b4e02b4b04b4a02b4702b4602b4315b4202a7f02a7d01a7b01a7902a7702a7501a7301a7102a6f01a6b02a6701a6301a5b02a5702a4f01a4b02a4701a430697f0797d06977069750296f029670494f049470193f0193e0193d0192f0192e019220287f0287e0287d0286f0286e0286b038690286302862028610385b9f05a06857068560684f0384b04847038430283f0683d0283b02839028370283502833038310182f0282b02827018230381b0781a068170681603d6b03d6a02b6f04b6b04b6702b6304b5f04b5d04b5b04b5904b5704b5504b5304b5101a6f01a6b01a6701a6301a5f01a5d01a5b01a5901a5701a5501a5301a5101a3f01a3b01a3701a330493e0286f0386b028630285f0285d0483f0383b04837038330182f0182b018270182303e7f03e7e03e7d04c7f04c7d04c7b04c7904c7704c7504c7304c7102c6f04c6b04c6702c6301b7f01b7d01b7b01b7901b7701b7501b7301b7101b6f01b6b01b6701b6301b4f01b4b01b4701b4304a4e01a360697eb817c06976069740296e0b9660494e049460193e0287f0287e0287d0286f0286e0386b038690286302862038610484f0384b04847038430183f0183b01837018330381903818068150681403d6f03d6e03d6d06c6fdb46d06c6b06c6706c6506c6305c5f08c5bda45705c5305b6f04b6d06b6b06b6905b6704b6506b63d936105b5f05b5b05b5705b5305b4fd834b05b4708b4306a6fd726d06a6b01a6906a6706a6506a6301a6105a5fd625bd525705a5308a4fd324bd124708a43cf23f05a3b05a37cb2330696f0796d0696b0696706965069630595fca15bc9157059530894fc714bc614708943c413f0593b05937c1133be12fbc12bb9127b71230586f0586e0586d0585f0585e0385b038590385305852038510684f0384b9e04a0684706846038430683f0383b05837038330682f0382b06827038230681f0381b3e01a06817068160381302c6f02c6b02c6702c6301b6f01b6b01b6701b6301b4f01b4b01b4701b4304a4e01a360296f0296e0494f0494e0494b0494a049470494604943049420193f0193e0193b0193a0193701936019330193202925029240286f0286b0286a02867028660384f0384b03847038430183f0183b01837018330381b0381902d7f02d7b02d7702d7301c7f01c7b01c7701c7301c5f01c5b01c5701c5304b5e01b4602a7e02a7604a5e04a5601a4e0297f0297d0297b0297a0297702976039750395f0395b03957039530194f0194b019470194303929039250287f0287e0287d0285f0485e0285b0285a028570485602853028520184f0184e0184b0184a018470184601843018420283507834028290282802825b50240281f0381e0281d02d6f02d6b02d6702d6302c6f02c6b02c6702c6305c5f05c5b05c5705c5302b6f02b6e01b6b01b6a02b6701b6602b6302b6202b5f02b5b08b5a02b5702b5602b5302b4f02b4e02b4b04b4a02b4702b4602b4305b4202a6f02a6e01a6b02a6701a6302a6202a5f01a5b08a5a02a5702a5601a5302a4f01a4b05a4a02a4702a4601a4302a3f02a3e02a3d0296f0296b02967029630895f0895b08957089530594f0594b05947059430293f0793d0293b0293702935029330192f0292b02927019230286f0286b02867028630385f0385b03857038530384f0384b03847038430183f0183d0283b02839028370183502833038310182f0282b028290282701823038210381f0381b038170381302b5f04b5b04b5702b5302a5f02a5b02a5702a5302a3f04a3b02a3704a330285f0385b03857028530383f0383b03837038330382f0282b028270382302c5f05c5b05c5702c5302b5f05b5b05b5702b5305b4f05b4b05b4705b4302a5f02a5b02a5702a5302a4f08a4b02a4708a4302a3f05a3b02a3705a330295f0595b05957029530794f0794b07947079430593f0593b05937059330792f0292b02927079230285f0385b0385a0385705856028530384f0384b03847038430383f0383b03837038330382f0282b02827038230381f0381b038170381302d6f05d6b05d6702d6302c6f05c6b05c6702c6305c5f05c5b05c5705c5302b6f02b6b02b6702b6302b5f08b5b02b5708b5302b4f05b4b02b4705b4302a6f05a6b05a6702a6308a5f08a5b08a5708a5305a4f05a4b05a4705a430fa3f02a3b02a37b42330296f0396d0396b0396a0396705966039650395f0395b03957039530394f0394b03947039430393f0293b02937039330392f0392b03927039230286f0586e0386d0385f0285b0385a0385708856028530384f0584e0284b0384a038470484602843038420283f0183e0283b0383a02837b303602833018320382f0382db202c0282b0382a038270782603825b1024028230381f0381e0381d05b6f04b6d0bb6b09b6905b6704b6511b6309b6105b5f05b5b05b5705b5312a6f02a6d0ba6b01a690ba6702a6512a6301a6105a5f0ba5b0ba5705a5311a3f05a3b05a3711a330686f0686d0386b03869068670686503863028610585f0685d0385b0685706855038530683f0383b05837038330682f0382b068270382302d7e0bd7602c7f05c7b05c7702c7309c5904c5501b7f05b7e01b7d01b7701b7501b7301b7201b5901b5801b5502b5401b4f01b4b01b4701b4301a7713a7601a7501a5901a5801a5502a5401a4f0da4e01a4b01a4a01a4704a4601a4301a4201a3f01a3e01a3d0287f0387b068770287303869068550684f0384b05847038430183f0183b01837018330182f0182d0182b038290182706825018230182101d6b01d6a02b6f05b6b05b6702b6305b5f04b5d09b5b09b5905b5704b5509b5309b5102a6f01a6b01a6302a5f02a5d02a3f01a3b02a3701a330286f0386b06867028630685f0685d0285b02859068570685503853028510683f0383b05837038330182f0282b028270182301e7f01e7e01e7d13c7ead47c02c7602c7402c6e0bc6605b7f04b7d02b7b11b7902b7704b7509b7311b7102b6f05b6b05b6702b6309b4904b4502a7f05a7e05a7d02a6f05a6e01a6b01a6901a6305a6201a6101a4901a4802a4502a4402a3f01a3b02a3701a330687f0687d0287b03879028770687503873038710286f0386b068670286303859068450683f0383b05837038330182f0282b028270182302d6f02d6e02d6b02d6a02d6702d6602d6302d6202b6f02b6b02b6702b6302b5f04b5d02b5b02b5902b5702b5502b5309b5102a6f01a6b02a6a02a6702a6601a6302a3f02a3e01a3b02a3701a3309a320286f0286b02867028630285f0685d0285b01859028570285501853018510683f0383b06837038330182f0682d0282b02827028250182305c6eaf4660cb6f11b6b0cb6711b6311b4904b4518a6fae26bac26718a6301a49ab24511a3f0ca3b0ca3711a330686f0386b068670386303859068450683f0383b06837038330682f0382b068270382302e7f08e7702d7f05d7b05d7702d7308d6b05d6701c7f05c7e01c7d01c7701c7501c7301c7201c6b01c6a01c6708c6601c5f01c5b01c5701c5301b770eb7601b7501b6b01b6a01b6708b6601b5f0cb5e01b5b01b5a01b5704b5601b5301b5201b4f01b4e01b4d02a7f0ea770ca5f05a5701a4f01a4701a3f01a3d01a3707a350297f0397b0397a039770e976029730396d03967039650395f0395b03957039530194f0194b01947019430193f0193d0193b03939019370393501933019310392b039270287f0287e0387b0387a038770b87602873028720386706866038650385f0985e0385b0385a038570485603853038520184f0184e0184b0184a018470184601843018420183f0183e0183d0183c0183b0183a038390283801837018360383502834018330183201831018300382b0382a038270782601d6f01d6d02d6b02d6903d6701d6502d6302d6106c6f06c6d08c6706c6502c5f08c5705b6f04b6d09b6b09b6905b6704b6509b6309b6102b5f05b5b05b5702b5308b4b05b4702a6f02a6d01a6b01a6902a6702a6501a6301a6102a5f01a5b02a5701a5301a4b08a4a02a4708a4602a3f01a3b02a3701a331096f0796d10967079650295f0e9570993f059370192f029270386f0286d0386b02867028650285f0385b0385a038570e856028530384b038470383f0383b03837038330182f0282b02827018230381b0381701e7f01e7e01e7d08d7f08d7d02d7708d7502d6f08d6705c7f04c7d02c7b0cc7902c7704c7509c730cc7102c6f05c6b05c6702c6308c5b05c5702b7f05b7e05b7d02b6f05b6e01b6b01b6901b6305b6201b6101b5b08b5a02b5708b5602b4f01b4b02b4701b4310a7f07a7d02a7707a7502a6f0ea6709a4f05a4701a3f02a370397f0397d0297b03979029770397503973039710296f0396b0396a039670e966029630395d03957039550394f0394b03947039430193f0293b02937019330392b039270387f1087e0387da807c0287b0287a038790287802877028760387502874038730387203871038700286f0286e0386b0386a038670b86602863028620385706856038550384f0984e0384b0384a038470484603843038420183f0183e0283b0283a028370283601833018320382b0382a038270782603d6b02d6904b6f04b6d0cb6b09b6904b6704b650cb6309b6104b5f05b5b04b5705b5310a6f02a6d17a6b01a6910a6702a6517a6301a6105a5f0ea5b0ea5705a530ca3f04a3b04a370ca3303867038650385b0385a038570e856038530383f0383b03837038330382f0382b038270382304c7f04c7d07c7b07c7904c7704c7507c730cc7104c6f05c6b04c6705c6307b7f10b7d07b7b01b7907b7707b7507b7301b7105b6f0eb6b0eb6705b630cb4f04b4b04b470cb4305a7e05a6e0397f0397d0397b03979039770397503973039710396f0396b0396a039670e96603963039550394f0394b03947039430393f0393b0393703933039250387f0787e0387da607c0387b0387a038790387803877078760387507874038730387203871038700386f0286e0386b0386a038670b8660386302862038550384f0c84e0384b0384a038470484603843038420383f0183e0383b0283a03837028360383301832038250782404c6f0cc6b04c670cc6301b6f01b6b01b6701b6301b4f01b4b01b4701b430ea6f02a6e10a6b0ba6a10a670ba660ea6302a620ca4f09a4e04a4b04a4a04a4704a460ca4309a4201a3b01a3a0794e019360386f0386b0386703863038550384f0384b03847038430183f0183b018330182f0182d04d7f0cd7b04d770cd7301c7f01c7b01c7701c7301c5f01c5b01c5701c5301b7f05b7e01b7b01b7a01b7710b7601b7301b7201b5f0cb5e01b5b01b5a01b5704b5601b5301b5207a5e01a4601a360397f0397b0397a03977a017603973039650395f0395b03957039530194f0194b01947019430193f0193d0193b0193a03939039380193701936039350693401933019310387f0287e0387b0387a038779d0760387302872038650385f0985e0385b0385a038570485603853038520184f0184e0184b0184a018470184601843018420183f0183e0183d0183c0183b0183a0383903838018370183603835a40340183301832018310183002c6f09c6b04c6702c6302b6f02b6e10b6b0bb6a10b670bb6602b6302b6209b4f09b4e04b4b04b4a04b4704b4609b4309b4202a6f01a6b02a6701a6302a4f01a4b02a4701a4301a3b01a390286f0386b03867028630384f0384b038470384302837028350282b028270182302d7f09d7b04d7702d7302c7f05c7e02c7b17c7a02c7707c7602c7305c7202c5f07c5e04c5b04c5a02c5704c5607c530cc5202b7f01b7b02b7701b7302b5f01b5b02b5701b5301a4e01a3e0297f0397b0397a039779f17602973039650395f0395b03957039530394f0394d0294b03949029470394503943039410193f0293b02937019330287f0287e0387b0387a038779c0760287302872038650385f0985e0385b0385a038570485603853038520384f0784e0384da204c0284b0284a038490284802847028460384502844038430384203841038400183f0183e0283b0283a02837028360183301832038250782403e7e03e7d06a7e01a7d10a7c01a7a06a7601a7506a7401a7202a6e01a6a0ba6601a620ca4e01a4a04a4601a420794e01936019260687e0387d0286e02862038550182d03829038250182103e7e02e7d02b7e06b7a02b7606b7202b6e02b6a02b6602b6202b4e04b4a02b460cb420193e0192e0687e0387d0286e02862038550383d0283902835038310381507814 19 524287 7 127 11 2047 20 1048575
def cc_58_6 : Nat → List (Nat × Nat) := unpackCursorV4 0xb9f40b3867ad365a844fa048099d6791b828b26980ea4768a6715536967f645515c67f590364f29e4b43e4486c3dd6b337a62f44326f852432c203401c34019a29118820ed2b0c02d07c440532900053 0x2d7f04d7b04d7702d7301c7f01c7b01c7701c7301c5f01c5b01c5701c5304b5e01b4602a7e0ba7604a5e04a5601a4e0297f0297e0397d039770397502973029720395f0395b03957039530194f0194b0194701943039290392803925069240387706876038750385f0485e0385b0385a038570485603853038520184f0184e0184b0184a01847018460184301842038290382803825188240281f0281e0281d02d6f02d6b02d6702d6302c6f02c6b02c6702c6305c5f08c5b05c5708c5302b6f01b6e02b6b02b6a02b6702b6601b6301b6202b5f02b5b08b5a02b5702b5602b5302b4f02b4e02b4b04b4a02b4702b4602b4309b4202a6f01a6b02a6a02a6702a6601a6302a5f01a5b02a5701a5302a4f01a4b02a4701a4302a3f02a3e02a3d0296f0296b02967029630895f0895b08957089530994f0594b05947099430293f0793d0293b0293702935029330192f0292b02927019230286f0286b02867028630385f0385b03857038530384f0384b03847038430183f0183d0283b02839028370183502833038310182f0282b028290282701823038210381f0381b038170381305d6f08d6b08d6705d6305c6f05c6b05c6705c6305c5f08c5b05c5708c5305b6fe536be436705b6308b5f08b5b08b5708b530cb4f05b4b05b470cb4305a6fe326be226705a6308a5f08a5b08a5708a530ca4f05a4b05a470ca43e123fe023bdf237de2330396f0596e0396d039670396503963039620395f0395b0395a0395708956039530394f0394b03947039430393f0393b03937039330392f0392b0392a0392710126039230386706866038650385f0385b0385a0385708856038530384f0c84e0384b0384a038470484603843038420383f0183e0383b0383a03837dd03603833018320382f0382b0382a0382707826038230381f0381e0381d03d6b03d6a08d6703d6605d6305c6f08c6a08c670ac6606c5706c5606c5505b6f05b6b05b6705b6305b5f04b5d0ab5b09b5905b5704b550ab5309b5108b4b0ab4905b4708b4105a6f0ea6b0ea6705a630aa5f02a5d0aa5b01a590aa5702a550aa5301a5108a4b08a47d023f05a3b05a37ce2330596f0e9670a95f0795d0a95707955c513f05937c012fbb1270586f0386b06867038630585f0285d0685705855038530684d0384b06847068450683f0383b05837038330682f0382b06827038230381b0681703e7b03e7a03e7903e7806e7706e7606e7506e7406e7303e7103d6f03d6e03d6d02c7f02c7e02c7d06c6f06c6e08c6d0ac6c06c6706c6506c6202c5f02c5e02c5205b7f04b7d05b7b05b7905b7704b7505b7305b7105b6f04b6d05b6b05b6905b6704b6505b6305b6102b5f05b5d05b5b05b5705b5502b5305b4b05b4702a7f02a7d0aa7b01a7902a7702a750ba7301a7102a6f02a6d06a6b01a6902a6702a6506a6301a6102a5f02a5b02a5702a5308a4b02a4702a3f05a3b02a3705a330b97f0797d0a977079750696f0796d06967069650295f059570593f059370f92f029270687f0687e0687d0687c0387b038790687706875038730887203871038700286f0286e0286d0285f0285e0385b038590285302852038510384b0884a06847068460583f0383b05837038330682f0282b02827038230381b0881a068170681605d6f05d6b05d6705d6304c6f05c6b05c6a04c6705c6605c6304c5f05c5b04c5705c5304b6f02b6e03b6b03b6a05b6703b6605b6302b6208b5f09b5b09b5a09b570ab5608b5305b4f05b4e06b4d05a6f05a6b05a6705a6308a5f09a5b09a5708a5305a4f04a4b04a4705a4309a3f02a3d09a3b01a3909a3702a3509a3301a310596f0496b05967049630895f0495b19957049530494f0494b04947049430993f0793d0493b0993707935049330992f0492b09927049230586f0386b05867038630685f0385b06857038530584f0684d0384b0484705845038430583f0283d0383b03839058370583503833038310682f0382b06827038230481f0381b068170381303e7f03e7e03e7d06d7f06d7e08d7d0ad7c06d7706d7506d7205d6f05d6704c7f04c7d05c7b05c7904c7704c7505c7305c7104c6f05c6b05c6a04c6705c6605c6304c5d04c5704c5506b7f06b7e0eb7d11b7c06b7b06b7a06b7906b7806b7706b7606b7506b7406b7306b7209b7109b7005b6f02b6e05b6b05b6a05b6705b6605b6302b6204b5704b5604b5506a7f09a7d06a7b01a7906a7706a7506a7301a7105a6f05a6b05a6705a6308a5b08a5705a4f04a4b04a4705a4309a3f02a3d09a3b01a3909a3702a3509a3301a310697f0797d06977069750596f059670494f049470993f0793d0e937079350d92f099270587f0587e0587d0586f0586e0386b038690386305862038610385b0885a06857068560584f0384b04847038430683f0683d0383b03839068370683503833038310682f0382b06827038230381b0881a068170681601d6f01d6e02d6b02d6a02d6702d6602d6301d6202c6f02c6b02c6702c6302c5f02c5d02c5b02c570ac5502c5302b6f02b6b02b6702b6302b5f02b5d02b5b09b5902b5704b5502b5302b5105b4f09b4b05b4708b4302a6f01a6b02a6a02a6702a6601a6302a5702a5602a5502a4f01a4b02a4701a4302a3f02a3e01a3b02a3701a3309a320296f0296b02967029630295f0295d0295b0295707955029530894f1094b1f947089430993f0593b05937099330192f0292b02927019230286f0286b02867028630285f0285d0185b01859028570585502853018510684f0384b06847038430683f0383b05837038330182f0682d0282b0282702825018230681f0381b068170381302e7f03e7e02e7d06d7f0ed7d06d7b06d7706d7506d7302d6f02d6b02d6702d6305c7f04c7d05c7b05c7905c7704c7505c7305c7102c6f02c6b02c6702c6305c5f05c5b05c5705c5301b7f02b7e01b7d02b7c01b7b01b7901b7701b7501b7301b7201b7101b7001b6f02b6e01b6d01b6701b6501b6301b6201b5f01b5b01b5a01b5702b5601b5301b4f01b4b01b4701b4301a7f02a7e01a7d02a7c01a7b01a7a01a7901a7801a7702a7601a7502a7401a7301a7201a7101a7001a6702a6601a6501a5f01a5b01a5a01a5702a5601a5301a4f02a4e01a4b01a4a01a4702a4601a4301a4201a3f01a3e01a3d0697f0797d0697b0697706975069730296f0296b02967029630895f0e95b0e957089530594f0594b05947059430193f0193b01937019330192f0192d0192b0192702925019230287f0287e0287d0286f0286e0286b038690286302862028610685f0385b0e85a0685706856038530584f0384b05847038430183f0183b01837018330182f0182d0182b0182a02829028280182701826028250282401823018210681f0381b0f81a06817068160381301e7f01e7e01e7d01e7c02e7b02e7a02e7902e7802e7702e7602e7502e7402e7301e7203e7101e7001d7f01d7e01d7d02d6f03d6e02d6d02c7f0ec7d02c7b02c7702c7502c7306c6f0ec6d06c6b06c6706c6506c6302c5f02c5b02c5702c5302b7f04b7d02b7b02b7902b7702b7502b7305b7105b6f04b6d05b6b05b6905b6704b6505b6305b6102b5f02b5d02b5b02b5705b5502b5305b4f05b4b05b4705b4302a7f02a7e02a7d02a6f02a6e02a6d02a6c01a6b01a6902a6702a6501a6306a6201a6101a6002a5f02a5e01a5b01a5901a5302a5201a5102a4f01a4b0ea4a02a4702a4601a4302a3f01a3b02a3701a330297f0797d0297b0297702975029730696f0796d0696b0696706965069630295f0295b02957029530894f0e94b0e947089430593f0593b05937059330192f0292b02927019230287f0287e0687d0687c0287b028790287702875028730287203871038700286f0286e0286d0285f0285e0285b038590285302852028510684f0384b0e84a0684706846038430583f0383b05837038330182f0282b02827018230681f0381b0f81a06817068160381301d6f01d6e03d6b03d6a01d6701d6601d6301d6202c6f08c6702c5f02c5d06c5702c5502b6f05b6b05b6702b6305b5f04b5d0db5b09b5905b5704b550db5309b5108b4b05b4701a6f01a6b01a6a01a670ea6601a6301a5f01a5d01a5b01a5701a5501a4b01a4701a3f01a3b01a3701a330296f0e9671695f0795d16957079550d93f059370192f019270286f0386b01867028630285f0285d0185b01859018570185501853018510384b0884a06847068460683f0383b05837038330182f0182b01827018230381b0881a068170681603e7f03e7e03e7d06d7f08d7d06d7706d7502d6f08d6705c7f04c7d06c7b06c7905c7704c7506c7309c7102c6f05c6b05c6702c6308c5b05c5701b7f01b7d01b7b01b7901b7701b7501b7301b7101b6f01b6b01b6a01b670eb6601b6301b5d01b5701b5501b4f01b4b01b4701b4301a7f06a7e01a7dd427c01a7b01a7a01a7901a7801a7706a7601a7506a7401a7301a7201a7101a7001a6f02a6e01a6b01a6a01a670ba6601a6301a6201a5702a5601a5501a4f0da4e01a4b01a4a01a4704a4601a4301a420697f0797d06977069750296f0e9670d94f059470193f019370192f0192d01927079250287f0287e0287d0286f0286e0386b038690286302862038610385b0885a06857068560684f0384b05847038430183f0183b01837018330182f0182d0182b03829018270682501823018210381b0881a068170681602d6f02d6702c6f02c6e02c6b02c6a02c6702c6602c6302c6201c5b01c5a06c5701c5602b6f02b6b02b6702b6308b5b05b5705b4f04b4d09b4b09b4905b4704b4509b4309b4102a6f01a6b02a6a02a6702a6601a6301a5b02a5701a4b01a4902a4701a4301a4102a3f01a3b02a3701a330296f029671694f0794d16947079450993f059370192f029270286f0286b02867028630385b0885a06857068560284f0284d0284b02849028470284502843028410683f0383b05837038330182f0282b02827018230381b0681702e7f03e7e02e7d02d7f02d7e02d7d02d7c02d7b06d7a02d7906d7802d7702d7602d7502d7402d7306d7202d71d257002d6f02d6e02d6b02d6a02d6702d6602d6302d6206c7f08c7d06c7706c7502c6f02c6701c5f01c5e01c5d05b7f04b7d06b7b06b7905b7704b7506b7309b7102b6f02b6b02b6702b6302b5f04b5d02b5b02b5902b5702b5502b5315b5108b4b05b4702a7f02a7d01a7b01a7902a7702a7501a7301a7102a6f01a6b02a6a02a6702a6601a6301a4b01a4901a4102a3f01a3b02a3701a330697f0797d06977069750296f029670295f0795d02957029550993f059370192f029270287f0287e0287d0286f0286e0286b038690286302862028610285f0685d0285b02859028570285502853038510384b0884a06847068460683f0383b05837038330182f0282b02827018230381b0881a068170681602e7a02e7602d7a02d7606d6606d6504c6d05c6904c6505c6105c5905c5102b7e02b7a02b7602b720ab6e02b6d0ab6c02b6a02b6902b680ab6602b650db6402b6202b6102b6002b5a08b5601b4e01b4d02a6d01a6902a6501a6104a4a01a4902a4601a4102a3602a350796d079650293d079350286d028650685d068550283d03839068350283102e7f03e7e02e7d06d7fd057d06d7b06d7706d7506d7302d6f02d6b02d6702d6304c7f04c7d05c7b05c7904c7704c7505c7305c7102c6f02c6b02c6702c6304c5f05c5b04c5705c5302b7f06b7e02b7d0db7c02b7b02b7a02b7902b7802b7706b7602b7506b7402b7302b7202b7102b7002b6f02b6e02b6b02b6a02b6702b6602b6302b6202b5f02b5b02b5a02b570db5602b5301b4f01b4e01b4d02a7f02a7e02a7d02a7c01a7b01a7902a7702a7501a7306a7201a7101a7002a6f01a6b02a6701a6302a5f01a5b02a5701a5301a4b04a4a01a4902a4702a4601a4301a4102a3702a3602a350697f0797d0497b0697706975049730296f0296b02967029630895f0495b1d957049530494f0494b04947049430293f0293d0293b0293707935029330192f0292b02927019230287f0287e0287d0286f0286e0286b038690286302862028610685f0385b0c85a0685706856038530584f0384b04847038430283f0283d0283b03839028370683502833028310182f0282b02827018230481f0381b0c81a06817068160381303e7a03e7605d7a05d7606d6606d6504c6d05c6904c6505c6105c5905c5101b6d01b6901b6501b6101b4d01b4a04b4601b4502a7e01a7d05a7c01a7a05a7601a7513a7401a720aa6e01a6d0aa6c01a6a01a6901a680aa6601a6513a6401a6201a6101a6001a5a08a5602a4e01a4d01a3e01a3d0796d079650192d079250286d028650685d068550182d0182a03829038280182606825068240182101d6f01d6e03d6b03d6a01d6701d6601d6301d6202c6f05c6b05c6702c6315c5f0ac5d08c5b15c570ac5508c5302b6f05b6b04b6702b6304b5f04b5d05b5b02b5904b5704b5502b5302b5104b4f05b4b04b4705b4301a6f01a6b01a6701a6301a5f01a5d01a5b01a5901a5701a5501a5301a5101a4f01a4b01a4701a4301a3f01a3b01a3701a330296f0496b05967029631595f0795d0495b1595707955049530894f0494b1b947049430493f0493b04937049330192f0192b01927019230286f0386b01867028630285f0285d0185b01859018570185501853018510684f0384b0c84a0684706846038430583f0383b04837038330182f0182b01827018230481f0381b0c81a06817068160381301d6f01d6e03d6b03d6901d6701d6301d6201d6101d600bc6f08c6b0bc6708c6306c5f13c5d06c5b06c5706c5506c5302b6f02b6b04b6705b6304b5f05b5b05b5904b5705b5305b5104b4f05b4b04b4705b4301a6f01a6b01a6701a6301a5f06a5e01a5b01a5901a5701a5301a5201a5101a5001a4f01a4b01a4701a4301a3f01a3b01a3701a330b96f0496b0b967049630695f0795d0495b0695706955049530894f0494b13947049430493f0493b04937049330192f0192b01927019230686f0686e0386b0386901867038630b862038610285f0285e0285d0684f0384b0c84a0684706846038430583f0383b04837038330182f0182b01827018230481f0381b0c81a06817068160381303e7f03e7e03e7d06d7fce57d06d7b06d7706d7506d7302d6f05d6b05d6702d6304c7f04c7d05c7b05c7904c7704c7505c7305c7102c6f05c6b04c6702c6304c5f05c5b04c5705c5301b7f06b7e01b7d09b7c01b7b01b7901b7701b7501b7301b7201b7101b7001b6f01b6b01b6701b6301b5f01b5b01b5701b5301b4f01b4d01b4b01b4a01b4704b4601b4501a7f06a7e01a7dcd27c01a7b01a7a01a7901a7801a7706a7601a7506a7401a7301a7201a7101a7001a6f02a6e01a6d05a6c01a6b01a6a01a6705a6601a65cc26401a6301a6201a5f01a5b01a5a01a570ea5601a5301a4f02a4e01a4d01a3f01a3e01a3d0697f0797d0497b0697706975049730296f0496b05967029630895f0495b1b957049530494f0494b04947049430193f0193b01937019330192f0192d0192b0192707925019230287f0287e0287d0286f0286e0386b038690286302862038610685f0385b0c85a0685706856038530584f0384b04847038430183f0183b01837018330182f0182d0182b0182a03829038280182701826068250682401823018210481f0381b0c81a06817068160381303e7f03e7e03e7d04c7f04c7d04c7b04c7904c7704c7504c7304c7102c6f04c6b04c6702c6302b7f02b7d06b7b01b7902b7702b7506b7301b7102b6f02b6b02b6702b6302b4f04b4b02b4704b4306a7e07a7c02a6e0397e0397c0697606974059660494e049460193e029360287f0287e0287d0286f0286e0386b038690286302862038610484f0384b04847038430683f0283b028370383306825068240381903818068150681403e7b03e7a03e7903e7806e7706e7606e7506e7406e7303e7103d6f03d6e03d6d07c7f0ec7d07c7707c7506c6f0ec6d06c6706c6502c5f05c5704b7f04b7d05b7b05b7904b7704b7505b7305b7104b6f04b6d05b6b05b6904b6704b6505b6305b6102b5f04b5d05b5b04b5704b5502b5305b4b04b4702a7f02a7d07a7b01a7902a7702a7507a7301a7102a6f02a6d06a6b01a6902a6702a6506a6301a6102a5f02a5b02a5702a530ea4b02a4702a3f04a3b02a3705a330297f0297e0297d0696f0696e0796d0796c0696706965069620295f0295e029520e94a079460493f049370792f029270687f0687e0687d0687c0387b038790687706875038730787203871038700286f0286e0286d0285f0285e0385b038590285302852038510384b0e84a06847068460583f0383b04837038330682f0282b02827038230681d0381b0781a0681706816068150681403d6b03d6a04b6f04b6b04b6704b6304b5f04b5d04b5b04b5904b5704b5504b5304b5105a6f0ea6b0ea6705a6310a5f02a5d13a5b01a5910a5702a5513a5301a5104a3f04a3b04a3704a330e9660586f0386b038630585f0285d0483f0383b04837038330682f0382b068270382303e7f03e7e03e7d04c7f04c7d04c7b04c7904c7704c7504c7304c7104c6f04c6b04c6704c6306b7f10b7d06b7b01b7906b7706b7506b7301b7105b6f0eb6b0eb6705b6304b4f04b4b04b4704b430ea660697ec817c06976069740296e0b9660494e049460193e029360587f0587e0587d0586f0586e0386b038690386305862038610484f0384b04847038430683f0383b06837038330381903818068150681403e7f03e7e03e7d06d7e07d7c06d7606d7402d6e07d6604b7f04b7d06b7b06b7904b7704b7506b7319b7104b6f05b6b04b6705b6307b5904b5506a7f1fa7d06a7b01a7906a7706a7506a7301a7105a6f0ea6b0ea6705a6301a5902a551da3f04a3b04a371ba33079660587f0587e0587d0586f0586e0386b03869038630586203861038590385806855068540683f0383b04837038330682f0382b068270382303e7a05d7606d6604c6d04c6904c6504c6104c5902b7e05b7a04b7602b7204b6e04b6d04b6c07b6a04b6907b6804b6604b6504b6407b6204b6107b6002a6d01a6902a6501a6102a3d01a3902a3501a3104946049360792e0286d068550683d03839048350383103e7f03e7e03e7d06d7fc557d06d7706d7505d6f05d6704c7f04c7d04c7b04c7904c7704c7504c7304c7104c6f04c6b04c6704c6304c5b04c5704b7f04b7e04b7d04b7c04b7b06b7a04b7906b7804b7704b7604b7504b7404b7306b7204b7107b7004b6f02b6e04b6b05b6a04b6704b6604b6302b6204b5b07b5a04b5704b5606a7f09a7d06a7b01a7906a7706a7506a7301a7105a6f05a6b05a6705a630da5b09a5704a4f04a4b04a4704a4304a3f02a3d04a3b01a3904a3702a3504a3301a310497f0697e0497d0797c0497704975049720496f049670494a04947049460493704936049350492f0792e04927049220587f0587e0587d0586f0586e0386b038690386305862038610385b0c85a06857068560484f0384b04847038430483f0683d0383b03839048370483503833038310682f0382b06827038230381b0481a048170481603d6b03d6a04b6f04b6b04b6704b6304b5f04b5d04b5b04b5904b5704b5504b5304b5105a6f05a6b05a6705a6309a5f02a5d0da5b01a5909a5702a550da5301a5104a3f04a3b04a3704a330586f0386b038630585f0285d0483f0383b04837038330682f0382b068270382303d6b03d6904b6f04b6b04b6704b6304b5f04b5b04b5904b5704b5304b5109a6f0ba6b09a670ba6306a5f09a5d06a5b06a5706a5506a5304a3f04a3b04a3704a330695e0686f0686e0386b03869038630b862038610585f0585e0585d0483f0383b04837038330682f0382b068270382303e7f03e7e03e7d04c7f04c7d04c7b04c7904c7704c7504c7304c7104c6f04c6b04c6704c6306b7f09b7d06b7b01b7906b7706b7506b7301b7105b6f05b6b05b6705b6304b4f04b4b04b4704b4306a7e07a7c04a460da3e0697ec317c06976069740296e0596c05966c21640494e0193e029360587f0587e0587d0586f0586e0386b038690386305862038610484f0384b04847038430683f0383b06837038330381903818068150681403e7a0ad7606d6604c6d09c6904c6509c610ac5901b6d01b6901b6501b6102a7e01a7a0ba7601a720aa6e01a6d0aa6c01a6a01a6901a680aa6601a6510a6401a6201a6101a600da4e01a4a04a4601a420794e01936019260286d068550182d03829068250182101d6f01d6e03d6b03d6a01d6701d6601d6301d6202c6f0fc6710c5f0ac5d10c570ac5502b6f05b6b04b6702b6304b5f04b5d0db5b09b5904b5704b550db5309b510db4b04b4701a6f01a6b01a6701a6301a5f01a5d01a5b01a5701a5501a4b01a4701a3f01a3b01a3701a330296f079670295f0295d06957029550493f0793e049370d9320192f019270286f0386b01867028630285f0285d0185b01859018570185501853018510384b1084a06847068460683f0383b04837038330182f0182b01827018230381b0781a0681706816 20 1048575 8 255 11 2047 20 1048575
def cc_58_7 : Nat → List (Nat × Nat) := unpackCursorV4 0x900218d42c8c90b86c5d8204c7ed337a34a77132751207262b7190d6bd5c6714c63f3260b345ba5156a50522484ee344cd2147e4f415693e82d3aa3e349612a5a4201a41be4313b830bc7f07d3f0007d 0x4c6f0263581319c098c605b6f06db5826d9c0b6c604b4f025a5812d1c0968604a4606d1f0165ba002cc0494e00c9f3fc4d80b0de0c86b6083381618c0909e0484b0242381210c1b07e0983b04c1b8320cc070320681500eb58075a4096de04b6d06db5826da4096ce04b6506db1826d84056be05b5b025ab80ad4c034ce01a6500d2d80695c034a601a3f00d1d8068dc034660793e0843781a1b4110d6038690843381a194110c6038610142f82216c1f0ae0285306c1f8120ec0906e0883300c178060ac0304e0182301fc604aa30035100aa8400d4001a9f0034f017a7400d380222200d10802d7e016b70131fc098fa0ac7b04e3c8131dc098ea0dc7304e3880b1bc0b8d604c6701631806dfc036fa01b7b00dbc806ddc036ea01b7300db8806dbc036d601b6700db1806d3c0369601b4700da18069fc254fc01a7d7e93e0069ec034f401a7900d3c0069dc154ec01a750553a0069cc034e401a7100d380069bc054dc01a6b00d3500699c174cc01a6300d3100693c1b49c01a4b00d2500691c0948c01a4300d2101e5380326c019267e03f81a1f4110f6038790543b81a1d4110e603871014378221ac1f0ce0286306c2781212c0908e0884300c1f8060ec0306e0183300c178060b4030560382900c1381a094030460182100eb78075b803ada0fc6f0563682f19c158ca02c5f05e2b812dbc096da0bb6b04db4812d9c096ca0db6304db080ad7c0b6b604b57015a9836d2c0968e01a6f00d3680699c034ca01a6300d2f80696c034b201a5700d298069440349601a4700d1f8068ec0346e01a3303cb781e5b4052ce02965014af81e5740f2ae079550249f8124dc0325e0192707c3781a1b4170d60386905c3381a1941f0c6038610142f82e16c170ae028530842587211c1b07e0483b0241b8360cc0305e0182b00c1380608c0f03607817056b780b5b815ad60ed6a056b382b59815ac602d6200e2f012dbc1b6d604b6706db1812d7c096ba0ab5b04dac812d5c096aa0ab5304da88069bc034d601a6700d318069240347e01a3b00d1b8068cc1d0de0886b0743382218c150be0685d0442d80e164150ae068550442980e1441508a0d83f0241d8120dc110660182f00c1580609c030460fd6f7dab38131bc1b8d604c6706e3183716c098ae01b6f00db5806d9c036c601b5b00dab806d3c0369601b4700da18069bc0b4dc01a6b00d3500699df44cc01a6300d3100696c034b401a577c92b00693c1b49c01a4b00d2500691c0948c01a4300d2101e5bc0f2ce0494f03ca701251c1b2840193a00c9b8064d80324e0192603c9283e1bdc20d6be06707c31a8c16d220ae0d84f0242581211c1b0860183f00c1d8060dc030660182f00c168060ac07052018270341280608c030420781b03c0b80adbc056da02b6b025b480ad9c096ca02b63015b080ad7c056b602b57015a980a9bc054da01a6b00d3480a99c054ca01a6300d3080a97c054ba01a5b0152b80a954034a602a3f00d1d80a8dc034660286f0143680a1ac070d2028670343280a18c050c20285f0142d80a15c050a60483f0241d8120dc090660182f0141580a09c0304602c6f0263581319c058c602b6f00db580ad9c036c602b4f00da580ad1c0368601a3e02cb73dc5980929c0494603c9b00a1bdc00d6bc0670143181213c0909604847024218060fc050760283700c1980e0640d02a02c6f0163580b19c058c602b6f00db580ad9c0569e01b4b015a3806d0c054de02a6e04d278269380949604a4a025238129181348609a4200d1f8068f8050de0286b0143380a18c1309e0484b0242382210c0307e0283b0141b8060cc2505e0682d0441580e0a42504e068250441180e08407f1802b8c055c400ae102570002b7c0bdbc00add00d6e0088880344201a0f00706002d7e016b70131fc098fa09c7b04e3c8131dc098ea09c7304e3880b1bc058d602c670163180adfc056fc02b7d015be00adec156f402b79055bc00addc056ec02b75015ba00adcc256e402b717a9b800adbc056dc02b6b015b500ad9c056cc02b63015b100ad3c0569c02b4b025a500ad1c0568c02b43781a100a9fc054fa01a7b00d3c80a9dc054ea01a7300d3880a9bc034d602a6700d3180a93c0349602a4700d218064f80325cf407f0343e8221ec070f20a8770343a8221cc070e20286f0143580a19c050c60984f0242581211c110860283f0341e80a0ec05072028370141a80a0cc070620182f0141580a09c0304602d6f016b380b1bc058d602c670163182716c098ae02b6f015b6806dac056ce02b6500db1806d6c056ae02b4f00da580ad1c0368602a670153300a994054b60aa5a0152b80a9580549e02a4e015258129280548e02a46015218269080347e01a3e0151b8068cc034640296f014b680a59c0f2ca0494f024a38064fc0526e0192f00c9680a49c0324a0286f0143580a19c050c61785b0e42b82613c090960484704c218060fc050760283700c1980a0bc0d05a0282b0141480a09c0504a0282301c1081e06c0f02e02c6f04e3581319c058c602b6f00db580ad9c036c602b55015a7806d2c0568e01b430153780a9b8154d60aa6a0553383a998054c602a620152a82693c1349c04a4b0252501291c0948c09a4304d2100a1bc110d60e8670143182613c0909604847044218060fc050760283700c1982a0bc0d05a0882b01c1482a09c0d04a0882301c1080b5f805adc04c7e0263e8131f0098f204c7504e390131c4138e002b7d00dbc80add4036e202b4d015a284a9f8134fa12a7c04d3d0269e4134f00aa7604d3a82a9d0134e409a7104d3800a9b8054da02a6c0153500a998134ca0ba6401531026954154a802a4e015268068f80327c0687d01c3c81a1d4070e2048490442081a0b4070520682501c1080b5bc13adc02d6d05e3782b1b4178ce0ac650162f80b174058ae0bc55015b780adb4056d602b69015b380ad94056c602b61015af80ad6c096b202b57015a980ad440969604b470153780a9b4034d601a690153380a994034c601a610152f80696c054ae01a5300d2580a91c0547e01a3b0151b8068cc092de0496d024b3812594052be029570249f8124dc0325e0292705c3781a1b4170d60386905c3381a194170c6038610142f80a174050b60285705c2a80a14c19096138470241f8120ec0906e0483300c1780a0ac0504e018230240d81205c05adef0567016378131ac098ce02c630262d81315c056de01b6b015b3806d8c036b602b57015a780ad340369602b47015a2806d0c054de02a6e04d358269a8134ceef2660153180a988134b609a5a04d2b82a9580549e02a4e015268068fc0347c02a3700d198068c8052de04967024a78125340928e0494500c9f8064f80526e0193200c978064b40924e01925014378321ac2b0ce028630642d85615c0909e0484b0242481211c090860984100c1f80a0ec0506e0183304c1781a0b4130560382904c1381a09413046038210240d81205c05adef3567016378271ac098ce02c6304e2d81315c056de05b6e015b5bc8da8056ce07b66015b1816d880f6b6f135a015ab81ed580569e07b4e025a5812d280568e04b4603da1bb8d08054de01a6b0153380698c034b602a570152780692c0548e01a43014b781e59c0929e0494700c9f8064f80327a0192f00c97006488050dedf06b5c83380a18d420b69005704c2781212c0908e0984303c1f81a0f405076038390141b81a0d40f0660383100c1780a0ac0504e0182303c0d81e05c096de04b6d025b5812da4096ce04b65025b1812d84056be04b5d025ad812d5c096aa02b5300d378069b4034d601a6900d33806994034c601a6100d2f80696c034b201a5700d298069440347e01a3b00d1b8068cc2f0de0686d05c3580e1a4170ce068650bc3180e184050be0b85b05c2b80a14c0907e0483b0241b8120cc0305e0182b00c1380608c098de04c6b0263381318c036de01b6b00db3806d8c0369e01b4b00da3806d0c0949c01a3602cb73b05980929c0494600c9f39c1bdbc0d6b70675a03181213c0909604847024218060fc030760183700c1980e0640d02a02d6b016b481759c05ac602d610163780b1b8058da02c5f0162f01715c058a405b6f025b6816dac0b6d205b67025b2816d8c0b6c202b5f02dad816d5c056a605b4b02da380a9bc054da0aa6b00d3480a99c054ca0aa6300d3080a97c054b602a570152982292c0548e02a3f02d1d80a8dc0b4660a96f03cb682a59c0f2ca0295f02cab8164fc0b26e0f92f0149381a1bc0d0da0386b0343381a194050be0385b02c2d01615c0b0ac028530342680e12c0d08e0684502c1f80e0ec0b06e038330341780a0ac0504e0382301c0d81a05c03ade01d6d016b580b5a405ace01d65016b180b584058de0ac6d0163580b19c058ca02c630162f80b16c058ae02c53015b7812db4056d602b69015b380ad94056c605b61015af80ad6c056ae02b5302da7816d2c0b68e05b430153780a9b8054da02a5f0152f00696c054ae01a530152900a93c034960ea4a0152380a9180348602a3f00d1d80a8dc034660296f03cb680a5ac052ce02965014b180a57c052b602957014a982253c1d2960e947044a18164fc0b2760593702c998064bc052560292700c9180a1bc0d0da0286b00c3480a19c050ca0186300c3080a17c050b6028570142981a13c070960684701c218160fc070760583701c198060bc0d05a0282b0141380a094030460681f01c0d81a05c0702602d6b016b4812dbc096da04b6b025b4812d9c096ca04b63025b080ad7c056b602b57015a98069bc034da01a6b00d3480699c034ca01a6300d3080697c034b601a5700d298068fc0347601a3700d1981a19c0d0ca0285b0142d00a15c050ac028530241f80e0ec0906e0383300c178060ac0304e018230173f80b9f805cfa02c7f0163d80b1dc058e602c6f0163680b1ac098d202c670263280b18c058c201b7f00dbd806ddc036e601b6f00db6806dac036d201b6700db2806d8c036c201b4f00da5806d1c0368604a4e00d1b00a5f8052ec0296e014b600a599d02c80494e024a30064f8050f60287a01c3c80a1dc050ec028730143880a19c050cc068650242780e12c0908e0384300c1f8060ec0306e0183301c0c81a05405ade03d6e01eb680b1bc0b8d605c670163180b17c0b8ba05c5b02e2bba9154058a602b6f02db5816d9c056c602b5f025ae816d6c0b6b205b57025aa80ad4c0b6a205b4f02da5816d1c0b68602a6f0153580a99c054c602a5f02d2e80a96c034b202a577492a80a94c034a202a4f0752580a91c1148602a3f02d1d80a8dc0b4660296f02cb581659c052c60295f02cae81656c0b2ae07955014a982253c1d2960e947044a18164fc0b2760593702c9983e4bc05256029277389180e1ac0b0d40386902c33816198050c60386102c2b8161580d0aa0684f01c2581a11c070860583f01c1d8160dc070660682f0141580a09c070460681f01c0d81a05c0702602e7f0173d80b9dc05ce602d7f016bd80b5dc05ae605d6f02eb581759c0bac601c7f0163f0071f4038ee01c7500e398071c8038de01c6b00e3500719c058cc01c6300e2f80716c038ae01c5300dbb80add8036ea01b6f00db5806da8036ce02b6600db1806d7c056bc01b5b00dad006d5c056ac01b5300da9006d3c0369c01b4d0153f80a9ec054ee02a73045378229ac114ce08a6302d2f81696c0b4ae05a5300d2780692c0348e01a4300d1f8068f40347601a370151a8068cc052fe0297e014be80a5dc072ea02973014b900e5bc072d60396a01cb3822598072c60395f01cad80e55c072a60194f00ca580651c032860193f00c9e8064ec03274029390149c0064dc0326c029350149a0064cc032620392f01c9580e4a80724e0f92601c9180a1dc050ec0387501c3780e1ac070d4038670443300e18c070be0585e01c2d80e168070ae0485601c2980e1480309e0184e00c26806130030960184a00c238061180508a0284400c218061080307e0183e00c1e8060f0030760183a0141c80a0e00306e018360141a80a0d0030660183200c188060c00705e0382b01c1500e09c0f04c038230140f80a0780503a01e7f00f3f0079f405afe08d7d016bd80b5dc05aea02d73016b780b5ac05ace02d630163f8131f4058f602c790163b80b1d4058e605c710163780b1ac058ce02c6302e2f81716c0b8ae05c53015bf80adf8056fa02b6f015b7006dac036d201b63015b1006d84056be01b5b045ad00ad5c056ac01b53015a7806d2c0568e01b430153f81e9f4054f602a770153a80a9cc054de02a6b0153380a98c114be08a5b0452b82294c0b49e05a4b02d2381690c0347e02a3b0151b8068cc052fe0297e01cbe81a5f0052f602979014bb80a5d4052e60297201cb880e5c0052de0296e014b680a59c072ca02963014b100e57c072b60395a01cab822558072a60394f01ca580e51c072860193f0149d80a4dc032660392f01c9580e4a80724e0f92601c9180a1fc030fc0387d00c3e00a1ec050f4028790143c00a1dc050ec028750143a0061cc030e40187100c3800a19c050cc0386501c2f80e16c070b4038570442b00e14c0709e0584e01c2580e1280708e0484601c2180e1080307e0183e01c1e8060f0050760283a0141b80a0d80506a0283400c198060c80705e0382b01c1500e09c0f04c038230140f80a0780503a02d7f026bd8135dc05ae602c7f0163d80b1dc058e602c5f0262d80b15c098a602b7e02d3b012978094ac01a4e0152300a5fc052fc0397d01cbb80e5d4052e60297201caf80e56c072ae0395301ca780a52c0528e0394301c9a83e4d0072520392801c9281a490070ee0587601c3a80e17c090bc0385b01c2d00e15c090ac0385301c2900e13c0309c0284b0142500a11c0508c0384300c2100e0d40f0680382901c1400e0940d0480281f0140f00a0740fafe08d7d03ebb81f5d405ade05d670263f8131f40b8f605c790263b8131d40b8e605c71016378171ac098ce02c6302e2d81315c056fe02b7d03dbd806de4056ee02b7503db9806dc4056de02b6b015b380ad8c116b602b57015a7812d2c0568e05b430153f80a9f8054fa02a6f0153700a988114b407a560252781291c0f47e02a3701cbf81e5f8072fa0697c01cbd80e5e4072ee0397501cb980e5c8072e203970014b780a5b8072da0396701cb280a58c052c40395b01cad00e55c112ac0394f01ca580e51c072860393f0149d80a4dc072660392d01c9580e4a80724e0792601c9281e490070fe0387d01c3d80e1e8070f20387801c3b81a1d8070ea0687401c33816198070ca0385b01c2d00e15c110ac0384f02c2700e12c07094038470242300e10c070840383f00c1f00a0ec05074028370141b00e0cc030640382d01c1580e0a80704e0782601c1281e0900503e0281e0140e80b9fc11cee02d7f02ebd8135dc05ae608d6b026b38071fc038f601c7700e398071ac038ce01c5f00e2d80715c038a601b7f015bf006dec036f401b7705dbb006dcc036e401b6b00db5006d9c116cc01b5f065af006d6c036b401b57025ab006d4c036a402a7f03d3b81297c0f4bc04a57065290069280348e01a4600d1b8068d80546a0297f014bf00e5f4072ee03975014b980a5c8072d60396a01cb3822598072be0395b01cab80e54c0329e0194b00ca380650c0327e0193d00c9d80e4e40326e0393500c998064c4072560392a01c9381e498070ee0687601c3a80e1ac070d4038670443300e17c130bc0385b01c2d00e15c090ac0385301c2900613c0309c0184b00c2500611c0308c0184300c210060fc0307c0183d00c1e0060ec030740383901c1c0060dc0306c038350c41a0060cc030640183100c1800e0ac070540382703c1300a07c0503c0281d016bf80b5ec05aee02d730163f8071ec058ee01c730162f80716c058ae01c5300da700a9f8054ec04a5e0252b00a918052fe0297e014be80a5dc072ea02973014b900e57c072b60395701ca980653c052960294700ca180e4a407250039250349200a1dc050ec0387501c2f812178070b60385a01c2b812158070a60385200c27806138050960284a0142380a118030860184201c1480e0a00704a188240140f80a0780503a02e7f0173b80b5fc05af602d77016b98235ac09ace02c7f0163f00b1ec058f402c770163b00b1cc058e402c6b0463500b19c058cc02c5f0162f00b16c098b402c570162b00b14c198a402b7f00dbd80addc036e601b6b015b380ad7c036b602b5700da980a9fc054ee04a5f0252b80693c0349c01a4d00d1f8068f8034640297f014bf00a5f4052ee03975014b980a5c8072d60396a01cb3822598072be0395b01cab80e54c0529e0394d014a580a5240528e02945014a180e5040327e0293b0149b8064cc072560392a01c9381e498050ee0287601c3a80e1ac070d4038670443300e17c130bc0385b01c2d00e15c090ac0385301c2900a13c0509c0384d0c42600a12c05094028490142400a11c0508c028450142200a10c050840384101c200060fc0307c0283b0141d00a0dc0506c0183300c1900e0ac070540382703c1300a07c0503c0281d 20 1048575 8 255 11 2047 21 2097151
def cc_58_8 : Nat → List (Nat × Nat) := unpackCursorV4 0xd0aff27b6c5e82f8beb8ab2c3beac09e9830a00c26fa1942fa31be84af9f3be74b09c2216aeb58d3d5b6fd582b4e2fd222d40ef4eab233ed8bfa02417c6b4a16c803748070d80038 0xf3f8079f803cfa13c7e8fa3e00b1d8058e802c6e05e33012dfc096fa02b7b08dbc80addc096ea09b7308db880adbc0b6d604b67015b1826d240968a02a7f02d3f0169f4054de05a6e00d358069a4034c605a6200d308069240349002a450152200a8fc0347602a3700d198221fc0d0fa0287b01c3c80a1dc0d0ea0887301c3880a1bc110d6088670143180e1240d08a0883f0241d8120dc110660182f0141580a09c0304602d6f016b700b5ac05ad402d67016b300b58c05ac402b6f015b580ad9c056c602b5f025ae80ad6c056b202b57015aa80ad4c136a202a6f00d3580a9a8054ce02a6600d3180a8fc0547c01a3b0151b8068cc134640286f0143580a19c050c60285f0342e80a16c050b2028570142a80a14c070a20883f0241d8120dc110660182f0441680a0ac0504e0282500c118171ba428cc04b6f08db5812d9c1f6c611b49025a283e9be404d71e26707d318069263a48a11a3f0251d8128dc234660886f0443582219c110c603849034228220fc0907604837044198220bc11056088270441180b5fc09af604d77016b98071fc0b8fc01c7d00e3b8071d4038e601c7200e2f80716c038ae01c5300dbb83add8036ea01b5f025af006d6c036b401b57025ab006d4c036a401b4f00da7006d341d4ec0297e05cbb012578092ac0194e00ca30064f803278019360149a00a1fc110f60e8770143981217c090b6048570242980613c030960184700c218060fc0307a0183b01c1c8060dc0d06a0183300c1880e0640d02a01d6f00eb6812dbc096da04b6b025b4812d9c096ca04b63025b080ad7c096b604b57015a980a9bc054da02a5f00d2d80694c0547e01a3b0151b8068cc1d2ac1086f034368221ac070d2108670343282218c070c20285f0442d83a15c050a60483f0241d8120dc090660182f0141580a09c0304601e7f00f3f0079f4098fe04c7d0163d8131e4058ee04c75026398131c4058de04c6b0263380b18c056fe05b7e02dbe80adbc0b6dc01b6b00db4806d8c0b6c401b61015a7806d2c0568e01b43075330425fa342f802976014ba00a5b8172cc0494e024a30064f80526c1087f0343e80a1ec070f2028770343a8221cc070e20286f0443583a19c050c60484f0242581211c090860183f0141d80a0dc03066038190340a812dbc096d604b67025b1812d7c096b604b57025a981e9bc0f4d607a6703d3181697c1d4b60ea5702d298128fc0947604a370251981e5b8052bc0786f03c3581e19c0f0c60585f0442d83a15c0b0a60483f0241d8120dc090666e02f0441595c09c1104606815025b7812db4096d604b69025b3812d94096c604b61025af812d6c096ae04b530753780a9b4174d601a6905d3380a9941d4c601a6102d2f82e96c174ae05a530251f8128ec0946e04a330743781a1b4110d60386905c3381a194110c60386102c2f82216c170ae058530241f8120ec0906e04833368178220acac04e088230163780b1ac058ce02c63015b780adb8056d602b6a015b380ad98056c602b62015a780ad380569604b4a015a380ad180568604b42015378069ac054ce01a630152780692c0548e01a430143780a1ac050ce028630242781212c0908e048430141f81a0f405076028390141b80a0d4050660383100c1780a0ac0504e01823026378131ac098ce04c63075b7c6cdae326ce0eb63025a7812d2c0968e04b438c1330165ba2e2cc0494e024a30064fa2c26c0e86f04435b1c19c110c60484f0242581211c090866b03f0441d9500dc11066038190340a80b9f80bcec04c7f0263f0131f4098ee04c75026398171c8098d204c65025bb812dd8096ea05b6903db4016d940b6c804b4f025a7016d340b4fe05a7b02d3b8169cc034d202a650252781292c0948e04a4302d1f84e8f40b47601a3902d1b8168d40b46601a3102cbb0161fc0b0f60587702c3980e1a40d0ca0484f0242581211c090860583f0341e8160ec070720583702c1a8160cc070620d82f0441582609c1104602e7e03f3b00b1fc0b8f604c770163981f1a4098ca01b7f02dbf006df4036ee01b7500db9806dc8036d201b6500da7806d2c0368e01b4300d3b83a9d8034ea01a6900d34006994054c801a4f06d2700692c0349401a470252300690c0348401a3f00d1f0068f40f2ec0287f0443d83a1dc050e6038690343283613c0909604847044218060fc030760183700c198060bc0305a0182b01c1480609c0d04a0182300c108079fc03cfc01e7d03ebf01f5f005aec02d74016b701f598096fe04b7d015bd84ede4056ee04b7504db9866dc4056de05b6b025b380ad8c0f6b204b550153f8169f80b4fa02a6f02d370069ac034d201a6302d31006984034b202a550151f8068ec0546e01a3303cb30421fc0d0fa0287b01c3c80a1dc0d0ea0887301c3880a1bc110d60e8670143180e1640d0aa0983f0241d8120dc110660182f0141580a09c0304602e7e03f3b00b1fc098f604c77016398131a4098ca02b7f02dbf00adec276f402b7706dbb00adcc0b6e402b69015b401ed940f6c801b4f00da7006d34054fe01a7b0153b8069cc034d202a6500d258129280349202a470252300690c0348202a370251b0128d40f2ec0287f0443d8761dc050e6038690343281213c09096048470242180a0fc0d07a0883b01c1c8360dc0d06a0283301c188060bc050560282700c1180b9f80fcec04c7f0263d8131dc098e604c6902632806dfc036f601b7700db9806da4036ca01b4f00da6806d2c0369401b47025a3006d14034fe05a7e00d3d8069e8034ee13a7600d398069c8034d201a6800d3281e990034aa0aa5400d278129380349a01a3f00d1f0068f40f2ec0192603c920161fc110f61b87702c3980e1a40d0ca0484f0242581211c090860183f00c1d8060dc030660182f00c168060ac07052018270341280608c0304205d6e03eb3012dbe286d604b67075b181ed64096aa0ea6f89935c4899c1d4c601a5903d2ac448fc0947604a378811981e5981d0de0886b6303382218c070b2068554081f8120ec0906e08833350178220aca604e0882300eb78075b8056de04b6b025b380ad8c096be04b5d025ad812d64096ae04b55025a9812d44034d605a6a01533816998034c602a570152a80a8fc0347602a3700d1980a1bc0b0d6058670143182217c0d0ba0885b01c2c82215c0d0aa0885301c288120fc0907604837024198060bc050560282700c118079fc03cfc01e7d0163f8131ec098ee02c73016378131b4098d604c6902633813194058c604c6100dbd816de8036f202b7702dbb006dcc036e202b6702db3042d940569e01b4b015a3806d0c052fc05976014b700a5b00b2cd0e164024a70125180327c029360143f8161ec0b0ee02873014378161b40b0d60386902c3381a194050c6038610242781212c0908e0484300c1f80a0ec0506e0183301c0c81a05405afe04d7b026bb80b5cc038fe05c7e00e3e8071dc038ea01c7300e3900717c038b601c5700e29806ddc216ec01b7500daf812d78036b601b5a00dab812d58036a601b5200da7806d380369a0297e05cbb012578092ac0194e00ca6006518052880193e00c9e0064d8052680287f0443d8221dc050e60485f0242d81215c090a60184f00c2580611c030860183f00c1e8060ec07072018370341a8060cc03062038190340a8075bc03ada04b6f025b6812dac096d204b67025b2812d8c096c202b5f025ad812d5c056a602a6f0153680a97c034b601a530151f8068ec0546e01a330443781a1b4110d6038690443381a194110c6038610142f82216c110ae028530241f8120ec0906e0483300c1780a0ac0504e0182300f3f8079f803cfa04c7f0263e80b1ec098f202c770263a8131cc098e202c6f0263581319c058c602b7f02dbf016df4056de05b6e00db5806da4036c605b6200db080ad3c0369602b4700da18425fa162f802976014ba00a5b8172cc0494e024a30064f803278029360149a0221fc0d0fa0287b01c3c80a1dc0d0ea0887301c3880a1bc110d6088670143181213c0909604847024218060fc050760283700c1980e0640d02a02c6f0263581319c058c601b6f00db5806da8036ce05b6600da7806d2c0368e01b430153780a9b80949e04a4e025258129280948e04a46025218129080347e01a3e014378161ac0b0ce028630242781212c0908e0484300c1f8060ec0306e018330441781a0b411056038290441381a0941104603821016bf8135ec09aee02d7300e3f8071f4038f601c7a00e3b8171d8038ea01c5f00e2d80715c038a601b7f02dbf006df4036be04b5e00dad806d68036ae04b5600da9806d480369e01b4e00da680a5f80b2ec0495e024ab0065380328c0193e00c9e0064da122680287f02c3d8161dc050e60485f0242d81215c090a60184f00c2580611c030860183f00c1e8060ec07072018370341a8060cc03062038190340a812dbc096da04b6b025b4812d9c096ca04b63025b0812d7c096ba04b5b025ab812d54096a612a6f0153682e9ac034d20ba670153284a98c034c205a5f05d2d82e95c0b4a604a3f0251d8128dc094660886f034368221ac070d2088670343282218c070c20585f0442d82215c0b0a60483f0241d8120dc090660882f0441582209c1104602c6f0163580b19c058c602b6f015b700adac056d402b67015b300ad8c056c402b4f015a700ad2c0969402b47015a300ad0c0968402a6f00d3580a9a8054ce02a6600d3180a93c0349604a4a0152380a918034860286f0143580a19c050c60484f0242581211c090860283f0341e80a0ec05072028370141a80a0cc070620182f0141580a0a40504e01823044108131bc098d604c6702631c34dbe186d70a367841b1812d3c0969604b47025a18165ba0e2cc0494e024a30064fa0c26c0886f0443582219c110c60484f0242581211c090860883f0441d8220dc11066038190340a8175f80badc04c7f0263e8131ec098f204c770263a8131cc098e204c6f0263581319c098c604b7f025bf012df4096f804b7b03dbd012de40f6f004b77025bb012dd4096e804b7303db9012dc40f6e004b6f015b7012dac0b6d404b67025b3012d8c056c409a7f04d3e82a9ec034f209a7704d3a8369cc034e205a6f02d3581699c0b4c604a4f0252581291c0948604a3f0151e8128ec0347204a370151a8128cc034620797e03cbe0125180926c0792e0d43f81a1f4110f6038790543b81a1d4110e60387102c378161ac0b0ce058630242781212c0908e048430241f81a0f409076038390241b8120d4090660383106c178220ac1304e0882302eb7c1159c098de04c6b0263381318c098b604c57025b7812db8096d607b6a025b3812d98096c605b62025ad81ed68096ae04b5602d378369ac134ce05a6306d2d82695c0949e04a4b0252381290c0947e07a3d0251d8068e40946e04a35025198068c4092de04967024a501251c0928c049370249b0124d40925e0792e024938124880b0de0c86b6203381618c190b6920570242781212c0908e048430241f81a0f409076038390241b8120d4090660383106c178260ac1304e0c8230240d81205c098de04c6b0263381318c0b6de05b6b02db3816d8c0969e04b4b025a3812d0c0949c0596e02cb30125180327c0d93602c378161ac0b0ce058630242781212c0908e048430641f8320ec1906e0c83301c0c81a0540bade05d67026378131b8098d605c6a02633813198098c605c620262d847168098ae04c56025b7812dac096ce04b63025ad812d5c0b4de05a6b02d3381698c1b4b60da57025278369340949601a49025238129140948601a410251f8128ec0946e04a33024b781259c0929e0494e024a68124fc0927c049320249781249c0b0de0586b02c3381618c190b60c8570242781a13409096038490242381211409086038410241f8120ec0906e04833064178320ac1904e0c8230240d81205c096de02b6d025b5812da4096ce04b65025b1812d84096be04b5b025ac812d5c096a604b5104d3780a9b4174d601a6904d3380a9941b4c601a6102d2f8169740b4b605a5704d2a81694c0947e04a3b0251b8128cc2f0de0686d05c3580e1a4170ce068650643180e1840b0be0585d02c2d81615d840aa058530241f8120ec0906e0483306c178260ac1304e0c8230163780b1ac058ce02c63015b780adb8056d602b6a015b380ad98056c602b62015a780ad380369601b4a015a3806d180568604b42015378069ac054d402a670153300698c0549e02a4e00d2580a91c0348604a4200c9f0064b8050de0286b0143380a18c0909e0484b0242381210c0507e0683d0141d80a0e40506e028350141980e0c40305e0d82d0141580a09c0504a01823 18 262143 7 127 11 2047 21 2097151
def cc_58_9 : Nat → List (Nat × Nat) := unpackCursorV4 0x87b3382d4e7e5487a3427614272f3270e216db336885363c4c5db6158d4e50d8048b8245d2e3fe5f3d12d3725f3472b2c68129531244511f54f16d881214c0ed340d5180bc1909a2206a3002b3f0002b 0x58dc02c5e025b7812db40b6d605b69025b3812d940b6c605b61015af816d6c096ae02b530153780a9b4154d601a690153380a994154c601a610152f80a96c054ae02a530151f8128ec0546e05a3302cab02a1bc0d0da0886b01c3482a19c0d0ca0886301c3080a17c0b0b605857014298160fc090760483702c198620bc0505602827044118075bc03ada02d6700eb280b58c058de0ac6d0163380b194058be02c57015b7812db4056d602b69015b380ad94056c605b61015af80ad6c056ae02b5302da5812d1c054de02a6e0153680a97c054bc01a5b0152b80694c054a401a4b0752500a91c0548c02a3f00d1d80a8dc034660296f03cb680a59c052ca0295f014ab8124fc0926e0192f03c9680a49c0524a0286f0343680a1ac050d2028670143280a18c070c20285f0142d80a15c050a60e84b074238160fc090760483702c198060bc050560282700c1181e06c0f02e02c6f02e3380b17c0b8ba05c579f22a80adbc0b6d604b67015b180ad7c096ba05b5b02dac812d5c096aa02b5302da8816d2c0968e02a6f0153580a99c054c602a5f02d2e80a96c034b202a579e92a80a94c034a20ea4b0152380a8fc0947602a3702d198165a80b2ce0596602cab8165580f2aa0493f0249b81e4bc0524e0286f02c3581619c050c60285f02c2e81616c070b2058570342a80a14c070a20e84b074238160fc090760483702c198620bc05056028272801181e06c0f02e02d7f016bd80b5dc05ae601c7f0163f0071f4038ee01c7500e398071c8038be01c5b00e2b80714c036ee02b7600dba806d7c056bc01b5b00dad006d5c056ac01b5300da9006d3c0369c01b4d0153f0068d80546802976024af0125580329c0194c00ca300a5100327c0193c00c9b00a4d0050fe0287b0143b80a1cc090be0485b0242b81214c0309e0184b00c2380610c0307e0183d00c1d80a0e40306e0283500c198060c41f04a038190340a8079fc03cfc01e7d0163f8131f4058f602c790163b80b1d4058e604c710163780b1ac058ce02c63015bf80adf8056fa02b6f015b7006dac036d201b63015b1006d840569e01b4b015a3806d0c054fc07a7c015370065f8032f802976014ba00a5980929c0494600c9f0064f00526c029340143f81a1f4050f6028790143b80a1d4050e6038710143780a1ac050ce028630242781212c0908e0484300c1f80a0ec0506e0183307c1280e0640d02a02c6f0163580b19c058c602b6f00db700adac056d402b67015b3006d8c036c402b4f015a700ad2c0969402b47015a300ad0c0968402a6f00d3580a9a8054ce02a6600d3180a93c0349602a4700d2180a1bc050d6028670143181213c09096048470242180a0fc0d07a0283b0141c80a0dc0506a0283301c188060bc050560282700c118131bc098d604c6702631816dbe766d73a36702db1812d3c0969604b47025a18169b80f2cc0494e024a30064fa7226c0586f71835b2819c0b0c60484f0242581211c090867203f3401d96c0dc9e0661102501c0c81a054158cc07c56025b7816dac096ce05b63025af812d74156b609b59025ab812d54156a609b51055a48169bc1d4d60ea6702d3182a97c054ba0aa5b00d2c82a95c054aa0aa5300d28cb08fc0947604a37951198161bc110d60e86702c3182a17c0d0ba0885b01c2c82a15c0d0aa0885301c28a0c0fc0907604837044199c40bc110565a0270441180b1f80f8dc0ac6c0162f012dfc096fa05b7b02dbc812ddc096ea05b7302db8812dbc096da05b6b02db4812d9c096ca05b6302db080ad7c096ba05b5b025ab812d54056a602a7f0153e82a9ec034f202a770153a82e9cc034e202a6f0153681e9ac034d202a670153281e98c034c202a5f0152d80a95c054a602a3f0251d80a8dc0b4660797e03cbe00a5b8052bc0b87f0343e8221ec070f20a8770343a8221cc070e20786f0343681e1ac070d2078670343281e18c070c20285f02c2d81615c050a60583f0241d8120dc0b0661782f0141580a09c110460781502eb781759c098de04c6b02e3501319c098cc04c630262d81315c096de02b6e025b3812d8c056c409b5b04dad026d5c156ac04b4f025a701ed340b4de05a6b02d3381698c134b609a570252781292c0948e04a4304d1f80a8f41347601a3904d1b80a8d41346601a31024b781259c0929e0494d024a38125140927e0293d0249b8124d40925e0492702c378161ac0b0ce058630642d85615c0909e0484b0242381210c1307e0683d04c1d80e0e41306e0683504c1980e0c41305e0982b04c1382608c090360481703ebf02b5f0098fe04c7d0263d8131e4098ee04c75026398131c4098de04c6b02e3501319c098cc04c630262a81edfc0f6fc0eb7d08dbe01edec0f6f407b7903dbc01eddc0f6ec07b7503dba01edcc0f6e409b7104db8016dbc056dc05b6b02db5016d9c0b6cc05b63015b1012d540f4fe09a7d03d3d8069e40f4ee07a7503d398069c40b4de05a6b02d3381698c0949e04a4b0252381290c1347e02a3d04d1d8068e41346e02a3504d198068c40b2fc0596e03c3f81a1f40f0f60387903c3b81a1d40f0e60387102c378161ac0b0ce058630242781212c0908e0484304c1f81a0f411076038390741b81a0d4110660383106c178220ac1304e0882303c0a8075bc03adc02d67016b1807588058de02c670162f80b174058ae0ac55015b780adac056ce02b63015af80ad74056b609b59015ab812d54056a602b5104da5812d1c054de01a6b0153500a99c054cc01a630152b80a958054aa01a4b0152380a8fc0547c01a3b0151b8068cc134640296f014b380a57c052ba0295702caa8124fc0926e0192f03c9680a49c0524a0286f0143580a19c050c60285f0142e80a16c070b2028570342a80a14c050a21084b0f4238260fc090760483704c198060bc050560282700c1181e06c0f02e07d7f076be81f5dc0faea02d6f016b38131fc098fa05c7b02e3c8131dc098ea05c7302e3880b1bc058d602c670163181716c098ae01b7f015bf006df4056f801b7b00dbc806ddc036ea01b7300db9006dc4036e001b6f015b7006db4036ce01b6500db1806d88036b601b5a00dab80ad580369e01b4b00da3806d0c034fe01a7d00d3d8069e8034f201a7800d3b80a9d8034ea02a7400d3380a998034ca01a5b00d2d00695c054ac01a4f0152700692c0349401a470152300690c0348401a3f00d1f0068f4052fe0297e014be80a5bc052dc02962074ad01e5580929e0494700c9f8064dc0325e0192d00c9500649c0324c029250149201e1fc0d0fa0787b01c3c81e1dc0d0ea0787301c3880a1bc050d6028670143183a16c1d0ae0584f0242581211c0b0860183f00c1d8060dc030660182f00c168060ac05052018270141280608c030421381d03c0d81e05c0f02a01e7f00f3f0079f403cf802e770173b00b9d405ce802e7300f390075fc03afc01d7d0163f83b1f4058ee02c7503e3783b1b40f8ce07c650162f80b15c056fe04b7d015bd80ade4056ee02b75015b9816dc4096de04b6d02db5816da4096ce04b6502db1816d84056be02b5d015ad80ad5c096aa02b5302da5812d1c054fe02a7e0153e80a9bc054dc02a6d015360069ac034d202a670153280698c0f4c401a6100d3000a97c054bc01a5b00d2c80694c054a401a5100d2583a9280548e02a460151f8068ec0546e01a33014bf80a5f80f2fa0797c014bb80a5d4052e40296f014b700a5b4052be0295e014a903a5280f28c0493f0249b8064bc0524e0287f0343e80a1ec050f2028770143a80a1cc070e20786f0343681e1ac070d2078670343281e18c070c20285f0142d80a15c050a60e84b074238160fc090760483702c198060bc050560282700c1184e0740f0360781703c0a8075bc03adc02b6f02db5812d9c056c604b5f025ae836d6c136b204b57025aa836d4c136a201a6b00d3500699c1d4cc01a6300d2b8069540347e01a3b00d1b8068cc050de0886b0743380a18c370be0685d0442d80e164370ae068550442980e1441b07e0483b0241b8220cc0305e0182b00c1380608c0f02a04c7f0263e81f1ec0f8f204c770263a81f1cc138e202c6f02e3581319c058c601b7f00dbe806dec036f201b7700dba806dcc036e201b6f00db5806da8036ce0eb6600db1806d540369e01b4b00da3806d0c034fe07a7e00d3ecc09f0034f601a7a00d3c8069e0034ee07a7600d3a81e9d0034e601a7200d388069c0034de02a6e00d358069a8034ce0ba6600d31806988034aa01a4f06d2700692c0349401a470252300690c034840297e014b701e1fc0d0fa0787b01c3c81e1dc0d0ea0787301c3880a1bc110d60e8670143183613c0909604847044218060fc030760183700c198060bc0305a0182b01c1480609c0d04a0182300c1081e054058de02c6e015b780adac056ce02b63025a7812d341369609b49025a3812d141368609b41015378069ac054d402a670153300692c0349202a3f00d1d80a8dc034660286f0143580a19c050c62084f0342682212c07092208470342282210c070820983f0241d8120dc110660182f0141580a09c0304602d7f016bf00b5f405af802d7b03ebd00b5e40faf002d77016bb00b5d405ae802d7303eb900b5c65cae002d6f016b700b5ac05ad402d67016b300b58c05ac401c5e025bf812df40f6f607b79025bb812dd40f6e609b71015b780adac056ce02b63015af812d74056b602b59015ab80ad54056a619b510153f80a9f4034f601a790153b80a9d4034e601a71015378069ac054d402a670153300698c0349202a3f00d1d80a8dc034660297e014b701e1fc0d0fa0787b01c3c81e1dc0d0ea0787301c3880a1bc050d6028670143180a17c0d0ba0285b0142c80a15c050aa0285301c288260fc0907604837044198060bc050560282700c1181e05405aec07d66026368131a4098ca04c610262c80adf8056f402b76015b902adb8056da0ab6c015b500ada4056d00ab66015b2836d90056c402b61015b0006d380369a02a6d00d3480a994034c204a4a00d2480a9180348202a360151a81a1b4070d20686501c3080a0f407072068350141881f5fe58afa07d7703eba80b5bc05ace04c7f0263e8131ec098f204c770263a8131cc098e202c6f0163580b19c058c604c5b0262b80adfc0f6fc02b7d06dbe00adec056f402b79015bc00addc0f6ec02b7503dba00adcc056e402b71015b800adbc056dc02b6b015b500ad9c056cc02b63015b100ad6c056b402b5706dab006d3c0369c01b4d0153f80a9f8054fa02a7c00d3d8069e4054ee02a7500d3981e9c8034e201a70015378069ac054ce01a6300d2d80a95c0349604a4a00d2480a91c0548c01a4300d2080a8dc0546c02a35014bf80a5f8052fa0296f014b700a588092b407956024a781251c0527e0293d0149b8124d40325e0292703c3f81a1f40f0f60387903c3b81a1d40f0e6038710143780a1ac050ce028630642d87615c0909e0484b0242381210c0507e0283d0141d80e0e40506e068350141980a0c40305e0282b0141380608c0903a0481b0240b81e0540baec07d66026368131a4098ca04c610262c806db4036d201b6500db0806d340369404b4600da280a9f8034fa05a7c00d3d0169d8034ea13a7400d3902a9b8034da0aa6c00d350069a4034d00aa6600d3284e990034c401a6100d3000a9380349a01a3e00d1e8064980f2480686d01c3481a194070c20182d01c1481a0940304201d6f00eb700759c03ac601d620163781719c338be0ac5d0ce2b82b154056de04b6b025b380ad8c096be04b5d025ad80ad64096ae04b55015a980ad440969604b4700d378069ac034ce01a6300d2f806974034b601a5900d2b806954034a601a5100d2580691c0347e01a3b00d1b8068cc052de01967014af80a574032ae01955024a501e5180927e0493700c9780649c050de0586b02c3380a18c330be0685d0642d80e164330ae068550642980e144190961b8470241f8120ec0906e0483300c178060ac0304e018230240e81206c0902e0781500eb78075b803ace01d6300eb102f1bc178ce07c5f09e2e81f15c0f8aa02b6f015b5812d9c096c604b5f025ad812d64096ae04b53025a8812d2c0968e01a6f00d3580699c034c601a5f03d2f00696c034b201a5700d29806948034a201a5000d2580691c0347e01a3b00d1b8068cc092de0796e00cb3812588052be0295e014ae8125280f28c0493f0249b8064bc0324e0b86f05c3582e19c170c60785f0342e81e16c0f0ae0685503c2983212c2708e0483f0241d8120dc090660182f00c1580609c030460481d0240d81205c0f02a07d7f952be81f5dc0faea02d6f02eb38131fc098fa04c7b0263c8131dc098ea04c730263880b1bc098d604c670163181316c098ae01b7f03dbf006df4136f801b7b00dbc806ddc036ea01b7300db9006dc4036e001b6f00db5806d9c036c601b5b00dab806d3c0369a01b4b00da5006d1c0968c01b4500d3f81e9f8034fb2927c00d3d8069e8034f201a7800d3b81e9d8034ea07a7400d398069c8034e201a7000d3780a9b8034da05a6c00d358069a8034ce05a6600d32ca0990034c601a6200d2d806968034ae0ea5600d2780a9380349a01a3f00d1f0068f4052fe0297e014be80a5bc052dc02962024ad01e5580929e0494700c9f8064dc0325e0192d00c9500649c0324c0492503c9201e1fc0d0fa0787b01c3c81e1dc0d0ea0787301c3880a1bc0b0d6058670143183216c370ae0484f0242581211c090860183f00c1d8060dc030660182f00c168060ac07052018270341280608c030420481d0240d81205c0f02a07c6f9ba3681f19c0f8ca05c5f9b22b812dbc096da07b6b03db4812d9c096ca07b639a9b0812d7c0b6b604b5702da9cd0d2c0968e07a6f9993681e9ac034d207a6703d3281e98c034c205a5f9912dcc495c0b4a72f24b96923cac8fc0947604a37939198165bc0b2dc0596d02caf8165780b2a51814a03ca30124fc0926e0792f03c9381e1bc0d0da0786b01c3481e19c0d0ca0786301c3081617dc40b6c905702c29a9412d2608e8203f0241d8120dcf80666f02f3301596009c9a0464501d03c0d81e05c0f02a02c6f0163580b19c058c602b6f015b7006dac036d402b6700db300ad8c056c402b4f015a700ad2c0969402b47015a300ad0c0968402a6f015370069ac054ce01a630153100a93c0349604a4a0152380a918034860286f0143580a19c050c60484f0242581211c090860283f0341e80a0ec05072028370141a80a0cc070620182f0141580a09c0304602b5f025ad812d5c056a602a5f0152d80a95c054a602a3f0251d80a8dc094660285f01c2d80e15c050a60383f01c1d80e0dc070660382f0141580a09c0704602b5f025ad812d5c056a602a5f0152d80a95c054a602a3f0251d80a8dc09466059560142f81616c0b0ae028530241f8120ec0906e048330341780a0ac0504e06823016378131ac098ce02c63015b780adac056ce02b63015a7812d2c0568e04b4302d330165b80929c0494600c9f4944d8050de0586b02c3380a18c0909e0484b0242381210c3107e0283b0141b92c0cc07033240180340ac8c050096de04b6d05db5826da4096ce04b6507db1826d84096be05b5b025ab816d4c1f4de02a6d05d358069a4174ce02a6507d318069840b4be0ba5b05d2b81694c2347e04a3b0251b8468cc110de0686d0443580e1a4110ce068650443180e1840b0be0885b0442b81614c1107e0483b0241b8220cc1105e0882b0441382208c05afc0bd760163f8171ec098ee02c7304e2c813154036fe05b7e00dbe806ddc036ea01b7300db9006d64036b001b55015aa006d3c0369601b4700da18069dc1f4ec01a7500d2c806960034aa02a5400d278369380349601a4a00d238129180348601a4200d1f8068f80347a0287f0443d8221dc050e6038590342a82213c0909604847044218060fc030760183700c198060bc0305a0182b01c1480609c0d04a0182300c108075ac03ad402b6f02db5812d9c056c604b5f025ae826d6c136b204b57025aa826d4c136a202a6f00d3580698c054be02a5d0151f8068ec0546e01a33014378221ac110ce028630442f81a174110b6038590442b81a154110a6038510441f8120ec0906e0883300c1780a0ac0504e01823 20 1048575 8 255 11 2047 21 2097151
def cc_58_10 : Nat → List (Nat × Nat) := unpackCursorV4 0x96e409313d8e54c8b1348674a8194e7d445781537354c6f83d6b444663515ed765a34a56f3454f204d27d47959434453d361372613363c31e182e23c2a63c23d691f04d16c841214b0b46d0615300061 0x3ade01d6e00eb68071bc038da01c5f00e2f00715c038a601c52015b782adb4056ce02b65015af80ad5c0569e02b4d015a380ad14054de02a6b0153480a99c054c609a610152f80a96c054ae02a5302d2782692c0b48e09a4304d1d8168dc052de02967014af80a55c2529e1294704c9781649c050de0286b0143380a18c050be0285b0142b80a14c2509e0884b0942382210c110760883704c178160ac0b04e088230440d84205c03ade01d6e00eb682b1bc058ce02c5f0562b816dbc056d602b6704db180ad7c0b6b605b57015a9826d2c0b68e01a6faf1370069b4034be02a5e00d2d80695c034a601a5200d2380a9180348a01a3f00d1d8068dc034661396f014b380a57c1d2ae0993f02c9b8064bc0324e1c86f0143580a19c110c60285f0442d83a15c050a60884b044238260fc0b07605837044198060bc030560182700c1182206c5802e01d6f00eb70075b4158de0ac6d0163380b194058be0ac5d0562b82b1540b6de04b6d05db5826da40b6ce04b6506db1826d84056be05b5b02dab80ad4c1569605b4700d378069b4034ce01a6500d3180697c034b601a5900d2b80694c034a201a4b00d238068fc0347601a3700d1983a5bc0f2da0b96703cb280a57c172ae0d93f02c9b8064bc0324e0e86f034368221ac070d20b8670343282218c070c20285f0442d82e15c050a60884b044238360fc0b07605837044198060bc030560182700c1182206c5602e02d6f016b700b5ac05ad402d67016b300b58c05ac401c5e015b780adac056ce02b63015af812d74056b602b59015ab80ad54056a609b5100d378069ac034d401a670153300698c0349201a3f00d1d8068dc034660286f0143580a19c050c60285f0342e80a16c050b2028570142a80a14c070a20883f0441d8220dc110660182f00c1580609c030460ad6f056b38371bc1b8d60dc6706e3182b16c158ae01b6f00db5806da8036cf5d36600db1806d74036ae01b5500da7806d2c0368e01b4300d378169b8034d601a6a00d33d70998034c601a6200d2bd6c958034aa01a4f06d2700692c0349401a470252300690c034840e96f978b383653c1b28e0193f00c9b8064bc0325a0192703c9283a1bc110d6d30670443182216c110ae0d84f0442583611c110860183f00c1d8060dc030660182f00c168060ac07052018270341280608c030420881b1480b80b5bc05ada02d67056b280b19c058cc02c6500e2d807168058ae01c56015b780adac136d202b67015b180ad84136b605b57015a7812d340569602b49015a380ad140568609b410153780a9b4034d602a670153280698c034b602a5700d258069240548e01a4300d2080a8fc0347602a3700d1980a5bc052ce0294f03ca680a51c0528a0993f02c9b8064bc0524e0286f0143580a19c050c60885b0442b80a13c0d09a0284b0142480a11c0508a0284301c208260fc0b07605837044198060bc050560282700c1182206c5002e02d6f016b700b5b4058de02c6e0563680b17c058ae02b6f025b680adac056d202b67015b280ad8c136c202b5f015ad80ad5c056a609b4b02da380a9bc054dc02a6d0152f80696c054ae01a5300d2580a91c0547e01a3b0151b8068cc052de0796d014b380a594052be0295704c9f8164dc0325e029270143781a1b4050d6028690143380a194050c6038610142f80a16c050ae028530442582211c1307e0583b02c1b8220cc0305e0282b0141380608c1103610817016b78275b805ada0ac6f0563681719c0b8ca02c5f0162b80adbc056da02b6b015b480ad9c056ca02b63015b080ad7c056b605b59015ab80ad4c056a205b4b04da5012d1c0b68c02a6f015368069ac034d202a670153280698c034c202a5f00d2d80a95c034a601a4b0152380a8fc0347602a3700d1982e5bc0f2da0b96703cb280a57c052ba0295705caa8124fc0926e0192f0149382e1bc0d0da0886b01c3482e19c0d0ca0886301c3080a17c050ba0285b0142b82e154050a60884b044238160fc090760483702c198060bc050560282700c1182206c2702e02d6f056b380b1bc0b8d604c670163182716c138b404c570562b00adbc056dc09b6b04db5026d9eae6cc02b63015b1006d6c036b409b5700dab00ad3c0569c02b4d015378069ac054ce01a6300d2d80a95c0549e02a4d00d2580a91c0548a01a4300d1d8068e40546e01a3300d1880a5bc332ce0494f024a38264fc0f27a0993703c9a8064bc0524e0286f0443585619c050c60885b0442b82613c0909604847044218260fc0d07a0883b01c1c8260dc0d06a0883301c188060bc050560282700c1182206c2b02e02d6f016b700b5ac05ace02d63016b100b1bc058ce01c5f00e2f007174056de02b6b015b380ad8c056be02b5b015ab80ad4c1369605b4700d3380a998034ca01a5f0152f0069740349601a4700d1f8068ec0346e01a33014b780a59c052be0295704c9f8164dc0325e019270143780a1ac050ce028630142f80a16c050ae028530442582211c1307e0583b02c1b8220cc0305e0182b00c1380608c110362701700eb78075b803ada02c6f0163700b19c058c602c620162f80b178058b602c590162b80b14c058a402c5102e2800adbc056dc02b67015b100ad7c056ae01b4f00da7006d34054de02a6b0153380a98c054be02a5b0152b80a94c0549e02a4b0152380a90c1347605a37014b780a59c052be02957014a780a51c1325e059270143780a1ac050ce028630142f80a16c050ae028530142780a12c0508e028430441d8220dc1305e0582b02c1382208c11036108170173f80b9f805cf602e7a0173b80b9d805ce602e72016bf80b5f805af602d7a016bb80b5d805ae602d7200e3700adfc056f602b77015b980adbc096da02b6b015b480ad9c056ca02b6304db0812d7c096ba07b5b04dac812d5c096aa07b5303da880a9fc034f602a7a0153b80a9d8034e601a490151f8068ec0546e01a33014b300a590052ac0793e0149300a1fc050f6028770143980a1bc210da0286b0143480a19c050ca028630443081e17c0d0ba0785b01c2c81e15c0d0aa0785301c288260fc0907604837044198060bc050560282700c1180b9fc05cfc02e7b0173d00b9dc05cec02e730173900b5fc05afc02d7b016bd00b5dc05aec02d73016b900b5bc05adc03d6d01eb600b1fc058ee01c6f00e370071b4038be01c5d0362b807154056fe02b7b015bb80adcc056de09b6d015b580ada4056ce02b65015b1826d840d6be04b5d035ad826d640d6ae04b55035a981ad441169608b470153f8069ec054f402a770153b0069cc034b601a590152b80694c034a201a4b00d248069040547e01a3b0151b8068cc052fe02977014b78425b4052ce02965034af81a5740d2ae0795504c9f8264dc0325e029270143f80a1ec050ee028730143580a1a8050d2028680143380a198050ca028640143180e184050ae028560142a80e12c11094068470342301a0fc0d07c0383b0341b80e0cc110640182f0141580a0a80504e0282600c1180e06c0d02e02d6f02eb700b5aeb2ad402d67ac2b300b58c0bac402c6f0563380717c038bc01c5d015b7826dac1b6ce02b6304daf812d74056b74c359015ab812d54136a75635104da582ad1c054de01a6baa93500a99ea84cc01a6300d258069240348202a3f00d1d80a8dc034660296f968b3d4c57c0f2ba0295703caa8264fc1b26e0192f0149380a1bc110d6d106701431d4817c0d0ba0285b01c2c80a15c0d0aa0885301c2882212c1108e0983f0441d8360dc110660182f0141580a09c030460881b1280b816dbc096da0bb6b04db4816d9c096ca0db6304db080ad7c1b6ba05b5b02dab836d54056a601a6f00d368069ac034d201a6700d3280698c034c201a5f00d2d806964034ae01a5300d288068fc0347601a3700d198221bc0d0da0886b01c3482219c0d0ca0886301c3080a17c110b608857014298220fc0b07605837044198060bc030560182700c118371bc1b8d60dc6706e31806dbc036d601b6700db1806d540369e01b4b00da3806d0c0b4dd5026606d270129180347c0886f0443582219c110c60884f0442582211c110860183f00c1d8060dc03066038290341280b5fc05afc02d7d016b780b5b805ac404c7f0263e8171ec0b8f204c770263a8171cc0b8e202c6f0163580b19c058c605c5b0262b80adfc1b6fc02b7d06dbe00adec056f402b79015bc00addc156ec02b75055ba00adcc056e402b71015b800adbc056dc02b6b015b500ad9c056cc02b63015b100ad6c056b402b57055ab006d3c0369c01b4d0153f80a9f8054fa02a7c00d3d8069e4054ee02a7500d398369c8034e201a70015378069ac054ce01a6300d2d80a95c0349604a4a00d2480a91c0548c01a4300d2080a8dc0546c02a350d4bf81e5f4152ee07975014b780a59c0929e049470149f80a4f40526e0793500c9780a49c350fe0687d0443d80e1e4150ee068750443980e1c4050de0286b0143380a18c110b60885702c2781212c0908e058430141f80a0f405076038390141b81a0d4050660283100c1780a0ac0504e018230440d89005c05ade02d6b016b380b58c058de02c6b0163380b18c098be05c5b0262b81714c056ce02b66015b280ad7c056b602b5a015ab82ad58056a602b4f02da700ad34054de01a6b0153380698c054be01a5b0152b80694c0549e01a4b0152380690c0546e02a360151a80a5bc052d602967014b184657c092b613957024a981253c0929604947024a180a4fc0527a0293b0149b81e4d4052660192f0149580a49c032460286f0143580a19c050c61185f0642d85615c190a60584f0242581211c0b0860283f0141e80a0ec07072028370341a80a0cc050620182f0141580a09c030460481f0640d84205c0902602d6f016b380b1bc058d602c670163182716c098ae02b6f015b700adac056d402b67015b300ad8c056c402b57055ab00ad540569e09b4e015a680a9bc034d602a6700d3180696c054ae02a4f00d2580a91c0348602a370151b00a8d4052de02967024a781251c0527e0293d0149b81e4d40325e029270143780a1ac050ce028630442d82215c1309e0484b0242382210c0507e0283d0141d80e0e40506e068350141980a0c40305e0282b0141380608c1103610817016b78475ae9cace02d63016378171ac098ce02c630262f82716c098ae09c53015b7816db8056d74d36a015b3836d98056c605b6206daf80ad6e986b40db5706dab00ad4c0369e01b4e00da680a9bc034d602a6700d3180a97c034b602a5700d2980692c0949401a49015238129180348601a410151b8128d80946a0296f024b5cac59c052c61195f024adc4455c092a60494f024a581251c092860293f03c9e8124ec1b26e07935014998064bc052560292700c9180a1bc190d6cf0670143184617c190b6950570642982613c090960484704c2180a0fc0d07a0c83b01c1c8360dc0d06a0283301c188060bc050560282700c1181207c1903623017024098175bc0bad605d6702eb18131bc098d604c670263181317c098b604c5702629806dbc036d601b6700db1806d7c036b601b5700da9806d3c0969c01b4d00da3806d140368601b4200d378169b8034d601a6a00d33816998034c601a6200d2f80696c034b401a5708d2b00694c0348e04a4600d228068fc0347c01a3d024b78125ac092ce04963024af81256c092ae04953024a781252c0928e0494300c9f8064ec0326e0193300c978064b403256019270249280648c0b0de0586b02c3381618c190be0c85b0642b83214c0909e0484b0242381210c0307e0183b00c1b8060cc0305e0182d00c1580e0a40304e0682500c118060840903e0481b0240b81204c058be05c5b02e2b80b14c056be04b5b025ab80ad4c0969e04b4b025a3812d0c054be04a5b0252b80a94c0949e04a4b0252381290c0347e04a3b0251b8128cc052be0195b014ab80654c0529e0194b014a380650c0527e0193b0149b8064cc0525e0192b0149380648c050be0585b02c2b80a14c1909e0c84b0642383210c0907e0483b0241b8120cc0905e0482b0241381208c0303e0281b0140b80604c056be04b5b025ab80ad4c054be01a5b0152b80694c0547e01a3b0151b8068cc050be0585b02c2b80a14c0907e0483b0241b8120cc0305e0282b0141380608c058be05c5b02e2b80b14c056be05b5b02dab80ad4c0d69e06b4b035a381ad0c054be04a5b0252b80a94c0949e04a4b0252381290c0347e04a3b0251b8128cc052be0195b014ab80654c0529e0194b014a380650c0527e0193b0149b8064cc0525e0192b0149380648c050be0485b0242b80a14c0909e0484b0242381210c0907e0483b0241b8120cc0905e0482b0241381208c0303e0281b0140b80604c058be05c5b02e2b80b14c056be04b5b025ab80ad4c0969e04b4b025a3812d0c054be01a5b0152b80694c0549e01a4b0152380690c0547e01a3b0151b8068cc052be0495b024ab80a54c0929e0494b024a381250c0927e0493b0249b8124cc0325e0292b0149380648c050be0385b01c2b80a14c0709e0384b01c2380e10c0707e0183b01c1b80e0cc0305e0282b0141380608c0703e0381b01c0b80e04c05ade05d6b02eb380b58c058de04c6e016358171a8058ce04c6601631817188058be04c5b08e2d00b15c098ac04c53015b7812dac096ce02b63025af812d6c096ae04b5300da7806d380369a02a6f00d3580a99c034c602a5f00d2d80a95c034a602a4f025270369340547e04a3e00d1d8068e40346604a3200d1880a5bc092d604967014b181257c092b604957024a981253c0929c0494da48a600a52c0528e04945024a181250a902800493f0249d8124dc092660192f0149580a49c032460286f02c3581619c050c60c85f0642d83215c190a60484f0242701a1368e0980284b01c2480a11c0908a048430242100e1068c0800483f0241d8120dc090660182f0141580a09c030460481f0240d81205c0902601d6b00eb480759c03ac601d610163780b1b4038ce01c650162f80715c096de04b6d02db580ada4096ce04b65015b180ad84056be05b5b025ab80ad4c0b69604b4700d378069b4034d601a6900d33806994034c601a6100d2f80696c034ae01a5300d2580691c0347e01a3b00d1b8068cc252de0796d094b381e594052be059570249f8124dc0325e019270943781a1b4110d6038690943381a194110c6038610142f81616c0b0ae028530442582211c0b07e0483b0241b8160cc0305e0182b00c1380608c1103622017016bf80b5f805afa02d6f016b700b588098fe04c7d02e3d8171e4098ee04c7502e398171c4058de05c6b0263380b18c0b8b604c5700dbf86adf8036fa09b7c00dbd806de4036ee01b7500db9806dc8036e201b7000db7806dac036ce01b6300dad806d5c0369e01b4d00da5806d280368e04b4600da28069fc254fc01a7da213e0069ec034f401a7900d3c0069dc154ec01a750553a0069cc034e401a7100d380069bc054dc01a6d02d360069ac034d401a6702d33006996844c801a6300d31006974034b601a5a00d2b82a958034aa0aa5400d2780a9380349a01a3f00d1f0068f4352fe0797d054bb81e5d4052de05967024a781251c0327e0193700c978064b40324e079250d43f81a1f4110f6038790543b81a1d4110e603871014378161ac0b0ce028630442d82215c0b09e0484b0242381610c0307e0183b00c1b8060cc0305e0182d00c1580e0a40304e0682500c11806084110362101700eb58075a403ace01d6300eb080b1bc058dc02c6d0562f82f178038ae0bc52025b7816dac0b6d204b6702db1816d84056be02b5b025ab816d4c0b69604b4700d3782e9b8034d601a6900d3380698c034c401a6100d3000697c034b601a5700d2980692c0348e01a3f00d1d8068dc034660b96f03cb682a59c0f2ca0b95f05cab8124fc0926e0192f00c9382e1bc0d0da0886b0543381a194110c60b85f0442d82e15c110a60884b044238160fc090760483702c198060bc030560182700c1182206c2702e01d6f00eb70075b4278de0ac6d05e3582f19c158ca11c630162f8171740b8b605c57a122a80b14c056de02b6d015b580ada4096ce04b6502db1816d84056be05b5b02dac812d5c056a605b51025a7816d2c0968e05b4300d378069b4034d601a6900d33806994034c601a6100d2f80696c034b201a5700d298069440349e01a4b00d2380690c0347e01a3b00d1b8068cc272de0796d024b582e59c0f2ca04963014af816574092b605957940aa80a54c2329e0494b09ca381250c0927e0493b0249b8124cc0325e0192b00c9380648c2f0de0686d05c3580e1a4170ce068650643180e184050be0585d02c2d81615d980aa0285308c2783212c3908e0c84302c1f8120ec0906e0583300c178060ac0304e018230240f83206c4002e0481302eb780b5b815ad60ed6a056b382b5980bac602d6202e3783b1a8158ce0ac6600e2f807178038ba04b6f02db5812d9c0b6c609b5b015ac812d5c136a609b5104da5826d240968e09b4100d378069ac034ce01a6300d2d806964034ae01a5300d2880692c0349201a4700d208068fc0347601a3700d198165bc1d2ce0a95f03cae82a55c0f2aa1194d054a28124fc0926e0192f00c938161bc110d60e86702c3182a17c0d0ba0885b01c2c82a15c0d0aa0885301c288461341109608847054228260fc0907604837044198060bc030560182700c1182206c3e02e05d6f08eb5d0d59c0bac604c6f02e3581319c0b8c604c5f04e2d81315c138a601b6f00db5806d9c036c601b5f00dad806d5c036a601b4f00da6806d2c0369401b47025a3006d14034de05a6e00d358069a8034cf4126600d31806988034be01a5b00d2d00695e804ac01a5300d278369380349a01a3f00d1f0068f40b2de0496b938b381258c232be0495b880ab81254c0929e0494b024a381250c0327e0193b00c9b8064cc0325e0192d00c9580649c0f24a0192302c378321ad960ce0586308c2f83216d280ae0c85304c2781212c0908e0984300c1f8060ec0306e0183300c178060b4030560382900c1381a09403046018210240f83206c3802e04813 20 1048575 8 255 11 2047 21 2097151
def cc_58_11 : Nat → List (Nat × Nat) := unpackCursorV4 0xa356d9d4619b4209714392c458e24a8984a8623682c3680c207bd4f75c617194369c7d639635ec4d5896350e7b4bf4f47c4343a423bc7e355672df7629f402059a16b9a108630b355052610203200020 0x5ade02d6b016b380b58c058de02c6b0163380b18c098be05c5b0262b81714c056de02b6e00db5806da8056ce01b66015b180ad88056be02b5b055ad00ad5c056ac02b53015a780ad380369601b4a015a3806d180568605b420153780a9b8034d602a6700d3180a988054be01a5b06d2d00a95c054ac01a530152780a9380349602a4700d218169080547e02a3e0151e80a5bc052d602967014b183e57c092b60e957024a981253c0929604947024a180a4fc0f27a0293b0149b80a4d4052660192f06c9680a4ac0524e0292500c9180a1bc050d6028670143184617c190b60e8570642981613c090960484702c2180a0fc0d07a0283b0141c80a0dc0506a0283301c188060bc1b05a0282b0141380a094030460481f0640d83e05c0902602d6f02eb581759c05ac602c6f026368171ac0b8d404c6702e33013194098be05c5b0262b81714c056de04b6e025b6816d7c056b605b5a02dabdfcd58056a605b4f02da7016d34054de02a6b0153380a98c054be0da5b0152b83694c0549e04a4b0152381690c0547e05a3d0151d8068e40546f7e235015198068c4052de0496b02cb380a58c1f2be0495b074ab81254c0929e0494b024a381250c0527e0593d0249d8164dc0f26a0293306c9780a4ac0524e04923014378161ac0b0ce0286308c2f83216c1d0ae0c85302c2781212c0908e058430141f8160f40b0760383902c1b81a0d4050660383106c1780a0ac0504e0c8230240f83206c1f02e0481302e37017198096de04b6b025b3812d8c096b204b4502d378169ac0b4ce05a6300d248369140947e04a3b0251b8128cc0b0de0586b02c3381618c07092068450241f8120ec0906e04833044178220ac1104e0882302eb781759c0b8de02c6e02e368171ac0b8ce09c6502e3180b188098ae04c560262a812d9c096cc04b6502dae816d6c0b6ae05b5502da780ad340b68e05b4502da18169bc0b4d605a6702d3182696c134ae09a4f04d2582691c1348605a3f02d1d8168dc0b4660596f02cb382653c1328e0593f02c9b8264bc1324e0586f02c3581619c0b0c60885b0442b82613c1109609847044218160fc0b0760583702c198260bc11056098270441182206c2b02e05d6f02eb38131bc0b8d604c6702e3181716c098ae05b6702db3026d940b6ae05b5602daa816d3c0b69c09b4d02d378169ac0b4ce05a6304d2d82695c0b49e04a4b0252381690c1347e02a3d04d1d8068e41346e02a3504d198068c40b2de05967024a781251c1327e0793d04c9b81e4d41325e0992702c378161ac0b0ce058630442d82215c0b09e0484b0242381610c1307e0683d0441d80e0e41306e068350441980e0c41305e0882b04c1382208c110361581702eb782b59c098de05c6bbda3501319c238cc05c630262e81315c098aa05b6f02db7026daef46d40eb6708db3016d8c0b6c404b57025ab012d540b4de0da6b04d3381698c154b609a5704d2781292c0948e09a4304d1fd308f41347601a3904d1b8468d41346601a3102cb7cd059c0929e0494704c9f81e4f42326e0793506c9782649c0b0de0886b6c03381618c110b60885704c2781212c0908e0884304c1f81a0f4110760383908c1b81a0d4110660383106c178220ac1304e088230440d8c805c09ade04d6e026b58175a809ace04d66026b18175880b8de05c670262f813178238ba04b6f025b5816da8096ce04b66025b1812d2c0969204b4102d378169ac0b4ce05a630252f836974094b601a590252b812954094a601a510552582a91c0947e04a3b0251b8128cc092de04967024af812574092ae049550249f8124dc0925e0492702c378161ac0b0ce058630242f81a174090b6038590242b812154090a6038510442582211c0907e0483b0241b8120cc1905e0882b0641382208c0903604817025b780adb40b6d605b69025b3812d940b6c605b61025af816d6c0b6b204b5702da9816d44134de02a6d05d358069a4134ce02a6506d318069840b4be05a5d02d2d81695c134aa05a5302d1f8128ec0946e05a330443781a1b4110d6038690443381a194110c60386102c2f8161740b0b6058570442a81614c0b07e0483b0241b8160cc1105e0882b0441382208c058de02c6b0163380b18c056de02b6e015b580ada8056ce02b66015b180ad880569e02b4e00da5806d280568e01b46015a1826d08054de01a6b0153500a99c054cc01a630152780a9380349602a4700d21826908050de0286b0143380a18c1109e0484b0242382210c0507e0683d0141d80a0e40506e028350141980e0c40305e0882d0141580a09c0504a01823026378171ac098ce05c630262a816dbaee6cc11b4e02d378369ac134ce05a6304d2781292c0948e09a4300d1cdd88d40b0de0886b0443381618c1109e0484b0242382210c0707206835044178220ac1104e0882300eb58075a40bace02d6300eb080b1bc058dc02c6d0162f80b1780b8ae02c5202db7812db40b6d605b6902db3812d940b6c605b61015af816d6c0b6ae02b5302da5816d1c054de02a6d00d3580a99c054ca02a5f00d2d816968054ae05a5600d2980a9340349602a470152280a8fc0347602a3700d1982a5bc0f2da0a96703cb280a57c0b2ae0593f02c9b8064bc0524e0a86f034368221ac070d20a8670343282218c070c20285f02c2d81615c050a60884b044238160fc0b0760583702c198060bc050560282700c1182206c1f02e01d6f00eb70075b4058de05c6b02e3380b18c058be05c5d02e2d81715ee88aa02c53015b7816dac0b6ce02b63015af812d740b6b605b5902dab812d54056a605b5102da7816d2c0b68e05b4300d358169a8034d202a6702d3300698c034c202a5702d2b5c09540549e01a4b0152380690c0547e01a3b0151b8068cc052de0596b02cb380a58c052be0595d02cad81655c0f2aa0295307ca783a52c1d28f0d14302c9f8164ec0b26e0593300c9780a4ac0524e01923014378161ac0b0ce028630142f8161740b0b60385902c2b81a154050a6038510c42783a12c1d08e8d04302c1f8160ec0b06e0583300c1780a0ac0504e018230c40f83e06c1f02e0d0130173f00b5d8058fe02c7b02e3c80b1dc058e602c7102e2c813154036fe02b7e00dbe806ddc036ea01b7300db9006d64036b001b55015aa006d3c0369601b4700da18069dc054ec01a7500d3280a990034b201a5800d2a80a9500349e02a4e00d258069280348e02a4600d218069080347e01a3e00d1e80a1fc050f6028770143980e1640d0aa0584f02c2581611c0b0860183f00c1d8060dc030660182f00c168060ac05052018270141280608c0304202d7f016bf00b5f405ade02d6e016b100b5800b8fe04c7d02e3d8171e40b8ee04c7502e398171c4058de02c6b0163380b18c0b8b605c5700dbf80adf8036fa02b7c00dbd806de4036ee01b7500db9806dc8036e201b7000db780adb8036da01b6700db2806d8c036c401b5b00dad006d5c056ac01b4f00da5806d1c0368601a7f00d3e8069ec034f401a7900d3c0069dc054ec01a750153a00699c054cc01a6500d2e80696c034b401a570152b006954054a801a4f0152700692c0349401a470152300690c0348401a3f00d1f0068f4172fe0797d054bb81e5d4052de0296702ca781651c0327e0193700c978064b40324e0292505c3f81a1f4110f6038790543b81a1d4110e6038710143780a1ac050ce028630442d82215c0b09e0584b02c2381610c0307e0183b00c1b8060cc0305e0182d00c1580a0a40304e0282500c11806084110360f81700eb78075b803ada02c6f0563680b1ac058ce02c650163180b17c058b602c570162980adbc096da02b6b015b480ad9c056ca02b6302db080ad7c056b602b57015a9816d3c0b69605b4702da18069bc054dc01a6d00d2f80a978034b601a5900d29806948034a201a4f00d258069280348e02a4600d218068fc0347601a3700d1980a5bc0f2da0296b014b380a594052c60295f014ad80a55c052a60f94f074a583a51c212860593f02c9d8164dc0b2660192f00c9580649c032460286f0343680a1ac050d2028670143280a18c070c20285f0142d80a15c050a61384f0742583a11c210860583f02c1d8160dc0b0660182f00c1580609c030461081f07c0d83e05c2102602d6f016b580b5a805ace02d660163780b1a8058ce02c6600e2f807178038ba02b6f015b580ad9c056c602b5f025ae80ad6c056b202b57015aa80ad4c136a20ab4b02da38069bc034d601a6700d3180696c034b201a5700d298069440349601a4900d238069040347e01a3b00d1b8068cc052de02967014af81e574052ae0295506c9f8164dc0325e019270143780a1ac050ce028630142f81a174050b6028590142b80a154050a6038510442582211c1b07e0583b02c1b8220cc0305e0182b00c1380608c1103631017016b7dc95aee2ace02d63016378171ac0b8ce02c6302e2f83716c0b8ae0dc5300db7816db8036da01b6700db2806d8c036c401b5f00dad806d68036af5535600da9806d3c0369601b4700da180699ee04cc01a6500d2f80696c034b401a57b792b00694c0349e0da4e00d258069280348e04a4600d218069080347e01a3e00d1e80a5be762d732167014b1c8057e362b713157860a983653c0b2960594706ca18064fc032760193700c998064bc0325a0192b00c9381e494032460286f72835b5819c050c6ae05f5482da5c15d180a60d84f02c2581611c1b0860183f00c1d8060dc030660182f00c168060ac07052018270341280608c030424801f2080d8c005c1802601e7f00f3f0079f403ad601d6a016b380759805ac602d620163d00b1e0058ee02c760163a80b1d0058de02c6a0163380b198058ae02c560162a80adfc0b6fa02b7b015bc80addc056ea02b7304db880adbc056d602b67015b1816d7c096ba09b5b04dac816d5c096aa09b5304da8826d2c1369205b4704da080a9fc054fc02a7d0153780a9b8034d601a6900d3180a988034c202a5f0152f00a974054b802a570152a80694c154a401a5100d2800a934034960aa4a0152380a9180548a02a440151f8068ec0546e01a33014bf84e5f4052ee02975014b780a59c152be0795d074ab81e5541327e0593700c9780a49c050fe1c87d0143d80a1e4050ee02875014398221c4050de0286b0143380a18c150be0685d0442d80e1641d0ae068550442980e144110960884704c1f8160ec0b06e0883300c1780a0ac0504e018230440d84205c03ad601d6a056b380759805ac602c6f0763502b19c158cc02c570162b00b154056de05b6b02db380ad8c0b6be04b5d04dad826d640b6ae04b5504da9826d441369609b4902da3826d04054de01a6b0153380698c054be02a5d0152b80a954034a602a4d00d2580a91c0548a02a3f00d1d80a8dc034660296f074b382a57c0f2ba0a95703caa8264fc0b26e0192f0149380a1bc110d60e8670143182a17c0d0ba0885b01c2c82a15c0d0aa0885301c2882212c1108e0983f02c1d8160dc110660182f0141580a09c030460881b1780b8079fc03cfc01e7d016bb00b5d005acc02c7e0563e00b1b8038cc02b7f02dbe80adec056f202b77015ba80adcc136e202b6f015b580ad9c056c609b5904da4812d14054fe02a7e0153e80a9bc054dc01a6b00d3480698c054c401a610152a80a9500349201a480152280a9100547e01a3b0151b8068cc050fe0887d0143d80a1e4050ee02875014398221c4050de0286b0143380a18c07092068450441f8160ec0b06e0883300c1780a0ac0504e0182300f3f8079f803cfa02d7e076be00b5b8038fc01c7c0163b00b1d0058cc02b7f025be80adec056f202b77015ba80adcc0b6e202b6f015b580ad9c056c605b49025a280a9fc054fc02a7d0153780a9b8034d601a6900d3180a988034c205a6000d248069200548a02a440151f8068ec0546e01a330143f81a1f4050f6028790143b80a1d4050e6038710143780a1ac050ce0286301c2481a1140b07e0583b02c1b8160cc0305e0282b0141380608c03cf601e7a00f3c8079e005cee02e760173a80b9d005ce601e7100eb78075b803ada02c7f0163f00b1f4058de02c6e0563682b1b0058ce02c650163100b17c058bc02c5202dbf812df40b6f605b7902dbb812dd40b6e605b71015b7812db4056d602b69015b380ad94056c605b61015af80ad74056b602b5702daa80ad4c0b69605b470153f80a9f8054fa02a7c00d3d8069e4054ee02a7500d3982e9c8034e201a700153780a9b8054da02a5f0152f00696c034b201a5301529006944034960aa4a0152380a9180547e01a3b0151b8068cc172fe0797d054bb81e5d4052de0796d014b380a594052be0295702c9f8164dc0325e0292705c3f81a1f4110f6038790543b81a1d4110e6038710143781a1b4050d6028690143380a194050c6038610142f80a16c050ae028530442582211c0b07e0583b02c1b8160cc0305e0282b0141380608c110360f817016b78175ac0bace02d63016378171ac0b8d404c6702e3300b18c098be05c5b0262b81714c056de02b6e00db5806da80b6ce01b66015b180ad88136be09b5b04dad026d5c156ac09b53015a780ad380569a02a6f00d3580a99c034c602a5f00d2d80a95c034a602a4f0152680692c0548e02a4500d2180a8fc0547a01a3b00d1c80a8dc0546a01a3300d1880a5bc092d605967014b184657c092b619957024a981253c0929604947024a18264fc0f27a0493b04c9b81e4d4092660192f0149580a49c032460286f02c3581619c050c61185f0642d85615c190a60584f0242581211c0b0860983f0341e8260ec07072098370341a8260cc070620182f0141580a09c030460481f0640d85605c0902601d7f00ebf0075f403ade01d6d016b380759405ac602d610163f84f1f4058ee02c7503e3781f1b40f8ce0ec650162f80b15c056fe04b7d015bd80ade4056ee02b75015b9826dc4096de04b6d03db5826da4096ce04b6503db181ed84056be02b5b015ab80ad4c1369604b470153f80a9f8054fa02a6f0153680a99c054ca01a6300d3080a97c054bc01a5b00d2c80694c054a401a5100d2584e9280548e02a460151f8068ec0546e01a33014bd00a5e0052ee02976014ba80a5d0052ce02966014b280a57c052b402957014ab0124fc0f27c0493704c990064bc05254029270149300a1fc210fa0287b0143c80a1dc050ea028730843881e1bc0d0da0786b01c3481e19c0d0ca0786301c3080a17c050b6028570142984212c2108e0983f0241d8120dc130660182f0141580a09c030460781b03c0b8079fc03cfc01e7d0163f8131f4058f602c790163b80b1d4058e604c710163780b1ac058ce02c63015bf80adf8056fa02b6f015b7006dac036d201b63015b1006d840569e01b4b015a3806d0c054ec02a74015330129380546c0297e03cbe00a5b8032cc0494e024a30064f80526c0287f0843e80a1ec050f2028770143a80a1cc210e20286f0143580a19c050c60484f0242581211c090860183f0141d80a0dc03066038190340a80b9fc05cfc03e7d01f3e0075fc03afc01d7d00eb78075b405ad602d69016b380759405ac602d610163f8731f4058f602c790163b80b1d4058e608c710363781b1b40d8d606c670763281b18c058be02c5b0162b80b14c056fe05b7d015bd80ade4056ee02b75015b9826dc40b6de04b6d035b5826da40b6ce04b65035b181ad84056be02b5b015ab80ad4c0b69e09b4b02da3822d0c054fe02a7e0153e80a9bc054da01a6b00d3480a99c054ca01a6300d3080a97c054bc01a5b00d2c80694c054a401a510152780692c3949402a470152300690c0547e01a3b0151b8068cc052fe1097d014bd80a5e4052ee02975014b98425c40d2de0696d034b581a59c0f2ca06963014af80a56c052ae02953044a784252c2128e0894304c9f8164ec0b26e0993300c9780a4ac0524e019230143d80a1e8050f2028780143b80a1d8050ea028740143980e1c4050ce028660143280a17c050b60285a0142b80a158050a60684f01c2581a11c070860683f0341f00e0ec0b06e0383304c190060bc050560282a0141380a098030460681f01c0d81a05c0702601e7f00f3f0079f405afe08d7d016bd80b5e405aee02d75016b98235c405ade02d6b016b380b58c058fe05c7d0163d80b1e4058ee02c75016398271c4058de02c6b0163380b18c0b8be08c5b02e2b82314c056fe02b7e015be80adbc056dc01b6b00db4806d8c056c401b61015af806d6c116b402b57015ab006d4c0569e01b4b015a3806d0c054fe10a7d0153d80a9e4054ee02a75015398429c4054de02a6b0153380a98c114be08a5b0452b82294c1349e05a4b02d2382690c0347e02a3b0151b8068cc052fe0397d014bd80a5e8052f202978014bb80a5d8052ea02974014b780a5ac052d402967014b300a58c072be0395b01cab80e54c0729e0994e01ca580e51c072860394200c9f80a4ec05274029370149b0064cc0725e0392b01c9380e48c050fe0287e01c3e81a1f0050de0286e00c358061a8050ce018660143180a188070be0385b01c2d00e15c110ac0385301c27826138070960384a01c23812118070860384200c1f8060f8050760283a0141b80a0d8030660183201c1780e0ac070540382703c1300e08c0503e0281e0140e8075bc03adc01d6db6a37db11b4058d602c67ac232dad18c058bf6a45bb4a2b80b14c0b6de04b6d015b5d34da4056ce04b6504db1da0d84056be05b5b02dab80ad4c0b69e09b4b02da3826d0c054de05a6e02d3680a97c0b4bc01a5b00d2c80694c0b4a401a510152780692eba49402a47aa12300690c0547e01a3b0151b8068cece2de0796d014b580a59c0f2cb66163014afce856e622ae029538f0a7c6452e2428f0a14304c9f8164ec0b26e0993300c9780a4ac0524e01923b283781a1b4050d6038690143381a196c80c6038610142fb9016daa0ae0285356027a9c12d2c08e8a04304c1f8160ec0b06e0983300c1780a0ac0504e018232300f8fc06c5a02e0a013016b780b5b80bace02d63016b100b1bc058dc05c670163100717c038bc01c5d015b7816dac0b6ce02b6302daf812d740b6b605b5902dab812d540b6a605b5102da6816d2c0b68e05b4500d378069ac034d401a6702d3300698c034b601a5900d2b80694c034a201a4b00d2480691c0348201a3f00d1d8068dc034660296f02cb382a57c0f2ba0a95703caa83e5341528a0593f02c9b8064bc0324e0286f02c3581619c050c60a85f0342e82216c070b20a8570342a82214c070a21884d0442582211c1508a0583f02c1d8160dc0b0660182f00c1580609c030460881b07c0b80b5bc0bad605d67016b180b1bc0b8d605c670163181717c0b8b605c5702e29806dbc036da01b6b00db5006d9c0b6cc01b6500daf806d6c036ae01b5300da7806d2c0368e01b4300d378169b8034da01a5f00d2d806968034af6225600d2980693c0b49c01a4b00d2500691c0948c01a4300d210068fc0347c01a3d014b78165ac0b2ce0296307caf83a56c1d2af0815302ca781652c0b28e0594300c9f8064ec0326e0193300c978064b4032560192703c9280648c050de0586b02c3380a18c310be0e85b0742ba2014c0b09e0584b02c2381610c0307e0183b00c1b8060cc0305e0182d00c1580e0a40304e0682500c118060843103e0f81b07c0b82004c056de02b6d015b5826da4056ce04b65015b180ad84056be02b5b015ab80ad4c054de02a6d00d358069a4054ce02a6500d31806984054be02a5d00d2d80a95c054aa01a530151f8068ec0546e01a330143780a1b4050d6038690143381a194050c6028610142f80a16c050ae028530441f8160ec0b06e0883300c1780a0ac0504e0182302e37581198056de09b6b06db380ad8c2369204b45015378069ac054ce01a6300d2cd6c9140547e01a3b0151b8068cc050de0886b0443380a18c07092068450441f8220ec1106e0883300c1780a0ac0504e01823 20 1048575 8 255 11 2047 21 2097151
def cc_58_12 : Nat → List (Nat × Nat) := unpackCursorV4 0x335ccc4722f8b2b7ecacfa0a5bca70cc8dbd20fce757d1ae4f5d1d150485106138184b0610e3c40860f6183a860de1834860be28237845c630ab8c0055 0x75ac03ad402d6700eb300b58c058de02c670162f82b174058ae02c55015b780adac056ce02b63015af812d74056b602b59015ab80ad54056a605b5102da5816d1c054de02a6e00d3580a99c034c602a620152f80a978054ba01a4b0552500a91c0548c02a3f00d1d80a8dc034660296f014b380a57c0f2ba02957014aa8164fc0b26e0192f0149380a1bc050d6028670143180a17c0d0ba0285b0142c80a15c050aa0285301c2882212c1108e0583f02c1d8160dc0b0660182f0141580a09c030460881b07c0b8171a80b8ce05c6602e2b81715b2e8aa02b6f02db5816d9c056c602b5f025ae816d6c0b6b205b57025aa80ad4c0b6a205b4b02da380a9bc054d602a670153180a97c0b4ba02a5b00d2c80a95f324aa02a5300d2882a92c0548e02a3f02d1d80a8dc0b4660296f02cb380a57c0b2ba0595703caa8164fc0b26e0f92f0149380a1bc0b0d6058670143180a17c0b0ba0585b01c2c81615c0d0aa0285301c2882212c1108e0583f02c1d8160dc0b0661882f0141580a09c110460881b07c0b80b1b8058bc05b6f025b6816dac0b6d205b67025b2816d8c0b6c202b5f02dad816d5c056a602a6f0153682a9ac034d202a670153282a98c034c202a5f0152d80a95c054a602a3f02d1d80a8dc0b4660886f034368221ac070d2088670343282218c070c20285f02c2d81615c050a60583f02c1d8160dc0b0660882f0141580a09c1104602c6f00e3700b1ac058d402c670163300718c038c402b6f015b580ad9c056c602b4f025a680ad2c0569202b47015a280ad0c1368202a6f00d3580a9a8054ce02a6600d3180a8fc0347602a3700d1980a1bc050d6028670143180a13c0d09a0284b0142480a11c0508a0284301c208220fc0b07605837044198060bc050560282700c118175bb2e8cc05b6f02db5816d9c0b6c611b49025a28169bee44d76a26702d318069272c48a11a3f02d1d8168dc234660586f0443582219c0b0c603849034228220fc0b07605837044198220bc1105608827044118175fc0bafc05d7d02eb78175b80bac404c7f0263e8171ec158f405c7904e3c0131dc0b8ec04c7502e3a0131bc0b8d605c6a026338171980b8c605c5b0562d01315c0b8ac04b7f025bf012df4096f804b6f015b7016d9c0b6c602b6202dad80ad680b6ae05b5602da7816d381569a09a7f04d3e82a9ec154f209a7704d3a82a9cc1b4e205a6f02d3581699c0b4c60aa5b04d2b81693c0949604a4702d218268fc0547a09a3b00d1c8268dc0546a09a3300d1882a5fc252fa0a977054ba8165bc0b2ce0494f024a38264fc0f27a1293703c9a8364bc1324e0a87f0943e8221ec110f20a8770543a8221cc110e20586f02c3581619c0b0c60885b0442b81613c090960484702c218260fc0d07a0883b01c1c84a0dc0d06a0883301c188360bc11056098270441182206c7202e05d6f02eb38131bc0b8d605c6a026338171980b8c605c5b04e2d01315c0b8ac04b6f015b7016d9c0b6c602b6202dad80ad680b6ae05b5602da7816d381369a05a6f02d3581699c0b4c609a5b04d2b81693c0949604a4702d218268fc0547a09a3b00d1c8268dc0546a09a3300d188165bc0b2ce0494f024a38264fc0f27a0993703c9a8264bc1324e0586f02c3581619c0b0c60885b0442b81613c090960484702c218260fc0d07a0883b01c1c8260dc0d06a0883301c188260bc11056098270441182206c2b02e01e7f00f3f0079f403cf801d6b00eb480b59c05ac602d610163f80b1f8058fa02c6f0163680b19c0b8ca02c5f0162f00b1480b6fe05b7d04dbd826de40b6ee05b7504db9826dc4056de02b6d015b586ada4056ce04b65015b180ad84056be02b5b015ab80ad4c1369605b4700d3d82a9e8034f20aa780153b80a9d8054ea02a7400d398069c4054ce02a660153280a97c034b602a5a0152b80a958034a601a4b0552500a91c0548c02a3f0151f0068ec0546e01a330d51902a5fc252fa0a977054ba80a5bc052da0296703cb280a57c052ae0993f02c9b8064bc0524e0a87f0943e8221ec110f20a8770543a8221cc110e20286f0143680a1ac070d2028670343280a18c050c20285f0142d80a15c050a60884b044238260fc0b07605837044198060bc050560282700c1182206c6e02e01d6b00eb480b59c05ac601d610163780b1b4058ce05c650162f80b15c056de02b6d015b5826da4056ce04b65015b180ad84056be02b5b015ab80ad4c1369605b470153380a998054ca02a5f00d2d80a968054ae02a5600d2980692c1549402a470152300a8fc0547c01a3b0151b8068cc134640296f014b680a59c0f2ca0295f014ab8264fc0b26e0192f0149380a1bc050da0286b01c3480a19c0d0ca028630143080a17c050b6028570142982212c1108e0983f02c1d8160dc110660182f0141580a09c030460881b0840b80b5fc05afc02d7d016b780b5b805ac405c7f02e3e82b1ec158f205c7702e3a82b1cc1b8e202c6f02e3581719c058c60ac5b02e2b806dfc036fa01b7b00dbd006de4036f001b77055bb006dd4156e801b6f00db5806da8036ce0bb6600db1806d6c036b401b57055ab006d3c1b69c01b4b00da3806d0c0368401a7f0153f0069f4054f801a6f0153700699c034c601a6200d2d806968034ae05a5600d278369380349601a4a00d238129180348601a4200d1f8068f80347a0a97f094be82a5dc152ea0296f05cb383653c0b28e0193f00c9b8064bc0325a0192703c9282a1fc250fa0887b0443c82a1dc150ea088730443880a1bc110d60b8670143182216c110ae0d84f02c2581611c110860183f00c1d8060dc030660182f00c168060ac07052018270341280608c030420881b1b00b8171f80b8bc04b7f025be82adec156f204b77025ba82adcc256e204b6f025b681edac276d204b67025b281ed8c0f6c204b5f02dad812d5c0b6a60aa7f0953e82a9ec154f20aa770553a82a9cc254e207a6f0153681e9ac034d207a670153281e98c034c205a5f05d2d82e95c0b4a61aa3f0251d8128dc354660797603cba01e5980f2ac0793e0543f84a1f4110f6088790543b82a1d4110e60887103c3781a1b40f0d60386903c3381a1940f0c60386102c2f82216c170ae058530d41f8120ec0906e088333b0178220acc404e0882301f3f80f9f807cfa03e7c01eb580b5a40dace05d63016b08171fc0b8fc05c7d02e3780b1b40d8ce05c6502e2f8171780b8a405b7f02dbe82adec156f205b7702dba82adcc256e205b6f025b681adac2f6d205b67025b281ad8c0d6c205b5f02dad816d5c0b6a608b4b02da382a9fc254fa0aa7b0553c82a9dc154ea0aa730953881a9bc054da06a6b00d3481a99c054ca06a6300d3081697c174b60ba5702d2982292c1148e1aa3f02d1d8168dc354660a97f094be82a5dc152ea0696f034b681a59c0f2ca0595f05cab86a4fc0b26efc12f7a09380e1ec110f4038790443c01a1dc0d0ec068750343a00e1cc070e2068670343301a1940b0be0385b0442d01a15c0d0ac0385301c258221280d08e068460341f81a0f8070760583701c198220c80d05e0382b0341380e08c070360681702e378171b80b8da05c5f02e2f0171480b6de04b6d055b5de8da40b6ce04b65ca1b1e4cd840b6be05b5b02dab816d4c1569605b47c9137e449b4154d601a6905533d60997204c601a6102d2fdc496ed24ae05a530552582a91e9c47e05a3b02d1bd0c8cf1e2de0796d054b381e5940b2bf361578209f8164ddf625ef3127c703781a1b4110d6038690543381a194110c60386102c2f82216db40ae058530442582211d0807e0583b02c1b8220ccea05e0882b3081382208c1103634017015af816d6c0b6ae02b530152f80a96c054ae02a530151f8168ec0546e05a330142f81616c0b0ae0285302c1f8160ec0b06e058330441780a0ac0504e08823015af812d6c096ae02b530152f80a96c054ae02a530151f8128ec0546e04a330142f81616c0b0ae028530241f8120ec0906e048330441780a0ac0504e08823015af816d6c0b6ae02b5300d2f80696c034ae01a5300d1f8068ec0346e01a330142f81616c0b0ae0285302c1f8160ec0b06e0583300c178060ac0304e018230163780b1b8038d601c6a01633807198058c602c62015b780adac056ce02b63015a7812d340569602b49015a380ad140568605b410153780a9b8034d602a6a0153380a998034c602a620151f80a8f80347605a3a0151b80a8d80346605a320143780a1ac050ce028630142781a13405096028490142380a114050860384102c1f8160ec0b06e0583300c178220b405056028290141380a0940304608821015af80ad6c056ae02b530152f81696c0b4ae02a5302d1f80a8ec0546e05a330142f81616c0b0ae028530441f80a0ec0506e0883302c178160ac0b04e05823015af812d6c096ae02b530152f80a96c054ae02a530151f8128ec0546e04a330142f81616c0b0ae028530241f8120ec0906e048330441780a0ac0504e088230152f81696c0b4ae02a53014af80a56c052ae02953014978164ac0524e059230142f81616c0b0ae0285302c178160ac0b04e058230440f80a06c0502e08813015af816d6c0b6ae02b530152f80a96c054ae02a530151f8168ec0546e05a330142f80e16c070ae0285301c1f80e0ec0706e0383301c1780a0ac0504e03823015af816d6c0b6ae02b530152f81696c0b4ae02a5302d1f8168ec0b46e05a33014af80a56c052ae029530149f81a4ec0526e06933014978164ac0524e0592302eb30171b8056de05b6b02db380ad8c0b6938c348025a2e2cd10054de02a6b0153380a98c034938a248c4922e209100547e05a3b0151b8168cf0e29186144014378161ac0b0ce0286301c24e141200d08b8404402c1f8160ec0b06e058330441780a0ac0504e08823016b78175b809ada02c6f02e3581719c058c602c5f0262e81316c098ae11c5501629812dac0b6d404b69025b3812d98056c604b61025ab812d58096aa04b4f025a5812d1c0968602a6f0153580a99c054c602a5f0252e80a96c034b202a5706d2a80a94c034a202a4f06d2580a91c1b48602a3f0251d80a8dc094660296f024b581259c052c60295f024ae81256c092ae04955014a981253c0929604947024a18124fc0927604937024998124bc05256029270249180a1bc0b0d6058670143180a17c090ba0485b01c2c81215c0d0aa0285301c2883213c190960c847064218120fc0907604837024198320bc05056028270641181207c0903604817024098175bc0bad605d6702eb18131bc0b8dc04c6d026338131940b8c605c620262f81716ef68b404c5702e2b01714c096ce04b66025b2816d7c0b6b77a35a02dab816d580b6a605b4f02da7016d340b4de05a6b02d3381698c134be0da5b04d2b83694c0b49e04a4b0252381690c0b47f4d23d02d1d8068e40b46e05a3502d198068c40b2de0496b02cb381258c232be0495b8a0ab81254c0929e0494b024a381250c0b27e0793d0249d8164dc0b26a0493306c978124ac1324e0492302c378161ac0b0ce0586308c2f83216d300ae0c85302c2781212c0908e0584302c1f81a0f40b0760383902c1b8160d40b0660383106c178260ac1304e0c8230240f83206c6602e04813026b78135b80bada04c6f08e368131ac098ce04c650263181717c0b8b605c5702e29812dbc096dc04b6d025af812d78096b604b59025a9816d48096a204b4f025a5846d280968e04b46025a18129bc1b4da04a6b00d3481299c094ca04a6300d3081697c0b4b605a5702d2983693c1b4960da4706d218128fc0947604a37025198125bc092da0496b024b3812594092c60495f024ad81255c092a60494f024a581251c092860493f0249d8124dc092660492f0249581249c092460486f034368121ac070d2048670243281218c070c20585f02c2d81615c0b0a60c84f0642583211c190860483f0241d8120dc090660c82f0641583209c190460481f0240d81205c0902602d6f016b701759c05ac602d620163780b1b80b8ce02c620162f80b178058ba02b6f02db5816da8096ce05b66015b1816d6c0b6b204b5702da9816d440b69605b49025a3816d04054de02a6b0153380a98c054be02a5d0552d806964054ae02a55055298069440549a0aa4b0152380a9140547e04a3b0151b8168cc052de05967054af81e574152ae0795507ca682a5140927e0493706c9780a49c050de0586b02c3380a18c150be0685d0442d80e164150ae068550442980e1442309a0884b0442382a1140b07e0483b0241b8160cc1b05e0282b0141382208c110360f817 18 262143 7 127 11 2047 21 2097151
def cur_58 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_58_12 (Nat.sub p 384)) (cc_58_11 (Nat.sub p 352)) (Nat.blt p 384)) (Bool.rec (cc_58_10 (Nat.sub p 320)) (cc_58_9 (Nat.sub p 288)) (Nat.blt p 320)) (Nat.blt p 352)) (Bool.rec (Bool.rec (cc_58_8 (Nat.sub p 256)) (cc_58_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_58_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (cc_58_5 (Nat.sub p 160)) (cc_58_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_58_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_58_2 (Nat.sub p 64)) (cc_58_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_58_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def f_58 : Nat → Nat × Nat := unpackForestF 0xcca5500c5fcb466cb24500c5bc7363c7361c726fc726dc7263c716fc706f00c57c2348c2344c2248c2245c2244c2148c2144c2048c204400c5300b5f00b5b00b57bf356bf23500b5300b4fbd46abd36a00b4b00b47bb366bb23500b43ba45500a5fb7d6bb7d67b7a66b7a5600a5bb246fb246db2463b245bb2457b2361b216fb2163b206fb206300a57b125600a53b046600a4faf26eadb66ada66ada5600a4ba956aa9566abb66a9351a926aa9266a915fa905f00a47a826600a43a6567a636aa635a00a3f00a3ba314ca3140a304ca304000a37a227ca0567a1455a0266a025600a339ec559ea550095f9cb6b9cb679c9360095b93c6d93c5793b6193b4b93a6d93a5b93a579827c93a4b9757093a479657d93a3f9457d9427c9426493a3300957919369181891814009538ec668ea6b8fc7c8ea678ea450094f8b36b8d17c8b3678b2668b1668b1360094b8836b8826b882678823f8823300947871648336f8336b8597c833678493483363831668313600943825670093f0093b009377f9667f936009337e27c7e07f7cd677ca667ca560092f7b9660092b7a3707a07f775677736a7735a77d6777a667734200927761660092373c5573a5574164739230085f6eb6b6eb676ea6b6ea676ea3f6ea3b6ea376ea336e8360085b5bc6d5bc575bb615bb4b5ba6d5ba5b5ba576a27c5ba4b695705ba476857d5ba3f6657d6627c662645ba335b95b5b9576417c5b94b5b94762d7d5b93f6117c611645b9335fd7d5fa7c5b92f5e97c5b92b5d57d5d3705b9275c17c5b923008575a82458a33588365882c588240085355c6655a6b56c7c55a6755a450084f4d36b5407c4d3675307c4d267520344d23f5104c4d2374f92f4f9274d1664e12f4e1274d0664d0360084b4836b4826b482674823f48233481674813f4812f4812700847470644336f4336b4587c43367448344336343066430360084340d6741d7d40967409570083f0083b008373e87c3ca673d9553c8663c836008333b27c3b17f3556735266352563516b3857d3827c351673627636176361343515b351570082f32a6b3387c32a67328660082b313703117f29d6729b6a29b5a2ed672ea6629b422996b2cd7d2cb70299672aa762a9762a94c2995b2995700827288642526f2526b2707c252672602425263250660082321b6b2397c21b6721a6621966219360081f1e36b2007c1e3671e1661e0661e0360081b1d2481ac731c2781ab7f1ab731aa70085670846b0845b18b660836b1757d17270083671547615376152380835b1367a1337a1326008357126770834f1138c0ee770eb760eb660f5670ea38083430cc5b0cb5b0cb430826a0bb430825a0a5670a166082420823a0816a0806a00817070640136f0136b0587c0136704834013630325b0325701124020140106601036008130003f 9 11
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV4 fullMask g_58 ep_58 410 bds_58 (dagTraceF fullMask rootStock 11 f_58) (cur_58 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_0 : treeBlockF 0 32 (dagCheckNodeV4 fullMask g_58 ep_58 bds_58 410 (dagTraceF fullMask rootStock 11 f_58) cur_58) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_1 : treeBlockF 32 64 (dagCheckNodeV4 fullMask g_58 ep_58 bds_58 410 (dagTraceF fullMask rootStock 11 f_58) cur_58) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_2 : treeBlockF 64 96 (dagCheckNodeV4 fullMask g_58 ep_58 bds_58 410 (dagTraceF fullMask rootStock 11 f_58) cur_58) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_3 : treeBlockF 96 128 (dagCheckNodeV4 fullMask g_58 ep_58 bds_58 410 (dagTraceF fullMask rootStock 11 f_58) cur_58) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_4 : treeBlockF 128 160 (dagCheckNodeV4 fullMask g_58 ep_58 bds_58 410 (dagTraceF fullMask rootStock 11 f_58) cur_58) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_5 : treeBlockF 160 192 (dagCheckNodeV4 fullMask g_58 ep_58 bds_58 410 (dagTraceF fullMask rootStock 11 f_58) cur_58) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_6 : treeBlockF 192 224 (dagCheckNodeV4 fullMask g_58 ep_58 bds_58 410 (dagTraceF fullMask rootStock 11 f_58) cur_58) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_7 : treeBlockF 224 256 (dagCheckNodeV4 fullMask g_58 ep_58 bds_58 410 (dagTraceF fullMask rootStock 11 f_58) cur_58) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_8 : treeBlockF 256 288 (dagCheckNodeV4 fullMask g_58 ep_58 bds_58 410 (dagTraceF fullMask rootStock 11 f_58) cur_58) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_9 : treeBlockF 288 320 (dagCheckNodeV4 fullMask g_58 ep_58 bds_58 410 (dagTraceF fullMask rootStock 11 f_58) cur_58) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_10 : treeBlockF 320 352 (dagCheckNodeV4 fullMask g_58 ep_58 bds_58 410 (dagTraceF fullMask rootStock 11 f_58) cur_58) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_11 : treeBlockF 352 384 (dagCheckNodeV4 fullMask g_58 ep_58 bds_58 410 (dagTraceF fullMask rootStock 11 f_58) cur_58) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_12 : treeBlockF 384 410 (dagCheckNodeV4 fullMask g_58 ep_58 bds_58 410 (dagTraceF fullMask rootStock 11 f_58) cur_58) = true := by decide +kernel
theorem nj_58_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeV4 fullMask g_58 ep_58 bds_58 410 (dagTraceF fullMask rootStock 11 f_58) cur_58) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_58_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_58_1 h1 h2)
theorem nj_58_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeV4 fullMask g_58 ep_58 bds_58 410 (dagTraceF fullMask rootStock 11 f_58) cur_58) i = true := block_join nj_58_1 (fun _ h1 h2 => treeBlockF_at nb_58_2 h1 h2)
theorem nj_58_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeV4 fullMask g_58 ep_58 bds_58 410 (dagTraceF fullMask rootStock 11 f_58) cur_58) i = true := block_join nj_58_2 (fun _ h1 h2 => treeBlockF_at nb_58_3 h1 h2)
theorem nj_58_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeV4 fullMask g_58 ep_58 bds_58 410 (dagTraceF fullMask rootStock 11 f_58) cur_58) i = true := block_join nj_58_3 (fun _ h1 h2 => treeBlockF_at nb_58_4 h1 h2)
theorem nj_58_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeV4 fullMask g_58 ep_58 bds_58 410 (dagTraceF fullMask rootStock 11 f_58) cur_58) i = true := block_join nj_58_4 (fun _ h1 h2 => treeBlockF_at nb_58_5 h1 h2)
theorem nj_58_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeV4 fullMask g_58 ep_58 bds_58 410 (dagTraceF fullMask rootStock 11 f_58) cur_58) i = true := block_join nj_58_5 (fun _ h1 h2 => treeBlockF_at nb_58_6 h1 h2)
theorem nj_58_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeV4 fullMask g_58 ep_58 bds_58 410 (dagTraceF fullMask rootStock 11 f_58) cur_58) i = true := block_join nj_58_6 (fun _ h1 h2 => treeBlockF_at nb_58_7 h1 h2)
theorem nj_58_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeV4 fullMask g_58 ep_58 bds_58 410 (dagTraceF fullMask rootStock 11 f_58) cur_58) i = true := block_join nj_58_7 (fun _ h1 h2 => treeBlockF_at nb_58_8 h1 h2)
theorem nj_58_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeV4 fullMask g_58 ep_58 bds_58 410 (dagTraceF fullMask rootStock 11 f_58) cur_58) i = true := block_join nj_58_8 (fun _ h1 h2 => treeBlockF_at nb_58_9 h1 h2)
theorem nj_58_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeV4 fullMask g_58 ep_58 bds_58 410 (dagTraceF fullMask rootStock 11 f_58) cur_58) i = true := block_join nj_58_9 (fun _ h1 h2 => treeBlockF_at nb_58_10 h1 h2)
theorem nj_58_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeV4 fullMask g_58 ep_58 bds_58 410 (dagTraceF fullMask rootStock 11 f_58) cur_58) i = true := block_join nj_58_10 (fun _ h1 h2 => treeBlockF_at nb_58_11 h1 h2)
theorem nj_58_12 : ∀ i, 0 ≤ i → i < 410 → (dagCheckNodeV4 fullMask g_58 ep_58 bds_58 410 (dagTraceF fullMask rootStock 11 f_58) cur_58) i = true := block_join nj_58_11 (fun _ h1 h2 => treeBlockF_at nb_58_12 h1 h2)
theorem nc_58 : ∀ i, 0 ≤ i → i < 410 → (dagCheckNodeV4 fullMask g_58 ep_58 bds_58 410 (dagTraceF fullMask rootStock 11 f_58) cur_58) i = true := nj_58_12
theorem lb_58 : LowerBin fullMask rootStock g_58 12 :=
  lowerDagV4 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) epk_58 kn_58 sub_58 gl_58 rc_58 nc_58

def wg : List Gate := [⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.and, [3, 7]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [3, 7]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [0, 13]⟩, ⟨GateOp.and, [6, 9]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [14, 15]⟩, ⟨GateOp.and, [16, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4008241312 * 2 ^ 32 + 3902857344) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4008241312 * 2 ^ 32 + 3902857344)) (13 - 1) := by
  rw [show canon fullMask (4008241312 * 2 ^ 32 + 3902857344) = g_58 by decide]
  exact lb_58

end PEqualNP.Outside.L_meta_49283

theorem PEqualNP.Outside.L_meta_49283 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241312 * 2 ^ 32 + 3902857344) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241312 * 2 ^ 32 + 3902857344) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_49283.table2_from_lowerBin (4008241312 * 2 ^ 32 + 3902857344) 13 PEqualNP.Outside.L_meta_49283.root_lb PEqualNP.Outside.L_meta_49283.wg 18 rfl PEqualNP.Outside.L_meta_49283.wfits PEqualNP.Outside.L_meta_49283.weval
