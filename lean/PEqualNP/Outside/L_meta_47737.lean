import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_47737

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

def m_0 : Nat := 0xa0a00000a0a
def s_0 : List Nat := [0x20200000202, 0xa0000000a, 0xa0a]
def g_0 : Nat := 0x20000020a
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

def m_1 : Nat := 0xcc000000cc
def s_1 : List Nat := [0x4400000044, 0xc0000000c, 0xcc]
def g_1 : Nat := 0x40000004c
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

def m_2 : Nat := 0xa0a0a0a
def s_2 : List Nat := [0x2020202, 0xa000a, 0xa0a]
def g_2 : Nat := 0x2020a
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

def m_3 : Nat := 0xcc00cc
def s_3 : List Nat := [0x440044, 0xc000c, 0xcc]
def g_3 : Nat := 0x4004c
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

def m_4 : Nat := 0xaaaa
def s_4 : List Nat := [0x2222, 0xa0a, 0xaa]
def g_4 : Nat := 0x22a
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

def m_5 : Nat := 0xcccc
def s_5 : List Nat := [0x4444, 0xc0c, 0xcc]
def g_5 : Nat := 0x44c
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

def m_6 : Nat := 0xf0f000000000000
def s_6 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_6 : Nat := 0x107000000000000
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

def m_7 : Nat := 0xf0f0
def s_7 : List Nat := [0x5050, 0x3030, 0xf0]
def g_7 : Nat := 0x1070
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

def m_8 : Nat := 0xff000000000000
def s_8 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_8 : Nat := 0x17000000000000
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

def m_9 : Nat := 0xff00
def s_9 : List Nat := [0x5500, 0x3300, 0xf00]
def g_9 : Nat := 0x1700
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

def m_10 : Nat := 0x4444444444444444
def s_10 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_10 : Nat := 0x4040404040444
def bds_10 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_10 : KnownBin bds_10 := by intro b hb; simp [bds_10] at hb
theorem sub_10 : ∀ b ∈ bds_10, m_10 &&& b.1 = b.1 := by intro b hb; simp [bds_10] at hb
theorem gl_10 : ∀ b ∈ bds_10, canon b.1 g_10 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_10] at hb
def f_10 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_10 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_10 : dagCheckRootsF m_10 g_10 bds_10 (dagRefF 64 (dagTraceF m_10 s_10 5 f_10) l_10 0) s_10 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_10_0 : treeBlockF 0 32 (dagCheckNodeF m_10 g_10 bds_10 64 (dagTraceF m_10 s_10 5 f_10) l_10) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_10_1 : treeBlockF 32 64 (dagCheckNodeF m_10 g_10 bds_10 64 (dagTraceF m_10 s_10 5 f_10) l_10) = true := by decide +kernel
theorem nj_10_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_10 g_10 bds_10 64 (dagTraceF m_10 s_10 5 f_10) l_10) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_10_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_10_1 h1 h2)
theorem nc_10 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_10 g_10 bds_10 64 (dagTraceF m_10 s_10 5 f_10) l_10) i = true := nj_10_1
theorem lb_10 : LowerBin m_10 s_10 g_10 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_10 sub_10 gl_10 rc_10 nc_10

def m_11 : Nat := 0x2222222222222222
def s_11 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_11 : Nat := 0x2002200220222
def bds_11 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_11 : KnownBin bds_11 := by intro b hb; simp [bds_11] at hb
theorem sub_11 : ∀ b ∈ bds_11, m_11 &&& b.1 = b.1 := by intro b hb; simp [bds_11] at hb
theorem gl_11 : ∀ b ∈ bds_11, canon b.1 g_11 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_11] at hb
def f_11 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c838c834053fbc18bc14053b0537b2440533052f052b97489740943c94300527814c814480188014052375387534043f682c6824043b04375d440433042f042b43484340413c413004272c4c2c442c2c2c240423214c2144041f144c1444041b041709240413000f 6 10
def l_11 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607227207206e26c16c06a16a06a06a06a06a06a06246206206206205a45a05a05625605605225015004e14e04e04e04e04e04e04644604604604603e43e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424cc38c834c018bc14b130b244a3489f40983c94308d4c894484188014793875346c2c68245c305d444f484b40453c4130384c3444302c2c24254c2144184c144408100924fe3ffa3be637d233c53fb93bb537ad33a92fa52b91277d23703f643b60375833542f502b3c2728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_11 : dagCheckRootsF m_11 g_11 bds_11 (dagRefF 64 (dagTraceF m_11 s_11 5 f_11) l_11 0) s_11 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_11_0 : treeBlockF 0 32 (dagCheckNodeF m_11 g_11 bds_11 64 (dagTraceF m_11 s_11 5 f_11) l_11) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_11_1 : treeBlockF 32 64 (dagCheckNodeF m_11 g_11 bds_11 64 (dagTraceF m_11 s_11 5 f_11) l_11) = true := by decide +kernel
theorem nj_11_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_11 g_11 bds_11 64 (dagTraceF m_11 s_11 5 f_11) l_11) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_11_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_11_1 h1 h2)
theorem nc_11 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_11 g_11 bds_11 64 (dagTraceF m_11 s_11 5 f_11) l_11) i = true := nj_11_1
theorem lb_11 : LowerBin m_11 s_11 g_11 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_11 sub_11 gl_11 rc_11 nc_11

def m_12 : Nat := 0xa0a0a0a0a0a0a0a
def s_12 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_12 : Nat := 0x200020002020a
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

def m_13 : Nat := 0xc0c0c0c0c0c0c0c
def s_13 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_13 : Nat := 0x404040404040c
def bds_13 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_13 : KnownBin bds_13 := by intro b hb; simp [bds_13] at hb
theorem sub_13 : ∀ b ∈ bds_13, m_13 &&& b.1 = b.1 := by intro b hb; simp [bds_13] at hb
theorem gl_13 : ∀ b ∈ bds_13, canon b.1 g_13 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_13] at hb
def f_13 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_13 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_13 : dagCheckRootsF m_13 g_13 bds_13 (dagRefF 64 (dagTraceF m_13 s_13 5 f_13) l_13 0) s_13 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_13_0 : treeBlockF 0 32 (dagCheckNodeF m_13 g_13 bds_13 64 (dagTraceF m_13 s_13 5 f_13) l_13) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_13_1 : treeBlockF 32 64 (dagCheckNodeF m_13 g_13 bds_13 64 (dagTraceF m_13 s_13 5 f_13) l_13) = true := by decide +kernel
theorem nj_13_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_13 g_13 bds_13 64 (dagTraceF m_13 s_13 5 f_13) l_13) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_13_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_13_1 h1 h2)
theorem nc_13 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_13 g_13 bds_13 64 (dagTraceF m_13 s_13 5 f_13) l_13) i = true := nj_13_1
theorem lb_13 : LowerBin m_13 s_13 g_13 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_13 sub_13 gl_13 rc_13 nc_13

def m_14 : Nat := 0xaa00aa00aa00aa
def s_14 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_14 : Nat := 0x200220022002a
def bds_14 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_14 : KnownBin bds_14 := by intro b hb; simp [bds_14] at hb
theorem sub_14 : ∀ b ∈ bds_14, m_14 &&& b.1 = b.1 := by intro b hb; simp [bds_14] at hb
theorem gl_14 : ∀ b ∈ bds_14, canon b.1 g_14 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_14] at hb
def f_14 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_14 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_14 : dagCheckRootsF m_14 g_14 bds_14 (dagRefF 64 (dagTraceF m_14 s_14 5 f_14) l_14 0) s_14 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_14_0 : treeBlockF 0 32 (dagCheckNodeF m_14 g_14 bds_14 64 (dagTraceF m_14 s_14 5 f_14) l_14) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_14_1 : treeBlockF 32 64 (dagCheckNodeF m_14 g_14 bds_14 64 (dagTraceF m_14 s_14 5 f_14) l_14) = true := by decide +kernel
theorem nj_14_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_14 g_14 bds_14 64 (dagTraceF m_14 s_14 5 f_14) l_14) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_14_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_14_1 h1 h2)
theorem nc_14 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_14 g_14 bds_14 64 (dagTraceF m_14 s_14 5 f_14) l_14) i = true := nj_14_1
theorem lb_14 : LowerBin m_14 s_14 g_14 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_14 sub_14 gl_14 rc_14 nc_14

def m_15 : Nat := 0xcc00cc00cc00cc
def s_15 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_15 : Nat := 0x400040004004c
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
def g_16 : Nat := 0x100050005000700
def bds_16 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_16 : KnownBin bds_16 := by intro b hb; simp [bds_16] at hb
theorem sub_16 : ∀ b ∈ bds_16, m_16 &&& b.1 = b.1 := by intro b hb; simp [bds_16] at hb
theorem gl_16 : ∀ b ∈ bds_16, canon b.1 g_16 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_16] at hb
def f_16 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_16 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsF m_16 g_16 bds_16 (dagRefF 64 (dagTraceF m_16 s_16 5 f_16) l_16 0) s_16 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16_0 : treeBlockF 0 32 (dagCheckNodeF m_16 g_16 bds_16 64 (dagTraceF m_16 s_16 5 f_16) l_16) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16_1 : treeBlockF 32 64 (dagCheckNodeF m_16 g_16 bds_16 64 (dagTraceF m_16 s_16 5 f_16) l_16) = true := by decide +kernel
theorem nj_16_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_16 g_16 bds_16 64 (dagTraceF m_16 s_16 5 f_16) l_16) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_16_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_16_1 h1 h2)
theorem nc_16 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_16 g_16 bds_16 64 (dagTraceF m_16 s_16 5 f_16) l_16) i = true := nj_16_1
theorem lb_16 : LowerBin m_16 s_16 g_16 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_16 sub_16 gl_16 rc_16 nc_16

def m_17 : Nat := 0xf000f000f000f0
def s_17 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_17 : Nat := 0x10003000300070
def bds_17 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_17 : KnownBin bds_17 := by intro b hb; simp [bds_17] at hb
theorem sub_17 : ∀ b ∈ bds_17, m_17 &&& b.1 = b.1 := by intro b hb; simp [bds_17] at hb
theorem gl_17 : ∀ b ∈ bds_17, canon b.1 g_17 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp [bds_17] at hb
def f_17 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c838c834053fbc18bc14053b0537b2440533052f052b97489740943c94300527814c814480188014052375387534043f682c6824043b04375d440433042f042b43484340413c413004272c4c2c442c2c2c240423214c2144041f144c1444041b041709240413000f 6 10
def l_17 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607227207206e26c16c06a16a06a06a06a06a06a06246206206206205a45a05a05625605605225015004e14e04e04e04e04e04e04644604604604603e43e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424cc38c834c018bc14b130b244a3489f40983c94308d4c894484188014793875346c2c68245c305d444f484b40453c4130384c3444302c2c24254c2144184c144408100924fe3ffa3be637d233c53fb93bb537ad33a92fa52b91277d23703f643b60375833542f502b3c2728231c1f101b0c170413000f 12 5 10 6 6
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsF m_17 g_17 bds_17 (dagRefF 64 (dagTraceF m_17 s_17 5 f_17) l_17 0) s_17 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17_0 : treeBlockF 0 32 (dagCheckNodeF m_17 g_17 bds_17 64 (dagTraceF m_17 s_17 5 f_17) l_17) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17_1 : treeBlockF 32 64 (dagCheckNodeF m_17 g_17 bds_17 64 (dagTraceF m_17 s_17 5 f_17) l_17) = true := by decide +kernel
theorem nj_17_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_17 g_17 bds_17 64 (dagTraceF m_17 s_17 5 f_17) l_17) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_17_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_17_1 h1 h2)
theorem nc_17 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_17 g_17 bds_17 64 (dagTraceF m_17 s_17 5 f_17) l_17) i = true := nj_17_1
theorem lb_17 : LowerBin m_17 s_17 g_17 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_17 sub_17 gl_17 rc_17 nc_17

def m_18 : Nat := 0xaaaa0000aaaa
def s_18 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_18 : Nat := 0x220000022a
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

def m_19 : Nat := 0xcccc0000cccc
def s_19 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_19 : Nat := 0x4040000044c
def bds_19 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_19 : KnownBin bds_19 := by
  intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_19 : ∀ b ∈ bds_19, m_19 &&& b.1 = b.1 := by intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_19 : ∀ b ∈ bds_19, canon b.1 g_19 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_19, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_19 : Nat → Nat × Nat := fun _ => (0, 0)
def l_19 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsF m_19 g_19 bds_19 (dagRefF 0 (dagTraceF m_19 s_19 4 f_19) l_19 0) s_19 4 = true := by decide +kernel
theorem nc_19 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_19 g_19 bds_19 0 (dagTraceF m_19 s_19 4 f_19) l_19 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_19 : LowerBin m_19 s_19 g_19 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_19 sub_19 gl_19 rc_19 nc_19

def m_20 : Nat := 0xf0f00000f0f0000
def s_20 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_20 : Nat := 0x107000005070000
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

def m_21 : Nat := 0xf0f00000f0f0
def s_21 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_21 : Nat := 0x103000001070
def bds_21 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
theorem kn_21 : KnownBin bds_21 := by
  intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_7
theorem sub_21 : ∀ b ∈ bds_21, m_21 &&& b.1 = b.1 := by intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_21 : ∀ b ∈ bds_21, canon b.1 g_21 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_21, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_21 : Nat → Nat × Nat := fun _ => (0, 0)
def l_21 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsF m_21 g_21 bds_21 (dagRefF 0 (dagTraceF m_21 s_21 4 f_21) l_21 0) s_21 4 = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_21 g_21 bds_21 0 (dagTraceF m_21 s_21 4 f_21) l_21 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_21 : LowerBin m_21 s_21 g_21 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_21 sub_21 gl_21 rc_21 nc_21

def m_22 : Nat := 0xf0f00000f0f
def s_22 : List Nat := [0x50500000505, 0x30300000303, 0xf0000000f, 0xf0f]
def g_22 : Nat := 0x5070000070f
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

def m_23 : Nat := 0xff000000ff0000
def s_23 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_23 : Nat := 0x17000000370000
def bds_23 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
theorem kn_23 : KnownBin bds_23 := by
  intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_8
theorem sub_23 : ∀ b ∈ bds_23, m_23 &&& b.1 = b.1 := by intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_23 : ∀ b ∈ bds_23, canon b.1 g_23 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_23, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_23 : Nat → Nat × Nat := fun _ => (0, 0)
def l_23 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsF m_23 g_23 bds_23 (dagRefF 0 (dagTraceF m_23 s_23 4 f_23) l_23 0) s_23 4 = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_23 g_23 bds_23 0 (dagTraceF m_23 s_23 4 f_23) l_23 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_23 : LowerBin m_23 s_23 g_23 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_23 sub_23 gl_23 rc_23 nc_23

def m_24 : Nat := 0xff000000ff00
def s_24 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_24 : Nat := 0x150000001700
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_24 : KnownBin bds_24 := by
  intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_24 : ∀ b ∈ bds_24, m_24 &&& b.1 = b.1 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_24 : ∀ b ∈ bds_24, canon b.1 g_24 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_24, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_24 : Nat → Nat × Nat := fun _ => (0, 0)
def l_24 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsF m_24 g_24 bds_24 (dagRefF 0 (dagTraceF m_24 s_24 4 f_24) l_24 0) s_24 4 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_24 g_24 bds_24 0 (dagTraceF m_24 s_24 4 f_24) l_24 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_24 sub_24 gl_24 rc_24 nc_24

def m_25 : Nat := 0xff000000ff
def s_25 : List Nat := [0x5500000055, 0x3300000033, 0xf0000000f, 0xff]
def g_25 : Nat := 0x370000007f
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
theorem kn_25 : KnownBin bds_25 := by
  intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_1
theorem sub_25 : ∀ b ∈ bds_25, m_25 &&& b.1 = b.1 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_25 : ∀ b ∈ bds_25, canon b.1 g_25 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_25, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_25 : Nat → Nat × Nat := fun _ => (0, 0)
def l_25 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsF m_25 g_25 bds_25 (dagRefF 0 (dagTraceF m_25 s_25 4 f_25) l_25 0) s_25 4 = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_25 g_25 bds_25 0 (dagTraceF m_25 s_25 4 f_25) l_25 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_25 : LowerBin m_25 s_25 g_25 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_25 sub_25 gl_25 rc_25 nc_25

def m_26 : Nat := 0xaaaaaaaa
def s_26 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_26 : Nat := 0x22022a
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_26 : KnownBin bds_26 := by
  intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_26 : ∀ b ∈ bds_26, m_26 &&& b.1 = b.1 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_26 : ∀ b ∈ bds_26, canon b.1 g_26 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_26, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_26 : Nat → Nat × Nat := fun _ => (0, 0)
def l_26 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsF m_26 g_26 bds_26 (dagRefF 0 (dagTraceF m_26 s_26 4 f_26) l_26 0) s_26 4 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_26 g_26 bds_26 0 (dagTraceF m_26 s_26 4 f_26) l_26 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_26 : LowerBin m_26 s_26 g_26 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_26 sub_26 gl_26 rc_26 nc_26

def m_27 : Nat := 0xcccccccc
def s_27 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_27 : Nat := 0x404044c
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_27 : KnownBin bds_27 := by
  intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_27 : ∀ b ∈ bds_27, m_27 &&& b.1 = b.1 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_27 : ∀ b ∈ bds_27, canon b.1 g_27 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_27, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_27 : Nat → Nat × Nat := fun _ => (0, 0)
def l_27 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsF m_27 g_27 bds_27 (dagRefF 0 (dagTraceF m_27 s_27 4 f_27) l_27 0) s_27 4 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_27 g_27 bds_27 0 (dagTraceF m_27 s_27 4 f_27) l_27 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_27 sub_27 gl_27 rc_27 nc_27

def m_28 : Nat := 0xf0f0f0f00000000
def s_28 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_28 : Nat := 0x107050700000000
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
theorem kn_28 : KnownBin bds_28 := by
  intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_6
theorem sub_28 : ∀ b ∈ bds_28, m_28 &&& b.1 = b.1 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_28 : ∀ b ∈ bds_28, canon b.1 g_28 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_28, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_28 : Nat → Nat × Nat := fun _ => (0, 0)
def l_28 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsF m_28 g_28 bds_28 (dagRefF 0 (dagTraceF m_28 s_28 4 f_28) l_28 0) s_28 4 = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_28 g_28 bds_28 0 (dagTraceF m_28 s_28 4 f_28) l_28 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_28 : LowerBin m_28 s_28 g_28 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_28 sub_28 gl_28 rc_28 nc_28

def m_29 : Nat := 0xf0f0f0f0
def s_29 : List Nat := [0x50505050, 0x30303030, 0xf000f0, 0xf0f0]
def g_29 : Nat := 0x10301070
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
theorem kn_29 : KnownBin bds_29 := by
  intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_7
theorem sub_29 : ∀ b ∈ bds_29, m_29 &&& b.1 = b.1 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_29 : ∀ b ∈ bds_29, canon b.1 g_29 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_29, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_29 : Nat → Nat × Nat := fun _ => (0, 0)
def l_29 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsF m_29 g_29 bds_29 (dagRefF 0 (dagTraceF m_29 s_29 4 f_29) l_29 0) s_29 4 = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_29 g_29 bds_29 0 (dagTraceF m_29 s_29 4 f_29) l_29 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_29 : LowerBin m_29 s_29 g_29 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_29 sub_29 gl_29 rc_29 nc_29

def m_30 : Nat := 0xf0f0f0f
def s_30 : List Nat := [0x5050505, 0x3030303, 0xf000f, 0xf0f]
def g_30 : Nat := 0x507070f
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
theorem kn_30 : KnownBin bds_30 := by
  intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_2
theorem sub_30 : ∀ b ∈ bds_30, m_30 &&& b.1 = b.1 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_30 : ∀ b ∈ bds_30, canon b.1 g_30 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_30, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_30 : Nat → Nat × Nat := fun _ => (0, 0)
def l_30 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsF m_30 g_30 bds_30 (dagRefF 0 (dagTraceF m_30 s_30 4 f_30) l_30 0) s_30 4 = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_30 g_30 bds_30 0 (dagTraceF m_30 s_30 4 f_30) l_30 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_30 : LowerBin m_30 s_30 g_30 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_30 sub_30 gl_30 rc_30 nc_30

def m_31 : Nat := 0xff00ff00000000
def s_31 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_31 : Nat := 0x17003700000000
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
theorem kn_31 : KnownBin bds_31 := by
  intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_8
theorem sub_31 : ∀ b ∈ bds_31, m_31 &&& b.1 = b.1 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_31 : ∀ b ∈ bds_31, canon b.1 g_31 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_31, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_31 : Nat → Nat × Nat := fun _ => (0, 0)
def l_31 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsF m_31 g_31 bds_31 (dagRefF 0 (dagTraceF m_31 s_31 4 f_31) l_31 0) s_31 4 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_31 g_31 bds_31 0 (dagTraceF m_31 s_31 4 f_31) l_31 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_31 sub_31 gl_31 rc_31 nc_31

def m_32 : Nat := 0xff00ff00
def s_32 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_32 : Nat := 0x15001700
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
theorem kn_32 : KnownBin bds_32 := by
  intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_9
theorem sub_32 : ∀ b ∈ bds_32, m_32 &&& b.1 = b.1 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_32 : ∀ b ∈ bds_32, canon b.1 g_32 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_32, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_32 : Nat → Nat × Nat := fun _ => (0, 0)
def l_32 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsF m_32 g_32 bds_32 (dagRefF 0 (dagTraceF m_32 s_32 4 f_32) l_32 0) s_32 4 = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_32 g_32 bds_32 0 (dagTraceF m_32 s_32 4 f_32) l_32 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_32 : LowerBin m_32 s_32 g_32 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_32 sub_32 gl_32 rc_32 nc_32

def m_33 : Nat := 0xff00ff
def s_33 : List Nat := [0x550055, 0x330033, 0xf000f, 0xff]
def g_33 : Nat := 0x37007f
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
theorem kn_33 : KnownBin bds_33 := by
  intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_3
theorem sub_33 : ∀ b ∈ bds_33, m_33 &&& b.1 = b.1 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_33 : ∀ b ∈ bds_33, canon b.1 g_33 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_33, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
def l_33 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsF m_33 g_33 bds_33 (dagRefF 0 (dagTraceF m_33 s_33 4 f_33) l_33 0) s_33 4 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_33 g_33 bds_33 0 (dagTraceF m_33 s_33 4 f_33) l_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_33 sub_33 gl_33 rc_33 nc_33

def m_34 : Nat := 0xffff000000000000
def s_34 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_34 : Nat := 0x1117000000000000
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
theorem kn_34 : KnownBin bds_34 := by
  intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_6
theorem sub_34 : ∀ b ∈ bds_34, m_34 &&& b.1 = b.1 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_34 : ∀ b ∈ bds_34, canon b.1 g_34 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_34, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
def l_34 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsF m_34 g_34 bds_34 (dagRefF 0 (dagTraceF m_34 s_34 4 f_34) l_34 0) s_34 4 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_34 g_34 bds_34 0 (dagTraceF m_34 s_34 4 f_34) l_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_34 sub_34 gl_34 rc_34 nc_34

def m_35 : Nat := 0xffff
def s_35 : List Nat := [0x5555, 0x3333, 0xf0f, 0xff]
def g_35 : Nat := 0x177f
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4), (m_5, s_5, 4, g_5), (m_7, s_7, 4, g_7), (m_9, s_9, 4, g_9)]
theorem kn_35 : KnownBin bds_35 := by
  intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_4
  · exact lb_5
  · exact lb_7
  · exact lb_9
theorem sub_35 : ∀ b ∈ bds_35, m_35 &&& b.1 = b.1 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_35 : ∀ b ∈ bds_35, canon b.1 g_35 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_35, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def f_35 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def l_35 : Nat → Nat → Option Nat := unpackLinksF 0x8e11c1fc3f07c2f81b43606c0d45a0b40662cc15c2b0542a8148a18420841009f13e0784f01d12b0540a814128050098921222440809001e21e00b001 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d347d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 11 4 10 6 5
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsF m_35 g_35 bds_35 (dagRefF 43 (dagTraceF m_35 s_35 6 f_35) l_35 0) s_35 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_0 : treeBlockF 0 32 (dagCheckNodeF m_35 g_35 bds_35 43 (dagTraceF m_35 s_35 6 f_35) l_35) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_1 : treeBlockF 32 43 (dagCheckNodeF m_35 g_35 bds_35 43 (dagTraceF m_35 s_35 6 f_35) l_35) = true := by decide +kernel
theorem nj_35_1 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeF m_35 g_35 bds_35 43 (dagTraceF m_35 s_35 6 f_35) l_35) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_35_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_35_1 h1 h2)
theorem nc_35 : ∀ i, 0 ≤ i → i < 43 → (dagCheckNodeF m_35 g_35 bds_35 43 (dagTraceF m_35 s_35 6 f_35) l_35) i = true := nj_35_1
theorem lb_35 : LowerBin m_35 s_35 g_35 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_35 sub_35 gl_35 rc_35 nc_35

def m_36 : Nat := 0xaaaaaaaaaaaaaaaa
def s_36 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_36 : Nat := 0x200220022022a
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 6, g_11), (m_14, s_14, 6, g_14), (m_12, s_12, 5, g_12), (m_18, s_18, 5, g_18), (m_26, s_26, 5, g_26), (m_0, s_0, 4, g_0), (m_2, s_2, 4, g_2), (m_4, s_4, 4, g_4)]
theorem kn_36 : KnownBin bds_36 := by
  intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_11
  · exact lb_14
  · exact lb_12
  · exact lb_18
  · exact lb_26
  · exact lb_0
  · exact lb_2
  · exact lb_4
theorem sub_36 : ∀ b ∈ bds_36, m_36 &&& b.1 = b.1 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_36 : ∀ b ∈ bds_36, canon b.1 g_36 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_36, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_36 : Nat → Nat × Nat := unpackForestF 0x38949200b4fdd11df0a4a785053ba239e052e7024a381051ba233dd09defa4fb7d033ba139decae6e84cf74077bb83eddc176e80e7750b9ba033005a1ee0d2b70293b8049c6a28edd5831a49fb6018da49ced40b3690738d24ed91ae6c89b364499b223cc6925eb91835c2b9b0450d70a86b81735d8a1ae050c6923eb093358281ac040d45aa6a29b351499a8928d44926a20a3510498d243d393669c9331a25fa623cc6895e940e34629da312ed1c2668c0671a253a0b58d05a86820f3410618d127cf52067a4b33d0419b234cd8b666c573362a99b14ccd80c66c0531a24799a6cccd266340bf312798d02bcbc9c65613b2d2999582ecac0f6340a7266b193350c989e64c4c31a04f91240c88906440b31b2698d86cc6c2e6361531b0998d82cc6c1263408c014878c246c5a2962c978014778a245b562f5ab14f0f69587949c3c24dab14b068a385949c2c24e0d1430669b83940c1c2060cd16d56a581c60c0db05aa97eff6a37f949bfc24daa97afa4b97d24cbe8945f40a2d54a77425dba1275d0936e847b7412aba094dd04a2f129974126bb8945dc492e805574029ba0145d2532e903174026b55295aa4aee18a572450b85a95c257ae10336a929b7cae5aa48ed50576c452b6e285b0d4ad80bd6c02eb5414dac172d504600a33b4d2480253ece47567b50b3c1859c8dab06a364c60b249c594d42c926958343ac0a7d88946c447362039ac0a75844f2b028760460ac09fd7893abc4855e029ac09f570572b82795c018ac099d6006eb36a35984eacc1f560066b107958013004a1d5c926976bd5546caa92e554912974a753352a992f54c94a9747350251a8da85408e6a026b5012ea5ca953690e9c4834e12ea6ca152e0e2992994c143a5c1a0024fe946934a1469ce2952158290471481349cda9d1714a8b6bd45b52a2c9b4e6d06864a343249a1da850c8c6732bd40452a0e28500d4a804bd402529cc9f4fc8e6776853e4509dd21cf0d0a7849d3c2429dd18ce6062752513a2439cc0a0024ee7147332c529aeb04d69726d69935a4c9ac944ca94e666a53325e99c144cc94a6548200937989a4cc492a3f8a52fd6097c9c47ed4e5a8a52d35e969a94b48ea3f68329351956284acd02554692934194926ca48fa3f4a528239921a149b1424d25124243925a149293a49485242318fd22480d46458a120341900a6c804fa4025b200198fca90024ce3b4bd1e1258eca90024be382911c14473e29c6c512318a318a3a8c9a04640c23146ce7b528bca2b9e97a2d8c0e7a53899a84549422649d1323d89da844c0a5cf4a50fb5e88dae43e94a1f26b1024287c1c39e93a1d2890bc5286ca2435142176a50c35085d2939e90a146c10a26073cafc1ad260d2a3080288349f41a4ca0d092e795e820ae410532082790401873ca9c0a4d205070f924e7c9213e4575f229cf914d7c8a63e4515f227af912e7eca23e44b5f8298fc1447c80d3e4065f2030f984c7cc163e4059cf2a4f825073ca7bd2d79e96a4f4a527ad283d2549e9072e794e79c9e39e50dd98a4f2450765a93c4d41d94a4ec95e774a63ba4b1dd030ec952764a6bb24b5d9032e794273c0dba4d49d56a0e92527482f3a4139cf032e803c73c0980248dcd4920084f7209d392d41c9260e4136681a8b87181c3070e235070c1a340d0da0486dec606f41437cd41bd048d023368027b6e945b7472db9416dc9cb40139b5058d00436ce303400fdaf49cd7a426bc94b400f9ab0b8d583c6ac163400cda005ed1b5168d21346539a3284d193e68c993400b9a1058d002300421b3c925876bccd46c6692e334911874a6cb3526592f32c94987472ca24361c9c3244f191286c393462128b1cd4188472c62416209c3100d589070c402e61c290020fd84692c204658e2930158180270c003458da9af71497b6bcbdb525ec1b2c6d05764a2bb2495dda82ec8c5630bcb84525ce282e0d49704bcb825258c1f2dc8e567684b645059d21ad0d096849cb424259d18ac60b165050b224358c120020ed61472aac5256eb02b69715d698ada4c56c142aa94d566a4ab25e55c942ac9495548200837549a4aa4529278a4a7d6053c1c24ed4d4a8a4a535e529a92944e927682a325c5189428c0a1274a6a125c508942840a1274669d3514f62827cd013d2689d3414e8a6a744f9272a49c2394c1a126b14135050982434c5a1262939314849823149ca2250d452d8a0943414a026a500f92805c9401d49c290020cd234bc9202548c290020bd20090900442b629a3c111198a28c93a469a02344c11926c56b52452302280a1156a08a0242b52995a90d1108a5695e43e3015a54d086a086250420a72104f5096a08412e2b4a9202d79056b880a5240d212024e10106a5694e3fc221f3148fd0887e4503e5a91f4d40f92a4569423d9b01ec580ad0be77b493bca49de144f10507783e3bc1915a178ea0b87504c3a81e1d40b0ad0a67393839c1a1a8538d42846a05d350271a8134d40986a0453501e9a80b8dc0986e044350169a80b0d90986a0253500f1aa110d50486a01d2b4291a4540ad09e6535e329a9194948ca2826513932d28194148ad09c6402c2b421975148c58a05d35230da8174548ba0bc5f04c2f81617c070ba0a45d04d2e817174074ad0845682f2c1a9160908b02bc581522c0a7160508b16a0580522b41715c0b0ad046008232a91c1544d0896a653a5129d24912578a54864494c28c9414490c892884f3522792f13c9488927c4ab5126d2092a530996a04a93e25c2612a0f89502a44852229a91249408a2bc48242228a611c0f08a0bc4614c22829114054890640081f2189c10c0d0656a6413512091f104098654a43eb521f52f0fa9487d04c32a321e1288f0924794a03c1221942f0de90c744823a12e1bca10e09087029c381421bc910ca1306d05036243194220ccd48664bc3325219da80cc5486507c0081b17d1c0c44b05f2703002c17c1c0acd4c5c6a22e13e159290aed48572bc2c14c15ca90ac8c80102e29248148a40a4120028a628038009a98988e04c27026038009a1890d444847c2412a00929086d48434bc21a5210c950048c83b6a21f3500fd2007c4903b4641d93e0ec96804548326a41b3500dd2006c490324a41915e0c8a90644b402264180280a12185a9042d25c141420a52105253829284141220089203cd44256a00f23208da803c4c81e09c0f03e0781683c074020a409c5204da0826948134640995204c99026178150780985204c1f004108036a40835000d2901cd40032a40185e024260120b0090380185200c2700c170030840182d00c0e8040c8010260001f 10 11
def l_36 : Nat → Nat → Option Nat := unpackLinksF 0x73a039c05cd43e6a0735039595cac0e56072b03930bc902e480724038e11c700e3417180b8c01c600e204710038705bdd7dee06f6077a83b98fdcc06e2137101b802dc006de0b6a15b4c1da606d3036885b344d9616cb036581b203d9006c8036287af48d7a06bd035e81ae83d7406ba035d01ae41d7206b8075811ac00d6006ac135583a9c4d4e06a50b5185a8c0d4216972b4b81a503d2806910f4491a240d120689034307a180d0c0685074281a140d080e7c233e019f00cf026770739899cc0ce216710337859b42cc656630330079800cba1e55232a819540caa06520f29019480ca20e510328819401c90462493120188c1c4606210b10818801c3a1e1d030e0386c1c205e100308018400c1046080304018200c0c15f73efb817dc0be81df402fa017d00bd455ea02f5017a80bd405e516f2817940bc615e302f0857840bc205e102ef077780bbc05dc0aee017700bb805dc02ec8771d2b8a15c406e20170c1b8605c302dd916ec0b7215b70adb036d80b6a0db502da816b48b5a05ab0aca2f6500b24159202c9016480b2015813ebe895f40af80d7a0ab9115c02ade0d6f02b78159c8ace05650ab2815883ac4056202b101560aab0055802ac0154c5aa2155006a8015400a90454802a3054bd7a5e052b1295034a02a50051e2a8e834740a380d18128b054580a2a0d15028a034386a161d0b0285814203a0a1d0502820340c19f83cfb067d813d469e614f10a788139ca9ca14e406710538809b834db066d8136c09b40cd6126a8335409a80cd402698333c499e04cc0e6601324399204c902648131839861cc302610330419743cb9065a892d0196804b40259052c029523ca806538329c094a14a1124e89274093a04961e4a0524c19105c860a4301218090c047f1e3e851f018f8047b063c851e408f204721e39011bc38de046f0235891ac08d6046b02340719438c6146302310318808c40462023101164989c5c4e0227011341896144b02248510488800c3c121e010f00878043a0a159f0ac08540c2a02138707c883e041e060f01078083a0c122e0883044081e140f020781030380c340506018500c08040c000a0000ffc17f03bf801fc00fd437ea03f501fa80fd017e803f401f514fa807d403ea01f500f9457ca03e501f184f8c07c603e301f084f8407bc1bde01ef00f7807b813dc01ee00f6827b403da01ed00f6807ae1bc549e280f0c278603c301e102f0807820bc101dc90ee4076e13b605db00ed0276803b305d980ecc076603b301d806ec0076003b001d392e9427480ba401d182e8c0746039b21cd80e642704bb8201c004e000700038001bf04dbcf6d6236b01b502da026c0435b15ab88d5c06ac0b5409a610d2826920b4901a480d2406824341019f84cfc06781b3c019e00cf006645332019900cc8065a2b2b099502ca80654032a019500ca806444322019004c2576120305118202c08260402f8297b82bdc05ec0af2117786bb035d802eb057502ba025d002e7057380b9035c802e4017182b7465ac3ad5056a80b3c659a12cb096580b04a57e12be055e04af0056c32b5055a80ad405680ab0115782abc055c0aae015682aa4455202a60d5300a8c354602a3015180a80353a1a9d014e02a6c15283a93054788a38151c028e014604a2825063a82054082a0404fe127b113b889dc04ee02701d37049b414c45a6009300098004c002591d2c8096404b20254152a0095004a8024f1526849301498024b052484924049202421d21008fc347e023f011d888ec0476023b011c068d4346612330119028c8046402320119008a4943c5a1e010f008741436121b010c8484484200a0c1106008300418020a08fd9e7dc43ee01f604fa047b083ce29e700f30279803c619db20ed8076813b401da00ec82738b39a09cd00e58472c039019c800e10c704137e11bf00df026f0237801bb04da0e6d0036801b10cd8806c4036201b100d8026c0034c51a600d300698034c01a114d080684033e119f00cf8067c033a119d00cd066680334019a00cd006602330019800ca86654032a019500c9846052302017f08bf805fc02fc097e00bf005f802fa097520ba805cc22e4097200b8045c002de096f00b7805bc02de016c0cb6005b002d8016324b08458012c0016000b00058002c0016000af8255c82ae0155089f2e4f0227801322898824c4025a212a0c938649c024c09250492024900246091f108e844740234191a008c824640230091800890c4402220010f0487804303218010b04858042422120103187e0e3e821f400f02877043b411da00e718728439011c410e2006e0c36c11b600db006d0235841a618d300698034031a000d0006800334319418ca006482320118e08c7006302318018a08c1105d0e2e8017400b8085c002d8215e38ae0456822a4415008a70453802942142209d104e80274013a0098144b82230b118008c00460021c510a10850042801f870f8107c003e001f000ea38730839021c800e2086f0837801bc00d0386608328219400c8086208310018800c4005b1c2d8015c40ae0057002a0615000a800540028861383098104c00258212c0094084a002500128009400412420801040082004100208010400820041002002100006c5034081a000cc106600320419000c8006400320017860bc005e002e0417000b8004a481a2c00b20001 0x38949389a31dc9b0622d42f56817e342bd51ed2a52663283c31298e490b0a12553083c282948410dead23014d9c1a5ce08947020a2624a120a40dc5a8e20d077e27d1c932904968a80877d03229011905246f6571522a094140dc1a8e1ed0453245bc03e484196ee0b8520449401d4a0a46ea1736f4a38ba49c4921e1c90787477c2239e0119dce8c69329330941dfc9def84e77a2671f9318dc91b0612551083bc83bdd81cee80cd270628f82314409e191430b8a186b52c29a86e4d2b6e4bbb1255a48accc054771293231418d498b04165500a3b80494b820a3a0c76eac184b50d9d2c5ec941df299b6018300266d40b36469d7b34daaca6cd85176b2732f93166c26ab811769072a7831d69223bc4a0be051b3b5cd99366ca93364479b0150d74286c114308681aca40d762860ed0358481b1460c19a05ee97357481b095cd7ca86bc1735c0a1ad24cd64a06b0102f14997524cbd9ae6aed53564d9aaa4cd50946a649352051a8824d3d3669c93348479a6138cf8925a298234481a623c7e9183bc4e34a070ef94c0240c68e1300a05948a4a9ad2369253a5f285a412e7e8969560b46104ba301914008da0542332819f930b3ca84644c33d241a2358d0da83f88f2ce2c118940cf0906840f3410619fa40cf89667a081fb250f99287e91c6788d33b2d99d15cce4aa670533370319b014cd1366669332b47998838c88123965811c2819893c3509865e4e0be0719694c0240c1801300a058c094a56ca310e4a85f24d9704e53c216580b8500459581e3500eb941411b08192030724282340c32304194b58ca1a81ae8f32727993130720302321032104192240c8c906440b0d60506a8283509c6424d3200d98f85cc782a63a1331c0598d824dbe28e0ad0b6d49fb424ed8d25eb691f5048773a42b34a8d5253e8f29735147978a1c604c74d25fa592bd1494e8049f35246f892171c28b3213d7f096ad04753821a300c73205f9802bca814e4a09f1a046698212a40f90a06c5e02e27813c612362f14b164bd8a245c35b05f8d23014d986450c2e28614d43116958225dc40a4c88506e5252f2921c3c24a58106dc05263021c30a4c8a506e4252f2121c2c24a5a106db05262821c20a060e1030d8a385450c25a6e0cd17034bb66151a38a4cba506e3252f192171828afc1254d0836d02931010e09183036c17c260be22ee02d470029365941a349ccb84c6ff092e28415f41ca980c6f86d97ea5cbf1265f64a2fa05178924ba8125de0a2e90497894c778965dc062ef25177124ba8a617c4b2e90317c25dbdd275ec936f547b4614996ca0de84aaf325379128bc0933b84857c092a5841bb4155d80a6eb051740262f410cb4941da46172350b92285cb14ae36a57115eb2ca93b44b44e0437081913008bb48e2df2b8a51502e8985b6d42db8a16e452b69a909a48ad90bce2852b6017098088ba03a5d138b582e62717b128a787452c15a960497efe4bd7ca53b9d2959054e8a2932c941b9895dc04a6de246ec12170829af4125490836e82bb5c14daa08cb904225813b4d24c5c48ad06a167830b322954897a584a516a418ad205a28eace46d6315e918a9580535170824202912810d6a064260232ba507891848a542ca2692b140b29a84aa502cc8c12a25078518488542bd27965938b249a3b84c2534a1219508a898486d36c64a362a39af518c52489480836203951818c86972c2279604608a1203fa502be49d5ea427f51ed4053a5228505131af014a2c08483032248117f5264225b2ba2b95c93cae00c0904c01e24113a40ad5a8c4c8c9472855a04e518215660f9160640f01d078945620f2cd6a364343a7d274a290a3b47d162338951958e53ec329d609438fca157e4febb27d5b9337c49928a10d130664082911c10d6c06eb20335801307408d58946ae49353241890914464c1df6894c844ab236550d22ab4b953248aa9225485822226102120a7824530112a32a0efa4caa1a954e97aa64a551152a8da453a122a36a14e038a9128d448e6a126b5012e810915360e29d2a1101308149053a9069c25d02922a7921d3650a1f2454c94ca60a1d5ad7aa94a752a39a7ca943c48a9a0714b8349f80c524d469569346341a50a35084fa7d0314194c9f00c3bc4927502949560a3a28518d42914714496ca08a65004f2902693d8189d00a50e5727a0313c8189b49a4f00628e8a546b5ea31a950c57a8b26d3b818a1da050ed42894a344249a0120d0c8c6836a141c507789450914a826a540a5ea01294f89067e4733c2319f2284f4d02784813d3429e5274f090a7d6853da439dd18cea4a27448749c52a3da9d14d06852bd3f93e9d80c4e60525028137a519c51cccc8c64f281271509b5a649a4c206299269309beb04d2d426e4b9332509b1264985026b25125940928984925026705134b529a12f4cc94a48281384529a929cca906472613035198da4cb6d06624950e232794990380461a480f2140935224c15825d8a12db50961304989521948101a30918b03c65025f270ee13095d2848a5425d8a52e35e96da94a894a5a4752215206c08caf141e22812b234959a04af142554692c351951a0ca69365247d01a32784990340464e4832823992518c9d1424b68124a4093494496d0a4a49d24a4293da149890e4846322c508612048b142466a32234185d194865364227cee13290496c800641402330c52979a9cb2d06514a523a448591947e549d8264e0853448198240463c24b1ea5e8eca946c9421d2811ab608712842e901e52a0f694c8e4a4470511dc2810d94086928430901e42a11b1448cda04640c2358a316a518ad2844493a194851a23a8c51b42a575ec29cf1942700289000a446042eb01904408c5e5162d8c10524c844b645493a18484f594e788a144e0a425042ea81904008c54942276a115b508a52742e90a2847b0a15d7a8a73c250a26052120217500c81e046234a111b5c8801c44090a1029d02942891af44494a0f2bd021528849ac3e0e21b4810d350874a24365121a8a10c250861a843914a196a50ba52838af406549f029a0c821855b0428982022c10802880a2ec24d25ed6830895183c9f41c4ca0d092df8411fc0c88a046024d90595c828a64124f208031031348141c3f2061f4028ef94c7ec963f0061fb288f98147e4a63f0511f4098f982c0240e40893a034850115d804a7400535ff298ff145770a13fa4f5fc25cfd12d1f814888085f7034fb0197d40c3e405808022f825076ca83d6541eb4a0f735e7b5a93b6d35ec4a4f515251020bd20e542062eda5c79c9e3c8d41e48a0f1250789a83be531de258ee818796293c6d49e14a4f015e770a93b6535da25aec819014088864c003240eaa50755a83acd49d44a4a194274c2f37e149d209ca104200c0e8064a1d00791bc538c1a945c97a2c4a712a528792742c90a132bf0615e81ca9be2549ef29ef414e798a1bb0509bc0a6a08431f014884085d7036e881973c09804045cd49288022729a83924c1c68a4e024163caf2805490f2828694072c9d3904d89c25c209226e82f25c149b309ad402e0981127e540c3260968507101a27c101c46a09e84071a30278540c2260960506c01e38a0e1c30685e83006090370171a7078d282c050100804c00e240128306f81207e081be6a01f0207023007a4c00d2401203068c1637e0a1bd048040204eca82561410c06095b4d6e928b728e5b0462dc1416dc9cb4a4c50b0449595c6d4163671810a2806f8406c527360908df47ad792968c90b101393a084760312580f078048df2987906c6b42e3580f1ab0581d93007c18212101a86a2d3a42698a734a509a427cd193207c96a100c81f278d082c71da8b84d0dc1486de23361ca72725092327c8713341c991284b83a244dd84f6d82736810d27084d903f6b81f3540ccd3064d482f6881734008c1d044ce25167924b2c9050604482830301a23245119c8d8cc34866d2e32c9219a488ca148644a231e181040607302063828180931986a4cba5e6592931a1498c0a0818303a01032890d8b084810226489e32250d8e690c6148639a83189058905c740226241c31e9458d472c59386281ab100b8e6044ceb5e66529b2a8e593270c813461c292000896e058c1351615a4af8d058408cba03e5b4162e61316c058b28242f80a3055817e8a0be3506049c2f21b172098b803c6001a2d60b164048bb85c5a8162d20b15d068b402c5fa292fad797c6a4bb05e5ec1b2ce0b177680bbb505e528af092570482bb2315cda82e7140be050ba4525c9a92e2979704a4b62415b91cad08c56c8a0b53405a1202d4d096949cb42425b5a12d690d67462b282859121b071497f6a6bd3415d42f2de0f966058b18244e0202be94561472ab2314dc2026c1415d6989a83039c2626a0c15fac0acb505792e2ac9415c4989a04056c1426610132060ab9284c4202b2d49584bcab2524c0202c11495a4a6aaa414bc182a0d4553692a5b41548a51fc4c8c60640e0223f0a018a10135288a856053628296d41402c09a1543eca01ca4c12e0c06204053c1c17a0c13f2a09685053629298d794b6a49e1525289d2581481b044a425c51c940340c1460500a0205112e2864a019060a10280141027f140c30809f1344f9a027f1413d268a03514f1a0a765353a27c7293230819030089364829c2394c518a6d1413368098a404d414266d093249c98a424dda126890d3046296c503e8a025b1412e6a2963413e4992561352a07c5e8324a4170280892803aa8c52539a9a92d05454a6a0a334e4a925e510f8264938522e4190240892404a92a5e48c2923c940ff0808eb603f8a81f2500c60a06784c48424240110bd0807e8403f0a81f4500c50a08f04446da02344c11d8a28ba5143ca8a1a5410429c7d9424709d2324d89325c1c9223dc2e99c138c40845b82e044110704c023240080304541206e081156a01b02045e3006a4c022240078302d01622c0a1140480402005c9019a170b60785902c014102221150f8c07614c3c836218538fa2848492e08c91196138c30845882e03811218941096a086b5042ca71f25090a27a8412e088911ec174ca09c610422c01701a089054a082b5c40c9c206908f109c74042419af208949022707805e398292020d4fd4807e3503fc221fa110fc8a07d1503e9a81fd148fb6a47c95205c911de178e50a46904d3ddb01ec580e40c0788283922e9e8d24cf682799492d0a09e4144f007c778322340f068048e42d87685c3b0261d60f0ea0587413839c1a1ba0b0d90486004c370161ac070dd0986e044364260140b0d50386b044354121cc538e52844592e0cc911c8174e309c7104d384261c0114bd0846f83d378171b60b4da0586c025020111ae078d403a691502f028196140cb4a06835e33da9178d34ce4a4669413309c9644c4ca0a45e15c3201618ad40c58a06195030da8180130bf0585f01c31a29188d48c22a46085e2f429178134bb05c028222e80e8644c004060588502c5a816ed48b64845a95e2d0a9166538b22840212d2c0290084f0ae0588fc53461a922694d124868815e438a9a0e5490029c7c14222497062488f50be7705e3a4299a6148d109e6484e31c21972108b805e5782e2b411804088a3488051242ad1c1505b0a52b851154280a613c4f0aa2684e06024c201160c0920605425129d2493c904910444d85024018118080a54864d04223c111464a0a24864c85002894140d489f4bc4f25226029136570992984da4125c17118088996a04b84c271a89345309827c4b03e22c1912a054922b84814c249281209088e09c460422381e1185306002849b52244af11e5308d0bc458522280a952d4ca62bc5214c284a213a4f8940a4448321b4a2012050844c0402401f91810e4e07b0d83b05c1b02a0d413068078430341d42e0ce130740984235120d1f0fc8c8730983303e208130f2170720983883c1c0260c4090806a43fa5e1f9290f01786f0983e8261e4980f29407b4a23d2491a1208f0488752a0391301c0900ea9047425c381221c9210e2538702843b2431cca10de4886d0503624319ca80120a0676a0353521a52f0d0948662a442b53205290f88c8770bc3704c1ac220ca0f86225818010180160600405d4c02d24018d1c0ae8c0612702f8380bc0805c0802d0202eb511709f0ae4c82c040158200a8080b0530290402d352164af0ae548280402f35316d290ac8c8270202a24814ca4038140520900a0400c0920949804648022230104b007250033260179240983002210050070040301391c09a4e01b0a0260380141807050010080253511251f0888c8352642412a0682101e0c8402a012850119a908a978444a41e95210c9504814819084202400382007e4903f480203500f892082d443d4641e13e0cc990764b418084068320e128046140372481ba400e1a806c490396a41aa520d0af0665483225a1105205c2105c5402b260149200c01405c9042d25c149220ad210545382928417a430b0a10504882548011940095a8046d40266a21223208899042138140841003e0201903e0b41e03a0a83c07229036d041a4a40ca32060a902e4c8160bc0a05204c1f00a0c8104a007150041a801cd400b0980502c0240e00c170116a407a52034a9018178080a40384e014210080b40303a28c5313da9896d0c474a4212320e8a90624c8272480e852048210040cb8869fb9b43c6521e2a8eed44676914fabca1d2c4fe72277321378f899c744bdce246e604f67c21b0c0fd62076aa03749819a440bcac0464401f1900d8aa05c010260001f 17 6 11 10 7
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsF m_36 g_36 bds_36 (dagRefF 906 (dagTraceF m_36 s_36 8 f_36) l_36 0) s_36 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_0 : treeBlockF 0 32 (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_1 : treeBlockF 32 64 (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_2 : treeBlockF 64 96 (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_3 : treeBlockF 96 128 (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_4 : treeBlockF 128 160 (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_5 : treeBlockF 160 192 (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_6 : treeBlockF 192 224 (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_7 : treeBlockF 224 256 (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_8 : treeBlockF 256 288 (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_9 : treeBlockF 288 320 (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_10 : treeBlockF 320 352 (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_11 : treeBlockF 352 384 (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_12 : treeBlockF 384 416 (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_13 : treeBlockF 416 448 (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_14 : treeBlockF 448 480 (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_15 : treeBlockF 480 512 (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_16 : treeBlockF 512 544 (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_17 : treeBlockF 544 576 (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_18 : treeBlockF 576 608 (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_19 : treeBlockF 608 640 (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_20 : treeBlockF 640 672 (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_21 : treeBlockF 672 704 (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_22 : treeBlockF 704 736 (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_23 : treeBlockF 736 768 (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_24 : treeBlockF 768 800 (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_25 : treeBlockF 800 832 (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_26 : treeBlockF 832 864 (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_27 : treeBlockF 864 896 (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36_28 : treeBlockF 896 906 (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) = true := by decide +kernel
theorem nj_36_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_36_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_36_1 h1 h2)
theorem nj_36_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := block_join nj_36_1 (fun _ h1 h2 => treeBlockF_at nb_36_2 h1 h2)
theorem nj_36_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := block_join nj_36_2 (fun _ h1 h2 => treeBlockF_at nb_36_3 h1 h2)
theorem nj_36_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := block_join nj_36_3 (fun _ h1 h2 => treeBlockF_at nb_36_4 h1 h2)
theorem nj_36_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := block_join nj_36_4 (fun _ h1 h2 => treeBlockF_at nb_36_5 h1 h2)
theorem nj_36_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := block_join nj_36_5 (fun _ h1 h2 => treeBlockF_at nb_36_6 h1 h2)
theorem nj_36_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := block_join nj_36_6 (fun _ h1 h2 => treeBlockF_at nb_36_7 h1 h2)
theorem nj_36_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := block_join nj_36_7 (fun _ h1 h2 => treeBlockF_at nb_36_8 h1 h2)
theorem nj_36_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := block_join nj_36_8 (fun _ h1 h2 => treeBlockF_at nb_36_9 h1 h2)
theorem nj_36_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := block_join nj_36_9 (fun _ h1 h2 => treeBlockF_at nb_36_10 h1 h2)
theorem nj_36_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := block_join nj_36_10 (fun _ h1 h2 => treeBlockF_at nb_36_11 h1 h2)
theorem nj_36_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := block_join nj_36_11 (fun _ h1 h2 => treeBlockF_at nb_36_12 h1 h2)
theorem nj_36_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := block_join nj_36_12 (fun _ h1 h2 => treeBlockF_at nb_36_13 h1 h2)
theorem nj_36_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := block_join nj_36_13 (fun _ h1 h2 => treeBlockF_at nb_36_14 h1 h2)
theorem nj_36_15 : ∀ i, 0 ≤ i → i < 512 → (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := block_join nj_36_14 (fun _ h1 h2 => treeBlockF_at nb_36_15 h1 h2)
theorem nj_36_16 : ∀ i, 0 ≤ i → i < 544 → (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := block_join nj_36_15 (fun _ h1 h2 => treeBlockF_at nb_36_16 h1 h2)
theorem nj_36_17 : ∀ i, 0 ≤ i → i < 576 → (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := block_join nj_36_16 (fun _ h1 h2 => treeBlockF_at nb_36_17 h1 h2)
theorem nj_36_18 : ∀ i, 0 ≤ i → i < 608 → (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := block_join nj_36_17 (fun _ h1 h2 => treeBlockF_at nb_36_18 h1 h2)
theorem nj_36_19 : ∀ i, 0 ≤ i → i < 640 → (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := block_join nj_36_18 (fun _ h1 h2 => treeBlockF_at nb_36_19 h1 h2)
theorem nj_36_20 : ∀ i, 0 ≤ i → i < 672 → (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := block_join nj_36_19 (fun _ h1 h2 => treeBlockF_at nb_36_20 h1 h2)
theorem nj_36_21 : ∀ i, 0 ≤ i → i < 704 → (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := block_join nj_36_20 (fun _ h1 h2 => treeBlockF_at nb_36_21 h1 h2)
theorem nj_36_22 : ∀ i, 0 ≤ i → i < 736 → (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := block_join nj_36_21 (fun _ h1 h2 => treeBlockF_at nb_36_22 h1 h2)
theorem nj_36_23 : ∀ i, 0 ≤ i → i < 768 → (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := block_join nj_36_22 (fun _ h1 h2 => treeBlockF_at nb_36_23 h1 h2)
theorem nj_36_24 : ∀ i, 0 ≤ i → i < 800 → (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := block_join nj_36_23 (fun _ h1 h2 => treeBlockF_at nb_36_24 h1 h2)
theorem nj_36_25 : ∀ i, 0 ≤ i → i < 832 → (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := block_join nj_36_24 (fun _ h1 h2 => treeBlockF_at nb_36_25 h1 h2)
theorem nj_36_26 : ∀ i, 0 ≤ i → i < 864 → (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := block_join nj_36_25 (fun _ h1 h2 => treeBlockF_at nb_36_26 h1 h2)
theorem nj_36_27 : ∀ i, 0 ≤ i → i < 896 → (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := block_join nj_36_26 (fun _ h1 h2 => treeBlockF_at nb_36_27 h1 h2)
theorem nj_36_28 : ∀ i, 0 ≤ i → i < 906 → (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := block_join nj_36_27 (fun _ h1 h2 => treeBlockF_at nb_36_28 h1 h2)
theorem nc_36 : ∀ i, 0 ≤ i → i < 906 → (dagCheckNodeF m_36 g_36 bds_36 906 (dagTraceF m_36 s_36 8 f_36) l_36) i = true := nj_36_28
theorem lb_36 : LowerBin m_36 s_36 g_36 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_36 sub_36 gl_36 rc_36 nc_36

def m_37 : Nat := 0x5555555555555555
def s_37 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_37 : Nat := 0x1115151515151555
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 6, g_10)]
theorem kn_37 : KnownBin bds_37 := by
  intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_10
theorem sub_37 : ∀ b ∈ bds_37, m_37 &&& b.1 = b.1 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_37 : ∀ b ∈ bds_37, canon b.1 g_37 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_37, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
def l_37 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsF m_37 g_37 bds_37 (dagRefF 0 (dagTraceF m_37 s_37 6 f_37) l_37 0) s_37 6 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_37 g_37 bds_37 0 (dagTraceF m_37 s_37 6 f_37) l_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_37 sub_37 gl_37 rc_37 nc_37

def m_38 : Nat := 0xcccccccccccccccc
def s_38 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_38 : Nat := 0x404040404044c
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 6, g_10), (m_13, s_13, 6, g_13), (m_15, s_15, 5, g_15), (m_19, s_19, 5, g_19), (m_27, s_27, 5, g_27), (m_1, s_1, 4, g_1), (m_3, s_3, 4, g_3), (m_5, s_5, 4, g_5)]
theorem kn_38 : KnownBin bds_38 := by
  intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_10
  · exact lb_13
  · exact lb_15
  · exact lb_19
  · exact lb_27
  · exact lb_1
  · exact lb_3
  · exact lb_5
theorem sub_38 : ∀ b ∈ bds_38, m_38 &&& b.1 = b.1 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_38 : ∀ b ∈ bds_38, canon b.1 g_38 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_38, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_38 : Nat → Nat × Nat := unpackForestF 0x3886d9c435cce51ff0cd3339477c023ee0c0c7004a781059c0029ce51cef65337b281bd84cdec206728df77479bb930ddc186e0d13704d9b825cdc0946e049370051b8024ce519edadb36d6b99c93fdad266724ef69051b293ed94976cc0f3650339c939d81266c090360099b0040ce49beb88c35c279ae030d55226aa5b3552b9aa93cd549a6aa063550299c933d49b66a4d733907fa814cce41de9c4a34a07da613cd281769407b39073a2a4cd152068a533452819c837d05186824c3410799d144ce8366741733a0799d034ce8166740933906600b43cdda480293f3269599940ccc20664d1b1a8a398560c6927e5a4e72d0738d24eca5266524a3290518d243c6895e491472429d92019c6894e445331a2478d02bc7628e3a13b1d05d8d029c6c2663408c014878b35ec5d1ae2c9480147f88b4ac48a06241031168d6ac52c3d22daad7b0dac16ab53c1a2860cd37098a183139c1e2860c0e6d56a581c60c0db05aa97eff4a37f949bfc24daa97afa4b97d24cbe8945f40a2d54a77425dba126dd08fae847b7412aba094dd04a2f127974126bb8945dc492e805574029ba0145d24f2e903174026b55295aa4aee18a572450b85a95c257ae10336a929b7ca65aa48ed50576c452b6e285b0d4ad80bd6c02eb5414dac132d504600a33b4da480253ece49567a40b3c2059c91ab08a364d60b249c595142c926958343b1eb056053ec447362039ac0a7580532c027960018ac0a1d604feba8a35d24eae9215740a6b027d5c13cac099d6006eb38a35984eacc1f560066b107958013004a1d58d7aad26b561520049fd4e92aa848154040a9d234cb14aa2ac151138a8e285444d2656a7501459952f53d582654a74bc50a5d26d351429747d4c450a5c14cca94a948c14a260994afd20926902a348049994af5165728b2994593ca2c0c4ca54e792bb3c94d9e49f4f24f6792793c9359e4975044d27925b3f93c9fc9a4f206a790333c8189e81e4f40b27902d329529949fce314a714bd38a529ce284e254a710533293e9bc9e4ca4ce65037344529ae284d094a680bd3403e9940cccc0f26502600933989a44c4912418a72fb5197da4c8297a5b8a52db5e96da948293a558a32c450955274aa53a5524b2095293a294a4d424e4bd2715e938a949c4964128522b43929a0c944fa4528523342918a748c50a452652082890d1c484d0e410480092f8f92447c5121d8a71d4518e9a74744da1d6a51ac528d5af46ad4a3526d0eb428c1a8c60d26316a118232874af45514a2a6bd153528ae2845494a1d29d10b43899a0c4c8fa21485113428892744490a214650e81887c9c43cd0e1d0280092b85da44348f2174910c13c85ca441d14e148a30a24e839a941f14a0f4bd0802883d2941cd080124f0614873e29c111460869d0423a73da940714a036bd01b5280d1d39ed09fb8a2ff4507fda03fc8d1fb684fda4e7ed1eb9e949f28a4fb4507dda03ec8d1f26a4f925e7c9293e48f5cf484f81387a1a1bdad05ed47cf42427a5a13d2939e9484f423273d1a3bd145e58a0ef34278e283bc909de29cef13d77896bbc065cf2a4e845276e283a0d49d98a0e8252740af3a84f1d4258ea018740a93a04f5d025ae801973ca100248dcd6920084f720a5392901c9280e414668228b87581c3070e245070c1a340d0dbeac0df0286fe2837c091a0486d02336eeb034013db8472dc13968027368131b4078da02c68021b400fdad8a2d6a4e6b52135a4c5ad252d003e6ac163400cda005ed1c5168d19346539a3284d193e68c993400b9a1058d002300421b38d799d06ace0520041fb2e52998480cc14065ca329714992ac0c903864e283240d14b6a6c6d606341431d1418d048a5a5352d19b141154b2bcc456052ca9b031418129ac24506049f3051418125ca59525fa302fc5814b0bebd2495e8a4af41454b0bcba85c5d4262ea0f175058a585358c2eac61356307cb183d58c1e2c60d56305cb583c5ac1a2c60b563058b403c58c12ac607964068b202458c0ea961494b07ead4525692f2b49495a262ad12956e282b41494b07cac02c52c19a960bd4e8a4a7232538af29c5494e27ca713253e2829c1494b05ca602c52c118020cd48690a424449e29a8ad454569293a5e50629282d79416a493a4e4fda1a4e4a13d2709e34349c92267145398a099a4e4dda0a664a1350309984e4cc12a4e149288a4983504a12f25cd0928250960184a02f2544a1280a49402549c210020bd242909204440e29a411452069c9003640da92371491b6bc8db5246c1b206d09166a28b34945da822c8c9030bc88452441af220d49118a08825240c2720ed0d0c6828623e41d21210d090849c8424241d192060b1050708234340c120020acfd6908023c3f5241fc0f0fd0907a4533ea289f4938f46a47ac523d52f1ec4a0f54a47a342004139e4120ad8a6774513b9a71dc4e8ad6a474c523a5af1d2d48e927456b42395261ca4a0e505056a53385261c24a0e105056a43366289b9140dd6806e134365a11b2538d927a56952342291a9140d56806a134341a91a0578d02a46813d2b4a119c0e0c668665b4132d1f18c908c768463a4e31d2118c8c8ad2685e45130e28178d08c18a05e1422f0271780f4bc05c5e01d2b42915d148b98a0573522de2815c548ae0bc5903c2c816164070ae0a45703d2b81715c074ad084008232a924154510898a653b5129da4912578a38a451b5e28da9112538a16864493c27c9c13cd0c892684ac5126e2812a538996824a93c25c1612a1389502a4485222a29124d408a2bc483422289e11c0b08a0bc4613c22829114054890840081f218a410c110658a64145120927104098654a43ec521f52f0fa9487d04c32a421e1a88f0d24796a03c1321942f0e5148726bc393521ce280e45486509c34b431b9a08dc4f869284353421a8a70d4508692643283c19c1c0ccd0c650680081b17d240c44b05f2903002c17c240ad14c5c8a22e14e159290af148572bc2c13c15ca90ac9080102e2a04800a298a08e05027028038009a98988e04c27026038009a18911444849c2412a00929087148434bc21a5210c950049083b8a21f4500fda007c4903b4841d94e0ec96804548328a41b4500dda006c490324a41915e0c8a90644b402284180380a1a185ad042d27c141420a5a105253829284141320089203d144258a00f24208e2803c5081e09c0f03e0781683c074020a40845206e28020948198a0081520402f0280f0140580a01c040290200f81005a0801d00821006d480368401a5200d21006548032840185e01c260061480309c0205c00c210040c8010260001f 10 11
def l_38 : Nat → Nat → Option Nat := unpackLinksF 0x73a039d01cd84e6a0f31139785cbc0e5a172d039585c84ae42071e0f8f01c6c3e264713038981c4c0e201f10038801c400e1e0f0f038703c188e0c0706038109c041dfa26fd037d85be42df206f70b7695bb40dd41eea037387b7c8dbe06df036f81b703db806dc036e01b6c1db606da076911b480da406ce136683b244d9206c70b6381b142d8616b92b5c81ad83d6c06b30f5591aac0d5606ab035407aa00d5006a8035383a9c0d4c0e9e233d499e80cf01678033c019e00cec16673f33819903cc80664032d159680cb4065a032a8b94c2ca40e520329019288c9406480b23059141c8a0645031e918f40c7616245f12018900c460e210b10818840c42061f0b081f8400c1e0e0f0306078108c08060403018380c0c040df72efb817dc0be81df402fa017d00bd455ea02f5017a80bd405e516f2817940bca05e30af0857840bc205e102ef077780bbc05dc0aee017700bb805dc02ec8771d2b8a15c406e20170c1b8605c302dd916ec0b7215b70adb036d80b6a0db502da816b48b5a05ab0aca2f6500b24159202c9016480b2015813ebe895f40af80d7a0ab9115c80ade1d6f02b781594aaca056502b2815805abc155d06ae815740aba055522aa8154c2aa2155006a8015400a90454802a3054bd7a5e052f0297034b02a58052c0296014a82a367d17128b814581a28150c22860142c1a1605080e80114000a0004ff067f813f819e65cf30279813c039e004f0027801398a9cc04e602730139809c22ce102708138409be14df026e0737009b804da0a6d0136809b014d8026c0136009b004d50e61a530429800cc0026001300097e0cbf025b912dc096a14b30a59032c809620cb10258812a4895204a70a482f238291c04842a418320c08fe247e063f011f418f224770a3b811d818ea0c7502378d1b428da046c0635831a428d204631a300718008c0045d0e2e8117408ba045a0e2b8715c08ac0c5506270f130289804422a20050fc187e04391a1b850d81868143402170d0b4185a042d0216030a0484e0c27021303098084a0c21120f07078083c041b0e0d8106c083604180e0a8705408280c1306060f0300818040a0a050102028023c0005ff82fec47f40bf905fc80fdc27e623ef11f702f8cb7c213e101f080f6877b013d801ec00f6007a23bcf09e702f38079a0bcb09e580f2c07883bc209e082f0407800bbe09df00ef8077c03b71ddb80ecc476603b301d806ec0076003b001d686ea8375013a801d382e9c074c0ba601d300e98074c039d25cd84e6c07340b9a01cc82e640732039901cc80e58372c039601cb00e3497045b8201c004e000700038001bf04dbcf6d6236b01b502da026c0435c11ae00d6c16b2135121a60ad3006921b4901a480cfca67e033f019f80ce856701337059b80cdc066e0337019790cbc065a132b099502ca80654032a019500ca806444322019004c2576120309018402c18260c0306018300c1025ea7af1117880bc015dc12e6217108b8805c20adf096b90b4855a402d1056880b38358c42c6016300b14158a02c4055c96ae4057202b60d5b00ad8056c02ac295600ab0055802ac01538aa9c054e02a7015284a9405441aa2015100a88054012a0015000a74353a029d014e80a6c25129287094302a18050c0286014300a18050a0a7d213e809ec24f21278053c009e004f00278013c009e004ee0a6f2137809b424acba54092a00928a4920a4901228891014880243051f888f034721a39011c028dc146a1235011a028d004621a310118028c00454322809140089c144e02240d120088c1446022109108086c64283a12090900820a40c12050502807fc63fa11fc04fd047e803e831f304f9807cc03e409ee10f6827b403d809ec00f58279c43c819e400f20078433c201e100f08077833b619db00ed0276413a439d200e90074023a001ce08e38e718138a09c110e0026fc137e01bd08dc886d4436809a92cd38469c034e01a01ccf04678033c019e00cb8e65c032e019700c90a6480324019200c68a62c2314098a00c48261c230e018700c00e5f822fa097d00be025e822f4017a00bd005cc72e6016f10b7805bc02d8196c00b6005b002d219660cb20459002c6096300b10258802c4016200b10056492ae115700ab0255802aa095500aa8055402aa01520ca90054802a40149249f164f0227801322898824c4025a212c0496004ac124e21240c90864840240091f048e844740238091c008c864640230091800890c4402220010f0487804303218010b04858042422120103187e0e3e821f400f02877043b411da00e718728439011c410e2006e0c36c11b600db006d0235841aa08d5006a0235001a608cf106606330019800c90c6480324019200c60c618630c018408c1045d0e2e8017400b8085c002d8215e38ae0456822a4415008a70453802942142209d104e02244b12200910048802305118008c00460021c510a10850042801f870f8107c003e001f000ea38730839021c800e2086f0837801bc00d0386608328219400c8086208310018800c4005b1c2d8015c40ae0057002a0615000a800540028861383098104c00258212c0094084a00250012800940041241f840fc007c083e001e820f4007a003d001e800e83074003a001d000c4906200310018800c4006200310018800c4006008300018000bc104a501a2c00b20001 0x3896d9c435ce11a670c923794699ab60c51a870cd32f5680ea9282c8143ac4f3830305a03ce04167088faf547b3193d8649af044a60c242a483d3fc1af000a4f20439a250c4d206f08c3334a189240ddd185ecd33324c188a50dd9186fc5337d281be04cdec206f28f378261bb830bc51c5d48e2f5691bb344dd5366e897373251b9124dc4146e00936e6d9b6b5cd9da66d65235d26968a60aa9286d693281480ea928da4143ac4f014031b303c0541647e8ea1746db413e830996ce4ba8125a5582d18412eca0645402368150aa4a06bc4c2cf2a154140d7098506d3363499b1240b38b054e5435b261b084cd80206bc8c35d279ae030a089c4f44e281491ada44d68b66b257358279ab934d580c6aa053536d9a935cd29a66a012341068e5960668a86a053163281a71282c8146984f0140305a03c0541624a4e8fd26c4392a17c9369a0f8f2065a582e150116940796303ae5050664206860c1c90a0cc040d08182ccd3348499a3a40d18a668a501c80c0cb850d00186868c342261a083c5941c2c80e163291a0144cfc3667c1733d0799e034cec16674093314a388241e1d1ff0a8ef7f473bd237dbd19dce8c6cd2a353141db09fed44ef64273af937d5099cf04c66125f1e92b85893c1648dc70a2cb041d441fe9e0ef49073a2037ce419ac40c54705e9182b3f0139e208ca903e4281b1780b8a604f3769387232cd0a06661030d6a385b50cd5a5664d1b304bb529518f09cc144c726252f312165428a440e4f00638f82931010e615830a6a17ba50bdda6dfa9072e273521318ec94c124872d072ca031484149de086f76b980a6ccad266544a3290510424077d18612d43268a384342c94a7548509df25a29021c900c8a0045df4719114c3b8a01784c3076a18fc51c19a10a248b1e09cca042c74170a0088bc03a5e138c6c266631471669d86343c15a165e93f2c49d94243b9d2154250e3927303931c9c95e464a721246ee92164421a3e0e4ed0639002bc7014e3408cbb04227813c5d1ae30d7b164a589940c482061ad470b6a18a34ac45a3608976cc2a31c13981898dca4a5dc242e30514781c9d80c6dc0525d021c3d22e1b582fd6b980a6cc249cbca4c6e4252ed921c1c1c9860c6db0525c821c262860f1430b8a18534dc0d2ee104e5e42637192976890e0c0e4c20636d0292e010e09183036c17c260be22ee0294700293659418dc94c0a486ff092e2841474149d6086f86d97ea5cbf1265f64a2fa05178924ba8125de0a2e90497893c754965dc062ef25177124ba89e1644b2e90317c25dbdd26dec8faf547b1b13981098de84aaf325379128bc0933a64851c07275031bb4155d80a6eb051740262c410c06901d146172350b92285cb14ae36a57115eb2ca93a24b44e0437081913008ba28e2df298749402b8985b6d42db8a16e452b69a909a48ad90bce2852b6017098088ae03a57138b582662114b0e6bd86353c15a960497efe4bd7ca53b9d2959054e3427301131b9895dc04a6de246e792170829a340e4e80636e82bb5c14daa08cad04225813b4da4d3e4cad048167840b31a8d3c9469c4a168a4ab39234b28fa014656395daf49f3cc4c9900a24202912810d6a0642602300240765183ca502ca268ff930b2a283fc4c2ccac0fea40761183c8502bb27965938b249a3a64c2c7ac14da50a20a8510d36c54735da31a38a0cac4b9fc2456203963c18906064490234425ca44b6584532c1279600187ed203c05029a2a15ec51af127576909e047b4c94239c18d740a4e5042f024cae09e0904c01e2414c250ad628d2e908e62655a04e63c215660f8e50640f01d078945620f2cd8a364343ab12753a90e964852a23e7e91958c53ec329d5f9439e0a157c4feb927d5b9337749931810ce40664082911c10d6c06eb20335801307408d5a4d6ae6bd56152aa520550102a56a34f251a712855492aa748d29a3e7e51952a5767627cee132704289000a4460433601907008bf0901e3460ed940a8c9a3ee4c2a38a0fb130a96b03ea901e2460ed1409d09e5484e2a2268e9930a80a2d3d5828e4b94896ca691f3c68ca7327cec932a601484a0866b0320d811a6a285311429c8a14da4da651f3c48ca942bb3913e7609952e0a4240433501906808d2b182944c144960a262ed249267448348951940973e848a90092e00411fc0c88a046894d94715ca34a65184f28b031400189ec0a3ac4f2822593f818a089a4f4052802793f9349ec1e4f40b01403927a3e7cd195125768829b4393ea189ed0a4f28426ae9932a0c975024b47e052220219f80d4fa0667c0313c81604c08be4901d2281399509ce284ed14a754bd3a2527491ece4548e30633882938410ba49326f27821930040904d69426b8a1364529a9291c44ca690bce00529a01f1c20c81003a081289981e54d14aa16a74fa5ea7529d2c94a4d47cf8a32a4cafd1e57a8a2a73c1529dc9fce04fa6e266e79326f4299c00cc7c052210219b40dcce06665026078117591a4860d2636913026c9752e4b6932624892c96094ca849e5024c05121024948a04c0d465f6932db41944994b0541d64712ec52971af4b6d4a572a52c25c92c144b11424a0312cc5195d274ac53a4f2852a925924144a4972480512935091c0c4304924605129c529452f4a057a4f2a52712591414496542482812313092da0c944fa462652434291ca748c50a4c68724942914994868e24268730c539792f4b493a542a52694291014482091d52490f8248f1b0470d42366811fa488ccb645c5722c2991f1448a00c43c0522b2b9138188980c4791463b69d1b3428a8a74744da250311895c8900c4460621a269110188e22946ed7a366a51815e8d49b4420623148118b508cda8c64d262c683182328ad283aa4e22b8a1174528b5af458d4a2a4a513a50891204448c2276831323e88919448d0a2349d112428a1a1c4a90a214650f938879a1c7b14e396a51a3428bcaf45253a200310e8148691e3e048218278f8120855b0424d421b69107b408652442e521ef240f71307b49042b1461449d07a427b0983d64c1ea240f49308401442514a114bd07a527a09842d14e136a50734279c903e08d20a6c103350811a0402981f94a0f9a407bd1a3cc581dc2a10614874ca03f0941db2a105451825a7408d09f54850423a768a101c046004a0f295081a2940ad7a046a4fea5280d1d3c85480d02300350764a83fe8d1ff681004507f91a403145fd684fe24e7cd213f68f5d8284060117e1a83c6541f7468fbb407e2283ec8d1f98a4fab527d12f3e6949f247af115202c08bdc941eb480f4a307c09c3dcd05ed47cf4a327ada13d4939e9484f7b437b1213d08c9e56a0f1a50796283c7141e68a2f2342789213c2539d3284f013d77c96bbc06406022edb50765283b7141d98a0eb13c754963a8061dc8a4ed352761293ae579d32a4e913d74496ba00640302305c5381da9404d09fa4a4f8a4279d1a3ba549cf284de05362c21804045cd692c483272920392501c66a2e0a51620a8b0c541cb294e41464e89f1be4c89c25c209226ec2eb620f8c4064d402e098111bc500b7260618407101a1ba0c1c48a06e03071ab01b6500b6260610406bc1e38a0e1c3068588301009803248025060df8240fc1037f1403e040e0d600f49803048024060d282c7001437c09013040051206b82634e0f1a3058030206eeb030a541720a0b934d6e51cb5e8c5b8272d29315e020a680b8da0444b01e0f0092e45717a0d8db04c6d41e3680b0d92805f04061028363145b049cd7a422f91eb5c4c5ad252d192160c2117c531ab0581d93007c18304141a88a2d3a32698a734a509a427cd193207c96b021081f278d082c71e28b84d0dbd486de233670a730e50d802849913e360991284b83a244dd04f6dc2736610d62084d903f6b01f3540ccbb064d482f6881734008c1d044ce835679af33814999480cc140655a8b20945882a2c3150668a532e5193127c6b93224c970724897f0bab003e2e8192aa0b81c0446b14030498172101930686a83064e281a80c195ac069940300981701015e078ca0386481a1620c0382601192006c1831c09037040c74500d8103215803526011120068182a40b18f050c682404c100124815d098aa03c540160060818a08ac45605e0ae2f41b18427c60932608970464895b07c5b83253c17032089848a0c145061a2830a5358327c60132604970444897e0baad03e2d81929c0b818044bfc605f8b02e6181738babe24957920af652552282bd0514ac171a40888d03c1a0125ccb62f017177098bb03c5d4162d80b1680485a03c5ac162ca0716c078b58345a01e02a0b164038b2834590122524f8d12644592e0cc912e61757209ab883e5c01eade0f16e06a588325b4172d40b569058b382504c112cc0796303a681402c0202b61415b8a0b045257d2f2bc948b047aae93157094aa04855a0a45814c560160644c011060a785053e282ab14954464a995e548a92a24f9502640892d538290224f14c058cb452645a9b1894d8b466c495e61ca9b005492727c67932224970624897d0bebc85e5d029ac41496107eac83e55c1995a0c95605ea682e52c1181e088b44689e934525a428c9b1434b8a0a4c5212227e4a13c2489d0604c42825210130080a3351515a4a82d052f0649c8502d11c287149426bca0b524e02926e1412e080950304fda1a6c1092d0649e9384f1a1a72971372509cc504dda0a6a0f92a0649a8184ea28a70939362509a04e4a421266095304b8971284c1a825cd092c09c950424b00c2544a0fe04898c524bd2f25a4a12b0bc948524a012a8f14d444bca024e4f894276491320a49384241492164051226c08f350471a024a521190d88a05c448262481110e058820244442e21a0b10c05891451485a7238d091009c9003642c1622e1710a0588482c4001a2100b11e8a48eb5e471a922c1791b06c8382c45d2022ed41196a28c349449a0a2c8c9114a05903844628229149136bc893524412921a9410a48084230435a0a188f90846485342425272109090e68685a4241d1920a0e10468691c5347da9234d09150bc8784e4181620609100478670203f81e19c080fb6c07c350405a41ead00ff4907e848334101980c0cb0407dc513e9271ea908ca06064830320101ec4a0c70607c4523dd2f1ea948c60607e4533e5a91e8d08c5040671343c1b01d8d40ea6806f96035ca81a2500cd268620602e8281e4120b10806b1502e4281e1144ef69c7534234ca11dc4e8b808407022378a8186140ec8a475b5e3a9a91b6548e927461052034111ce930e6250060303941400c080e34987112802c181c20a0030406f3502dc281ba4d0dd6806f4503709a1bf144db6846d14e344a11b24f4b608405022359a8182140d52686ab4035a281a84d0d78a469b52348af1a2548d027a6005202411198940c948063a303381c198d04cb47c63a32325a1190938c748466b433292118c8c8c36a06095030e28183140c48a261342300a117e138b10845f03d2f41700c088bc03a5cb502dca8173140b78a05a03c2cc16164070ba8a45c3522d8a916a178b10a45803d2bc17006088ae03a78c533b5a91d0d08e44a670243360a919e508c52685d8522b4210040889f4680a9242ad241505b0a52b85194c2a8a21424f09e2684e06024c28116100920805435129da4946d04910644d8500549c14b148a46bc51b52268291321409008046030285a19301088f0644f938279a1936570992784dc50265a092e0f88c0644b82c27228934538982784b04e22c2112a054922b84813c249a8120d088e09c46042238161184f06002849c52244af11e4f08d0bc458522280a95314ca62bc5114e2809e13a4d0940a44484219c9a028050844c0402501f92010e5207b0d83b05c1d02610c11070078330341cc2e0de0f06e0584245120d270fc9087209c3683c208130f21706c0783582c1a81e0c4090808a43fa5e1f9290f0178690783e8261e4a00f2d407b6a23d3491d1a08f04c8732a00a0381ce280ed148756bc3a3521c8a90de5406c280351301bda08dc4f86a264363421aca70d450870686369421a4990ce0e06668642c53205290f8908770bc3884e1a01e0ca0d06225818010180160600405d4c02d25018d240ae900612902f8480bc0805c0802d0202ec51170a70ae5082c040158200a8080b04f0290402d452164af0ae548280402f45316d290ac90827020181241293008c94044480209600e4a80665002f24813060070280a812013080292381449c01c10050070030301391c09a4e00d0802603800c180705401b0a02545112527088908352842412a068210180c8402a01285011a2908a978444a41e95210c950481480b064202500642807e4903f680204500f8920831443d4841e14e0cca10764b418084050320e128046140372481bb400e22806c490398a41aa520d0af0665483225a110520241905c5402b280149300c01c05cd042d27c149320ada10545382928417b430b0a10504c8254a01195009628047140268a212242088a1042138130841003e0181903e0b41e03a0da50064a8037140198a00b03c054160280701c8a40d252060a902e178130a40903e00c190220b41003a0384c0102e01cd480d6840625202d21014548092840405e0182900a1380308429c5313da9896d0c474a4212420e8a9062508272480e85203c210040cb386879b24fc6521e2a8fed44676914fabca1d564fe642672012f87095c1a49dce246e604f67c21b360fd4a0669302f408159e609cac0464401f1900d8aa05c010260001f 17 6 11 10 7
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsF m_38 g_38 bds_38 (dagRefF 906 (dagTraceF m_38 s_38 8 f_38) l_38 0) s_38 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_0 : treeBlockF 0 32 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_1 : treeBlockF 32 64 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_2 : treeBlockF 64 96 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_3 : treeBlockF 96 128 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_4 : treeBlockF 128 160 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_5 : treeBlockF 160 192 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_6 : treeBlockF 192 224 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_7 : treeBlockF 224 256 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_8 : treeBlockF 256 288 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_9 : treeBlockF 288 320 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_10 : treeBlockF 320 352 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_11 : treeBlockF 352 384 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_12 : treeBlockF 384 416 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_13 : treeBlockF 416 448 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_14 : treeBlockF 448 480 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_15 : treeBlockF 480 512 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_16 : treeBlockF 512 544 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_17 : treeBlockF 544 576 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_18 : treeBlockF 576 608 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_19 : treeBlockF 608 640 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_20 : treeBlockF 640 672 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_21 : treeBlockF 672 704 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_22 : treeBlockF 704 736 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_23 : treeBlockF 736 768 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_24 : treeBlockF 768 800 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_25 : treeBlockF 800 832 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_26 : treeBlockF 832 864 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_27 : treeBlockF 864 896 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_28 : treeBlockF 896 906 (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) = true := by decide +kernel
theorem nj_38_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_38_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_38_1 h1 h2)
theorem nj_38_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_1 (fun _ h1 h2 => treeBlockF_at nb_38_2 h1 h2)
theorem nj_38_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_2 (fun _ h1 h2 => treeBlockF_at nb_38_3 h1 h2)
theorem nj_38_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_3 (fun _ h1 h2 => treeBlockF_at nb_38_4 h1 h2)
theorem nj_38_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_4 (fun _ h1 h2 => treeBlockF_at nb_38_5 h1 h2)
theorem nj_38_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_5 (fun _ h1 h2 => treeBlockF_at nb_38_6 h1 h2)
theorem nj_38_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_6 (fun _ h1 h2 => treeBlockF_at nb_38_7 h1 h2)
theorem nj_38_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_7 (fun _ h1 h2 => treeBlockF_at nb_38_8 h1 h2)
theorem nj_38_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_8 (fun _ h1 h2 => treeBlockF_at nb_38_9 h1 h2)
theorem nj_38_10 : ∀ i, 0 ≤ i → i < 352 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_9 (fun _ h1 h2 => treeBlockF_at nb_38_10 h1 h2)
theorem nj_38_11 : ∀ i, 0 ≤ i → i < 384 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_10 (fun _ h1 h2 => treeBlockF_at nb_38_11 h1 h2)
theorem nj_38_12 : ∀ i, 0 ≤ i → i < 416 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_11 (fun _ h1 h2 => treeBlockF_at nb_38_12 h1 h2)
theorem nj_38_13 : ∀ i, 0 ≤ i → i < 448 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_12 (fun _ h1 h2 => treeBlockF_at nb_38_13 h1 h2)
theorem nj_38_14 : ∀ i, 0 ≤ i → i < 480 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_13 (fun _ h1 h2 => treeBlockF_at nb_38_14 h1 h2)
theorem nj_38_15 : ∀ i, 0 ≤ i → i < 512 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_14 (fun _ h1 h2 => treeBlockF_at nb_38_15 h1 h2)
theorem nj_38_16 : ∀ i, 0 ≤ i → i < 544 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_15 (fun _ h1 h2 => treeBlockF_at nb_38_16 h1 h2)
theorem nj_38_17 : ∀ i, 0 ≤ i → i < 576 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_16 (fun _ h1 h2 => treeBlockF_at nb_38_17 h1 h2)
theorem nj_38_18 : ∀ i, 0 ≤ i → i < 608 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_17 (fun _ h1 h2 => treeBlockF_at nb_38_18 h1 h2)
theorem nj_38_19 : ∀ i, 0 ≤ i → i < 640 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_18 (fun _ h1 h2 => treeBlockF_at nb_38_19 h1 h2)
theorem nj_38_20 : ∀ i, 0 ≤ i → i < 672 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_19 (fun _ h1 h2 => treeBlockF_at nb_38_20 h1 h2)
theorem nj_38_21 : ∀ i, 0 ≤ i → i < 704 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_20 (fun _ h1 h2 => treeBlockF_at nb_38_21 h1 h2)
theorem nj_38_22 : ∀ i, 0 ≤ i → i < 736 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_21 (fun _ h1 h2 => treeBlockF_at nb_38_22 h1 h2)
theorem nj_38_23 : ∀ i, 0 ≤ i → i < 768 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_22 (fun _ h1 h2 => treeBlockF_at nb_38_23 h1 h2)
theorem nj_38_24 : ∀ i, 0 ≤ i → i < 800 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_23 (fun _ h1 h2 => treeBlockF_at nb_38_24 h1 h2)
theorem nj_38_25 : ∀ i, 0 ≤ i → i < 832 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_24 (fun _ h1 h2 => treeBlockF_at nb_38_25 h1 h2)
theorem nj_38_26 : ∀ i, 0 ≤ i → i < 864 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_25 (fun _ h1 h2 => treeBlockF_at nb_38_26 h1 h2)
theorem nj_38_27 : ∀ i, 0 ≤ i → i < 896 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_26 (fun _ h1 h2 => treeBlockF_at nb_38_27 h1 h2)
theorem nj_38_28 : ∀ i, 0 ≤ i → i < 906 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := block_join nj_38_27 (fun _ h1 h2 => treeBlockF_at nb_38_28 h1 h2)
theorem nc_38 : ∀ i, 0 ≤ i → i < 906 → (dagCheckNodeF m_38 g_38 bds_38 906 (dagTraceF m_38 s_38 8 f_38) l_38) i = true := nj_38_28
theorem lb_38 : LowerBin m_38 s_38 g_38 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_38 sub_38 gl_38 rc_38 nc_38

def m_39 : Nat := 0x3333333333333333
def s_39 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_39 : Nat := 0x1113113311331333
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 6, g_11)]
theorem kn_39 : KnownBin bds_39 := by
  intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl
  · exact lb_11
theorem sub_39 : ∀ b ∈ bds_39, m_39 &&& b.1 = b.1 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
theorem gl_39 : ∀ b ∈ bds_39, canon b.1 g_39 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_39, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl ; decide +kernel
def f_39 : Nat → Nat × Nat := fun _ => (0, 0)
def l_39 : Nat → Nat → Option Nat := fun _ _ => none
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsF m_39 g_39 bds_39 (dagRefF 0 (dagTraceF m_39 s_39 6 f_39) l_39 0) s_39 6 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeF m_39 g_39 bds_39 0 (dagTraceF m_39 s_39 6 f_39) l_39 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_39 : LowerBin m_39 s_39 g_39 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_39 sub_39 gl_39 rc_39 nc_39

def m_40 : Nat := 0xf0f0f0f0f0f0f0f0
def s_40 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_40 : Nat := 0x1010103010301070
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 6, g_17), (m_21, s_21, 5, g_21), (m_29, s_29, 5, g_29), (m_7, s_7, 4, g_7)]
theorem kn_40 : KnownBin bds_40 := by
  intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_17
  · exact lb_21
  · exact lb_29
  · exact lb_7
theorem sub_40 : ∀ b ∈ bds_40, m_40 &&& b.1 = b.1 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_40 : ∀ b ∈ bds_40, canon b.1 g_40 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_40, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def f_40 : Nat → Nat × Nat := unpackForestF 0x500189d2933c0b2742480b4f948bd2917665284a3569747128d3a509cca03901696eed39dda4bba528969d12d262497449228905d1448224113ba50872a0ee57a15283b952772a304d25dca83f9507f0a0ee179ed283d95c7b2a0ee149dc28bc349770a002d1dd1ae3a250548acded71bd28379506f0a0a915551af2a35d5469ca8d35511d3212e64244c80b994903202254470c48e1509d2a13954270bc4a1509b2d2385a270b44d1501d2a03954070aa4a154142a03601686971652e28a594e4b28c9606931a4a63414b0300252d0e2ca1c514329c8a9011420219464325a0250ce52d1fa483f09072578f09e1e018392b472558e4a90093b2b4a456578d40c1595a332a056558bc9e1792c2f03056548ac969581a2b030024cc8a2c914512209c44118881691b4923682440b004258d4591a8a23413871200e1401a08c3407404218815a164902c520402f0983c1305820168402b080520107604548082f0602c020b414140082b0303c060580c07008290102d020580407404198001f 8 11
def l_40 : Nat → Nat → Option Nat := unpackLinksF 0x8982241890222182b20818186060800e0007e8dfa07e81db07605d237199c607181c607105c407101c216ca1b206b0dac06911a406901a026801a00668d9a066819a0649192064818e259d166059816225881620588162056915a056815a056815245481501540150053854645181403500140050013a34e813a04e813434d013404d013404b8cff83f04fa13e04f803e00f803e00f4237acde03780de03780de0360cd8031a4c413100c402f8cbe02f80b832e00b802a9ca812a00a802984a602904a402900a40278c9e027809e023248a122048612180860218086020886cb1b006c01b006c01b006631980549148452014804c313004c0118c46011803870d843600d803410d003210c803200c802c30b002c00b001a900b0001 0x14006278164b45e6c8bb36d6a69acc93566c6a324d1a61a2cf949392833a1244020bab44726a932940cca80505097470604e0181c4dc5e9a8bb23155aa294c356916ab2cd39a9a6a9159492a32a4e4d09894859200a3280e42c18c7a508e4a104541e0284745c8f6b90e57214a84005c7d0a114082289047b4e8e692e8d09c5a0c692e8c245160ba241119c5c872a0f81420a2e42a507f0b8f614209a4b83410a8b900541fc283c45c7d4a0f8571eca83c3496f68323179ae2ec935e6d6bb24d3a45a4b9b426e6832094a21284315e3b2b30854a0ca8c09507e0bc24165e8293c851770a0ead71d1283935c714a0e0541bc28311385e268b80e1581a3282065240d04b99c913302e64044c48e16c1c2a83430478bc4a168142e2385b270b44d0191e2b12855050d9175aa2d39c566e8aadad79b1aeb5b4e6a69ad28e98d1c28959482a2c24e9809caf9385d26c5c4c4a02c8f85159074b00e55c1c2a036050629a061300c181384d69298d054a2ca8c51434a48292940a71d94a4f28c685090c96a701a4b0308c900cca022840498b2911450d2d1ba424729c7252910a3171424325a604910124181483f0907a4f0cc961e018414b45a908f8af1d95a3a2ac72548b496999243503066540c49e1812c2f0306e948b5251b15e342b464558b8a91692d2c0345606090161182c0607048d248da094c59288a23454860a51384e120944c1182c211282d220583407475200e1400a080411647e288d15a0e2843c13840250d8460508434074180a0ba48162900c120501e0982c0a0383056808a10a85e120b42215840290101d0a028180b028280403c070580c07038a90114a0d0bc16168242b028520405a060b0080ece34f93696ecd1d4da1a514b42286704eca8999084b190861e0ec04198001f 14 5 11 8 6
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsF m_40 g_40 bds_40 (dagRefF 161 (dagTraceF m_40 s_40 7 f_40) l_40 0) s_40 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_0 : treeBlockF 0 32 (dagCheckNodeF m_40 g_40 bds_40 161 (dagTraceF m_40 s_40 7 f_40) l_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_1 : treeBlockF 32 64 (dagCheckNodeF m_40 g_40 bds_40 161 (dagTraceF m_40 s_40 7 f_40) l_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_2 : treeBlockF 64 96 (dagCheckNodeF m_40 g_40 bds_40 161 (dagTraceF m_40 s_40 7 f_40) l_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_3 : treeBlockF 96 128 (dagCheckNodeF m_40 g_40 bds_40 161 (dagTraceF m_40 s_40 7 f_40) l_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_4 : treeBlockF 128 160 (dagCheckNodeF m_40 g_40 bds_40 161 (dagTraceF m_40 s_40 7 f_40) l_40) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_5 : treeBlockF 160 161 (dagCheckNodeF m_40 g_40 bds_40 161 (dagTraceF m_40 s_40 7 f_40) l_40) = true := by decide +kernel
theorem nj_40_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_40 g_40 bds_40 161 (dagTraceF m_40 s_40 7 f_40) l_40) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_40_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_40_1 h1 h2)
theorem nj_40_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_40 g_40 bds_40 161 (dagTraceF m_40 s_40 7 f_40) l_40) i = true := block_join nj_40_1 (fun _ h1 h2 => treeBlockF_at nb_40_2 h1 h2)
theorem nj_40_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_40 g_40 bds_40 161 (dagTraceF m_40 s_40 7 f_40) l_40) i = true := block_join nj_40_2 (fun _ h1 h2 => treeBlockF_at nb_40_3 h1 h2)
theorem nj_40_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_40 g_40 bds_40 161 (dagTraceF m_40 s_40 7 f_40) l_40) i = true := block_join nj_40_3 (fun _ h1 h2 => treeBlockF_at nb_40_4 h1 h2)
theorem nj_40_5 : ∀ i, 0 ≤ i → i < 161 → (dagCheckNodeF m_40 g_40 bds_40 161 (dagTraceF m_40 s_40 7 f_40) l_40) i = true := block_join nj_40_4 (fun _ h1 h2 => treeBlockF_at nb_40_5 h1 h2)
theorem nc_40 : ∀ i, 0 ≤ i → i < 161 → (dagCheckNodeF m_40 g_40 bds_40 161 (dagTraceF m_40 s_40 7 f_40) l_40) i = true := nj_40_5
theorem lb_40 : LowerBin m_40 s_40 g_40 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_40 sub_40 gl_40 rc_40 nc_40

def m_41 : Nat := 0xf0f0f0f0f0f0f0f
def s_41 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_41 : Nat := 0x10705070507070f
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 6, g_13), (m_16, s_16, 6, g_16), (m_12, s_12, 5, g_12), (m_20, s_20, 5, g_20), (m_22, s_22, 5, g_22), (m_28, s_28, 5, g_28), (m_30, s_30, 5, g_30), (m_0, s_0, 4, g_0), (m_2, s_2, 4, g_2), (m_6, s_6, 4, g_6)]
theorem kn_41 : KnownBin bds_41 := by
  intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_13
  · exact lb_16
  · exact lb_12
  · exact lb_20
  · exact lb_22
  · exact lb_28
  · exact lb_30
  · exact lb_0
  · exact lb_2
  · exact lb_6
theorem sub_41 : ∀ b ∈ bds_41, m_41 &&& b.1 = b.1 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_41 : ∀ b ∈ bds_41, canon b.1 g_41 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_41, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_41 : Nat → Nat × Nat := unpackForestF 0xad24500b4fa6a5fa6a5daa46caa160aa060a6a57a9154a695ba6953a7854a685ba685300b47a5c5ea4b55a4b4500a4f9a35f9a35da1c6ca1960a18609a357a0c5e9a34d9f35c9f26c9a3479db4e9da5e9a3459c9549a15b9a1539b0549a05b9a05300a4798b5498a547245f97d6c7245b96b567245a9336c9326c9316c931609306c93060724578bc5e8bb5e8ba5e8b95e8fb5c8fa5c8b9528e05c8e0508b85e8c35c8c25c8c15c8b852724568ab5c87d6487b5c879388793487838878347245385b4985b4185a5e7235682b4982b4182a5e82a4682a447225681048810447214f7da5c7d9447d9347d8187e14c7d8147214b7c35c7c25c721477b14c7aa547214379148791447204f7595c75844758347582c7604c758247204b7435c7425c720477304c729547204300a377125d6d3457035d6d2456dc586dc546db546da546d2370094f6c3470094b6b2456635d6a3456625d68c6c68c6066237679276605c66a3766050009476515c5c34763a4d63a355c1466223f622375c1446034a60346602465c1365ea3b5ea375c1345da375c0185ca375c014009435ac6c5a96c55b5759a5d55a5658a5d559565635a563565625656156559360093b54a4d009375336c5316c4dc575235d4da564da4650b5d4d9564e45a4e4564e3564e1564d9460092b4c34a4c14a009274b25d473454a35d4724547c5847c5447b5447a54472370084f463470084b452454035d443454025d42c6c42c6040237419274015c40a3740150008473f05c363473da4d3da35360463c23f3c237360443a34a3a3463a2463603638a3b38a373603437a373602c36a37360240084334c6c3486c2fb5733a5d2f95632a5d2f8563035a3035630256300562f8360083b2ca4d2d3502d3482d25c2c927008372b36c2b06c25c572a35d259562594628b5d258562645a264562635626056258460082b2234a23350233482325c221472204a008272115c1e3472024d1e1461eb4a1eb461e1360081f1d05c1a3471c24d1a0461ab4a1ab461a0360081b19347008171806c014571706c013571605c013471524d012461434a0123611a4d122381214c11926011460f34a0fa380f94c0f146011360e04c0da37011240b35d0b3450b25d0b2450105606c5a09a5c06c5606b5606a4d06a3506926068260104601b5a0535c01b5601b4a01b4601a5601a46019460184601036008130001f 9 11
def l_41 : Nat → Nat → Option Nat := unpackLinksF 0x8501090a0f1c16482c10506090c08581010186030406080830101f37be607c82f901f013da37a48f481e80bce1788af101e10bc207840ef0dde03bc076c6ed81da0bb407680ec85d90394f7280e501c6238a17048e081bf137e06fc0df81bf037e06fc0dba1b7036a26cc4d889b1036206b86d701ae035826b00d601ac035236850d081a00b4006800d001a0034006610cc01980330064cac981930326064c0c9818e2b1c06380c58d89131206240c481890310160cac18183030036000bf857e0afc05f80bd8d7912f205e40bc817902f015ccab9817302e035c00b7856e0aa5c5480a78d4f029835300a6014c029805208a28d45028815100a08d41027c34f809f013a227404e429c81380a6274c4095992b025604a06940128024c249809301260246348c091812112420480290011f0a30746008c01142228044848901101220044008801100218441ca8289012202040407e90fd01f623ec07d80f911f203e407c80f901ea43c0a7708ee01d443a80738ce701c8339007200e401c8038086e8cdd01b8137006c8cd901ac335806b00d221a4034426880d00992732406198c30186030066000c0017c22f805f00be017632ec05d80b9117202e025c00b7096072c005800ac215802a845500a8115002a005400a80148427ca4e889d0138126c24b90932126024c047908f011a2234046808b1116022c045808b010e4208a40088000fe11f823d107a00ec41d803a087400e421c8039007010da31b4035886b00d221a4034806710c8318c230886100ba417402c905808a651482278c4e08963128225004a0090211462204440088010841f8c3f007c10f421e803d007a00f401b9837006e00d821b0036006c00d801b002e405c00b8016842d005a00b4016802d005a009500d2c01c8001 0xa0255ad245912649da4485a34912569f246539292b8298fa5c8ca5cab46c9fb6c9125caa960aa060a9154a7854ac25faba5da9a578b255a524d9ea479d24585235a895ba81535292ba705ba68532a82b17813a5c5ea5355a4b4591b649e35483a349fb5691b465b139350399035c8d35ca2c6c91b5c9f26ca2160a1860a0c5e9fb5c9f26c832349e34e9da5e82a349c9549b054a3b5fa335da13578b355a034d9eb479d345822369c15b9b9535a13b9a85b9a0533403b1681397c6896c549935498a548ab5497d6c9256486c6484a6496b5692355924588a45095b6c9526c9496c941609386c93060901508d0508f9508c8508e85c8c0509035c8fa5c8e05c8e85c8e0508d35c8ca5c8c15c9245e89c5d91b5e9125e9095e8f1528d85e8b8528ab5c8a5648646489b5c842648913888934880388783486b498634185a5e8324682a4484b498434183a5e8324682a448015881848810447b1447e0147e14c8025c7f9447f1347e8187d8147cb5c7c25c7a9407b14c7aa5479948791447805873044760147604c7815c77844770347682c7582474b5c7425c728407304c729549845f9745b9645a92c578b4568745385356822566d15f6c15b68157649538094f7d14b7b9477a1434705f4605b420573e8537884f7504b73847720432081f1c81b19017158137125d6ea556e2357035d6eb556da366f4586ec546e3546da5470b456fa456d2376c3476924d6b2455212a6934d6a3455993a6946c68c606786c668606792766a376ab5d69a5d682375913a5192a6705c660506515c6095463944601345d8185c8146424d60a4563a3562a3f622376134a60b46602465f23b5ea375da375ca3764b4763146619445f9365e1345d0185c0145b46c5a96c571645693459a5d5612658a5d5725557b5a5735656a56561565a357592564c2365815655936230251501154a4d5112a228271481153b6c5316c4f1644e9445235d4e13650b5d4f3554fc5a4f4564eb564e15652c5751a5651246501564d9462d845140114cb4a4c14a2c847138114b25d48a55482354a35d48b5547a364945848c544835447a544ab4549a4547237463474324d452452a02a4334d443453383a4346c42c604196c409604192740a3744b5d43a5d422374115c401503303a2982a3f05c3a8543d8443a0343782c368243e24d3aa453da353ca3f3c2373b34a3ab463a2463923b38a3737a3736a373eb473d0463b84439836380343702c360243546c3486c310643083433a5d3002632a5d3125531b5a3135630a5630056343573315622136320562f8362d1251301212810120102e3502db482d25c118102ea4d2c9272902a110122bb6c2b06c27064268442a35d2603628b5d2735527c5a2745626b56260562ac57299562914628056258462394510812100100f8102435023b482325c0f01024b4a229472204a0e8122115c1e9542024d1ea451f34a1eb4620b471f9461e1361d05c1a8541c24d1aa451b34a1ab461cb471b8461a0360d810193470d0101806c090640c054088441706c048640b054030340e0140d9241605c0385407844028340f9241524d0f12602026129441434a11946070461212412a381214c1324d119260182610144102380f94c10b4a0f146068460e04c0da370cb5d093550c3450ba5d04a550b24509a5c0a45a0945608b560824d03a4507a3507126068260535c05b5a04b560434a03b460325602a46021460184617c5716b5715b4714a4613a36111460e9360d1240a8560604601036acb4fa6347a424f99a4771a376c94f6b94b659475b9435513b541374d12b4b9274684f4584b3f847358432f03b2c0372502b218271d81f1981b18817008130001f 15 5 11 9 6
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsF m_41 g_41 bds_41 (dagRefF 347 (dagTraceF m_41 s_41 8 f_41) l_41 0) s_41 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_0 : treeBlockF 0 32 (dagCheckNodeF m_41 g_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_1 : treeBlockF 32 64 (dagCheckNodeF m_41 g_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_2 : treeBlockF 64 96 (dagCheckNodeF m_41 g_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_3 : treeBlockF 96 128 (dagCheckNodeF m_41 g_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_4 : treeBlockF 128 160 (dagCheckNodeF m_41 g_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_5 : treeBlockF 160 192 (dagCheckNodeF m_41 g_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_6 : treeBlockF 192 224 (dagCheckNodeF m_41 g_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_7 : treeBlockF 224 256 (dagCheckNodeF m_41 g_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_8 : treeBlockF 256 288 (dagCheckNodeF m_41 g_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_9 : treeBlockF 288 320 (dagCheckNodeF m_41 g_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_10 : treeBlockF 320 347 (dagCheckNodeF m_41 g_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) l_41) = true := by decide +kernel
theorem nj_41_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_41 g_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_41_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_41_1 h1 h2)
theorem nj_41_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_41 g_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := block_join nj_41_1 (fun _ h1 h2 => treeBlockF_at nb_41_2 h1 h2)
theorem nj_41_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_41 g_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := block_join nj_41_2 (fun _ h1 h2 => treeBlockF_at nb_41_3 h1 h2)
theorem nj_41_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_41 g_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := block_join nj_41_3 (fun _ h1 h2 => treeBlockF_at nb_41_4 h1 h2)
theorem nj_41_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_41 g_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := block_join nj_41_4 (fun _ h1 h2 => treeBlockF_at nb_41_5 h1 h2)
theorem nj_41_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_41 g_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := block_join nj_41_5 (fun _ h1 h2 => treeBlockF_at nb_41_6 h1 h2)
theorem nj_41_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_41 g_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := block_join nj_41_6 (fun _ h1 h2 => treeBlockF_at nb_41_7 h1 h2)
theorem nj_41_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_41 g_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := block_join nj_41_7 (fun _ h1 h2 => treeBlockF_at nb_41_8 h1 h2)
theorem nj_41_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_41 g_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := block_join nj_41_8 (fun _ h1 h2 => treeBlockF_at nb_41_9 h1 h2)
theorem nj_41_10 : ∀ i, 0 ≤ i → i < 347 → (dagCheckNodeF m_41 g_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := block_join nj_41_9 (fun _ h1 h2 => treeBlockF_at nb_41_10 h1 h2)
theorem nc_41 : ∀ i, 0 ≤ i → i < 347 → (dagCheckNodeF m_41 g_41 bds_41 347 (dagTraceF m_41 s_41 8 f_41) l_41) i = true := nj_41_10
theorem lb_41 : LowerBin m_41 s_41 g_41 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_41 sub_41 gl_41 rc_41 nc_41

def m_42 : Nat := 0xff00ff00ff00ff00
def s_42 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_42 : Nat := 0x1100150015001700
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 6, g_16), (m_24, s_24, 5, g_24), (m_32, s_32, 5, g_32), (m_9, s_9, 4, g_9)]
theorem kn_42 : KnownBin bds_42 := by
  intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl
  · exact lb_16
  · exact lb_24
  · exact lb_32
  · exact lb_9
theorem sub_42 : ∀ b ∈ bds_42, m_42 &&& b.1 = b.1 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_42 : ∀ b ∈ bds_42, canon b.1 g_42 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_42, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
def f_42 : Nat → Nat × Nat := unpackForestF 0x4f9499f09202d3e522f4a45d9b4a128d5a651c4a34e97031284e654164a03901696eed39dda4bba528969d12d262497449228905d1448224113ba50872a0ee57a15283b952772a304d39dca83f9507f0a0ee179ed283d95c7b2a0ee149dc28bc34e770a002d1dc9ae39250722a0e4141522b37b5c6f4a0a915551af2a35d5469ca8d35511d3212e64244c80b994903202254470c48e1509d2a13954270bc4a1509b2d2385a270b44d1501d2a03954070aa4a154142a03601686a28e1441c2794e4f28c0252d24a7249464925a92069240c009433a8bc75148e92d1d15e4227884060e8ad1d1563f03074548e80d1db4e3b68474060049d95c5e2b8a456948acaf1595a314a062540c428159562d2785a4b0b40c159522b25a024cca11c141382609c4c11804259004e2008c400b480161001d010862317846290895a110bc320f064160885a110ac2c0b044290882d1269c24d0844160083b028bc0514808a90105e020b41094020a804050020ac080f010160201c020a40407404198001f 8 11
def l_42 : Nat → Nat → Option Nat := unpackLinksF 0x898226081c204180860207f0dfc07d8df607d05f407c85dac750dd217199c607181c607105c407101c216ca1b206b0dac06911a406901a026801a00668d9a066819a0649192064818e259d1660598166059815e457815e056895a056815a056815245481501540150053854645181403500140050013a34e813a04e813434d013404d013404b8cff83f80fe03e0cf803a9cea03a04e803a00e8035a4d413484d013384ce03380c833200c803184c603180c603088acb2b00ac02a84aa02a80aa02a80aa0290ca402900a40278c9e023248c0230086321807871e007611d807601d80649188460117845c117005c0158c5601580541150054015005020eac3a00e803810e003800e003800e003230c803200c802c30b001a900b0001 0x131179b22eceb5a9c6b324d59b1a8c93469a68b40524f8a0a3939382633e12454208f0390f062ead11c1aa4da50322a010142651c17138040712e06254164ec5e9c8bb23155aa294d356916ab30d39a9a6cb13934263280e42c18c7a50822a0f014239284745c8f6b90e57214a84005c7d0a114082289047b4e8e692e8d09bda0c692e8c245160ba24111945c872a0f814209ae42a507f0b8f614209a739b42088b900541fc283c35c7d4a0f8571eca83c34e7268523179ae2ec935e6d6bb24d3a45a4b8b426e6832094a21284315e412b30854a0ca8c09507e0bc30165e8293c851770a0ead71d12839950720a0e0d71bd28311385e268b80e1581a3282065240d04b99c913302e64044c48e16c1c2a8342e478bc4a168142e2385b270b44d0111e2b12855050d9175aa2d38c566e8aadad79b1aeb5b4e6a69ad28e98d1c2314937282c24e9809caf9385d26c584c474248704159074b00e55c1c2a03603062a48e0b89c288384b4a48a92940a72094a4f28c685092c96991404b4b46c90934a71f14a4c28c585092c96a501a4903078060ec0c171242e290864f0c896210183f03078d38eda123c5e468a48a968ad212215e412b480558f8a91592d3d03474060c89219a50322a062140bc9e1712c2d03071178de291b2522b4946a578d0ad181562c2a4564b4a51c14138040704054870a51384e180944c1182c211001d080804056834a11204e15094461180c211102d21058400744c160902c0402808120681e0c82c080382c0b04da7093421e8bc3b14870ad011421b0bc301685c2b0a8521405a220b0080e840140a4a01254020280303c05058080703e2f074520d2a404528302f0585a070ac06148080ecf34f93696ecd1d4da1a714b48286724eca8999284b1f086200ec04198001f 14 5 11 8 6
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsF m_42 g_42 bds_42 (dagRefF 161 (dagTraceF m_42 s_42 7 f_42) l_42 0) s_42 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_0 : treeBlockF 0 32 (dagCheckNodeF m_42 g_42 bds_42 161 (dagTraceF m_42 s_42 7 f_42) l_42) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_1 : treeBlockF 32 64 (dagCheckNodeF m_42 g_42 bds_42 161 (dagTraceF m_42 s_42 7 f_42) l_42) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_2 : treeBlockF 64 96 (dagCheckNodeF m_42 g_42 bds_42 161 (dagTraceF m_42 s_42 7 f_42) l_42) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_3 : treeBlockF 96 128 (dagCheckNodeF m_42 g_42 bds_42 161 (dagTraceF m_42 s_42 7 f_42) l_42) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_4 : treeBlockF 128 160 (dagCheckNodeF m_42 g_42 bds_42 161 (dagTraceF m_42 s_42 7 f_42) l_42) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42_5 : treeBlockF 160 161 (dagCheckNodeF m_42 g_42 bds_42 161 (dagTraceF m_42 s_42 7 f_42) l_42) = true := by decide +kernel
theorem nj_42_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_42 g_42 bds_42 161 (dagTraceF m_42 s_42 7 f_42) l_42) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_42_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_42_1 h1 h2)
theorem nj_42_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_42 g_42 bds_42 161 (dagTraceF m_42 s_42 7 f_42) l_42) i = true := block_join nj_42_1 (fun _ h1 h2 => treeBlockF_at nb_42_2 h1 h2)
theorem nj_42_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_42 g_42 bds_42 161 (dagTraceF m_42 s_42 7 f_42) l_42) i = true := block_join nj_42_2 (fun _ h1 h2 => treeBlockF_at nb_42_3 h1 h2)
theorem nj_42_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_42 g_42 bds_42 161 (dagTraceF m_42 s_42 7 f_42) l_42) i = true := block_join nj_42_3 (fun _ h1 h2 => treeBlockF_at nb_42_4 h1 h2)
theorem nj_42_5 : ∀ i, 0 ≤ i → i < 161 → (dagCheckNodeF m_42 g_42 bds_42 161 (dagTraceF m_42 s_42 7 f_42) l_42) i = true := block_join nj_42_4 (fun _ h1 h2 => treeBlockF_at nb_42_5 h1 h2)
theorem nc_42 : ∀ i, 0 ≤ i → i < 161 → (dagCheckNodeF m_42 g_42 bds_42 161 (dagTraceF m_42 s_42 7 f_42) l_42) i = true := nj_42_5
theorem lb_42 : LowerBin m_42 s_42 g_42 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_42 sub_42 gl_42 rc_42 nc_42

def m_43 : Nat := 0xff00ff00ff00ff
def s_43 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_43 : Nat := 0x1700370037007f
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 6, g_14), (m_17, s_17, 6, g_17), (m_15, s_15, 5, g_15), (m_23, s_23, 5, g_23), (m_25, s_25, 5, g_25), (m_31, s_31, 5, g_31), (m_33, s_33, 5, g_33), (m_1, s_1, 4, g_1), (m_3, s_3, 4, g_3), (m_8, s_8, 4, g_8)]
theorem kn_43 : KnownBin bds_43 := by
  intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_14
  · exact lb_17
  · exact lb_15
  · exact lb_23
  · exact lb_25
  · exact lb_31
  · exact lb_33
  · exact lb_1
  · exact lb_3
  · exact lb_8
theorem sub_43 : ∀ b ∈ bds_43, m_43 &&& b.1 = b.1 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_43 : ∀ b ∈ bds_43, canon b.1 g_43 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_43, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_43 : Nat → Nat × Nat := unpackForestF 0xad23500b4ba6a5fa6a5daa36caa160aa060a6a57a9144a695ba6953a7844a685ba685300b4789b5f89b5da346ca3364a3354a323489b5b9fc6c9fa6c9f96c9f9609f86c9f86089b579eb5c9c4649c1389c1349c0389c03489b539a34e9a3429a25e89b4598858988548995f9526c9515495134950189595c950148995b93c6c93a6c899579295c922648995390958909548985f8d16c8d0548d0348d02c8d85c8d0248985b8bc6c8ba6c898578a85c8a1648985300a4788b5e87c5687b5600a3f7245b7245a84b6c8496084860724577cc5e7cb5e7cb5d7ca5e7c95e80c5c80a5c7c9527f05c7f0507c85e7d45c7d25c7d15c7c852724567bb4e7235a7a4587a26c7235778b4978a5e7235675b4975a5e75a5275a4575a4472256749447214b72143730447204b7204300a3770d687095c6d3476fa4d6d1466db4a6db466da466d1360094b6c25d009476b25d6735669b6c69b546725767c5a67c5667a56672350093f663570093b652355ec5a644605ea5762b5a62b565ea4d6124d611265e95a601475e84c5f2475e840009375d96c54b575c25d5c245549565aa4f5aa475495458b5a58b5658a56549365724b572475493456247548185524754814009335336c5316c4dc574da5651c5a4da464fb5d4fb454f9364d9564e45a4e4564d9460092b4c35a4c15a009274ad684a85c4734749a4d4704647b4a47b4647a46470360084b4425d44b6044b5844a6c44127008474325d3f35641b6c41b543f2573fc5a3fc563fa563f2350083f3e3570083b3d23536c5a3c46036a573ab5a3ab5636a4d399473694c38a47369403724d370263685a008373586c2cb573425d342452c85632a4f32a472c85430b5a30b5630a562c8362f24b2f2472c8342e2472c82c2d2472c824008332b36c2b06c25c572595629c5a2594627b5d27b4527836258562645a26456258460082b2235a23360233582326c221572205a008272116c1e3572025d1e1561eb5a1eb561e1360081f1d06c1a3571c25d1a0561ab5a1ab561a0360081b19357008171806c014571706c013571605c013471525d012561435a0123611a5d122481215c11926011560f35a0fa480f95c0f156011360e05c0da47011240a35d0a3450a25d0a2450a1260a0260105606c5a08a5c06c5606b5606a4d06a350104601b5a01b5601b4a0445801b4601a5601a46019560185601036008130001f 9 11
def l_43 : Nat → Nat → Option Nat := unpackLinksF 0x8501090a0f1c16482c10506090c08581010186030406080830101f37bde47b44f605ec03d807b00f411e803d007a00f401e803d007810f001df0bbe077c0ef81df03ae875c0eb81d703a457480e901cf1b9a27340e681cd039a07302e395c7038e07106e201c30b8417080e101bf1b7a26f40de81bd037a06f02db95b7036e06d06da01b30b64165b8cb01950b2a064c4c80d8c2318062c2c505852b06260c0c1818112fe25fc0bf817c1af805f00bd097a02f405e80bb8d6f42de05b82b7016e02d635ac0b581681ad005a00b4016802d0058cab181620ac405880b0856102a4f5480a9014e229c05304a6014c029805208a19541127a44f409d0d3a027404d889b0136026c04cc6980d30025e14bc0960d2c025044a009401251a4a0494091892302441488090851a3a340450c8a011402223444088810f121e043c087810c1a180430085090a0212142408405013a02040407e90fd01fa03ec47d80fb01f603dc87b80f701ea23c0a7708ee01d443a807500e621cc039047200e401c8038086d94d911b2036026b84d3219e433c0660ccc0198032086400c8019003146610cc20182130405f0cbe017442e805d00b7196e02d825b00b5096a02d405988ac39580298c5300a60146328c05180a111420284050809e193c027804e089c0136126c04d04933926024c047908f011e0234446808d011a02248448089010e2208a40088000fe11f823d107a00ec41d803a087400e421c8039007010da31b4035886b00d221a4034806710c8318c230886100ba417022b945700a641482278c4e08963128225004a0090211462204440088010841f8c3f007c10f421e803d007a00f401e803d006a80d401a8034086800d001a002e305c00b8017002e005a10b4016802d005a009500d2c01c8001 0x7b245ad235822649a24478a34822567a236539292b82980a5c7da5c7ac6cab36c8225caa960aa060a9144a7844ac25faba5da9a577c25599a458823d79a3778235a895ba81535292ba705ba68532a82b17813a4b68833649b3547723483346a43459eb44a4c6ca4364a3b54a3234a246c8335c9e350a1a6ca116ca0960a006c9f8609eb5c9e4649ac5482b6c76a449d9389d1349c8389c0349b34e9ab429a25e7623675a3497968990589885492954958149595c97a6c971549693496018950149446c93a6c921509295c9226491158909548f8688a8548d8148d85c8f96c8f0548e8348e02c8d0248c46c8ba6c8a0508a85c8a164a5b5fa535da2b5b9f3577c3559bb5399b45752369815f9495b93157919536913f6613b639375d1339005f8c85b8b057898534103f3e03b3b837350332081f1c81b190171681388b5e8845687b5683d647946477a647ac5583b55711594b059814587e45883c5885b6c7a26c8516084860811507e050809507d8507f85c7d0508145c80a5c7f05c7f85c7f0507e45c7da5c7d15c83c5e8335e82b5d8225e8195e801527e85e7c8527bb4e7ac587a26c762547934978a5e75a4477b497725e76a527624575a44749447304486c5b8645a844577c4567b35a79b5778356752567015b7414b739434a05b7284b7204315813715687095c6e1546d9346fa4d6e2456eb4a6e3466da46611467034760a464c2366f1466d13623025150116c25d5212a22827148116b25d6825569a456a36c6836469b5467a3468c5a6845667a566ab566925767235663576323d652355192a63468644606004c5f0406335a62b566195a61a4d61126601475f24764c5a63a576224d6095a5112a5f84c5e8405d96c591645c1545893456018550145ca5d592555c2455b24f5aa4759b5a5935658a5657a4b5724756247552475d3575b9565a1545813656934558185481453b6c5316c4e1645015451c5a4f95650b5d4e355503454f9364ec5a4e45652c5752256512464f1564d94645055140114cb5a4c15a44057138114b5684a85c480544783449a4d4824548b4a4834647a46370464a347369462213649046470364492513012128101201045b604535844a6c118104625d441272a02a110124325d4025541a454236c4036441b543fa3440c5a404563fa5642b56412573f2353e3573b23d3d2352982a3b4683c4603994c389403b35a3ab563785a3994738a4737a4d370263cc5a3ba573a24d3914c381403685a2902a3586c3106434054308342e02c2d02434a5d31255342453324f32a4731b5a3135630a562fa4b2f2472e2472d247353573385632054300362e8342d82c2c8242bb6c2b06c260642805429c5a2785628b5d26355283452783626c5a264562ac572a1562914627056258462395510812100100f8102436023b582326c0f01024b5a229572205a0e8122116c1e9642025d1ea551f35a1eb5620b571f9561e1361d06c1a8641c25d1aa551b35a1ab561cb571b8561a0360d810193570d0101806c080640c054078440e0140d9241706c050640b054030341605c0385406844028340f9241525d0f12602026129541435a119560a8561212412a481215c1325d119260182610154102480f95c10b5a0f1560a0560e05c0da470cb5d083550c3450ba5d052550b2450a9260a02608a5c0945a0845607b560724d03a4506a350445805b5a0535604b4a03b460325602a46021560185617c5716b5715b4714a5613a36111560e9360d124098560604601036acb4ba6347892478723f71a376c94b6b9476693f6593b5e137541334d12b4b9274684b438473e83f3d83b360372c0332502b218271d81f1981b18817008130001f 15 5 11 9 6
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsF m_43 g_43 bds_43 (dagRefF 347 (dagTraceF m_43 s_43 8 f_43) l_43 0) s_43 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_0 : treeBlockF 0 32 (dagCheckNodeF m_43 g_43 bds_43 347 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_1 : treeBlockF 32 64 (dagCheckNodeF m_43 g_43 bds_43 347 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_2 : treeBlockF 64 96 (dagCheckNodeF m_43 g_43 bds_43 347 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_3 : treeBlockF 96 128 (dagCheckNodeF m_43 g_43 bds_43 347 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_4 : treeBlockF 128 160 (dagCheckNodeF m_43 g_43 bds_43 347 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_5 : treeBlockF 160 192 (dagCheckNodeF m_43 g_43 bds_43 347 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_6 : treeBlockF 192 224 (dagCheckNodeF m_43 g_43 bds_43 347 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_7 : treeBlockF 224 256 (dagCheckNodeF m_43 g_43 bds_43 347 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_8 : treeBlockF 256 288 (dagCheckNodeF m_43 g_43 bds_43 347 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_9 : treeBlockF 288 320 (dagCheckNodeF m_43 g_43 bds_43 347 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_10 : treeBlockF 320 347 (dagCheckNodeF m_43 g_43 bds_43 347 (dagTraceF m_43 s_43 8 f_43) l_43) = true := by decide +kernel
theorem nj_43_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_43 g_43 bds_43 347 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_43_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_43_1 h1 h2)
theorem nj_43_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_43 g_43 bds_43 347 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_1 (fun _ h1 h2 => treeBlockF_at nb_43_2 h1 h2)
theorem nj_43_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_43 g_43 bds_43 347 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_2 (fun _ h1 h2 => treeBlockF_at nb_43_3 h1 h2)
theorem nj_43_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_43 g_43 bds_43 347 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_3 (fun _ h1 h2 => treeBlockF_at nb_43_4 h1 h2)
theorem nj_43_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_43 g_43 bds_43 347 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_4 (fun _ h1 h2 => treeBlockF_at nb_43_5 h1 h2)
theorem nj_43_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_43 g_43 bds_43 347 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_5 (fun _ h1 h2 => treeBlockF_at nb_43_6 h1 h2)
theorem nj_43_7 : ∀ i, 0 ≤ i → i < 256 → (dagCheckNodeF m_43 g_43 bds_43 347 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_6 (fun _ h1 h2 => treeBlockF_at nb_43_7 h1 h2)
theorem nj_43_8 : ∀ i, 0 ≤ i → i < 288 → (dagCheckNodeF m_43 g_43 bds_43 347 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_7 (fun _ h1 h2 => treeBlockF_at nb_43_8 h1 h2)
theorem nj_43_9 : ∀ i, 0 ≤ i → i < 320 → (dagCheckNodeF m_43 g_43 bds_43 347 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_8 (fun _ h1 h2 => treeBlockF_at nb_43_9 h1 h2)
theorem nj_43_10 : ∀ i, 0 ≤ i → i < 347 → (dagCheckNodeF m_43 g_43 bds_43 347 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := block_join nj_43_9 (fun _ h1 h2 => treeBlockF_at nb_43_10 h1 h2)
theorem nc_43 : ∀ i, 0 ≤ i → i < 347 → (dagCheckNodeF m_43 g_43 bds_43 347 (dagTraceF m_43 s_43 8 f_43) l_43) i = true := nj_43_10
theorem lb_43 : LowerBin m_43 s_43 g_43 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_43 sub_43 gl_43 rc_43 nc_43

def m_44 : Nat := 0xffff0000ffff0000
def s_44 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_44 : Nat := 0x1117000015370000
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_20, s_20, 5, g_20), (m_23, s_23, 5, g_23), (m_34, s_34, 5, g_34), (m_6, s_6, 4, g_6), (m_8, s_8, 4, g_8)]
theorem kn_44 : KnownBin bds_44 := by
  intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact lb_20
  · exact lb_23
  · exact lb_34
  · exact lb_6
  · exact lb_8
theorem sub_44 : ∀ b ∈ bds_44, m_44 &&& b.1 = b.1 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_44 : ∀ b ∈ bds_44, canon b.1 g_44 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_44, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_44 : Nat → Nat × Nat := unpackForestF 0xe3049c092780a4f00450169faf17b5e2eebb56d769dae8e7640a6b939d706a02d2ef1a75e349bc4bd7894af128e8349bc4a19a57334a85e15eca4b994942f0a95e151c769d7854308ae61150c20b984142f02f5e05dbc0b97a942f4a85e0520168f72d72e4a84dc56b66b96c9426e2acdb5e9b6bb36d3a6da6cda3a9b473368e26d1b55a38ab469364ea6c9ccd938a62514c4926c9b51a38a3271360ea78944f1249e0513c0926c1b4d8359b06802d0e4e2cc9c519349d2691a4c94c9826930480292e262cc4c518949d1a502342644a468b069128f6249480a4387048fad6a10a4420447d4bd024a204123ea5a7d4acfa949f49480a3b6c6a4d8979e4123625a774a0d8959cd1e3992873048d8949b11eb61296c04cda909b51d3602401466d28e1a41a3314e6628ccc4f804a5af14e5e28cbc4f97896af0165f294bc05004a1a7c5e4f8a49e9693caf2b93c570289e5693cab2a0144f2a49e4f93c0b2814a4f028024ecf62f1ec524b0487a948f4af1e95a454a08a541142e1e95641278824b1040a1e9523d27c7c090f49680933206a440d28812d10242202bc6c05080ad1a240202ac60530c0a218014202a440538b40a1014a2b260405189cae139542702840508800b10a4221474425288499100140124638d2474a80e3450109e2ed74651c0bb511709c0211c39af0735a134a01cd58411c081380e6a41c178041f8145e028b41094020a80405c028ac0c4e00a2902350020ac040f8041b8001f 8 11
def l_44 : Nat → Nat → Option Nat := unpackLinksF 0x3100c3870e0c382ef0bb06ea1b90ede3b782de0b706dc0af42ba1ae06b04a996a60a982a22a882a20a6929a0a682905a402900a30a8c0a3028c0a302844a102840a1028409f8e5179402500930a4c0930248292024809202480901240090023848e023808c123008c023008c022848a02280888e220888222088821a486821a0796de407901e217881e207805dc270b5c207081c207081c206f0dbc06e85ba068b1a2067899e067819836601980648d92064819205fa97a25e817a05e057805d857605d817605c0d6e15b816c15b016c05a0952b5481520530d4c0530138a4e013614d813414c853204b8918b460118045091214481120430d0c043010a1428108142010423ab4ea03a80ea03988e603980e603980e60380ce003800e00368cda03680d813030bc22e84b812d08b402d00b212c80b012c00b002c00aa32a80aa02a04a802984a602980a60280ca002800a002800a0026107ce1f007c01e086a71a806a01988660161c5801600580150854015004e313043e70f803e00f803e00f803830e003420d003210c8024700c4001 0xe3049b717ace2eef35add6b3aad5acda8eab46dc68bc4925f920f094953282b84e534988604de008b74d12ddaa3ba50462a010171d51c2113804069b20537a2f6ec5dd48ab6314b71ab6a355db69d62d36652cc8a51da472f08c7609ca41311407bae0d71ca868250778b99c5732ca86285cd08b99a57328a86205cbe0a1a0d26d9a0a345cce2b99a5430c2e63b5ccb4b994943082e5e850c769d72d0b14ae62150c30b984142f9285e950080b9a917aca2eeab5eb46bbaad3b51a4dc342b5683a697a012ce9252d14a39e94330af2b159c92a59054718a86085ec00bb7e1701c2ade052ba6b972542ddae5b250ac2714e4d2901c5083475479564a2989250024ac471568d28c1c4f834424794e4a298924f024a4471464e0101a50928a02493e0a2781259c5db18b57115ad62ada35eb36bb64d3ac5a6cc259904a3608eabd1cd7238ad46ce48c56ca4a6141aa275524e6a09c52936402621e0f6881d4e8369c06b360d1d51c4593c8b4850e8ea662ccc4518a6a50cd2a5d274024a9648cf090a291eca929352432809a4c123ba408e2811a1322c1a48c59908a314d69eda147a4e7e49518919c9214523d3b263124a4bc90baa3487048ea92214a44204477479044a204124335a716850697a012d3fa567e4a4e28f4e898be9292c242ee8d1b8123c824774a0ea8f1d094398246d048da4f1b92136a3a7b6a4e2d29e92f3c25a764ace4949c51eb812926242de099b0123523842270d20d185292d24a39464d053958a53394648284cc4f8d4993092d46280be0517c162f94a4b264c296929213214e53294c651900a13113e2f264c24b5800b2f01442248a009108a42c13c46258ae051500a1f02c502947c4c9722f2dc525a4b47a90964af2b15a552aca6549489f161323d25aa20593c0a231244b0488e94118a82285c43278844b1040a1f0244d8bc9914929291ea4a384649257920ad22156402a47e4f898991e92d342a8480508c0a110142b28842050d80a1a2403229862510c00a168142b26052570a0aa1381424484468e888a5109323b6a474d28e52d1c242372bc6a568ccab179522e29c58528a8a3131422502c4005074a80405c0c69a3cd2471a287b41170ac2e118381f0ca380406834d7451ac83b55186a22e1785c2701836134a010170451c08138040681091055af0a35a126ac1ed48382f010460206c1494024a80405c06270080d011a80645e0b8b40f1581629018560209c040fb7da7eb34bbb68f34d0e4925c42437c476d68cd94a5ae9434e276784cc7c918d84f1608e1a0fc041b8001f 14 5 11 8 6
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsF m_44 g_44 bds_44 (dagRefF 228 (dagTraceF m_44 s_44 7 f_44) l_44 0) s_44 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_0 : treeBlockF 0 32 (dagCheckNodeF m_44 g_44 bds_44 228 (dagTraceF m_44 s_44 7 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_1 : treeBlockF 32 64 (dagCheckNodeF m_44 g_44 bds_44 228 (dagTraceF m_44 s_44 7 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_2 : treeBlockF 64 96 (dagCheckNodeF m_44 g_44 bds_44 228 (dagTraceF m_44 s_44 7 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_3 : treeBlockF 96 128 (dagCheckNodeF m_44 g_44 bds_44 228 (dagTraceF m_44 s_44 7 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_4 : treeBlockF 128 160 (dagCheckNodeF m_44 g_44 bds_44 228 (dagTraceF m_44 s_44 7 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_5 : treeBlockF 160 192 (dagCheckNodeF m_44 g_44 bds_44 228 (dagTraceF m_44 s_44 7 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_6 : treeBlockF 192 224 (dagCheckNodeF m_44 g_44 bds_44 228 (dagTraceF m_44 s_44 7 f_44) l_44) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_7 : treeBlockF 224 228 (dagCheckNodeF m_44 g_44 bds_44 228 (dagTraceF m_44 s_44 7 f_44) l_44) = true := by decide +kernel
theorem nj_44_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_44 g_44 bds_44 228 (dagTraceF m_44 s_44 7 f_44) l_44) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_44_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_44_1 h1 h2)
theorem nj_44_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_44 g_44 bds_44 228 (dagTraceF m_44 s_44 7 f_44) l_44) i = true := block_join nj_44_1 (fun _ h1 h2 => treeBlockF_at nb_44_2 h1 h2)
theorem nj_44_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_44 g_44 bds_44 228 (dagTraceF m_44 s_44 7 f_44) l_44) i = true := block_join nj_44_2 (fun _ h1 h2 => treeBlockF_at nb_44_3 h1 h2)
theorem nj_44_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_44 g_44 bds_44 228 (dagTraceF m_44 s_44 7 f_44) l_44) i = true := block_join nj_44_3 (fun _ h1 h2 => treeBlockF_at nb_44_4 h1 h2)
theorem nj_44_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_44 g_44 bds_44 228 (dagTraceF m_44 s_44 7 f_44) l_44) i = true := block_join nj_44_4 (fun _ h1 h2 => treeBlockF_at nb_44_5 h1 h2)
theorem nj_44_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_44 g_44 bds_44 228 (dagTraceF m_44 s_44 7 f_44) l_44) i = true := block_join nj_44_5 (fun _ h1 h2 => treeBlockF_at nb_44_6 h1 h2)
theorem nj_44_7 : ∀ i, 0 ≤ i → i < 228 → (dagCheckNodeF m_44 g_44 bds_44 228 (dagTraceF m_44 s_44 7 f_44) l_44) i = true := block_join nj_44_6 (fun _ h1 h2 => treeBlockF_at nb_44_7 h1 h2)
theorem nc_44 : ∀ i, 0 ≤ i → i < 228 → (dagCheckNodeF m_44 g_44 bds_44 228 (dagTraceF m_44 s_44 7 f_44) l_44) i = true := nj_44_7
theorem lb_44 : LowerBin m_44 s_44 g_44 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_44 sub_44 gl_44 rc_44 nc_44

def m_45 : Nat := 0xffff0000ffff
def s_45 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_45 : Nat := 0x15370000177f
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_35, s_35, 7, g_35), (m_18, s_18, 5, g_18), (m_19, s_19, 5, g_19), (m_21, s_21, 5, g_21), (m_22, s_22, 5, g_22), (m_24, s_24, 5, g_24), (m_25, s_25, 5, g_25), (m_0, s_0, 4, g_0), (m_1, s_1, 4, g_1), (m_4, s_4, 4, g_4)]
theorem kn_45 : KnownBin bds_45 := by
  intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_35
  · exact lb_18
  · exact lb_19
  · exact lb_21
  · exact lb_22
  · exact lb_24
  · exact lb_25
  · exact lb_0
  · exact lb_1
  · exact lb_4
theorem sub_45 : ∀ b ∈ bds_45, m_45 &&& b.1 = b.1 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_45 : ∀ b ∈ bds_45, canon b.1 g_45 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_45, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_45 : Nat → Nat × Nat := unpackForestF 0x5a7e6356016978e96f1d29e395bc72a602d1f051c60a34c1271824d3041c00b43bf68a0293c0525d5b5dac07f580eee0a65c140ac06f6a0b2d41256033ac03f5806eb00bd6924ad0995c052b42256013ab0a00291e79264f246a227f444ee942051137a3031444ce79224f1289e2493c0a00521ce0380147f2d15e64284b3569768b2c958051d80a37934ac028ce44240094f8b8af1c4d22da5c63568b28c0252c04a3c414601286f8d5a15aa3e25f7c4b702db204303e2577d4a8fa911f4143e2530127ee6d7dcdadbbc6c770c0e6d5dd1aa3a038736a6024ed1e2d38458474bedd5a11d2db54606b098d41811d2bb2568644b8ccd61912232028474a68e5692127a424b5e0b8bc1412123ad2445a050b40912121a414a4809e9012d512e2a2504808ea20f1441a240434805e900ad2013a4934490b894091242a2402347080024dd14aa09b5f136b67f1b0fcb6200143f0c026d5cedaa1d9343b07026d4c4cae19a4d334926c140cd229a0283348226558a9279524b2e6b85c140a92395a442b0505490c4caa0993c132682893c51259185c230a02891c7d220f8281f0482890c50278a04b1a4b83494050238a0431405e280ac50138a02313030024cc452b0092f0f28c024ac3418009270b2d80515c21ae84345022ac07168142801c56036ac0451804918001f 8 11
def l_45 : Nat → Nat → Option Nat := unpackLinksF 0x242190824018f863e08f063c08b9e2e08b822e08b822e089162408696124838a0e083820e083820a282820a0818a0608182041808602080820017e8de0d749dd207291ca07281ca07189c607089ba46e81ba06c919ea67819c166859a0660598065858e463818e063058c06285881620186161818415f117c05f017a15e817a05e057805e017805d097405d017405b8d64559016405901640580960058015c2551150254014c25301482518546050893c34e853814e013424c85285498526049812604981222488122048811c347011c047011c04701182460118045091404501121440510044010e1420ceed381ce00368cd623504d213480cc33094be22f04b822b94ae02b80ae02b80aa22a80a6227909e027809e027809a226809a025888e423808e023808e023808e022888a022808a0210c8402100840210080220008002000800200068c15285401484520140450013844e01190460118040310004000f843e00e0c32300e0001 0x331a2e6356974a918513292de4a539a4779056f1ca9c794b0a2478a8e3111a61938c2269820e2fda2c213f7a276de4dd1099c194f79296da51d0ca1bc1394226372532e0a05b02cb504960042b81a57014b02495e132b4224ca3a8127eee4eda89b9f933bb07f740eedc1bda033b303f6406ec40bd6013bc6bb308ea009fbb13b6926e7c4ceac283f93d75272ca4d4f498b3458a5080585528c0c5393fa6277484de8899be93f74276c84dcec99d4a4ca848d42911f0a7b994b6328e7450e80944f9249e051380e25d2a4c8509768b3515e61ab4b2568d2b72695a4424461448e26918d5a3e2bc6b4b6248d1651a20a342b54826d902181fd2a3f2447d0510cd5a112fc1a5b804aef894de2363b860756a8e80e1e9afbcb5b766aee6d4db92cb4251708b0c2101bab4300505e060d61317820364606a0c0ba101992a2d830666b0b80c16c2034568674b8ca91164283202858080be17178282e2445b050b4091552e2a25052078a20d13010250444a048984d12c2e248546149ec092d7523aca4358294ae13d5825a9847500869e0bd3815a682748046e3169bd2fb6a5b694aec694d88ad23840382c88a550980c1b964250305e5508c281b15423030800510a362096c352a87e180880c1615421030400a0d0aa100183d6a866590f09a1d8381e0305ed70d828162443405070934dd249aa45334825ed70b828162442b0506293cc12596a472a486481708c2810a44200503e0906d2e0d2502649e4a92c89238f2431d09e3812c64238c0431705e2c0ac54138a023446be86d6cf9ab9d353392b864558a4aa1413c2726826060452b079460d060165b010b2041540328812d7411aa84345050a00d168122b01b560a8ae0e55808a366b4fcb6978cd1f01a1df24fbd4975491e7521cda3f95477288de4919c814f8a2971251e1ca1bd93f722768c4dc48998812f0e2561849c04918001f 14 5 11 8 6
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsF m_45 g_45 bds_45 (dagRefF 206 (dagTraceF m_45 s_45 8 f_45) l_45 0) s_45 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_0 : treeBlockF 0 32 (dagCheckNodeF m_45 g_45 bds_45 206 (dagTraceF m_45 s_45 8 f_45) l_45) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_1 : treeBlockF 32 64 (dagCheckNodeF m_45 g_45 bds_45 206 (dagTraceF m_45 s_45 8 f_45) l_45) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_2 : treeBlockF 64 96 (dagCheckNodeF m_45 g_45 bds_45 206 (dagTraceF m_45 s_45 8 f_45) l_45) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_3 : treeBlockF 96 128 (dagCheckNodeF m_45 g_45 bds_45 206 (dagTraceF m_45 s_45 8 f_45) l_45) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_4 : treeBlockF 128 160 (dagCheckNodeF m_45 g_45 bds_45 206 (dagTraceF m_45 s_45 8 f_45) l_45) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_5 : treeBlockF 160 192 (dagCheckNodeF m_45 g_45 bds_45 206 (dagTraceF m_45 s_45 8 f_45) l_45) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45_6 : treeBlockF 192 206 (dagCheckNodeF m_45 g_45 bds_45 206 (dagTraceF m_45 s_45 8 f_45) l_45) = true := by decide +kernel
theorem nj_45_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_45 g_45 bds_45 206 (dagTraceF m_45 s_45 8 f_45) l_45) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_45_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_45_1 h1 h2)
theorem nj_45_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_45 g_45 bds_45 206 (dagTraceF m_45 s_45 8 f_45) l_45) i = true := block_join nj_45_1 (fun _ h1 h2 => treeBlockF_at nb_45_2 h1 h2)
theorem nj_45_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_45 g_45 bds_45 206 (dagTraceF m_45 s_45 8 f_45) l_45) i = true := block_join nj_45_2 (fun _ h1 h2 => treeBlockF_at nb_45_3 h1 h2)
theorem nj_45_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_45 g_45 bds_45 206 (dagTraceF m_45 s_45 8 f_45) l_45) i = true := block_join nj_45_3 (fun _ h1 h2 => treeBlockF_at nb_45_4 h1 h2)
theorem nj_45_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_45 g_45 bds_45 206 (dagTraceF m_45 s_45 8 f_45) l_45) i = true := block_join nj_45_4 (fun _ h1 h2 => treeBlockF_at nb_45_5 h1 h2)
theorem nj_45_6 : ∀ i, 0 ≤ i → i < 206 → (dagCheckNodeF m_45 g_45 bds_45 206 (dagTraceF m_45 s_45 8 f_45) l_45) i = true := block_join nj_45_5 (fun _ h1 h2 => treeBlockF_at nb_45_6 h1 h2)
theorem nc_45 : ∀ i, 0 ≤ i → i < 206 → (dagCheckNodeF m_45 g_45 bds_45 206 (dagTraceF m_45 s_45 8 f_45) l_45) i = true := nj_45_6
theorem lb_45 : LowerBin m_45 s_45 g_45 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_45 sub_45 gl_45 rc_45 nc_45

def m_46 : Nat := 0xffffffff00000000
def s_46 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_46 : Nat := 0x1117153700000000
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_28, s_28, 5, g_28), (m_31, s_31, 5, g_31), (m_34, s_34, 5, g_34), (m_6, s_6, 4, g_6), (m_8, s_8, 4, g_8)]
theorem kn_46 : KnownBin bds_46 := by
  intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact lb_28
  · exact lb_31
  · exact lb_34
  · exact lb_6
  · exact lb_8
theorem sub_46 : ∀ b ∈ bds_46, m_46 &&& b.1 = b.1 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_46 : ∀ b ∈ bds_46, canon b.1 g_46 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_46, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_46 : Nat → Nat × Nat := unpackForestF 0xe3049c092780a4f00450169faf17b5e2eebb56d769dae8e7640a6b939d706a02d2ef1a75e349bc4bd7894af128e8349bc4a19a57334a85e15eca4b994942f0a95e151c769d7854308ae61150c20b984142f02f5e05dbc0b97a942f4a85e0520168f72d72e4a84dc56b66b96c9426e2acdb5e9b6bb36d3a6da6cda3a9b473368e26d1b55a38ab469364ea6c9ccd938a62514c4926c9b51a38a3271360ea78944f1249e0513c0926c1b4d8359b06802d0e4e2cc9c519349d2691a4c94c9826930480292e262cc4c518949d1a502342644a468b069128f6249480a4387048fad6a10a4420447d4bd024a204123ea5a7d4acfa949f49480a3b6c6a4d8979e4123625a774a0d8959cd1e3992873048d8949b11eb61296c04cda909b51d3602401466d28e1a41a3314e6628ccc4f804a5af14e5e28cbc4f97896af0165f294bc05004a1a7c5e4f8a49e9693caf2b93c570289e5693cab2a0144f2a49e4f93c0b2814a4f028024ecf62f1ec524b0487a948f4af1e95a454a08a541142e1e95641278824b1040a1e9523d27c7c090f49680933206a440d28812d10242202bc6c05080ad1a240202ac60530c0a218014202a440538b40a1014a2b260405189cae139542702840508800b10a4221474425288499100140124638d2474a80e3450109e2ed74651c0bb511709c0211c39af0735a134a01cd58411c081380e6a41c178041f8145e028b41094020a80405c028ac0c4e00a2902350020ac040f8041b8001f 8 11
def l_46 : Nat → Nat → Option Nat := unpackLinksF 0x3100c3870e0c382ef0bb06ea1b90ede3b782de0b706dc0af42ba1ae06b04a996a60a982a22a882a20a6929a0a682905a402900a30a8c0a3028c0a302844a102840a1028409f8e5179402500930a4c0930248292024809202480901240090023848e023808c123008c023008c022848a02280888e220888222088821a486821a0796de407901e217881e207805dc270b5c207081c207081c206f0dbc06e85ba068b1a2067899e067819836601980648d92064819205fa97a25e817a05e057805d857605d817605c0d6e15b816c15b016c05a0952b5481520530d4c0530138a4e013614d813414c853204b8918b460118045091214481120430d0c043010a1428108142010423ab4ea03a80ea03988e603980e603980e60380ce003800e00368cda03680d813030bc22e84b812d08b402d00b212c80b012c00b002c00aa32a80aa02a04a802984a602980a60280ca002800a002800a0026107ce1f007c01e086a71a806a01988660161c5801600580150854015004e313043e70f803e00f803e00f803830e003420d003210c8024700c4001 0xe3049b717ace2eef35add6b3aad5acda8eab46dc68bc4925f920f094953282b84e534988604de008b74d12ddaa3ba50462a010171d51c2113804069b20537a2f6ec5dd48ab6314b71ab6a355db69d62d36652cc8a51da472f08c7609ca41311407bae0d71ca868250778b99c5732ca86285cd08b99a57328a86205cbe0a1a0d26d9a0a345cce2b99a5430c2e63b5ccb4b994943082e5e850c769d72d0b14ae62150c30b984142f9285e950080b9a917aca2eeab5eb46bbaad3b51a4dc342b5683a697a012ce9252d14a39e94330af2b159c92a59054718a86085ec00bb7e1701c2ade052ba6b972542ddae5b250ac2714e4d2901c5083475479564a2989250024ac471568d28c1c4f834424794e4a298924f024a4471464e0101a50928a02493e0a2781259c5db18b57115ad62ada35eb36bb64d3ac5a6cc259904a3608eabd1cd7238ad46ce48c56ca4a6141aa275524e6a09c52936402621e0f6881d4e8369c06b360d1d51c4593c8b4850e8ea662ccc4518a6a50cd2a5d274024a9648cf090a291eca929352432809a4c123ba408e2811a1322c1a48c59908a314d69eda147a4e7e49518919c9214523d3b263124a4bc90baa3487048ea92214a44204477479044a204124335a716850697a012d3fa567e4a4e28f4e898be9292c242ee8d1b8123c824774a0ea8f1d094398246d048da4f1b92136a3a7b6a4e2d29e92f3c25a764ace4949c51eb812926242de099b0123523842270d20d185292d24a39464d053958a53394648284cc4f8d4993092d46280be0517c162f94a4b264c296929213214e53294c651900a13113e2f264c24b5800b2f01442248a009108a42c13c46258ae051500a1f02c502947c4c9722f2dc525a4b47a90964af2b15a552aca6549489f161323d25aa20593c0a231244b0488e94118a82285c43278844b1040a1f0244d8bc9914929291ea4a384649257920ad22156402a47e4f898991e92d342a8480508c0a110142b28842050d80a1a2403229862510c00a168142b26052570a0aa1381424484468e888a5109323b6a474d28e52d1c242372bc6a568ccab179522e29c58528a8a3131422502c4005074a80405c0c69a3cd2471a287b41170ac2e118381f0ca380406834d7451ac83b55186a22e1785c2701836134a010170451c08138040681091055af0a35a126ac1ed48382f010460206c1494024a80405c06270080d011a80645e0b8b40f1581629018560209c040fb7da7eb34bbb68f34d0e4925c42437c476d68cd94a5ae9434e276784cc7c918d84f1608e1a0fc041b8001f 14 5 11 8 6
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsF m_46 g_46 bds_46 (dagRefF 228 (dagTraceF m_46 s_46 7 f_46) l_46 0) s_46 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_0 : treeBlockF 0 32 (dagCheckNodeF m_46 g_46 bds_46 228 (dagTraceF m_46 s_46 7 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_1 : treeBlockF 32 64 (dagCheckNodeF m_46 g_46 bds_46 228 (dagTraceF m_46 s_46 7 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_2 : treeBlockF 64 96 (dagCheckNodeF m_46 g_46 bds_46 228 (dagTraceF m_46 s_46 7 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_3 : treeBlockF 96 128 (dagCheckNodeF m_46 g_46 bds_46 228 (dagTraceF m_46 s_46 7 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_4 : treeBlockF 128 160 (dagCheckNodeF m_46 g_46 bds_46 228 (dagTraceF m_46 s_46 7 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_5 : treeBlockF 160 192 (dagCheckNodeF m_46 g_46 bds_46 228 (dagTraceF m_46 s_46 7 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_6 : treeBlockF 192 224 (dagCheckNodeF m_46 g_46 bds_46 228 (dagTraceF m_46 s_46 7 f_46) l_46) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_7 : treeBlockF 224 228 (dagCheckNodeF m_46 g_46 bds_46 228 (dagTraceF m_46 s_46 7 f_46) l_46) = true := by decide +kernel
theorem nj_46_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_46 g_46 bds_46 228 (dagTraceF m_46 s_46 7 f_46) l_46) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_46_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_46_1 h1 h2)
theorem nj_46_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_46 g_46 bds_46 228 (dagTraceF m_46 s_46 7 f_46) l_46) i = true := block_join nj_46_1 (fun _ h1 h2 => treeBlockF_at nb_46_2 h1 h2)
theorem nj_46_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_46 g_46 bds_46 228 (dagTraceF m_46 s_46 7 f_46) l_46) i = true := block_join nj_46_2 (fun _ h1 h2 => treeBlockF_at nb_46_3 h1 h2)
theorem nj_46_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_46 g_46 bds_46 228 (dagTraceF m_46 s_46 7 f_46) l_46) i = true := block_join nj_46_3 (fun _ h1 h2 => treeBlockF_at nb_46_4 h1 h2)
theorem nj_46_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_46 g_46 bds_46 228 (dagTraceF m_46 s_46 7 f_46) l_46) i = true := block_join nj_46_4 (fun _ h1 h2 => treeBlockF_at nb_46_5 h1 h2)
theorem nj_46_6 : ∀ i, 0 ≤ i → i < 224 → (dagCheckNodeF m_46 g_46 bds_46 228 (dagTraceF m_46 s_46 7 f_46) l_46) i = true := block_join nj_46_5 (fun _ h1 h2 => treeBlockF_at nb_46_6 h1 h2)
theorem nj_46_7 : ∀ i, 0 ≤ i → i < 228 → (dagCheckNodeF m_46 g_46 bds_46 228 (dagTraceF m_46 s_46 7 f_46) l_46) i = true := block_join nj_46_6 (fun _ h1 h2 => treeBlockF_at nb_46_7 h1 h2)
theorem nc_46 : ∀ i, 0 ≤ i → i < 228 → (dagCheckNodeF m_46 g_46 bds_46 228 (dagTraceF m_46 s_46 7 f_46) l_46) i = true := nj_46_7
theorem lb_46 : LowerBin m_46 s_46 g_46 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_46 sub_46 gl_46 rc_46 nc_46

def m_47 : Nat := 0xffffffff
def s_47 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_47 : Nat := 0x1537177f
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_35, s_35, 7, g_35), (m_26, s_26, 5, g_26), (m_27, s_27, 5, g_27), (m_29, s_29, 5, g_29), (m_30, s_30, 5, g_30), (m_32, s_32, 5, g_32), (m_33, s_33, 5, g_33), (m_2, s_2, 4, g_2), (m_3, s_3, 4, g_3), (m_4, s_4, 4, g_4)]
theorem kn_47 : KnownBin bds_47 := by
  intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_35
  · exact lb_26
  · exact lb_27
  · exact lb_29
  · exact lb_30
  · exact lb_32
  · exact lb_33
  · exact lb_2
  · exact lb_3
  · exact lb_4
theorem sub_47 : ∀ b ∈ bds_47, m_47 &&& b.1 = b.1 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_47 : ∀ b ∈ bds_47, canon b.1 g_47 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_47, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_47 : Nat → Nat × Nat := unpackForestF 0x5a7e6356016978e96f1d29e395bc72a602d1f051c60a34c1271824d3041c00b43bf68a0293c0525d5b5dac07f580eee0a65c140ac06f6a0b2d41256033ac03f5806eb00bd6924ad0995c052b42256013ab0a00291e79264f246a227f444ee942051137a3031444ce79224f1289e2493c0a00521ce0380147f2d15e64284b3569768b2c958051d80a37934ac028ce44240094f8b8af1c4d22da5c63568b28c0252c04a3c414601286f8d5a15aa3e25f7c4b702db204303e2577d4a8fa911f4143e2530127ee6d7dcdadbbc6c770c0e6d5dd1aa3a038736a6024ed1e2d38458474bedd5a11d2db54606b098d41811d2bb2568644b8ccd61912232028474a68e5692127a424b5e0b8bc1412123ad2445a050b40912121a414a4809e9012d512e2a2504808ea20f1441a240434805e900ad2013a4934490b894091242a2402347080024dd14aa09b5f136b67f1b0fcb6200143f0c026d5cedaa1d9343b07026d4c4cae19a4d334926c140cd229a0283348226558a9279524b2e6b85c140a92395a442b0505490c4caa0993c132682893c51259185c230a02891c7d220f8281f0482890c50278a04b1a4b83494050238a0431405e280ac50138a02313030024cc452b0092f0f28c024ac3418009270b2d80515c21ae84345022ac07168142801c56036ac0451804918001f 8 11
def l_47 : Nat → Nat → Option Nat := unpackLinksF 0x242190824018f863e08f063c08b9e2e08b822e08b822e089162408696124838a0e083820e083820a282820a0818a0608182041808602080820017e8de0d749dd207291ca07281ca07189c607089ba46e81ba06c919ea67819c166859a0660598065858e463818e063058c06285881620186161818415f117c05f017a15e817a05e057805e017805d097405d017405b8d64559016405901640580960058015c2551150254014c25301482518546050893c34e853814e013424c85285498526049812604981222488122048811c347011c047011c04701182460118045091404501121440510044010e1420ceed381ce00368cd623504d213480cc33094be22f04b822b94ae02b80ae02b80aa22a80a6227909e027809e027809a226809a025888e423808e023808e023808e022888a022808a0210c8402100840210080220008002000800200068c15285401484520140450013844e01190460118040310004000f843e00e0c32300e0001 0x331a2e6356974a918513292de4a539a4779056f1ca9c794b0a2478a8e3111a61938c2269820e2fda2c213f7a276de4dd1099c194f79296da51d0ca1bc1394226372532e0a05b02cb504960042b81a57014b02495e132b4224ca3a8127eee4eda89b9f933bb07f740eedc1bda033b303f6406ec40bd6013bc6bb308ea009fbb13b6926e7c4ceac283f93d75272ca4d4f498b3458a5080585528c0c5393fa6277484de8899be93f74276c84dcec99d4a4ca848d42911f0a7b994b6328e7450e80944f9249e051380e25d2a4c8509768b3515e61ab4b2568d2b72695a4424461448e26918d5a3e2bc6b4b6248d1651a20a342b54826d902181fd2a3f2447d0510cd5a112fc1a5b804aef894de2363b860756a8e80e1e9afbcb5b766aee6d4db92cb4251708b0c2101bab4300505e060d61317820364606a0c0ba101992a2d830666b0b80c16c2034568674b8ca91164283202858080be17178282e2445b050b4091552e2a25052078a20d13010250444a048984d12c2e248546149ec092d7523aca4358294ae13d5825a9847500869e0bd3815a682748046e3169bd2fb6a5b694aec694d88ad23840382c88a550980c1b964250305e5508c281b15423030800510a362096c352a87e180880c1615421030400a0d0aa100183d6a866590f09a1d8381e0305ed70d828162443405070934dd249aa45334825ed70b828162442b0506293cc12596a472a486481708c2810a44200503e0906d2e0d2502649e4a92c89238f2431d09e3812c64238c0431705e2c0ac54138a023446be86d6cf9ab9d353392b864558a4aa1413c2726826060452b079460d060165b010b2041540328812d7411aa84345050a00d168122b01b560a8ae0e55808a366b4fcb6978cd1f01a1df24fbd4975491e7521cda3f95477288de4919c814f8a2971251e1ca1bd93f722768c4dc48998812f0e2561849c04918001f 14 5 11 8 6
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsF m_47 g_47 bds_47 (dagRefF 206 (dagTraceF m_47 s_47 8 f_47) l_47 0) s_47 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_0 : treeBlockF 0 32 (dagCheckNodeF m_47 g_47 bds_47 206 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_1 : treeBlockF 32 64 (dagCheckNodeF m_47 g_47 bds_47 206 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_2 : treeBlockF 64 96 (dagCheckNodeF m_47 g_47 bds_47 206 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_3 : treeBlockF 96 128 (dagCheckNodeF m_47 g_47 bds_47 206 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_4 : treeBlockF 128 160 (dagCheckNodeF m_47 g_47 bds_47 206 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_5 : treeBlockF 160 192 (dagCheckNodeF m_47 g_47 bds_47 206 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_6 : treeBlockF 192 206 (dagCheckNodeF m_47 g_47 bds_47 206 (dagTraceF m_47 s_47 8 f_47) l_47) = true := by decide +kernel
theorem nj_47_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF m_47 g_47 bds_47 206 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_47_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_47_1 h1 h2)
theorem nj_47_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF m_47 g_47 bds_47 206 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_1 (fun _ h1 h2 => treeBlockF_at nb_47_2 h1 h2)
theorem nj_47_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF m_47 g_47 bds_47 206 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_2 (fun _ h1 h2 => treeBlockF_at nb_47_3 h1 h2)
theorem nj_47_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF m_47 g_47 bds_47 206 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_3 (fun _ h1 h2 => treeBlockF_at nb_47_4 h1 h2)
theorem nj_47_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF m_47 g_47 bds_47 206 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_4 (fun _ h1 h2 => treeBlockF_at nb_47_5 h1 h2)
theorem nj_47_6 : ∀ i, 0 ≤ i → i < 206 → (dagCheckNodeF m_47 g_47 bds_47 206 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := block_join nj_47_5 (fun _ h1 h2 => treeBlockF_at nb_47_6 h1 h2)
theorem nc_47 : ∀ i, 0 ≤ i → i < 206 → (dagCheckNodeF m_47 g_47 bds_47 206 (dagTraceF m_47 s_47 8 f_47) l_47) i = true := nj_47_6
theorem lb_47 : LowerBin m_47 s_47 g_47 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_47 sub_47 gl_47 rc_47 nc_47

def g_48 : Nat := 0x111715371537177f
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_47, s_47, 9, g_47), (m_45, s_45, 9, g_45), (m_43, s_43, 9, g_43), (m_41, s_41, 9, g_41), (m_38, s_38, 9, g_38), (m_36, s_36, 9, g_36), (m_46, s_46, 8, g_46), (m_44, s_44, 8, g_44), (m_42, s_42, 8, g_42), (m_40, s_40, 8, g_40), (m_39, s_39, 7, g_39), (m_37, s_37, 7, g_37), (m_35, s_35, 7, g_35), (m_10, s_10, 6, g_10), (m_11, s_11, 6, g_11), (m_13, s_13, 6, g_13), (m_14, s_14, 6, g_14), (m_12, s_12, 5, g_12), (m_22, s_22, 5, g_22), (m_19, s_19, 5, g_19), (m_25, s_25, 5, g_25), (m_26, s_26, 5, g_26), (m_27, s_27, 5, g_27), (m_30, s_30, 5, g_30), (m_33, s_33, 5, g_33), (m_34, s_34, 5, g_34), (m_18, s_18, 5, g_18), (m_8, s_8, 4, g_8), (m_6, s_6, 4, g_6), (m_3, s_3, 4, g_3), (m_2, s_2, 4, g_2), (m_1, s_1, 4, g_1), (m_0, s_0, 4, g_0)]
theorem kn_48 : KnownBin bds_48 := by
  intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_47
  · exact lb_45
  · exact lb_43
  · exact lb_41
  · exact lb_38
  · exact lb_36
  · exact lb_46
  · exact lb_44
  · exact lb_42
  · exact lb_40
  · exact lb_39
  · exact lb_37
  · exact lb_35
  · exact lb_10
  · exact lb_11
  · exact lb_13
  · exact lb_14
  · exact lb_12
  · exact lb_22
  · exact lb_19
  · exact lb_25
  · exact lb_26
  · exact lb_27
  · exact lb_30
  · exact lb_33
  · exact lb_34
  · exact lb_18
  · exact lb_8
  · exact lb_6
  · exact lb_3
  · exact lb_2
  · exact lb_1
  · exact lb_0
theorem sub_48 : ∀ b ∈ bds_48, fullMask &&& b.1 = b.1 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_48 : ∀ b ∈ bds_48, canon b.1 g_48 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by intro b hb; simp only [bds_48, List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def f_48 : Nat → Nat × Nat := unpackForestF 0x174d8f0638dd263be8e37cdc6e8b1ddc71bb6e37418c062bdc356016b76cd9805a5d9c5bb34ac0296ec52257c6baf4cc0292e893f5496ba92c7521aea431d127ca67194c4d288b9d1b8ca3069441ce7eb3cfa669f4ac028ce5e2dce134976b7344d25da1cc233972ac0256e54a247c6b8f6d7244d23da1c82338f2cc0252e21b9c6271882fd105f225464407380acf0cd9a01b5c1b768326900d6e00b34015601266f31cdf5b8bc97e792f8f4a31e439b8d67768ccec511c635ba476718b6e2599c4ab00923618b6dc0d185adb603461686d4091852db402461486cc0918519b123362266c448d842b0085b5f088a31ad45b5ae03451686b40914535ac02451486ac0914519a923352266a448d44330084b4a6e6949cd3138a61714a0fc941f0ceb3a4366336d68add9141a19b5b424cc84090cd359fa763f0486696cf1461e08c38cee709d8e1331c024334666c48ccc331a123330ac020ccb239962732e6e25c5c4b03f1607c15ace53198a4220ac6b278ec2b16c913312024154d6429d884120aa5b1e5183c2306b3b8d2761a4cc3409055218c133150cc2c4cc542b00823128e624dcc0ab388466028d61d1d80a2d85d6b0b6cc04dac22bd84376026b60ce300f3b81b76036cc04d0c04098003f 8 11
def l_48 : Nat → Nat → Option Nat := unpackLinksF 0x9b34d8260d3009804ad65612b0932c72a327127879c21e0e30437ebbf41f64f8378bbbc9de0ef07783bc1d4aea07503a09d00e807313855c02df16bc35c1ae0d616b03509a80d13653b281922c9064831c98e0c435ebaf05780ba25c8ae41702b355982c85640b205812bc55c2a68528a941464a21510284538a9c04e026893409914c0a5c51f08f047823851c08c246022c516089244821c90e0870438210cfae7d03e09f00f807a23d01e44f207723b81d48ea07503a81c8cd6e6a13489a40d206723309854c206013001800bc45e02f01708b805c02d11680b405822c01600b005262901444a2050124411c48c246023011088623e51f00f807843c01d88ec07603921c80e406e43701b80d486a03501a80bd85e02e11700b444b0250128088c44020210007883c01e00e107003801a20d006443201900b1841803e001 0xc14e37e5c5f891de071310462604f0638df1718d287761c53c2189013bf8e37cdc695a1a704330067791c6edb8d134388486f28cf09b1e0263a14677a58e1c99bc123ba0c6920ccac1188813772465408c4009dc356b04b72856dd491af05b280461e04dd091938230e0276cd9ad135ce96b73246de1ac9811868130c0270c4cd201985813b48b76695a4cadc29435d0b68e10c2809d8a4409027084cd181984013b08d75e99a6cb5c11436d0d68810c1c09d3971a40e3585aeacb1d506ba90c60c04e9dc653134a4719460d2b53f5427ca52e7441cc140982013030274359e81334fa56992d72256dac35ad85b02027384d260b34d13498466860cc9411cec5b9b6b732d0e5cab2c85b41086460ce54a24817692269208cd001991023948d726dae45a1c7966690d67c10c8019c618c8c4e3121c47c11c4a8c8d6e7165fa28be440731d0670cd9a11bb419341c0463608e1eb3c2b6b826b70259a00ab3386b570b6320cdf4c63eb717a0e27a0cde9463f4737c2fcf65f1e4399d843778ccec511d23b1d03339066f159dd635b9c5b722cce25599435aa85b37086dc0d19033360346a048c6199a0123106666048c88cd8c99b11236f8b6dad6dada1b4a5b67486ca8cd842b2f844540ecb80d168122987658048a41d958122a23353266a448d7a35aeb6b5b686b29ad5d21aaa33510cc9a231304626a714c2e27848d3db9a72733b466961f9283e24366466ec8a0d10d3321024404ec7e090f5461e08c3bcee749d8e5331b076340cc70090d8919a12349ace8edad11ada0a6b3e4b66e8ccd433198562f1185c230bdb8971711e266631ccc1398ea432d0fc581f0aa3314844278ec4a998901211276210483ea3078460ee771c4ec36998603b0b0661a048304cc589995d67288d64d16c8d359025b194862e198542b09c73126e60ad0c423304b6b0e8ec18dec32b585b6609af610dd819c602e77046ec06d9846b387c6b0d8b614dac1dad81343b98af6ed6ed5a5d925bae4973c8ce58adc714b7f266e048d802da804b320662808c04098003f 13 4 11 8 5
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsF fullMask g_48 bds_48 (dagRefF 195 (dagTraceF fullMask rootStock 11 f_48) l_48 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_0 : treeBlockF 0 32 (dagCheckNodeF fullMask g_48 bds_48 195 (dagTraceF fullMask rootStock 11 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_1 : treeBlockF 32 64 (dagCheckNodeF fullMask g_48 bds_48 195 (dagTraceF fullMask rootStock 11 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_2 : treeBlockF 64 96 (dagCheckNodeF fullMask g_48 bds_48 195 (dagTraceF fullMask rootStock 11 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_3 : treeBlockF 96 128 (dagCheckNodeF fullMask g_48 bds_48 195 (dagTraceF fullMask rootStock 11 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_4 : treeBlockF 128 160 (dagCheckNodeF fullMask g_48 bds_48 195 (dagTraceF fullMask rootStock 11 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_5 : treeBlockF 160 192 (dagCheckNodeF fullMask g_48 bds_48 195 (dagTraceF fullMask rootStock 11 f_48) l_48) = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_6 : treeBlockF 192 195 (dagCheckNodeF fullMask g_48 bds_48 195 (dagTraceF fullMask rootStock 11 f_48) l_48) = true := by decide +kernel
theorem nj_48_1 : ∀ i, 0 ≤ i → i < 64 → (dagCheckNodeF fullMask g_48 bds_48 195 (dagTraceF fullMask rootStock 11 f_48) l_48) i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_48_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_48_1 h1 h2)
theorem nj_48_2 : ∀ i, 0 ≤ i → i < 96 → (dagCheckNodeF fullMask g_48 bds_48 195 (dagTraceF fullMask rootStock 11 f_48) l_48) i = true := block_join nj_48_1 (fun _ h1 h2 => treeBlockF_at nb_48_2 h1 h2)
theorem nj_48_3 : ∀ i, 0 ≤ i → i < 128 → (dagCheckNodeF fullMask g_48 bds_48 195 (dagTraceF fullMask rootStock 11 f_48) l_48) i = true := block_join nj_48_2 (fun _ h1 h2 => treeBlockF_at nb_48_3 h1 h2)
theorem nj_48_4 : ∀ i, 0 ≤ i → i < 160 → (dagCheckNodeF fullMask g_48 bds_48 195 (dagTraceF fullMask rootStock 11 f_48) l_48) i = true := block_join nj_48_3 (fun _ h1 h2 => treeBlockF_at nb_48_4 h1 h2)
theorem nj_48_5 : ∀ i, 0 ≤ i → i < 192 → (dagCheckNodeF fullMask g_48 bds_48 195 (dagTraceF fullMask rootStock 11 f_48) l_48) i = true := block_join nj_48_4 (fun _ h1 h2 => treeBlockF_at nb_48_5 h1 h2)
theorem nj_48_6 : ∀ i, 0 ≤ i → i < 195 → (dagCheckNodeF fullMask g_48 bds_48 195 (dagTraceF fullMask rootStock 11 f_48) l_48) i = true := block_join nj_48_5 (fun _ h1 h2 => treeBlockF_at nb_48_6 h1 h2)
theorem nc_48 : ∀ i, 0 ≤ i → i < 195 → (dagCheckNodeF fullMask g_48 bds_48 195 (dagTraceF fullMask rootStock 11 f_48) l_48) i = true := nj_48_6
theorem lb_48 : LowerBin fullMask rootStock g_48 12 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_48 sub_48 gl_48 rc_48 nc_48

def wg : List Gate := [⟨GateOp.and, [2, 0]⟩, ⟨GateOp.and, [5, 4]⟩, ⟨GateOp.or, [5, 4]⟩, ⟨GateOp.and, [3, 1]⟩, ⟨GateOp.or, [3, 1]⟩, ⟨GateOp.and, [2, 1]⟩, ⟨GateOp.or, [9, 6]⟩, ⟨GateOp.or, [8, 12]⟩, ⟨GateOp.and, [13, 10]⟩, ⟨GateOp.and, [7, 12]⟩, ⟨GateOp.or, [11, 0]⟩, ⟨GateOp.and, [14, 16]⟩, ⟨GateOp.or, [15, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4008241864 * 2 ^ 32 + 3939035264) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4008241864 * 2 ^ 32 + 3939035264)) (13 - 1) := by
  rw [show canon fullMask (4008241864 * 2 ^ 32 + 3939035264) = g_48 by decide]
  exact lb_48

end PEqualNP.Outside.L_meta_47737

theorem PEqualNP.Outside.L_meta_47737 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241864 * 2 ^ 32 + 3939035264) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241864 * 2 ^ 32 + 3939035264) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_47737.table2_from_lowerBin (4008241864 * 2 ^ 32 + 3939035264) 13 PEqualNP.Outside.L_meta_47737.root_lb PEqualNP.Outside.L_meta_47737.wg 18 rfl PEqualNP.Outside.L_meta_47737.wfits PEqualNP.Outside.L_meta_47737.weval
