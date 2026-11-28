import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48514

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

theorem masked_self (mask : Nat) : Masked mask mask := by
  unfold Masked; simp

theorem masked_land_right (mask w : Nat) : Masked mask (w &&& mask) := by
  unfold Masked; apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and]

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

def swapIndex (i : Nat) : Nat :=
  if i < 64 then if i.testBit 3 == i.testBit 4 then i else i ^^^ 24 else i

def swapWord (w : Nat) : Nat :=
  (((w >>> 64) <<< 64) ||| (w &&& 0xff0000ffff0000ff)) |||
    (((w &&& 0x0000ff000000ff00) <<< 8) ||| ((w &&& 0x00ff000000ff0000) >>> 8))

theorem swapIndex_inv (i : Nat) : swapIndex (swapIndex i) = i := by
  by_cases hi : i < 64
  · interval_cases i <;> decide
  · simp [swapIndex, hi]

theorem swapWord_bit (w i : Nat) : (swapWord w).testBit i = w.testBit (swapIndex i) := by
  by_cases hi : i < 64
  · interval_cases i <;>
      simp only [swapWord, Nat.testBit_or, Nat.testBit_and,
        Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
    all_goals norm_num [swapIndex, Nat.testBit, Nat.shiftRight_eq_div_pow]
  · have h64 : 64 ≤ i := by omega
    have h8 : 8 ≤ i := by omega
    have e64 : 64 + (i - 64) = i := by omega
    have hkeep : (0xff0000ffff0000ff : Nat).testBit i = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 0xff0000ffff0000ff < 2 ^ 64)
        (Nat.pow_le_pow_right (by decide) h64))
    have hlow : (0x0000ff000000ff00 : Nat).testBit (i - 8) = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 0x0000ff000000ff00 < 2 ^ 56)
        (Nat.pow_le_pow_right (by decide) (by omega)))
    have hhigh : (0x00ff000000ff0000 : Nat).testBit (8 + i) = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 0x00ff000000ff0000 < 2 ^ 64)
        (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [swapWord, swapIndex, hi, h64, h8, e64, hkeep, hlow, hhigh,
      Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]

theorem swapWord_inv (w : Nat) : swapWord (swapWord w) = w := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [swapWord_bit, swapIndex_inv]

theorem swapWord_injective : Function.Injective swapWord :=
  fun _ _ h => by simpa only [swapWord_inv] using congrArg swapWord h

def swap23Index (i : Nat) : Nat :=
  if i < 64 then if i.testBit 2 == i.testBit 3 then i else i ^^^ 12 else i

def swap23Word (w : Nat) : Nat :=
  (((w >>> 64) <<< 64) ||| (w &&& 0xf00ff00ff00ff00f)) |||
    (((w &&& 0x00f000f000f000f0) <<< 4) ||| ((w &&& 0x0f000f000f000f00) >>> 4))

theorem swap23Index_inv (i : Nat) : swap23Index (swap23Index i) = i := by
  by_cases hi : i < 64
  · interval_cases i <;> decide
  · simp [swap23Index, hi]

theorem swap23Word_bit (w i : Nat) : (swap23Word w).testBit i = w.testBit (swap23Index i) := by
  by_cases hi : i < 64
  · interval_cases i <;>
      simp only [swap23Word, Nat.testBit_or, Nat.testBit_and,
        Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
    all_goals norm_num [swap23Index, Nat.testBit, Nat.shiftRight_eq_div_pow]
  · have h64 : 64 ≤ i := by omega
    have h4 : 4 ≤ i := by omega
    have e64 : 64 + (i - 64) = i := by omega
    have hkeep : (0xf00ff00ff00ff00f : Nat).testBit i = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 0xf00ff00ff00ff00f < 2 ^ 64)
        (Nat.pow_le_pow_right (by decide) h64))
    have hlow : (0x00f000f000f000f0 : Nat).testBit (i - 4) = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 0x00f000f000f000f0 < 2 ^ 60)
        (Nat.pow_le_pow_right (by decide) (by omega)))
    have hhigh : (0x0f000f000f000f00 : Nat).testBit (4 + i) = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 0x0f000f000f000f00 < 2 ^ 64)
        (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [swap23Word, swap23Index, hi, h64, h4, e64, hkeep, hlow, hhigh,
      Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]

theorem swap23Word_inv (w : Nat) : swap23Word (swap23Word w) = w := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [swap23Word_bit, swap23Index_inv]

theorem swap23Word_injective : Function.Injective swap23Word :=
  fun _ _ h => by simpa only [swap23Word_inv] using congrArg swap23Word h

structure RowTransform where
  word : Nat → Nat
  slot : Nat → Nat
  bit_spec : ∀ w i, (word w).testBit i = w.testBit (slot i)
  word_injective : Function.Injective word

def composeRows (outer inner : RowTransform) : RowTransform where
  word := outer.word ∘ inner.word
  slot := inner.slot ∘ outer.slot
  bit_spec := by intro w i; simp only [Function.comp_apply, outer.bit_spec, inner.bit_spec]
  word_injective := outer.word_injective.comp inner.word_injective

def firstRowSwap : RowTransform :=
  ⟨swap23Word, swap23Index, swap23Word_bit, swap23Word_injective⟩

def lastRowSwap : RowTransform :=
  ⟨swapWord, swapIndex, swapWord_bit, swapWord_injective⟩

def chooseRows (tag : Nat) : RowTransform :=
  match tag with
  | 1 => firstRowSwap
  | 2 => composeRows firstRowSwap (composeRows lastRowSwap firstRowSwap)
  | 3 => lastRowSwap
  | 4 => composeRows firstRowSwap lastRowSwap
  | 5 => composeRows lastRowSwap firstRowSwap
  | _ => ⟨id, id, by intros; rfl, Function.injective_id⟩

def moveWord (tag word : Nat) : Nat := (chooseRows tag).word word

def moveSlot (tag slot : Nat) : Nat := (chooseRows tag).slot slot

theorem moveWord_bit (tag w i : Nat) : (moveWord tag w).testBit i = w.testBit (moveSlot tag i) :=
  (chooseRows tag).bit_spec w i

theorem moveWord_injective (tag : Nat) : Function.Injective (moveWord tag) :=
  (chooseRows tag).word_injective

theorem moveWord_and (tag x y : Nat) :
    moveWord tag (x &&& y) = moveWord tag x &&& moveWord tag y := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [moveWord_bit, Nat.testBit_and]

theorem moveWord_or (tag x y : Nat) :
    moveWord tag (x ||| y) = moveWord tag x ||| moveWord tag y := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [moveWord_bit, Nat.testBit_or]

theorem moveWord_xor (tag x y : Nat) :
    moveWord tag (x ^^^ y) = moveWord tag x ^^^ moveWord tag y := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [moveWord_bit, Nat.testBit_xor]

theorem moveWord_zero (tag : Nat) : moveWord tag 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [moveWord_bit, Nat.zero_testBit]

theorem canonByTopBit {mask top : Nat} (hp : mask = 2 ^ (top + 1) - 1) (w : Nat) :
    canon mask w =
      if (w &&& mask).testBit top then mask ^^^ (w &&& mask) else w &&& mask := by
  unfold canon; dsimp only
  set v := w &&& mask
  have hhigh (j : Nat) (hj : top < j) :
      v.testBit j = (mask ^^^ v).testBit j := by
    have hj' : ¬ j < top + 1 := by omega
    have hb : mask.testBit j = false := by
      rw [hp, Nat.testBit_two_pow_sub_one]
      simp [hj']
    simp [Nat.testBit_xor, hb]
  have hone : mask.testBit top = true := by
    rw [hp, Nat.testBit_two_pow_sub_one]
    simp
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

theorem moveWord_canon {mask top : Nat} {tag : Nat} (hp : mask = 2 ^ (top + 1) - 1)
    (hm : moveWord tag mask = mask) (ht : moveSlot tag top = top) (w : Nat) :
    moveWord tag (canon mask w) = canon mask (moveWord tag w) := by
  rw [canonByTopBit hp, canonByTopBit hp]
  have h : ((moveWord tag w) &&& mask).testBit top = (w &&& mask).testBit top := by
    rw [← hm, ← moveWord_and, moveWord_bit, ht, hm]
  rw [h]
  by_cases htop : (w &&& mask).testBit top = true <;>
    simp [htop, moveWord_xor, moveWord_and, hm]

theorem moveWord_gate {mask top : Nat} {tag : Nat} (hp : mask = 2 ^ (top + 1) - 1)
    (hm : moveWord tag mask = mask) (ht : moveSlot tag top = top) (op a b : Nat) :
    moveWord tag (binOp mask op a b) = binOp mask op (moveWord tag a) (moveWord tag b) := by
  unfold binOp
  simp only [bsel]
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;>
    simp [moveWord_canon hp hm ht, moveWord_and, moveWord_or, moveWord_xor, hm]

theorem moveWord_drop (tag : Nat) (keep : Bool) (w : Nat) (S : Finset Nat) :
    (dropIf keep w S).image (moveWord tag) = dropIf keep (moveWord tag w) (S.image (moveWord tag)) := by
  cases keep <;> simp [dropIf, Finset.image_erase (moveWord_injective tag)]

theorem moveLiveBin {mask top goal fuel tag : Nat} {S : Finset Nat}
    (hp : mask = 2 ^ (top + 1) - 1) (hm : moveWord tag mask = mask) (ht : moveSlot tag top = top)
    (g : moveWord tag goal = goal)
    (h : LiveBin mask goal fuel S) : LiveBin mask goal fuel (S.image (moveWord tag)) := by
  induction h with
  | done => simpa only [Finset.image_singleton, g] using (LiveBin.done (mask := mask) (goal := goal))
  | @step k T a b op ha hb hab ha0 hb0 hop hz hf keepA keepB tail ih =>
    refine LiveBin.step (a := moveWord tag a) (b := moveWord tag b) (op := op)
      (Finset.mem_image_of_mem (moveWord tag) ha) (Finset.mem_image_of_mem (moveWord tag) hb)
      ((moveWord_injective tag).ne hab) ?_ ?_ hop ?_ ?_ keepA keepB ?_
    · intro h; exact ha0 (moveWord_injective tag (h.trans (moveWord_zero tag).symm))
    · intro h; exact hb0 (moveWord_injective tag (h.trans (moveWord_zero tag).symm))
    · rw [← moveWord_gate hp hm ht]
      intro h; exact hz (moveWord_injective tag (h.trans (moveWord_zero tag).symm))
    · rw [← moveWord_gate hp hm ht]
      intro h
      obtain ⟨x, hx, eq⟩ := Finset.mem_image.mp h
      exact hf ((moveWord_injective tag eq) ▸ hx)
    · simpa only [Finset.image_insert, moveWord_drop, moveWord_gate hp hm ht] using ih

def moveBankF (tag : Nat) (saved current : List Nat) : Bool :=
  let mapped := current.map (moveWord tag)
  Bool.rec false (allN (fun w => memN w mapped) saved)
    (allN (fun w => memN w saved) mapped)

theorem moveBank_image {tag : Nat} {saved current : List Nat} (h : moveBankF tag saved current = true) :
    current.toFinset.image (moveWord tag) = saved.toFinset := by
  let mapped := current.map (moveWord tag)
  change Bool.rec false (allN (fun w => memN w mapped) saved)
    (allN (fun w => memN w saved) mapped) = true at h
  have hh : (allN (fun w => memN w saved) mapped) = true ∧
      (allN (fun w => memN w mapped) saved) = true := by
    cases hc : allN (fun w => memN w saved) mapped <;> rw [hc] at h
    · contradiction
    · exact ⟨rfl, h⟩
  simp only [allN_eq, List.all_eq_true, memN_eq, List.contains_iff_mem] at hh
  ext w; constructor
  · intro hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact List.mem_toFinset.mpr (hh.1 _ (List.mem_map.mpr ⟨v,List.mem_toFinset.mp hv,rfl⟩))
  · intro hw
    obtain ⟨v, hv, he⟩ := List.mem_map.mp (hh.2 _ (List.mem_toFinset.mp hw))
    exact Finset.mem_image.mpr ⟨v,List.mem_toFinset.mpr hv,he⟩

def allowedMove (mask goal top tag : Nat) : Bool :=
  Nat.beq (moveWord tag mask) mask && (Nat.beq (moveWord tag goal) goal && Nat.beq (moveSlot tag top) top)

def dagRefPermF (mask goal top count : Nat) (states : Nat → Option ReplayState)
    (links : Nat → Nat → Option Nat) (parent token : Nat) (current : ReplayState) : Bool :=
  match links parent token with
  | none => false
  | some code =>
    let dest := Nat.shiftRight code 3
    let tag := Nat.land code 7
    Bool.rec false
      (match states dest with
       | none => false
       | some saved =>
         Bool.rec false
           (Bool.rec
             (Bool.rec false (moveBankF tag saved.2.1 current.2.1) (allowedMove mask goal top tag))
             (eqListN saved.2.1 current.2.1) (Nat.beq tag 0))
           (Nat.beq saved.1 current.1))
      (Nat.blt dest count)

theorem permRefTransfers {mask top goal count : Nat} (hp : mask = 2 ^ (top + 1) - 1)
    (states : Nat → Option ReplayState) (links : Nat → Nat → Option Nat) :
    RefTransfers mask goal count states (dagRefPermF mask goal top count states links) := by
  intro parent token current h
  unfold dagRefPermF at h
  cases he : links parent token with
  | none => rw [he] at h; contradiction
  | some code =>
    rw [he] at h
    let dest := Nat.shiftRight code 3
    let tag := Nat.land code 7
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
          refine ⟨dest, saved, hlt, hs, Nat.beq_eq.mp hf, ?_⟩
          intro k hLive
          change Bool.rec _ (eqListN saved.2.1 current.2.1) (Nat.beq tag 0) = true at h
          cases hz : Nat.beq tag 0
          · rw [hz] at h
            change Bool.rec false _ (allowedMove mask goal top tag) = true at h
            cases hm : allowedMove mask goal top tag
            · rw [hm] at h; contradiction
            · rw [hm] at h
              change moveBankF tag saved.2.1 current.2.1 = true at h
              have hfixed : moveWord tag mask = mask ∧ moveWord tag goal = goal ∧ moveSlot tag top = top := by
                simpa only [allowedMove, Bool.and_eq_true, Nat.beq_eq] using hm
              simpa only [moveBank_image h] using
                moveLiveBin hp hfixed.1 hfixed.2.2 hfixed.2.1 hLive
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

theorem dagAllNodesWithPicks {mask goal fuel count : Nat} {stock : List Nat}
    {picked : Nat → List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {reference : Nat → Nat → ReplayState → Bool}
    (hrefs : RefTransfers mask goal count (dagTrace mask stock fuel forest) reference)
    (hgm : Masked mask goal) (hknown : ∀ i, KnownBin (picked i))
    (hsub : ∀ i b, b ∈ picked i → mask &&& b.1 = b.1) (snd : stock.Nodup)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeWith mask goal (picked i)
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
          · have hopen := dagLocal_open (state := (rem - 1, ws', (z, x, y) :: hist)) hgm (hknown i) (hsub i) hnd' (k := k') (by omega) hlive'
            rw [hopen] at hloc; exact Bool.noConfusion hloc
          · obtain ⟨dest, saved, hdest, htr2, hfEq, hMove⟩ :=
              hrefs (i + 1) (makeToken a b op keep) _ href
            have hbelow : rem - 1 < cap := by omega
            exact ih (rem - 1) hbelow dest saved hdest htr2 hfEq k' (by omega) (hMove k' hlive')

theorem lowerDagWithPicks {mask goal fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {picked : Nat → List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {reference : Nat → Nat → ReplayState → Bool}
    (hrefs : RefTransfers mask goal count (dagTrace mask stock fuel forest) reference)
    (hgm : Masked mask goal) (hgnz : goal ≠ 0)
    (hcs : stock.all (fun w => Nat.beq (canon mask w) w) = true)
    (snd : stock.Nodup)
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hknownPicked : ∀ i, KnownBin (picked i))
    (hsubPicked : ∀ i b, b ∈ picked i → mask &&& b.1 = b.1)
    (hroots : dagCheckRoots mask goal bounds
      (reference 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeWith mask goal (picked i)
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
    exact dagAllNodesWithPicks hrefs hgm hknownPicked hsubPicked snd hnodes fuel dest saved hdest htr hfEq k
      (by omega) (hMove k hlive')

abbrev ReplayBound := Nat × List Nat × Nat × Nat

def pickedBounds (bounds : List ReplayBound) (indices : List Nat) : List ReplayBound :=
  indices.filterMap (fun j => bounds[j]?)

theorem memPickedBounds {bounds : List ReplayBound} {indices : List Nat} {b : ReplayBound}
    (h : b ∈ pickedBounds bounds indices) : b ∈ bounds := by
  obtain ⟨_, _, hb⟩ := List.mem_filterMap.mp h
  exact List.mem_of_getElem? hb

def pickBlockF (index split low high : Nat) : Nat :=
  Bool.rec high low (Nat.blt index split)

def pagedUnpackF (width pageLog : Nat) (blocks : Nat → Nat) (index : Nat) : Nat :=
  unpackF (blocks (Nat.shiftRight index pageLog)) width
    (Nat.land index (Nat.sub (Nat.shiftLeft 1 pageLog) 1))

def unpackIndexedForestF (words : Nat → Nat) (tokenBits : Nat) : Nat → Nat × Nat :=
  fun i =>
    let code := words i
    (Nat.shiftRight code tokenBits, Nat.land code (Nat.sub (Nat.shiftLeft 1 tokenBits) 1))

def unpackIndexedLinksF (index data : Nat → Nat) (sizeBits tokBits steps : Nat) : Nat → Nat → Option Nat :=
  fun parent tok =>
    let entry := index parent
    let sz := Nat.land entry (Nat.sub (Nat.shiftLeft 1 sizeBits) 1)
    let off := Nat.shiftRight entry sizeBits
    (Nat.rec (motive := fun _ => Nat → Nat → Option Nat) (fun _ _ => none)
      (fun _ next lo hi =>
        Bool.rec none
          (let mid := Nat.shiftRight (Nat.add lo hi) 1
           let code := data mid
           let key := Nat.land code (Nat.sub (Nat.shiftLeft 1 tokBits) 1)
           Bool.rec
             (Bool.rec (next (Nat.add mid 1) hi) (next lo mid) (Nat.blt tok key))
             (some (Nat.shiftRight code tokBits)) (Nat.beq tok key))
          (Nat.blt lo hi)) steps) off (Nat.add off sz)
def unpackIndexedPicks (positions elems : Nat → Nat) (lenSize i : Nat) : List Nat :=
  forceW (positions i) fun atIndex =>
    forceW (Nat.land atIndex (Nat.sub (Nat.shiftLeft 1 lenSize) 1)) fun count =>
      forceW (Nat.shiftRight atIndex lenSize) fun start =>
        (List.range count).map fun j => elems (Nat.add start j)

theorem lowerDagPickedF {mask top goal fuel count : Nat} {stock : List Nat}
    {bounds : List ReplayBound} {picks : Nat → List Nat}
    {forest : Nat → Nat × Nat} {links : Nat → Nat → Option Nat}
    (hp : mask = 2 ^ (top + 1) - 1) (hgm : Masked mask goal) (hgnz : goal ≠ 0)
    (hcs : stock.all (fun w => Nat.beq (canon mask w) w) = true)
    (snd : stock.Nodup)
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hroots : dagCheckRootsF mask goal bounds
      (dagRefPermF mask goal top count (dagTraceF mask stock fuel forest) links 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeWithF mask goal (pickedBounds bounds (picks i))
      (dagTraceF mask stock fuel forest)
      (dagRefPermF mask goal top count (dagTraceF mask stock fuel forest) links) i = true) :
    LowerBin mask stock goal (fuel + 1) := by
  have htr : dagTraceF mask stock fuel forest = dagTrace mask stock fuel forest := by
    funext i; exact dagTraceF_eq mask stock fuel forest i
  rw [htr, dagCheckRootsF_eq hgoals] at hroots
  rw [htr] at hnodes
  refine lowerDagWithPicks (picked := fun i => pickedBounds bounds (picks i))
    (permRefTransfers hp _ _) hgm hgnz hcs snd hknown hsub ?_ ?_ hroots ?_
  · intro i b hb; exact hknown b (memPickedBounds hb)
  · intro i b hb; exact hsub b (memPickedBounds hb)
  · intro i hlo hhi
    have hg : ∀ b ∈ pickedBounds bounds (picks i), canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 :=
      fun b hb => hgoals b (memPickedBounds hb)
    simpa only [dagCheckNodeWithF_eq hg] using hnodes i hlo hhi



def oracleChildren (mask goal : Nat) (rule : Nat → ReplayState → Bool)
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
                          rule tok ch))
                        true (Nat.blt fuel newLen)))
                    true (memN z ws))
                  true (Nat.beq z 0))))))
        (Nat.blt n 17))
      true (Nat.beq fuel 0))
    false (memN goal ws)

def packPairColors (a b c d : Bool) : Nat :=
  Bool.rec 0 1 a + Bool.rec 0 2 b + Bool.rec 0 4 c + Bool.rec 0 8 d

def pairColors (x y rows : Nat) : Nat :=
  forceW (Nat.land rows x) fun hi =>
  forceW (Nat.xor rows hi) fun lo =>
  forceW (Nat.land lo y) fun loHi =>
  forceW (Nat.land hi y) fun hiHi =>
    packPairColors (Nat.blt 0 (Nat.xor lo loHi)) (Nat.blt 0 loHi)
      (Nat.blt 0 (Nat.xor hi hiHi)) (Nat.blt 0 hiHi)

def clashLeaf (p n : Nat) : Nat :=
  Nat.land (Nat.shiftRight 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffffffffffffffffffffffffffffffff53070000ffffffffffffffffffffffffffffffffffffffffffffffffffff0753ffff0000ffffffffffffffffffffffffffffffffffffffffffffffff5555055151050000ffffffffffffffffffffffffffffffffffffffffffff7035ffffffffffff0000ffffffffffffffffffffffffffffffffffffffff33333031ffffffff13030000ffffffffffffffffffffffffffffffffffff7777ffff7035ffff0753ffff0000ffffffffffffffffffffffffffffffff35703570313030301550055011000000ffffffffffffffffffffffffffff3570ffffffffffffffffffffffffffff0000ffffffffffffffffffffffff77773570ffffffffffffffffffffffff53070000ffffffffffffffffffff3333ffff3130ffffffffffffffffffff0313ffff0000ffffffffffffffff7035303170353030ffffffffffffffff5015001150050000ffffffffffff5555ffffffffffff1550ffffffffffff5015ffffffffffff0000ffffffff07530551ffffffff07530550ffffffff03130011ffffffff03030000ffff5307ffff5105ffff1303ffff1100ffff5307ffff5005ffff0303ffff00000000000000000000000000000000000000000000000000000000000000000000 (16 * (p + 16 * n))) 65535

def pairClashes (x y : Nat) (ws : List Nat) : Nat → Nat → Nat :=
  List.rec
    (fun p n => clashLeaf (pairColors x y p) (pairColors x y n))
    (fun w _ rest p n =>
      Bool.rec (Bool.rec
        (forceW (Nat.land p w) fun ph => forceW (Nat.land n w) fun nh =>
          Nat.lor (rest ph nh) (rest (Nat.xor p ph) (Nat.xor n nh)))
        0 (Nat.beq n 0)) 0 (Nat.beq p 0)) ws

def clashFlag (word op keep : Nat) : Bool :=
  Bool.rec false (word.testBit (4 * op + keep))
    (Bool.rec false (Nat.blt keep 4) (Nat.blt op 4))

def clashChildren (mask goal : Nat) (rule : Nat → ReplayState → Bool)
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
            forceW (pairClashes x y (dropValF true x (dropValF true y ws))
              (Nat.land mask goal) (Nat.land mask (Nat.xor mask goal))) fun clash =>
            treeBlockF 0 4 (fun op =>
              forceW (binOpF mask op x y) (fun z =>
                Bool.rec
                  (Bool.rec
                    (treeBlockF 0 4 (fun keep =>
                      let keepA := Nat.beq (Nat.land keep 1) 1
                      let keepB := Nat.beq (Nat.land (Nat.shiftRight keep 1) 1) 1
                      let newLen := Nat.add (Nat.add (Nat.sub n 1) (Bool.rec 0 1 keepA)) (Bool.rec 0 1 keepB)
                      Bool.rec
                        (Bool.rec (forceWs (insertSortedF z (dropValF (Bool.rec true false keepA) x (dropValF (Bool.rec true false keepB) y ws))) (fun ws' =>
                          let ch := (Nat.sub fuel 1, ws', (z, x, y) :: hist)
                          let tok := Nat.add (Nat.shiftLeft (Nat.add (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2) op) 2) keep
                          rule tok ch)) true (clashFlag clash op keep))
                        true (Nat.blt fuel newLen)))
                    true (memN z ws))
                  true (Nat.beq z 0))))))
        (Nat.blt n 17))
      true (Nat.beq fuel 0))
    false (memN goal ws)


theorem fpDagPartPair {ws : List Nat} {p n r s : Nat}
    (hp : p.testBit r = true) (hn : n.testBit s = true)
    (hws : ∀ w ∈ ws, w.testBit r = w.testBit s) : dagPart ws p n = false := by
  induction ws generalizing p n with
  | nil =>
    have p0 : Nat.beq p 0 = false := beq_false_ne (by rintro rfl; simp at hp)
    have n0 : Nat.beq n 0 = false := beq_false_ne (by rintro rfl; simp at hn)
    change (Nat.beq p 0 || Nat.beq n 0) = false
    rw [p0,n0]; rfl
  | cons w ws ih =>
    have p0 : Nat.beq p 0 = false := beq_false_ne (by rintro rfl; simp at hp)
    have n0 : Nat.beq n 0 = false := beq_false_ne (by rintro rfl; simp at hn)
    have same := hws w List.mem_cons_self
    have rest : ∀ w' ∈ ws, w'.testBit r = w'.testBit s :=
      fun w' hw' => hws w' (List.mem_cons_of_mem _ hw')
    change ((Nat.beq p 0 || Nat.beq n 0) ||
      forceW (p &&& w) (fun up => forceW (n &&& w) (fun down =>
        dagPart ws up down && forceW (p ^^^ up) (fun offP =>
          forceW (n ^^^ down) (dagPart ws offP))))) = false
    simp only [p0,n0,Bool.false_or,forceW_eq,Bool.and_eq_false_iff]
    cases hw : w.testBit r
    · right
      exact ih (by simp [Nat.testBit_xor,Nat.testBit_and,hp,hw])
        (by simp [Nat.testBit_xor,Nat.testBit_and,hn,← same,hw]) rest
    · left
      exact ih (by simp [Nat.testBit_and,hp,hw]) (by simp [Nat.testBit_and,hn,← same,hw]) rest

theorem fpBitExists {w : Nat} (h : w ≠ 0) : ∃ r, w.testBit r = true := by
  by_contra! all
  apply h
  apply Nat.eq_of_testBit_eq
  intro r
  simp [all r]

theorem packPairColors_small : ∀ a b c d, packPairColors a b c d < 16 := by decide +kernel

theorem packPairColors_bit : ∀ a b c d (i : Fin 4),
    (packPairColors a b c d).testBit i.val = [a,b,c,d][i.val]! := by decide +kernel

def pairSelect (u w : Nat) (high : Bool) : Nat :=
  Bool.rec (u ^^^ (u &&& w)) (u &&& w) high

def pairRows (x y u : Nat) (i : Fin 4) : Nat :=
  pairSelect (pairSelect u x (i.val.testBit 1)) y (i.val.testBit 0)

theorem pairColors_small (x y u : Nat) : pairColors x y u < 16 := by
  simp only [pairColors, forceW_eq]
  exact packPairColors_small _ _ _ _

theorem pairColors_bit (x y u : Nat) (i : Fin 4) :
    (pairColors x y u).testBit i.val = Nat.blt 0 (pairRows x y u i) := by
  simp only [pairColors, forceW_eq, packPairColors_bit]
  fin_cases i <;> rfl

theorem pairSelect_bits {u w r : Nat} {high : Bool}
    (h : (pairSelect u w high).testBit r = true) :
    u.testBit r = true ∧ w.testBit r = high := by
  cases high
  · exact offBits h
  · change (u &&& w).testBit r = true at h
    simpa only [Nat.testBit_and, Bool.and_eq_true] using h

def pairPattern (x y r : Nat) (i : Fin 4) : Prop :=
  x.testBit r = i.val.testBit 1 ∧ y.testBit r = i.val.testBit 0

theorem pairColor_exists {x y u : Nat} {i : Fin 4}
    (h : (pairColors x y u).testBit i.val = true) :
    ∃ r, u.testBit r = true ∧ pairPattern x y r i := by
  rw [pairColors_bit, Nat.blt_eq] at h
  obtain ⟨r, hr⟩ := fpBitExists (Nat.ne_of_gt h)
  have hb := pairSelect_bits hr
  have ha := pairSelect_bits hb.1
  exact ⟨r,ha.1,ha.2,hb.2⟩

def pairGate (op : Nat) (x y : Bool) : Bool :=
  Bool.rec (Bool.rec (Bool.rec ((!x) && y) (x && !y) (Nat.beq op 2))
    (x || y) (Nat.beq op 1)) (x && y) (Nat.beq op 0)

def pairToken (i j : Fin 4) (t : Fin 16) : Bool :=
  let ix := i.val.testBit 1
  let iy := i.val.testBit 0
  let jx := j.val.testBit 1
  let jy := j.val.testBit 0
  (pairGate (t.val >>> 2) ix iy == pairGate (t.val >>> 2) jx jy) &&
    ((!t.val.testBit 0 || ix == jx) && (!t.val.testBit 1 || iy == jy))

def clashKind (i j : Fin 4) : Nat :=
  (0xffff3030055011003030ffff0011500505500011ffff0303110050050303ffff >>> (16 * (4 * i.val + j.val))) &&& 65535

theorem clashKind_ok : ∀ (i j : Fin 4) (t : Fin 16),
    (clashKind i j).testBit t.val = pairToken i j t := by decide +kernel

def clashWords (p n : Fin 16) : List (Fin 4 × Fin 4) :=
  ((List.finRange 4).flatMap fun i => (List.finRange 4).map fun j => (i,j)).filter
    (fun (i,j) => p.val.testBit i.val && n.val.testBit j.val)

def clashJoin (p n : Fin 16) : Nat :=
  ((clashWords p n).map fun (i,j) => clashKind i j).foldr Nat.lor 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem clashLeaf_eq : ∀ p n : Fin 16, clashLeaf p.val n.val = clashJoin p n := by decide +kernel

theorem clashFold {words : List Nat} {bit : Nat}
    (h : (words.foldr Nat.lor 0).testBit bit = true) : ∃ w ∈ words, w.testBit bit = true := by
  induction words with
  | nil => simp at h
  | cons w words ih =>
    change (w ||| words.foldr Nat.lor 0).testBit bit = true at h
    rw [Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨w,List.mem_cons_self,h⟩
    · obtain ⟨v,hv,ht⟩ := ih h
      exact ⟨v,List.mem_cons_of_mem _ hv,ht⟩

theorem clashLeaf_valid (p n : Fin 16) (t : Fin 16)
    (h : (clashLeaf p.val n.val).testBit t.val = true) :
    ∃ i j : Fin 4, p.val.testBit i.val = true ∧ n.val.testBit j.val = true ∧ pairToken i j t = true := by
  rw [clashLeaf_eq] at h
  obtain ⟨word,hw,hwbit⟩ := clashFold h
  obtain ⟨⟨i,j⟩,hm,he⟩ := List.mem_map.mp hw
  have hb := (List.mem_filter.mp hm).2
  rw [Bool.and_eq_true] at hb
  subst word
  rw [clashKind_ok] at hwbit
  exact ⟨i,j,hb.1,hb.2,hwbit⟩

def pairClashWitness (x y p n : Nat) (ws : List Nat) (t : Fin 16) : Prop :=
  ∃ r s i j, p.testBit r = true ∧ n.testBit s = true ∧ pairPattern x y r i ∧ pairPattern x y s j ∧
    pairToken i j t = true ∧ ∀ w ∈ ws, w.testBit r = w.testBit s

theorem pairClashes_valid {x y p n : Nat} {ws : List Nat} {t : Fin 16}
    (hit : (pairClashes x y ws p n).testBit t.val = true) : pairClashWitness x y p n ws t := by
  induction ws generalizing p n with
  | nil =>
    change (clashLeaf (pairColors x y p) (pairColors x y n)).testBit t.val = true at hit
    obtain ⟨i,j,hi,hj,hij⟩ := clashLeaf_valid ⟨_,pairColors_small x y p⟩ ⟨_,pairColors_small x y n⟩ t hit
    obtain ⟨r,hr,hx⟩ := pairColor_exists hi
    obtain ⟨s,hs,hy⟩ := pairColor_exists hj
    exact ⟨r,s,i,j,hr,hs,hx,hy,hij,by simp⟩
  | cons w ws ih =>
    change (Bool.rec (motive := fun _ => Nat) (Bool.rec
      (forceW (p &&& w) fun ph => forceW (n &&& w) fun nh =>
        pairClashes x y ws ph nh ||| pairClashes x y ws (p ^^^ ph) (n ^^^ nh))
      0 (Nat.beq n 0)) 0 (Nat.beq p 0)).testBit t.val = true at hit
    simp only [forceW_eq] at hit
    cases hp : Nat.beq p 0 <;> cases hn : Nat.beq n 0 <;> simp [hp,hn] at hit
    rcases hit with on | off
    · obtain ⟨r,s,i,j,hr,hs,hx,hy,hij,hw⟩ := ih on
      rw [Nat.testBit_and, Bool.and_eq_true] at hr hs
      refine ⟨r,s,i,j,hr.1,hs.1,hx,hy,hij,?_⟩
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · rw [hr.2,hs.2]
      · exact hw v hv
    · obtain ⟨r,s,i,j,hr,hs,hx,hy,hij,hw⟩ := ih off
      have hr' := offBits hr
      have hs' := offBits hs
      refine ⟨r,s,i,j,hr'.1,hs'.1,hx,hy,hij,?_⟩
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · rw [hr'.2,hs'.2]
      · exact hw v hv

theorem clashToken_fields : ∀ op keep : Fin 4,
    ((4 * op.val + keep.val) >>> 2) = op.val ∧
    (4 * op.val + keep.val).testBit 0 = Nat.beq (keep.val &&& 1) 1 ∧
    (4 * op.val + keep.val).testBit 1 = Nat.beq ((keep.val >>> 1) &&& 1) 1 := by
  decide +kernel

theorem pairBool_eq {a b : Bool} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> simp_all

def pairRaw (m op x y : Nat) : Nat :=
  Bool.rec (Bool.rec (Bool.rec ((m ^^^ x) &&& y) (x &&& (m ^^^ y)) (Nat.beq op 2))
    (x ||| y) (Nat.beq op 1)) (x &&& y) (Nat.beq op 0)

theorem pairBin (m op x y : Nat) : binOpF m op x y = canonF m (pairRaw m op x y) := by
  unfold binOpF pairRaw
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> rfl

theorem pairRaw_at {m r : Nat} (hm : m.testBit r = true) (op x y : Nat) :
    (pairRaw m op x y).testBit r = pairGate op (x.testBit r) (y.testBit r) := by
  unfold pairRaw pairGate
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;>
    simp [Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,hm]

theorem pairCanon_agree {m v r s : Nat} (hr : m.testBit r = true) (hs : m.testBit s = true)
    (h : v.testBit r = v.testBit s) : (canonF m v).testBit r = (canonF m v).testBit s := by
  have hv : (v &&& m).testBit r = (v &&& m).testBit s := by simp [Nat.testBit_and,hr,hs,h]
  unfold canonF
  dsimp only
  cases Nat.beq (v &&& m) 0 <;> cases Nat.beq (v &&& m) m <;>
    cases Nat.blt (v &&& m) (m ^^^ (v &&& m)) <;> simp [Nat.testBit_xor,hr,hs,hv]

theorem pairClash_close {m g x y op keep f : Nat} {ws : List Nat} {hist : List (Nat × Nat × Nat)}
    (hit : clashFlag (pairClashes x y (dropValF true x (dropValF true y ws))
       (m &&& g) (m &&& (m ^^^ g))) op keep = true) :
    dagLocalF m g [] (f, insertSortedF (binOpF m op x y)
      (dropValF (Bool.rec true false (Nat.beq (keep &&& 1) 1)) x
        (dropValF (Bool.rec true false (Nat.beq ((keep >>> 1) &&& 1) 1)) y ws)), hist) = true := by
  unfold clashFlag at hit
  cases ho : Nat.blt op 4 <;> cases hk : Nat.blt keep 4 <;> simp [ho,hk] at hit
  have hOp := Nat.blt_eq.mp ho
  have hKeep := Nat.blt_eq.mp hk
  have fields := clashToken_fields ⟨op,hOp⟩ ⟨keep,hKeep⟩
  have ht : 4 * op + keep < 16 := by omega
  obtain ⟨r,s,i,j,hr,hs,hi,hj,hij,hrest⟩ := pairClashes_valid (t := ⟨_,ht⟩) hit
  rw [Nat.testBit_and, Bool.and_eq_true] at hr hs
  have hGate := hij
  simp only [pairToken, Bool.and_eq_true] at hGate
  have sameInput : pairGate op (x.testBit r) (y.testBit r) = pairGate op (x.testBit s) (y.testBit s) := by
    rw [hi.1,hi.2,hj.1,hj.2]
    apply pairBool_eq
    simpa only [fields.1] using hGate.1
  have zx : (binOpF m op x y).testBit r = (binOpF m op x y).testBit s := by
    rw [pairBin]
    apply pairCanon_agree hr.1 hs.1
    rw [pairRaw_at hr.1, pairRaw_at hs.1]
    exact sameInput
  have hx : Nat.beq (keep &&& 1) 1 = true → x.testBit r = x.testBit s := by
    intro hx
    have hx' : (4 * op + keep).testBit 0 = true := fields.2.1.trans hx
    rw [hi.1,hj.1]
    have rule : (!(4 * op + keep).testBit 0 || (i.val.testBit 1 == j.val.testBit 1)) = true := hGate.2.1
    exact pairBool_eq (by simpa only [hx', Bool.not_true, Bool.false_or] using rule)
  have hy : Nat.beq ((keep >>> 1) &&& 1) 1 = true → y.testBit r = y.testBit s := by
    intro hy
    have hy' : (4 * op + keep).testBit 1 = true := fields.2.2.trans hy
    rw [hi.2,hj.2]
    have rule : (!(4 * op + keep).testBit 1 || (i.val.testBit 0 == j.val.testBit 0)) = true := hGate.2.2
    exact pairBool_eq (by simpa only [hy', Bool.not_true, Bool.false_or] using rule)
  let ka := Nat.beq (keep &&& 1) 1
  let kb := Nat.beq ((keep >>> 1) &&& 1) 1
  let bank := insertSortedF (binOpF m op x y)
    (dropValF (Bool.rec true false ka) x (dropValF (Bool.rec true false kb) y ws))
  have agree : ∀ w ∈ bank, w.testBit r = w.testBit s := by
    intro w hw
    change w ∈ insertSortedF (binOpF m op x y) _ at hw
    rw [insertSortedF_eq,insertSorted_mem] at hw
    rcases hw with heq | hw
    · rw [heq]; exact zx
    · rw [dropValF_eq,dropVal_mem] at hw
      have hyMem := hw.1
      rw [dropValF_eq,dropVal_mem] at hyMem
      by_cases ex : w = x
      · have kept : ka = true := by
          cases h : ka
          · exact False.elim (hw.2 (by rw [h]) ex)
          · rfl
        rw [ex]; exact hx kept
      by_cases ey : w = y
      · have kept : kb = true := by
          cases h : kb
          · exact False.elim (hyMem.2 (by rw [h]) ey)
          · rfl
        rw [ey]; exact hy kept
      apply hrest w
      rw [dropValF_eq,dropVal_mem,dropValF_eq,dropVal_mem]
      exact ⟨⟨hyMem.1,fun _ => ey⟩,fun _ => ex⟩
  change dagLocalF m g [] (f,bank,hist) = true
  have part : dagPartF bank g (Nat.xor m g) = false := by
    rw [dagPartF_eq]
    exact fpDagPartPair hr.2 hs.2 agree
  unfold dagLocalF
  dsimp only
  rw [part]
  cases Nat.blt (Nat.add f 1) (lenN bank) <;> rfl

theorem clashEarly_eq {m g x y op keep f : Nat} {ws : List Nat} {hist : List (Nat × Nat × Nat)}
    (rule : Nat → ReplayState → Bool)
    (closed : ∀ t st, dagLocalF m g [] st = true → rule t st = true) (tok : Nat) :
    let ch : ReplayState := (f, insertSortedF (binOpF m op x y)
      (dropValF (Bool.rec true false (Nat.beq (Nat.land keep 1) 1)) x
        (dropValF (Bool.rec true false (Nat.beq (Nat.land (Nat.shiftRight keep 1) 1) 1)) y ws)), hist)
    Bool.rec (rule tok ch) true (clashFlag (pairClashes x y (dropValF true x (dropValF true y ws))
      (Nat.land m g) (Nat.land m (Nat.xor m g))) op keep) = rule tok ch := by
  dsimp only
  cases hit : clashFlag (pairClashes x y (dropValF true x (dropValF true y ws))
      (Nat.land m g) (Nat.land m (Nat.xor m g))) op keep
  · rfl
  · exact (closed _ _ (pairClash_close hit)).symm

theorem clashChildren_eq (m g : Nat) (rule : Nat → ReplayState → Bool) (st : ReplayState)
    (closed : ∀ t s, dagLocalF m g [] s = true → rule t s = true) :
    clashChildren m g rule st = oracleChildren m g rule st := by
  rcases st with ⟨f,ws,hist⟩
  simp only [clashChildren, oracleChildren, forceW_eq, forceWs_eq, clashEarly_eq rule closed]


theorem simple_or (m g : Nat) (bounds : List ReplayBound) (ch : ReplayState) :
    dagLocalF m g bounds ch = (dagLocalF m g [] ch || knownClosesF bounds ch) := by
  rcases ch with ⟨fuel, ws, hist⟩
  unfold dagLocalF
  dsimp only
  cases Nat.blt (Nat.add fuel 1) (lenN ws) <;> cases dagPartF ws g (Nat.xor m g) <;> rfl

def withPickedBounds (bounds : List ReplayBound) : List Nat → (List ReplayBound → Bool) → Bool
  | [], k => k []
  | j :: rest, k =>
    match bounds[j]? with
    | none => withPickedBounds bounds rest k
    | some b => withPickedBounds bounds rest (fun bs => k (b :: bs))

theorem withPickedBounds_eq (bounds : List ReplayBound) (picks : List Nat)
    (k : List ReplayBound → Bool) :
    withPickedBounds bounds picks k = k (pickedBounds bounds picks) := by
  induction picks generalizing k with
  | nil => rfl
  | cons j rest ih =>
    unfold withPickedBounds
    cases h : bounds[j]? <;> simp [pickedBounds, h, ih]


def forceHistory : List (Nat × Nat × Nat) → (List (Nat × Nat × Nat) → Bool) → Bool
  | [], k => k []
  | (w,x,y) :: tail, k => forceW w fun v => forceW x fun a => forceW y fun b =>
      forceHistory tail fun rest => k ((v,a,b) :: rest)

theorem forceHistory_eq (ht : List (Nat × Nat × Nat)) (k : List (Nat × Nat × Nat) → Bool) :
    forceHistory ht k = k ht := by
  induction ht generalizing k with
  | nil => rfl
  | cons head tail ih =>
    rcases head with ⟨w,x,y⟩
    simp only [forceHistory, forceW_eq, ih]

theorem fixedImageDrop {f : Nat → Nat} {P : Nat → Prop} {S : Finset Nat} {x : Nat}
    (hinj : ∀ {a b}, P a → P b → f a = f b → a = b)
    (hS : ∀ y ∈ S, P y) (hx : P x) (d : Bool) :
    (dropIf d x S).image f = dropIf d (f x) (S.image f) := by
  cases d
  · rfl
  · simp only [dropIf, ite_true]
    ext y
    simp only [Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨v, ⟨hne, hmem⟩, rfl⟩
      exact ⟨fun h => hne (hinj (hS _ hmem) hx h), v, hmem, rfl⟩
    · rintro ⟨hne, v, hmem, rfl⟩
      exact ⟨v, ⟨fun h => hne (congrArg f h), hmem⟩, rfl⟩

theorem liveByNormalizedMap {f : Nat → Nat} {P : Nat → Prop} {mask goal k : Nat}
    (hzero : f 0 = 0) (hzP : P 0) (hgoal : f goal = goal)
    (hinj : ∀ {a b}, P a → P b → f a = f b → a = b)
    (hP : ∀ op a b, P (binOp mask op a b))
    (hgate : ∀ op a b, f (binOp mask op a b) = 0 ∨ f (binOp mask op a b) = f a ∨
      f (binOp mask op a b) = f b ∨ ∃ op' < 4, f (binOp mask op a b) = binOp mask op' (f a) (f b))
    {S : Finset Nat} (hLive : LiveBin mask goal k S) (hS : ∀ w ∈ S, P w) :
    LiveBin mask goal k (S.image f) := by
  induction hLive with
  | done => simpa only [Finset.image_singleton, hgoal] using (LiveBin.done (mask := mask) (goal := goal))
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB tail ih =>
    let v := binOp mask op a b
    have hpv : P v := hP op a b
    have hz' : f v ≠ 0 := fun h => hz (hinj hpv hzP (h.trans hzero.symm))
    have hf' : f v ∉ S.image f := by
      rintro h
      obtain ⟨w, hw, he⟩ := Finset.mem_image.mp h
      have eq : w = v := hinj (hS _ hw) hpv he
      have hvS : v ∈ S := eq ▸ hw
      exact hf hvS
    have hfa := Finset.mem_image_of_mem f ha
    have hfb := Finset.mem_image_of_mem f hb
    rcases hgate op a b with h | h | h | ⟨op', hop', heq⟩
    · exact (hz' h).elim
    · exact (hf' (h ▸ hfa)).elim
    · exact (hf' (h ▸ hfb)).elim
    · refine LiveBin.step hfa hfb (fun h => hab (hinj (hS a ha) (hS b hb) h))
        (fun h => ha0 (hinj (hS a ha) hzP (h.trans hzero.symm)))
        (fun h => hb0 (hinj (hS b hb) hzP (h.trans hzero.symm))) hop'
        (heq ▸ hz') (heq ▸ hf') keepA keepB ?_
      have small : ∀ y ∈ dropIf (!keepB) b S, P y :=
        fun y hy => hS y (dropIf_subset _ _ _ hy)
      have inter := fixedImageDrop hinj small (hS _ ha) (!keepA)
      have inner := fixedImageDrop hinj hS (hS _ hb) (!keepB)
      have htail := ih (by
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hpv
        · exact small _ (dropIf_subset _ _ _ hy))
      simpa only [Finset.image_insert, inter, inner, heq] using htail

theorem doubleSelect64 (rows : List Nat) (hlen : rows.length = 64)
    (hback : ∀ i : Fin 64, (rows[i.val]?).bind (fun j => rows[j]?) = some i.val)
    (w : Nat) : selectRows (selectRows w rows) rows = w &&& fullMask := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [selectRows_testBit, Nat.testBit_and]
  have hm : fullMask.testBit i = decide (i < 64) := by
    change (2 ^ 64 - 1 : Nat).testBit i = _
    rw [Nat.testBit_two_pow_sub_one]
  rw [hm]
  by_cases hi : i < 64
  · have hb := hback ⟨i, hi⟩
    change (rows[i]?).bind (fun j => rows[j]?) = some i at hb
    cases hj : rows[i]? with
    | none => simp [hj] at hb
    | some j =>
      simp only [hj, Option.bind_some] at hb
      simp [selectRows_testBit, hb, hi]
  · have hnone : rows[i]? = none := List.getElem?_eq_none (by omega)
    simp [hnone, hi]

theorem normalizedRowGate {rows : List Nat} {m : Nat} (hm : selectRows m rows = m) (op a b : Nat) :
    rowProjection rows m (binOp m op a b) = 0 ∨
    rowProjection rows m (binOp m op a b) = rowProjection rows m a ∨
    rowProjection rows m (binOp m op a b) = rowProjection rows m b ∨
    ∃ op' < 4, rowProjection rows m (binOp m op a b) = binOp m op' (rowProjection rows m a) (rowProjection rows m b) := by
  have hs := canon_sub_binOp (op := op) (a := selectRows a rows) (b := selectRows b rows) (masked_self m)
  rw [binOp_canon, ← rowProjection_op hm] at hs
  exact hs

theorem normalizedLive64 {rows : List Nat} (hlen : rows.length = 64)
    (hback : ∀ i : Fin 64, (rows[i.val]?).bind (fun j => rows[j]?) = some i.val)
    (hm : selectRows fullMask rows = fullMask) {goal k : Nat} {S : Finset Nat}
    (hgoal : rowProjection rows fullMask goal = goal) (hLive : LiveBin fullMask goal k S)
    (hS : ∀ w ∈ S, canon fullMask w = w) :
    LiveBin fullMask goal k (S.image (rowProjection rows fullMask)) := by
  let f := rowProjection rows fullMask
  have hinv (w : Nat) : f (f w) = canon fullMask w := by
    change rowProjection rows fullMask (canon fullMask (selectRows w rows)) = _
    rw [rowProjection_canon hm]
    change canon fullMask (selectRows (selectRows w rows) rows) = _
    rw [doubleSelect64 rows hlen hback, canon_land]
  apply liveByNormalizedMap (P := fun w => canon fullMask w = w)
    (rowProjection_zero rows fullMask) (canon_zero _) hgoal ?_ (binOp_canon _) (normalizedRowGate hm) hLive hS
  intro a b ha hb he
  change f a = f b at he
  simpa only [hinv, ha, hb] using congrArg f he

def dualRows (_ : Nat) : List Nat := [63, 61, 62, 60, 59, 57, 58, 56, 55, 53, 54, 52, 51, 49, 50, 48, 47, 45, 46, 44, 43, 41, 42, 40, 39, 37, 38, 36, 35, 33, 34, 32, 31, 29, 30, 28, 27, 25, 26, 24, 23, 21, 22, 20, 19, 17, 18, 16, 15, 13, 14, 12, 11, 9, 10, 8, 7, 5, 6, 4, 3, 1, 2, 0]

theorem dualRows_len (tag : Nat) : (dualRows tag).length = 64 := by
  unfold dualRows; decide +kernel

theorem dualRows_inv (tag : Nat) :
    ∀ i : Fin 64, ((dualRows tag)[i.val]?).bind (fun j => (dualRows tag)[j]?) = some i.val := by
  unfold dualRows; decide +kernel

theorem dualRows_mask (tag : Nat) : selectRows fullMask (dualRows tag) = fullMask := by
  unfold dualRows; decide +kernel


abbrev LaneStep := Nat × Nat × Nat × Nat

def laneMove (s : LaneStep) (w : Nat) : Nat :=
  (w &&& s.2.1) ||| ((w >>> s.1) &&& s.2.2.1) ||| ((w <<< s.1) &&& s.2.2.2)

def laneSlots (s : LaneStep) (i : Nat) : List Nat :=
  (if s.2.1.testBit i then [i] else []) ++
  (if s.2.2.1.testBit i then [s.1+i] else []) ++
  (if s.2.2.2.testBit i && decide (s.1 ≤ i) then [i-s.1] else [])

theorem laneMove_bit (s : LaneStep) (w i : Nat) :
    (laneMove s w).testBit i = (laneSlots s i).any w.testBit := by
  simp only [laneMove, laneSlots, Nat.testBit_or, Nat.testBit_and,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight, List.any_append]
  cases e1 : s.2.1.testBit i <;> cases e2 : s.2.2.1.testBit i <;>
    cases e3 : s.2.2.2.testBit i <;> by_cases h : s.1 ≤ i <;> simp [h]

def applyLanes : List LaneStep → Nat → Nat
  | [], w => w
  | s :: ss, w => forceW (applyLanes ss w) (laneMove s)

def traceLanes : List LaneStep → Nat → List Nat
  | [], i => [i]
  | s :: ss, i => (laneSlots s i).flatMap (traceLanes ss)

theorem applyLanes_bit (ss : List LaneStep) (w i : Nat) :
    (applyLanes ss w).testBit i = (traceLanes ss i).any w.testBit := by
  induction ss generalizing i with
  | nil => simp [applyLanes, traceLanes]
  | cons s ss ih =>
    simp only [applyLanes, forceW_eq, laneMove_bit, traceLanes, List.any_flatMap]
    exact congrArg (List.any (laneSlots s i)) (funext (fun j => ih j))

def dualLanes (_ : Nat) : List LaneStep := [(0x1, 0x9999999999999999, 0x2222222222222222, 0x4444444444444444), (0x1, 0x0, 0x5555555555555555, 0xaaaaaaaaaaaaaaaa), (0x2, 0x0, 0x3333333333333333, 0xcccccccccccccccc), (0x4, 0x0, 0xf0f0f0f0f0f0f0f, 0xf0f0f0f0f0f0f0f0), (0x8, 0x0, 0xff00ff00ff00ff, 0xff00ff00ff00ff00), (0x10, 0x0, 0xffff0000ffff, 0xffff0000ffff0000), (0x20, 0x0, 0xffffffff, 0xffffffff00000000)]

theorem dualLanes_rows (tag : Nat) : ∀ i : Fin 64,
    traceLanes (dualLanes tag) i.val = ((dualRows tag)[i.val]?).toList := by
  unfold dualLanes dualRows; decide +kernel

def fastDual (tag w : Nat) : Nat := canon fullMask (applyLanes (dualLanes tag) w)

theorem fastDual_eq (tag : Nat) : fastDual tag = rowProjection (dualRows tag) fullMask := by
  funext w
  unfold fastDual rowProjection
  rw [← canon_land fullMask (applyLanes (dualLanes tag) w)]
  congr 1; apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and, applyLanes_bit, selectRows_testBit]
  have hm : fullMask.testBit i = decide (i < 64) := Nat.testBit_two_pow_sub_one 64 i
  rw [hm]
  by_cases hi : i < 64
  · rw [dualLanes_rows tag ⟨i,hi⟩]
    cases (dualRows tag)[i]? <;> simp [hi]
  · have hn : (dualRows tag)[i]? = none := List.getElem?_eq_none (by rw [dualRows_len]; omega)
    simp [hn, hi]

def sameMovedBank (f : Nat → Nat) (saved current : List Nat) : Bool :=
  let mapped := current.map f
  allN (fun w => memN w mapped) saved && allN (fun w => memN w saved) mapped

theorem sameMovedBank_spec {f : Nat → Nat} {saved current : List Nat}
    (h : sameMovedBank f saved current = true) : current.toFinset.image f = saved.toFinset := by
  simp only [sameMovedBank, Bool.and_eq_true, allN_eq, List.all_eq_true, memN_eq, List.contains_iff_mem] at h
  ext w
  constructor
  · intro hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact List.mem_toFinset.mpr (h.2 _ (List.mem_map.mpr ⟨v, List.mem_toFinset.mp hv, rfl⟩))
  · intro hx
    obtain ⟨v, hv, eq⟩ := List.mem_map.mp (h.1 _ (List.mem_toFinset.mp hx))
    exact Finset.mem_image.mpr ⟨v, List.mem_toFinset.mpr hv, eq⟩


theorem knownOne {b : ReplayBound} (ch : ReplayState) {bs : List ReplayBound}
    (hb : b ∈ bs) (ok : boundClosesF ch b = true) : knownClosesF bs ch = true := by
  induction bs with
  | nil => simp at hb
  | cons x xs ih =>
    change Bool.rec (knownClosesF xs ch) true (boundClosesF ch x) = true
    rcases List.mem_cons.mp hb with rfl | hs
    · rw [ok]
    · rw [ih hs]; cases boundClosesF ch x <;> rfl

def selectedCut (bs : List ReplayBound) (j : Option Nat) (ch : ReplayState) : Bool :=
  match j with
  | none => false
  | some i => match bs[i]? with
    | none => false
    | some b => boundClosesF ch b

theorem selectedCut_covers (bs : List ReplayBound) (j : Option Nat) (ch : ReplayState)
    (h : selectedCut bs j ch = true) : knownClosesF bs ch = true := by
  cases j with
  | none => contradiction
  | some i =>
    cases he : bs[i]? with
    | none => simp [selectedCut, he] at h
    | some b =>
      exact knownOne ch (List.mem_of_getElem? he) (by simpa [selectedCut, he] using h)

def routeMix (x : Nat) : Nat :=
  forceW (((x ^^^ (x >>> 16)) * 0x85ebca6b) &&& 0xffffffff) fun y =>
    forceW (((y ^^^ (y >>> 13)) * 0xc2b2ae35) &&& 0xffffffff) fun z => z ^^^ (z >>> 16)

def routeLookup (m seed width cells tok : Nat) : Option Nat :=
  forceW (routeMix (tok + (seed <<< 11))) fun h =>
    let read := fun i => cells >>> (width * (i % m))
    some (((read h) ^^^ (read (h >>> 11)) ^^^ (read (h >>> 21))) &&& ((1 <<< width)-1))

def withRouter (descriptor deck : Nat → Nat) (i : Nat) (k : (Nat → Option Nat) → Bool) : Bool :=
  forceW (descriptor i) fun h =>
    if h = 0 then k (fun _ => some 0) else
    forceW (h &&& 7) fun width => forceW ((h >>> 3) &&& 255) fun m =>
      forceW ((h >>> 11) &&& 31) fun seed =>
        forceW (((deck (i >>> 5)) >>> (h >>> 16)) &&& ((1 <<< (m*width))-1)) fun cells =>
          k (routeLookup m seed width cells)

def thinChild (bs : List ReplayBound) (hint : Nat → Option Nat)
    (ref : Nat → ReplayState → Bool) (tok : Nat) (ch : ReplayState) : Bool :=
  Bool.rec (Bool.rec (knownClosesF bs ch) true (ref tok ch)) true (selectedCut bs (hint tok) ch)

theorem replayRec_mono (test : Bool) {a b c d : Bool}
    (left : a = true → b = true) (right : c = true → d = true) :
    Bool.rec a c test = true → Bool.rec b d test = true := by
  cases test
  · exact left
  · exact right

theorem replayAnd_mono {a b c d : Bool} (left : a = true → b = true) (right : c = true → d = true) :
    Bool.rec false c a = true → Bool.rec false d b = true := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

def replayRange (steps : Nat) (f : Nat → Bool) (lo hi : Nat) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ next a b =>
      Bool.rec true
        (let mid := Nat.shiftRight (Nat.add a b) 1
         Bool.rec (Bool.rec false (next mid b) (next a mid)) (f a) (Nat.beq a mid))
        (Nat.blt a b)) steps) lo hi

theorem replayRange_mono (steps : Nat) {a b : Nat} {f g : Nat → Bool}
    (point : ∀ i, f i = true → g i = true) :
    replayRange steps f a b = true → replayRange steps g a b = true := by
  induction steps generalizing a b with
  | zero => exact id
  | succ n ih =>
    change Bool.rec true (Bool.rec
      (Bool.rec false (replayRange n f ((a+b) >>> 1) b) (replayRange n f a ((a+b) >>> 1)))
      (f a) (Nat.beq a ((a+b) >>> 1))) (Nat.blt a b) = true →
      Bool.rec true (Bool.rec
      (Bool.rec false (replayRange n g ((a+b) >>> 1) b) (replayRange n g a ((a+b) >>> 1)))
      (g a) (Nat.beq a ((a+b) >>> 1))) (Nat.blt a b) = true
    exact replayRec_mono _ id (replayRec_mono _ (replayAnd_mono ih ih) (point a))

theorem replayBlock_mono {lo hi : Nat} {f g : Nat → Bool}
    (point : ∀ i, f i = true → g i = true) :
    treeBlockF lo hi f = true → treeBlockF lo hi g = true :=
  replayRange_mono (Nat.add (Nat.sub hi lo) 1) point

theorem clashChildren_mono (m g : Nat) {u v : Nat → ReplayState → Bool}
    (st : ReplayState) (point : ∀ tok ch, u tok ch = true → v tok ch = true) :
    clashChildren m g u st = true → clashChildren m g v st = true := by
  rcases st with ⟨f,ws,hist⟩
  simp only [clashChildren, forceW_eq, forceWs_eq]
  refine replayRec_mono _ ?_ id
  refine replayRec_mono _ ?_ id
  refine replayRec_mono _ id ?_
  apply replayBlock_mono; intro a
  apply replayBlock_mono; intro b
  apply replayBlock_mono; intro op
  refine replayRec_mono _ ?_ id
  refine replayRec_mono _ ?_ id
  apply replayBlock_mono; intro keep
  refine replayRec_mono _ ?_ id
  exact replayRec_mono _ (point _ _) id

theorem thinChild_sound (m g : Nat) (bs : List ReplayBound) (hint : Nat → Option Nat)
    (ref : Nat → ReplayState → Bool) (tok : Nat) (st : ReplayState)
    (ok : thinChild bs hint ref tok st = true) :
    Bool.rec (dagLocalF m g bs st) true (ref tok st) = true := by
  unfold thinChild at ok
  cases r : ref tok st
  · change dagLocalF m g bs st = true
    rw [simple_or, Bool.or_eq_true]
    right
    cases h : selectedCut bs (hint tok) st
    · simpa only [r,h] using ok
    · exact selectedCut_covers bs (hint tok) st h
  · rfl

theorem clashChildren_sound (m g : Nat) (bs : List ReplayBound) (hint : Nat → Option Nat)
    (ref : Nat → ReplayState → Bool) (st : ReplayState)
    (ok : clashChildren m g (thinChild bs hint ref) st = true) :
    dagCheckChildrenF m g bs ref st = true := by
  let v : Nat → ReplayState → Bool := fun tok ch => Bool.rec (dagLocalF m g bs ch) true (ref tok ch)
  have good : clashChildren m g v st = true :=
    clashChildren_mono m g st (thinChild_sound m g bs hint ref) ok
  have closed : ∀ tok ch, dagLocalF m g [] ch = true → v tok ch = true := by
    intro tok ch h
    dsimp only [v]
    rw [simple_or, h]
    cases ref tok ch <;> rfl
  rw [clashChildren_eq m g v st closed] at good
  exact good

def clashNode (m g : Nat) (bs : List ReplayBound) (st : Nat → Option ReplayState)
    (ref : Nat → Nat → ReplayState → Bool) (hint : Nat → Option Nat) (i : Nat) : Bool :=
  match st i with
  | none => false
  | some (fuel,ws,hist) => forceW fuel fun f => forceWs ws fun bank => forceHistory hist fun hx =>
      clashChildren m g (thinChild bs hint (ref (Nat.add i 1))) (f,bank,hx)

theorem clashNode_sound (m g : Nat) (bs : List ReplayBound) (st : Nat → Option ReplayState)
    (ref : Nat → Nat → ReplayState → Bool) (hint : Nat → Option Nat) (i : Nat)
    (ok : clashNode m g bs st ref hint i = true) : dagCheckNodeWithF m g bs st ref i = true := by
  unfold clashNode at ok
  unfold dagCheckNodeWithF
  cases h : st i with
  | none => simp [h] at ok
  | some s =>
    obtain ⟨fuel,ws,hist⟩ := s
    rw [h] at ok
    simp only [forceW_eq,forceWs_eq,forceHistory_eq] at ok
    exact clashChildren_sound m g bs hint _ _ ok

def clashRouted (m g : Nat) (bs : List ReplayBound) (st : Nat → Option ReplayState)
    (ref : Nat → Nat → ReplayState → Bool) (descriptor deck : Nat → Nat) (i : Nat) : Bool :=
  withRouter descriptor deck i fun hint => clashNode m g bs st ref hint i

theorem clashRouted_sound (m g : Nat) (bs : List ReplayBound) (st : Nat → Option ReplayState)
    (ref : Nat → Nat → ReplayState → Bool) (descriptor deck : Nat → Nat) (i : Nat)
    (ok : clashRouted m g bs st ref descriptor deck i = true) : dagCheckNodeWithF m g bs st ref i = true := by
  unfold clashRouted withRouter at ok
  simp only [forceW_eq] at ok
  split at ok <;> exact clashNode_sound m g bs st ref _ i ok


def fixedGoal : Nat := 0x11515571337377f

theorem directFacts : ∀ t : Fin 6, moveWord t.val fullMask = fullMask ∧
    moveSlot t.val 63 = 63 ∧ moveWord t.val fixedGoal = fixedGoal := by decide +kernel

theorem flippedGoal : rowProjection (dualRows 6) fullMask fixedGoal = fixedGoal := by decide +kernel

def twelveMove (t : Nat) : Nat → Nat :=
  if t < 6 then moveWord t else fun w => moveWord (t-6) (fastDual 6 w)

theorem twelveLive {t k : Nat} (ht : t < 12) {S : Finset Nat}
    (h : LiveBin fullMask fixedGoal k S) (hcan : ∀ w ∈ S, canon fullMask w = w) :
    LiveBin fullMask fixedGoal k (S.image (twelveMove t)) := by
  by_cases hp : t < 6
  · obtain ⟨hm,hi,hg⟩ := directFacts ⟨t,hp⟩
    simpa only [twelveMove, if_pos hp] using (moveLiveBin (top := 63) (by decide +kernel) hm hi hg h)
  · have hi' : t-6 < 6 := by omega
    obtain ⟨hm,hi,hg⟩ := directFacts ⟨t-6,hi'⟩
    have hflip := normalizedLive64 (dualRows_len 6) (dualRows_inv 6) (dualRows_mask 6) flippedGoal h hcan
    have both := moveLiveBin (top := 63) (by decide +kernel) hm hi hg hflip
    simpa only [twelveMove, if_neg hp, fastDual_eq, Finset.image_image, Function.comp_def] using both

def strictMovedBank (f : Nat → Nat) (saved current : List Nat) : Bool :=
  forceWs (current.map f) fun mapped => allN (fun w => memN w mapped) saved &&
    allN (fun w => memN w saved) mapped

theorem strictMovedBank_eq (f : Nat → Nat) (saved current : List Nat) :
    strictMovedBank f saved current = sameMovedBank f saved current := forceWs_eq _ _

def groupRef (n : Nat) (states : Nat → Option ReplayState) (links : Nat → Nat → Option Nat)
    (p tok : Nat) (cur : ReplayState) : Bool :=
  match links p tok with
  | none => false
  | some word => forceW word fun code =>
    let d := code >>> 4
    let t := code &&& 15
    if d < n then
      match states d with
      | none => false
      | some st => Nat.beq st.1 cur.1 &&
          (if t = 0 then eqListN st.2.1 cur.2.1
           else decide (t < 12) && allN (fun w => Nat.beq (canonF fullMask w) w) cur.2.1 &&
             strictMovedBank (twelveMove t) st.2.1 cur.2.1)
    else false

theorem groupTransfers (n : Nat) (states : Nat → Option ReplayState) (links : Nat → Nat → Option Nat) :
    RefTransfers fullMask fixedGoal n states (groupRef n states links) := by
  intro p tok cur h
  cases he : links p tok with
  | none => simp [groupRef, he] at h
  | some word =>
    let d := word >>> 4
    let t := word &&& 15
    change groupRef n states links p tok cur = true at h
    simp only [groupRef, he, forceW_eq, ← show d = word >>> 4 from rfl,
      ← show t = word &&& 15 from rfl] at h
    by_cases hd : d < n
    · simp only [if_pos hd] at h
      cases hs : states d with
      | none => simp [hs] at h
      | some st =>
        simp only [hs, Bool.and_eq_true, Nat.beq_eq] at h
        refine ⟨d, st, hd, hs, h.1, ?_⟩
        have hm := h.2
        by_cases hz : t = 0
        · simp only [if_pos hz, eqListN_eq, beq_iff_eq] at hm
          intro k hk
          rwa [hm]
        · simp only [if_neg hz, Bool.and_eq_true, decide_eq_true_eq, allN_eq, List.all_eq_true,
            Nat.beq_eq, canonF_eq, strictMovedBank_eq] at hm
          intro k hk
          rw [← sameMovedBank_spec hm.2]
          exact twelveLive hm.1.1 hk (fun w hw => hm.1.2 w (List.mem_toFinset.mp hw))
    · simp [hd] at h

theorem lowerDagGroupF {fuel count : Nat} {stock : List Nat}
    {bounds : List ReplayBound} {picks : Nat → List Nat}
    {forest : Nat → Nat × Nat} {links : Nat → Nat → Option Nat}
    (hgm : Masked fullMask fixedGoal) (hgnz : fixedGoal ≠ 0)
    (hcs : stock.all (fun w => Nat.beq (canon fullMask w) w) = true)
    (snd : stock.Nodup)
    (hknown : KnownBin bounds) (hsub : ∀ b ∈ bounds, fullMask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 fixedGoal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hroots : dagCheckRootsF fullMask fixedGoal bounds
      (groupRef count (dagTraceF fullMask stock fuel forest) links 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeWithF fullMask fixedGoal (pickedBounds bounds (picks i))
      (dagTraceF fullMask stock fuel forest)
      (groupRef count (dagTraceF fullMask stock fuel forest) links) i = true) :
    LowerBin fullMask stock fixedGoal (fuel + 1) := by
  have htr : dagTraceF fullMask stock fuel forest = dagTrace fullMask stock fuel forest := by
    funext i; exact dagTraceF_eq fullMask stock fuel forest i
  rw [htr, dagCheckRootsF_eq hgoals] at hroots
  rw [htr] at hnodes
  refine lowerDagWithPicks (picked := fun i => pickedBounds bounds (picks i))
    (groupTransfers _ _ _) hgm hgnz hcs snd hknown hsub ?_ ?_ hroots ?_
  · intro i b hb; exact hknown b (memPickedBounds hb)
  · intro i b hb; exact hsub b (memPickedBounds hb)
  · intro i hlo hhi
    have hg : ∀ b ∈ pickedBounds bounds (picks i), canon b.1 fixedGoal = b.2.2.2 ∧ b.2.2.2 ≠ 0 :=
      fun b hb => hgoals b (memPickedBounds hb)
    simpa only [dagCheckNodeWithF_eq hg] using hnodes i hlo hhi

def unpackRows (size word : Nat) : List Nat :=
  (Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun _ rest v => (v &&& 63) :: rest (v >>> 6)) size) word

def projectionOK (mask cut goal smallGoal : Nat) (big small rows : List Nat) : Bool :=
  Nat.beq (selectRows mask rows) cut &&
    (big.all (fun w => availB small (rowProjection rows cut w)) &&
       Nat.beq (rowProjection rows cut goal) smallGoal)

theorem lowerByCheckedRows {mask cut goal smallGoal n : Nat} {big small : List Nat} (rows : List Nat)
    (cert : LowerBin cut small smallGoal n) (ok : projectionOK mask cut goal smallGoal big small rows = true) :
    LowerBin mask big goal n := by
  simp only [projectionOK, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, availB_spec] at ok
  exact lowerByRows rows ok.1 ok.2.1 ok.2.2 cert

def f_1761 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def l_1761 : Nat → Nat → Option Nat := unpackLinksF 0x8608608608608608607e47e07e07e07e07647607607607607607606e46e06e06e06e06646606606226206205e25c15c05a15a05a05a05a05a05a05245205205205204a44a04a04624604604224014003e13e03e03a23a03a0362341340321038001 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 12 5 10 6 6
def m_1761 : Nat := 0xaaaaaaaa
def s_1761 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_1761 : Nat := 0x222222a
def bds_1761 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_1761 : KnownBin bds_1761 := by
  intro b hb
  simp [bds_1761] at hb
theorem sub_1761 : ∀ b ∈ bds_1761, m_1761 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_1761] at hb
theorem gl_1761 : ∀ b ∈ bds_1761, canon b.1 g_1761 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_1761] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1761 : dagCheckRootsF m_1761 g_1761 bds_1761 (dagRefF 64 (dagTraceF m_1761 s_1761 5 f_1761) l_1761 0) s_1761 5 = true := by decide +kernel
def node_1761 : Nat → Bool := dagCheckNodeF m_1761 g_1761 bds_1761 64 (dagTraceF m_1761 s_1761 5 f_1761) l_1761
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1761_0 : treeBlockF 0 64 node_1761 = true := by decide +kernel
theorem nc_1761 : ∀ j, 0 ≤ j → j < 64 → node_1761 j = true :=
  (certBlock nb_1761_0)
theorem lb_1761 : LowerBin m_1761 s_1761 g_1761 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1761 sub_1761 gl_1761 rc_1761 nc_1761

def m_1770 : Nat := 0xff00ff00
def s_1770 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_1770 : Nat := 0x13003700
theorem lb_1770 : LowerBin m_1770 s_1770 g_1770 6 :=
  lowerByCheckedRows (unpackRows 32 0x7c07407807006c06406806003c03403803002c0240280200) lb_1761 (by decide +kernel)

def f_15 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def l_15 : Nat → Nat → Option Nat := unpackLinksF 0x9 0x7 2 1 3 1 2
def m_15 : Nat := 0xcccc
def s_15 : List Nat := [0x4444, 0xc0c, 0xcc]
def g_15 : Nat := 0x44c
def bds_15 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_15 : KnownBin bds_15 := by
  intro b hb
  simp [bds_15] at hb
theorem sub_15 : ∀ b ∈ bds_15, m_15 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_15] at hb
theorem gl_15 : ∀ b ∈ bds_15, canon b.1 g_15 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_15] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_15 : dagCheckRootsF m_15 g_15 bds_15 (dagRefF 1 (dagTraceF m_15 s_15 3 f_15) l_15 0) s_15 3 = true := by decide +kernel
def node_15 : Nat → Bool := dagCheckNodeF m_15 g_15 bds_15 1 (dagTraceF m_15 s_15 3 f_15) l_15
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_15_0 : treeBlockF 0 1 node_15 = true := by decide +kernel
theorem nc_15 : ∀ j, 0 ≤ j → j < 1 → node_15 j = true :=
  (certBlock nb_15_0)
theorem lb_15 : LowerBin m_15 s_15 g_15 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_15 sub_15 gl_15 rc_15 nc_15

def f_1742 : Nat → Nat × Nat := fun _ => (0, 0)
def l_1742 : Nat → Nat → Option Nat := fun _ _ => none
def m_1742 : Nat := 0xffff
def s_1742 : List Nat := [0x5555, 0x3333, 0xf0f, 0xff]
def g_1742 : Nat := 0x377f
def bds_1742 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
theorem kn_1742 : KnownBin bds_1742 := by
  intro b hb
  simp only [bds_1742, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_15
theorem sub_1742 : ∀ b ∈ bds_1742, m_1742 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1742, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_1742 : ∀ b ∈ bds_1742, canon b.1 g_1742 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1742, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1742 : dagCheckRootsF m_1742 g_1742 bds_1742 (dagRefF 0 (dagTraceF m_1742 s_1742 4 f_1742) l_1742 0) s_1742 4 = true := by decide +kernel
def node_1742 : Nat → Bool := dagCheckNodeF m_1742 g_1742 bds_1742 0 (dagTraceF m_1742 s_1742 4 f_1742) l_1742
theorem nc_1742 : ∀ j, 0 ≤ j → j < 0 → node_1742 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_1742 : LowerBin m_1742 s_1742 g_1742 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1742 sub_1742 gl_1742 rc_1742 nc_1742

def m_42 : Nat := 0xcc00cc
def s_42 : List Nat := [0x440044, 0xc000c, 0xcc]
def g_42 : Nat := 0x4004c
theorem lb_42 : LowerBin m_42 s_42 g_42 4 :=
  lowerByCheckedRows (unpackRows 16 0x5d60004d20001c60000c2000) lb_15 (by decide +kernel)

def f_1743 : Nat → Nat × Nat := fun _ => (0, 0)
def l_1743 : Nat → Nat → Option Nat := fun _ _ => none
def m_1743 : Nat := 0xff00ff
def s_1743 : List Nat := [0x550055, 0x330033, 0xf000f, 0xff]
def g_1743 : Nat := 0x37007f
def bds_1743 : List (Nat × List Nat × Nat × Nat) := [(m_42, s_42, 4, g_42)]
theorem kn_1743 : KnownBin bds_1743 := by
  intro b hb
  simp only [bds_1743, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_42
theorem sub_1743 : ∀ b ∈ bds_1743, m_1743 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1743, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_1743 : ∀ b ∈ bds_1743, canon b.1 g_1743 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1743, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1743 : dagCheckRootsF m_1743 g_1743 bds_1743 (dagRefF 0 (dagTraceF m_1743 s_1743 4 f_1743) l_1743 0) s_1743 4 = true := by decide +kernel
def node_1743 : Nat → Bool := dagCheckNodeF m_1743 g_1743 bds_1743 0 (dagTraceF m_1743 s_1743 4 f_1743) l_1743
theorem nc_1743 : ∀ j, 0 ≤ j → j < 0 → node_1743 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_1743 : LowerBin m_1743 s_1743 g_1743 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1743 sub_1743 gl_1743 rc_1743 nc_1743

def m_124 : Nat := 0x3300cc00
def s_124 : List Nat := [0x11004400, 0xcc00, 0x3000c00]
def g_124 : Nat := 0x13000400
theorem lb_124 : LowerBin m_124 s_124 g_124 4 :=
  lowerByCheckedRows (unpackRows 16 0x3ce00075c0002ca000658000) lb_15 (by decide +kernel)

def m_118 : Nat := 0x3030c0c0
def s_118 : List Nat := [0x10104040, 0xc0c0, 0x3000c0]
def g_118 : Nat := 0x10300040
theorem lb_118 : LowerBin m_118 s_118 g_118 4 :=
  lowerByCheckedRows (unpackRows 16 0x3ce00075c0001c6000554000) lb_15 (by decide +kernel)

def m_104 : Nat := 0x22228888
def s_104 : List Nat := [0x8888, 0x2020808, 0x220088]
def g_104 : Nat := 0x2220008
theorem lb_104 : LowerBin m_104 s_104 g_104 4 :=
  lowerByCheckedRows (unpackRows 16 0x3dd0002d90001d50000d1000) lb_15 (by decide +kernel)

def f_1749 : Nat → Nat × Nat := unpackForestF 0xa54da4410637964d963594410537774a8840774676467d347546743105276345624560366026043b3f463e3553443d4a48243c4a3c463c26042b0a460a362e44094a2634093a1c34084a08461044083a0836041b000f 6 10
def l_1749 : Nat → Nat → Option Nat := unpackLinksF 0x8e11c1fc3f07c2f81b43606c0d45a0b40662cc15c2a1522a41482184027c4f81e13c0744e81d02b05049893024248088910202400800f11e01e00b001 0xa94d8545993581254449a4416c3958297d249e4d86459a357926184994416839341988407d347d348f4a8746824679460c3974315429301951382d286f456a454d3a292a443a6436182a602651382528534448245b4656354d4a212a444a40460c2a3c262d3825282e4426341c34104436463236294a213a184a14460c3a0836a237913771275c3b382b041b000f 11 4 10 6 5
def m_1749 : Nat := 0x3333cccc
def s_1749 : List Nat := [0x11114444, 0xcccc, 0x3030c0c, 0x3300cc]
def g_1749 : Nat := 0x1333044c
def bds_1749 : List (Nat × List Nat × Nat × Nat) := [(m_124, s_124, 4, g_124), (m_15, s_15, 4, g_15), (m_118, s_118, 4, g_118), (m_104, s_104, 4, g_104)]
theorem kn_1749 : KnownBin bds_1749 := by
  intro b hb
  simp only [bds_1749, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact lb_124
  · exact lb_15
  · exact lb_118
  · exact lb_104
theorem sub_1749 : ∀ b ∈ bds_1749, m_1749 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1749, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_1749 : ∀ b ∈ bds_1749, canon b.1 g_1749 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1749, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1749 : dagCheckRootsF m_1749 g_1749 bds_1749 (dagRefF 43 (dagTraceF m_1749 s_1749 6 f_1749) l_1749 0) s_1749 6 = true := by decide +kernel
def node_1749 : Nat → Bool := dagCheckNodeF m_1749 g_1749 bds_1749 43 (dagTraceF m_1749 s_1749 6 f_1749) l_1749
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1749_0 : treeBlockF 0 43 node_1749 = true := by decide +kernel
theorem nc_1749 : ∀ j, 0 ≤ j → j < 43 → node_1749 j = true :=
  (certBlock nb_1749_0)
theorem lb_1749 : LowerBin m_1749 s_1749 g_1749 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1749 sub_1749 gl_1749 rc_1749 nc_1749

def m_1765 : Nat := 0xcccccccc
def s_1765 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_1765 : Nat := 0x4044c
theorem lb_1765 : LowerBin m_1765 s_1765 g_1765 7 :=
  lowerByCheckedRows (unpackRows 30 0x18700038f00059700079f08300028b00049300069b000) lb_1749 (by decide +kernel)

def m_1768 : Nat := 0xf0f0f0f0
def s_1768 : List Nat := [0x50505050, 0x30303030, 0xf000f0, 0xf0f0]
def g_1768 : Nat := 0x10303070
theorem lb_1768 : LowerBin m_1768 s_1768 g_1768 6 :=
  lowerByCheckedRows (unpackRows 32 0x7c07407807005c05405805003c03403803001c0140180100) lb_1761 (by decide +kernel)

def m_75 : Nat := 0xc0c0c0c
def s_75 : List Nat := [0x4040404, 0xc000c, 0xc0c]
def g_75 : Nat := 0x4040c
theorem lb_75 : LowerBin m_75 s_75 g_75 4 :=
  lowerByCheckedRows (unpackRows 16 0x6da0004d20002ca0000c2000) lb_15 (by decide +kernel)

def f_1745 : Nat → Nat × Nat := fun _ => (0, 0)
def l_1745 : Nat → Nat → Option Nat := fun _ _ => none
def m_1745 : Nat := 0xf0f0f0f
def s_1745 : List Nat := [0x5050505, 0x3030303, 0xf000f, 0xf0f]
def g_1745 : Nat := 0x307070f
def bds_1745 : List (Nat × List Nat × Nat × Nat) := [(m_75, s_75, 4, g_75)]
theorem kn_1745 : KnownBin bds_1745 := by
  intro b hb
  simp only [bds_1745, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_75
theorem sub_1745 : ∀ b ∈ bds_1745, m_1745 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1745, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_1745 : ∀ b ∈ bds_1745, canon b.1 g_1745 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1745, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1745 : dagCheckRootsF m_1745 g_1745 bds_1745 (dagRefF 0 (dagTraceF m_1745 s_1745 4 f_1745) l_1745 0) s_1745 4 = true := by decide +kernel
def node_1745 : Nat → Bool := dagCheckNodeF m_1745 g_1745 bds_1745 0 (dagTraceF m_1745 s_1745 4 f_1745) l_1745
theorem nc_1745 : ∀ j, 0 ≤ j → j < 0 → node_1745 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_1745 : LowerBin m_1745 s_1745 g_1745 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1745 sub_1745 gl_1745 rc_1745 nc_1745

def m_136 : Nat := 0x44444444
def s_136 : List Nat := [0x4040404, 0x440044, 0x4444]
def g_136 : Nat := 0x40444
theorem lb_136 : LowerBin m_136 s_136 g_136 4 :=
  lowerByCheckedRows (unpackRows 16 0x79a00059200038a000182000) lb_15 (by decide +kernel)

def f_1752 : Nat → Nat × Nat := fun _ => (0, 0)
def l_1752 : Nat → Nat → Option Nat := fun _ _ => none
def m_1752 : Nat := 0x55555555
def s_1752 : List Nat := [0x11111111, 0x5050505, 0x550055, 0x5555]
def g_1752 : Nat := 0x11151555
def bds_1752 : List (Nat × List Nat × Nat × Nat) := [(m_136, s_136, 4, g_136)]
theorem kn_1752 : KnownBin bds_1752 := by
  intro b hb
  simp only [bds_1752, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_136
theorem sub_1752 : ∀ b ∈ bds_1752, m_1752 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1752, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_1752 : ∀ b ∈ bds_1752, canon b.1 g_1752 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1752, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1752 : dagCheckRootsF m_1752 g_1752 bds_1752 (dagRefF 0 (dagTraceF m_1752 s_1752 4 f_1752) l_1752 0) s_1752 4 = true := by decide +kernel
def node_1752 : Nat → Bool := dagCheckNodeF m_1752 g_1752 bds_1752 0 (dagTraceF m_1752 s_1752 4 f_1752) l_1752
theorem nc_1752 : ∀ j, 0 ≤ j → j < 0 → node_1752 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_1752 : LowerBin m_1752 s_1752 g_1752 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1752 sub_1752 gl_1752 rc_1752 nc_1752

def m_1771 : Nat := 0xffff0000
def s_1771 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_1771 : Nat := 0x13370000
theorem lb_1771 : LowerBin m_1771 s_1771 g_1771 6 :=
  lowerByCheckedRows (unpackRows 32 0x7c07407807006c06406806005c05405805004c0440480400) lb_1761 (by decide +kernel)

def f_2310 : Nat → Nat × Nat := unpackForestF 0x647151c5279d82127111db60555c4273980b57105c01f 4 10
def l_2310 : Nat → Nat → Option Nat := unpackLinksF 0x7971696861595851494841390e01 0x205d427815e760849db60555ce602d5f247b51e927711d027105c01f 8 3 10 4 4
def m_2310 : Nat := 0xffffffff
def s_2310 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_2310 : Nat := 0x1337377f
def bds_2310 : List (Nat × List Nat × Nat × Nat) := [(m_1770, s_1770, 6, g_1770), (m_1742, s_1742, 5, g_1742), (m_1743, s_1743, 5, g_1743), (m_1765, s_1765, 7, g_1765), (m_1768, s_1768, 6, g_1768), (m_1745, s_1745, 5, g_1745), (m_1761, s_1761, 6, g_1761), (m_1752, s_1752, 5, g_1752), (m_1771, s_1771, 6, g_1771)]
theorem kn_2310 : KnownBin bds_2310 := by
  intro b hb
  simp only [bds_2310, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_1770
  · exact lb_1742
  · exact lb_1743
  · exact lb_1765
  · exact lb_1768
  · exact lb_1745
  · exact lb_1761
  · exact lb_1752
  · exact lb_1771
theorem sub_2310 : ∀ b ∈ bds_2310, m_2310 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_2310, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_2310 : ∀ b ∈ bds_2310, canon b.1 g_2310 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_2310, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_2310 : dagCheckRootsF m_2310 g_2310 bds_2310 (dagRefF 13 (dagTraceF m_2310 s_2310 8 f_2310) l_2310 0) s_2310 8 = true := by decide +kernel
def node_2310 : Nat → Bool := dagCheckNodeF m_2310 g_2310 bds_2310 13 (dagTraceF m_2310 s_2310 8 f_2310) l_2310
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2310_0 : treeBlockF 0 13 node_2310 = true := by decide +kernel
theorem nc_2310 : ∀ j, 0 ≤ j → j < 13 → node_2310 j = true :=
  (certBlock nb_2310_0)
theorem lb_2310 : LowerBin m_2310 s_2310 g_2310 9 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2310 sub_2310 gl_2310 rc_2310 nc_2310

def m_2311 : Nat := 0xffffffff00000000
def s_2311 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_2311 : Nat := 0x115155700000000
theorem lb_2311 : LowerBin m_2311 s_2311 g_2311 9 :=
  lowerByCheckedRows (unpackRows 32 0x822863926967a2aa6bb2eb6fc32c73d36d77e3ae7bf3ef7f) lb_2310 (by decide +kernel)

def m_1986 : Nat := 0xf0f0f0f00000000
def s_1986 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_1986 : Nat := 0x105050700000000
theorem lb_1986 : LowerBin m_1986 s_1986 g_1986 6 :=
  lowerByCheckedRows (unpackRows 32 0xec0e80e40e00cc0c80c40c00ac0a80a40a008c0880840800) lb_1761 (by decide +kernel)

def m_60100 : Nat := 0xffffffff00000000
def s_60100 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xff00ff00000000, 0xffff00000000]
def g_60100 : Nat := 0x1155557700000000
theorem lb_60100 : LowerBin m_60100 s_60100 g_60100 6 :=
  lowerByCheckedRows (unpackRows 60 0xefae78000000cf2c70000000aeaa680000008e2860000000000000000000000000000000000000000000000000) lb_1986 (by decide +kernel)

def m_60101 : Nat := 0xffffffff
def s_60101 : List Nat := [0x55555555, 0x33333333, 0xff00ff, 0xffff]
def g_60101 : Nat := 0x337777ff
theorem lb_60101 : LowerBin m_60101 s_60101 g_60101 5 :=
  lowerByCheckedRows (unpackRows 28 0x6da6588208204d24508208202ca2488208200c2040) lb_1745 (by decide +kernel)

def m_297 : Nat := 0xa0a00000a0a
def s_297 : List Nat := [0x20200000202, 0xa0000000a, 0xa0a]
def g_297 : Nat := 0x20000020a
theorem lb_297 : LowerBin m_297 s_297 g_297 4 :=
  lowerByCheckedRows (unpackRows 16 0xae90008e10002c90000c1000) lb_15 (by decide +kernel)

def f_1776 : Nat → Nat × Nat := fun _ => (0, 0)
def l_1776 : Nat → Nat → Option Nat := fun _ _ => none
def m_1776 : Nat := 0xf0f00000f0f
def s_1776 : List Nat := [0x50500000505, 0x30300000303, 0xf0000000f, 0xf0f]
def g_1776 : Nat := 0x5070000070f
def bds_1776 : List (Nat × List Nat × Nat × Nat) := [(m_297, s_297, 4, g_297)]
theorem kn_1776 : KnownBin bds_1776 := by
  intro b hb
  simp only [bds_1776, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_297
theorem sub_1776 : ∀ b ∈ bds_1776, m_1776 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1776, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_1776 : ∀ b ∈ bds_1776, canon b.1 g_1776 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1776, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1776 : dagCheckRootsF m_1776 g_1776 bds_1776 (dagRefF 0 (dagTraceF m_1776 s_1776 4 f_1776) l_1776 0) s_1776 4 = true := by decide +kernel
def node_1776 : Nat → Bool := dagCheckNodeF m_1776 g_1776 bds_1776 0 (dagTraceF m_1776 s_1776 4 f_1776) l_1776
theorem nc_1776 : ∀ j, 0 ≤ j → j < 0 → node_1776 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_1776 : LowerBin m_1776 s_1776 g_1776 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1776 sub_1776 gl_1776 rc_1776 nc_1776

def m_60102 : Nat := 0xffff0000ffff
def s_60102 : List Nat := [0x555500005555, 0x333300003333, 0xff000000ff, 0xffff]
def g_60102 : Nat := 0x5577000077ff
theorem lb_60102 : LowerBin m_60102 s_60102 g_60102 5 :=
  lowerByCheckedRows (unpackRows 44 0xaeaa684104108e28604104104104104104104104104104102ca2484104100c2040) lb_1776 (by decide +kernel)

def f_1963 : Nat → Nat × Nat := fun _ => (0, 0)
def l_1963 : Nat → Nat → Option Nat := fun _ _ => none
def m_1963 : Nat := 0xc0c0c0c0c0c0c0c
def s_1963 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_1963 : Nat := 0x404040004040c
def bds_1963 : List (Nat × List Nat × Nat × Nat) := [(m_75, s_75, 4, g_75)]
theorem kn_1963 : KnownBin bds_1963 := by
  intro b hb
  simp only [bds_1963, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_75
theorem sub_1963 : ∀ b ∈ bds_1963, m_1963 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1963, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_1963 : ∀ b ∈ bds_1963, canon b.1 g_1963 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1963, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1963 : dagCheckRootsF m_1963 g_1963 bds_1963 (dagRefF 0 (dagTraceF m_1963 s_1963 4 f_1963) l_1963 0) s_1963 4 = true := by decide +kernel
def node_1963 : Nat → Bool := dagCheckNodeF m_1963 g_1963 bds_1963 0 (dagTraceF m_1963 s_1963 4 f_1963) l_1963
theorem nc_1963 : ∀ j, 0 ≤ j → j < 0 → node_1963 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_1963 : LowerBin m_1963 s_1963 g_1963 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1963 sub_1963 gl_1963 rc_1963 nc_1963

def m_60103 : Nat := 0xcccccccccccccccc
def s_60103 : List Nat := [0x4444444444444444, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_60103 : Nat := 0x444444004444cc
theorem lb_60103 : LowerBin m_60103 s_60103 g_60103 5 :=
  lowerByCheckedRows (unpackRows 60 0xefa000000000cf2000000000aea0000000008e20000000006da0000000004d20000000002ca0000000000c2000) lb_1963 (by decide +kernel)

def m_566 : Nat := 0xa000a000a000a
def s_566 : List Nat := [0x2000200020002, 0xa0000000a, 0xa000a]
def g_566 : Nat := 0x20002000a
theorem lb_566 : LowerBin m_566 s_566 g_566 4 :=
  lowerByCheckedRows (unpackRows 16 0xcf10008e10004d10000c1000) lb_15 (by decide +kernel)

def f_1828 : Nat → Nat × Nat := fun _ => (0, 0)
def l_1828 : Nat → Nat → Option Nat := fun _ _ => none
def m_1828 : Nat := 0xf000f000f000f
def s_1828 : List Nat := [0x5000500050005, 0x3000300030003, 0xf0000000f, 0xf000f]
def g_1828 : Nat := 0x500070007000f
def bds_1828 : List (Nat × List Nat × Nat × Nat) := [(m_566, s_566, 4, g_566)]
theorem kn_1828 : KnownBin bds_1828 := by
  intro b hb
  simp only [bds_1828, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_566
theorem sub_1828 : ∀ b ∈ bds_1828, m_1828 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1828, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_1828 : ∀ b ∈ bds_1828, canon b.1 g_1828 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1828, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1828 : dagCheckRootsF m_1828 g_1828 bds_1828 (dagRefF 0 (dagTraceF m_1828 s_1828 4 f_1828) l_1828 0) s_1828 4 = true := by decide +kernel
def node_1828 : Nat → Bool := dagCheckNodeF m_1828 g_1828 bds_1828 0 (dagTraceF m_1828 s_1828 4 f_1828) l_1828
theorem nc_1828 : ∀ j, 0 ≤ j → j < 0 → node_1828 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_1828 : LowerBin m_1828 s_1828 g_1828 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1828 sub_1828 gl_1828 rc_1828 nc_1828

def m_60104 : Nat := 0xff00ff00ff00ff
def s_60104 : List Nat := [0x55005500550055, 0x33003300330033, 0xff000000ff, 0xff00ff]
def g_60104 : Nat := 0x550077007700ff
theorem lb_60104 : LowerBin m_60104 s_60104 g_60104 5 :=
  lowerByCheckedRows (unpackRows 52 0xcf2c702082082082082082088e28602082082082082082084d24502082082082082082080c2040) lb_1828 (by decide +kernel)

def f_1820 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def l_1820 : Nat → Nat → Option Nat := unpackLinksF 0x9 0xf 2 1 4 1 2
def m_1820 : Nat := 0xf0f00000f0f0
def s_1820 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_1820 : Nat := 0x105000003070
def bds_1820 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_1820 : KnownBin bds_1820 := by
  intro b hb
  simp [bds_1820] at hb
theorem sub_1820 : ∀ b ∈ bds_1820, m_1820 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_1820] at hb
theorem gl_1820 : ∀ b ∈ bds_1820, canon b.1 g_1820 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_1820] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1820 : dagCheckRootsF m_1820 g_1820 bds_1820 (dagRefF 1 (dagTraceF m_1820 s_1820 3 f_1820) l_1820 0) s_1820 3 = true := by decide +kernel
def node_1820 : Nat → Bool := dagCheckNodeF m_1820 g_1820 bds_1820 1 (dagTraceF m_1820 s_1820 3 f_1820) l_1820
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1820_0 : treeBlockF 0 1 node_1820 = true := by decide +kernel
theorem nc_1820 : ∀ j, 0 ≤ j → j < 1 → node_1820 j = true :=
  (certBlock nb_1820_0)
theorem lb_1820 : LowerBin m_1820 s_1820 g_1820 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1820 sub_1820 gl_1820 rc_1820 nc_1820

def m_1978 : Nat := 0xf000f000f000f00
def s_1978 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_1978 : Nat := 0x100050003000700
theorem lb_1978 : LowerBin m_1978 s_1978 g_1978 4 :=
  lowerByCheckedRows (unpackRows 48 0xefae78000000aeaa680000000000000000000000000000006da6580000002ca248000000) lb_1820 (by decide +kernel)

def m_60105 : Nat := 0xff00ff00ff00ff00
def s_60105 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xff000000ff00, 0xff00ff00]
def g_60105 : Nat := 0x1100550033007700
theorem lb_60105 : LowerBin m_60105 s_60105 g_60105 4 :=
  lowerByCheckedRows (unpackRows 60 0xefae78000000000000000000aeaa680000000000000000006da6580000000000000000002ca248000000000000) lb_1978 (by decide +kernel)

def f_1947 : Nat → Nat × Nat := fun _ => (0, 0)
def l_1947 : Nat → Nat → Option Nat := fun _ _ => none
def m_1947 : Nat := 0xa0a0a0a0a0a0a0a
def s_1947 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_1947 : Nat := 0x20202020a
def bds_1947 : List (Nat × List Nat × Nat × Nat) := [(m_566, s_566, 4, g_566)]
theorem kn_1947 : KnownBin bds_1947 := by
  intro b hb
  simp only [bds_1947, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_566
theorem sub_1947 : ∀ b ∈ bds_1947, m_1947 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1947, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_1947 : ∀ b ∈ bds_1947, canon b.1 g_1947 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1947, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1947 : dagCheckRootsF m_1947 g_1947 bds_1947 (dagRefF 0 (dagTraceF m_1947 s_1947 4 f_1947) l_1947 0) s_1947 4 = true := by decide +kernel
def node_1947 : Nat → Bool := dagCheckNodeF m_1947 g_1947 bds_1947 0 (dagTraceF m_1947 s_1947 4 f_1947) l_1947
theorem nc_1947 : ∀ j, 0 ≤ j → j < 0 → node_1947 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_1947 : LowerBin m_1947 s_1947 g_1947 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1947 sub_1947 gl_1947 rc_1947 nc_1947

def m_60106 : Nat := 0xaaaaaaaaaaaaaaaa
def s_60106 : List Nat := [0x2222222222222222, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_60106 : Nat := 0x22222222aa
theorem lb_60106 : LowerBin m_60106 s_60106 g_60106 5 :=
  lowerByCheckedRows (unpackRows 60 0xec0e40000000cc0c40000000ac0a400000008c08400000006c06400000004c04400000002c02400000000c0040) lb_1947 (by decide +kernel)

def m_1984 : Nat := 0xf0f00000f0f0000
def s_1984 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_1984 : Nat := 0x105000003070000
theorem lb_1984 : LowerBin m_1984 s_1984 g_1984 4 :=
  lowerByCheckedRows (unpackRows 48 0xefae78000000cf2c700000000000000000000000000000006da6580000004d2450000000) lb_1820 (by decide +kernel)

def m_60107 : Nat := 0xffff0000ffff0000
def s_60107 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xff000000ff0000, 0xffff0000]
def g_60107 : Nat := 0x1155000033770000
theorem lb_60107 : LowerBin m_60107 s_60107 g_60107 4 :=
  lowerByCheckedRows (unpackRows 60 0xefae78000000cf2c700000000000000000000000000000006da6580000004d2450000000000000000000000000) lb_1984 (by decide +kernel)

def f_60190 : Nat → Nat × Nat := unpackIndexedForestF (pagedUnpackF 21 7 (fun p => (pickBlockF p 4 (pickBlockF p 2 (pickBlockF p 1 0x1f4a20fa4f07d268361531e92f0f45586c2823613b1dca00d84dc752b83612b1c9a80e45406c24e36a341bc920da5706d288361230041b8d4550388be341440e22d8cc5b0388ae31348189a20c4510388a6301540e1af8bc4d0386b62e16c0e1ab8b0d70586a82c1340e1a98ac5103869e2a1340e1a58a45703868e281340e1a18709284c6b4263560e123090d7448274241360e0ab083168418ac20b5a105ab0828e4414621c1460e5ab07c8d03969c1ca560e5230725283928c1c13e0040f86c960028be19a480cca400516c314c0014570b1a4058d102c4901614800a29854960026be14238009ad84a980252c001357081ae040d502047010138009a983a9201d2900134f06d1c004d2c194a0013470591c02c4e0026860a1460092d0191781168806452031a6818d140c2b4061560092500ed780768c0395601ca30048c8034b401a3200c968045280102e0001f 0x3f4221fa0b8fd03c560233bda69ded14ef4a477a3a3bca51ea540f50b8779463bc2f1de118f1488778363bc0f15806ced4907034d3ad281c0d14e04a47024a39c9b1c0920e52907023a384a41c40e0e10587004a2b00b9bc110ad69a6e05c2b5a295a578ad2a45693a359a81ac910ad26c6a0343391e9a4500ce46a671423389519c074ad2485685e32c1a15a148c92485684d3149218c050c50885684a30c0a15a118c1280601242b422968934b40845a03e2d0191680a8b404c5a8322d41816a088b50345a0142b422164110ad074573502b9a215c910ad06c560130042311ed58a96a84795f29ca211e56ca36d851a6c28d3011e55c9e2a84f1442789e13c4d08f2a64e2502692b1345588f2724bb4825ca211e4ac956904792724d1c1208d0902a84814423c918020fc6c8b4464681b1af9151606c6ae444581b0af90c5706c2b641460209361049806c2ae3e95c) (pickBlockF p 3 0x2b11eaf6d797d47cbda445ec149588ed7649cbc0245d9212ec144ac46eb33435991fae4d096647cb7a4e5bc122cc8c96609eb304b5a8ae2d45416608eb414059caa2cc10cac46ab024d58122ac08d561288b01392b027aaed455769aabb45565a82b294159488ab83655c1715810d4e68aa7249538af29c549506a0a82445381b29c0b8ac0769fa5d529262941413f46aa41354fcae27e54545080a22354fca82841413f26aa01504fc211580dd2c68c9e24e4b1a22749112c4bc962464b1222584a52c250999364cc9a2584912d68896a444b49425c4d12d048960522b017a3ed791f6a48fb4d47da2a3e529252a08f94647c2f23e1491f0948f84647c171580ad0a6a485350429a5234d410a49a8bb5045d22214929154808524644da021491510464880424292221c5110a26285b5042d22214128ac04e7eb5e41c1a1fa578fd2a47e85e3f4232008f90007c80032 0x7fd233fc8d1be27efba5a7ed283ee959f72b4fb9567dc9f37c4eded8b4f6b5a7b5ab3da905ed2b4f724a7b9233dc129ed098df1377a4ab3d24f9e925cdf133781a53c0969e44a0f215c7812b3c0559e028cf012e6f895bb6d69db694ee13c76cad37c49dcd494ec04c735233aa8e9d525ae6a3474d1a39a569d1248e6956734a539c131cd28cdf12371da238e911c7250e413471c9237e0bdbf04ee20446fc11b7e06dc0490e00106fc0bb7c11801094c5b5d62da6b731b1b96a8c5b4b6ddae316d1d8b68ada14662ca8b1652dae4d8d72606bd2835c5418b28ed2454691b6348d51a4470d42446911a34a8e1a5268d216062c9fb431b1a12d8c593b67a3033cd518b26ecd46c668b63345518b266cbb6065cb63164ad946c0ca35862c93b249418c468c616c638a031c4c18d248c615462c9180211d89088c40392b127b080a584050c20242b121b00d39816b8c024f)) (pickBlockF p 6 (pickBlockF p 5 0x9f51d4fa8da7d29b1ba469e8a24f41126e69f3c2389b9a5cec9426e68f392389c89a4e40d26e6873723a9bd1b4dc4b637469352349ac924d4152372bf31a4699d1d4c68d2652493195698ca346e56a614a1302348dcabc9ed765d08927b4d93da2c9e54a4f2752bb5095d2249e4da550692823d9411aca050a502812812a93c9246e55a4c4912623892d1a46e53e482ad241468dca548a922454712123490c924841723728f1d45a8ea2b474d6a3a6ad1d04e8ec2a47410a3728d1c3448dc0b80248e358bd09355849a2c6451a1229314c648a62a452d92296a914a388a92a454912294690913f89caa4244ee228b111364889aa4445621226f0f96487caa4244ce1d2a90912b865b4432d62192b10912784d1a42c492132c90a12484caa42448c0109f081396f9a5c1c545be68f0604c828a34144f9be29702b5d8152e40a946054a0df1477fa2b3fcd59fe472ff238 0xbf4a25fa4d2fd0317c943be495df4d32f924f7c04c0049bdea552f50a971b5fbcc9a5c6d6ef12d971b57bb5aa5da4d2ed06971b53bac225d2936e948b71956b99ab5cc95ae327d72156b8c970024cee02a970054afa2fdbad22dd2895f45bb69b05b45b2be8af6b348b58a25ac112be8a769b46b4da257cd4ad126d5f34ab3da557c96acc4a16623aaf92b590d76c94b96423aaf8ab58116ac08ad6035ab01ab58056ac12a160156af8a357c4b8012575cb58aec9e572562b90a95145fadda454516eb56c151457ac5a4562522b108951453ab22cd5c112ac8a356246a89ad55296aa94ad5134aa8da554696aa327b5214aa8c9e5445680124f4f954a7c2a46f17e9d2891bc5ba6cb646f15e982894c0448de29d28d169428b4a1448dd2f51e91a9047548236a3d2246e94a8d2894435ea29a25148d2886a54434a8dd254fad6a7d6ad41a44a0ca24fa97a814693ea52) (pickBlockF p 7 0xdf62a6fad537d0a9b2a5fded226ca96f786d9bc160d952bee695373489b9928dcc126ca94f71089b735edb9ab6dc95b65473b6044da127ed45436848fb4027d951c6cc91b654680093fd8c2a67d17f3e8afaf954d7c2a67cd7f5d2699f35bd6cb667cd5f576a9ab934d5c1a67cd4f3e697aa13ecf92d6a44934c4a3a723dd391ae9c49b4c4a1a615dcf92b6941533e2bf9f15acf8abe8ad374568b9f156cf89fe82d5b414ad9f13ecf89be7c05c012779e254ce41f674153390657c45acce34667163332b19a340ccc2a5f0d7f316ad7c35acba2c65c582f86af96152be1ab64d163266a993158c9da064c152f84bf91d68c8d2e5f096f208c190160be12be315a3184b98e358c61226304a3192818c024be129e2c913146bd8a256be120e244a2f847788150be11be14d6b0a6ad8514dc2ca66144baf82b57cb46c1da25f293ef948f82344be4a7df252f010a17c947 0x7d2527e908800b4ff99ab7cc4e401697ea95ff8d367aa56fdf4d9efa60f7c367aa55fdc4a1ee15cf6d327aa54fd52a3ea85ff58b67ac583d50ae00b47f349cfa04bfd024fe8017f349c79a4d3cd06800b43f21a2f9491bc8493e4044004a7f6916fb48afda35bf09a4784d13b429fe005ced0a3f74d6bba6addd04eeec2a77410bb428dda13fedd237684fbb426fda017004a5f32d77b08d9d8138e65a5f5ad73ad2c1ccb47ea925f5491f994b9d4246e6528f4c4e39f697d2150e7da3f3e8ffa1099cfa37e7c13f329439d2b9ce128e6525f345839948e00947e10a670851b8f47fc7a3be4c2671e8df8f467c783fe3c1bf085138d48dc213ee211ff141338846fc4027e109e7084d38425dc2014004a1f04d7b658adb2b56))))) 11
def l_60190 : Nat → Nat → Option Nat := unpackIndexedLinksF
  (pagedUnpackF 18 7 (fun p => (pickBlockF p 4 (pickBlockF p 2 (pickBlockF p 1 0xcc0033000c81032000c80031040c40031000c30430c00c20430800c2002f840bd042f400bc042f000b90c29150a40028c10a30028030a000270409c00270009c0026430990026010980025c109700254209500254009500248309200240209000238208e00234108d0022c208908224008900214408500214008500204408100204008100204008100204007b181ec007b001e8107a001e8007a001e800741818d106300184206100184005f0817c005d08174005c04170005c0015c505700154205500150105400150005208148005200148005200138404e00138004b0c12c004a0412800470c11c0047001142045001083042001080041041040041001040041000ec603b000ec003b000ec0036140d80036000d800330c08d0001880001 0x19900664019120644019004640019000640019000640018e08638018e00638018d046301182286080180085fc117c0c5ec117b005ec0179085e40177085d42175005d011710c5a091670459421650057c615e04574115c04570015c0056431590056011580055c11560455411550052ca14b0052c014a0452411470851811460051411430850c014204508014104500114000500014000500014000500014000500014000500013c104bcd12f004b8112e004b8012e004ac3117503f5a0fd003f400fc043f000fb043ec00fb003e810f6103d800f6003d800f6003c840f2003c410f1003b830ee003b800ec083ac10e9083a400e8043a000e80039430d63c35020d40034c10d30034810d20034020d00033c10cf0033c00cf0033030cc003300) (pickBlockF p 3 0x278049e002750c9d4026f189bc026f009b4226c04978e25d04974025d00970125c0097002590c96402580496002570494c4253009481250088d1c234008d00234008d00233048b0722a088a80228088a00228008a002250c89402183485822150485402150085402150084c22130081cc2060481802050480442010080011fd0c7f401fc047dc51f7007d031f4007cc11ea247a411e90079051e40078c11e30078811e20078411e10078401df0877811de0077801de0077411d91074091d00074001d00073c11cf0073c01ce0473801ce0073801ce0073801c0386fc11b9186e401b9006dc21b7006dc01b5086d401b3086cc01b2046c801b2006bc31af006b811ae006b801ac08680c19f0467c019d08670119c00670019c00670019c006643 0x37208db0636c00db0036b04dac036b00dac036224d88036104d7c235f00d78135e00d78035e00d68435124d40135000d40034c10d30034c00d30034c00d28234a00d28034a00d0c734204d04134100cfc233918ce4033900ce0133800ce0033314ccc033204cc4132f08cbc032f00cb8132428c8c132300c8c032300c88131e10c70231c00c6c131b00c6c031a04c60230b34be132f218bc412f100bc402ef08bb812ed04ba442e900b9442e500b9402e404b9002e304b8032df04b7c02df00b7812de00b7412dd00b7402db08b5462d500b5402d308b4c02d300b4422d100b4402d100b3832ce00b3802cc08b2c12cb00b2032c704b1422c500b1402c500b0c22c204afc32a85caa002a704a64e29900a64029708a2cc28a04a280288089e4f)) (pickBlockF p 6 (pickBlockF p 5 0x49e0127804932d248149105234448d01230148b05220348801220048801214347d211f404791119934630d18c046205178445e01178045a1116414570915c04501d13c144d0912c244a05124144709110344305108144201108043f0d0fc043e050f8043d050ec243a050c0a42041080042001078241c0906c141b0105c44170105c04140d05004130504424110104014100103c140f0103c040e05010a4040100c13e770f9c03e01cf7043dc00f6433d708f5813d504f5403d404f4c13d300f4033c91cf2403c708f1c03c604f1803c600f0453c004f0003bd0cef403bb08ee813ba00ee803b418ec433b004eb823ae00eb413a910e61139800e50439400e2c938b00e28138a00e08838200e08038104dfc237918ddc237604dd8037504dd01 0x5bf016fc05bc0d6f005bc016ec15b225669859a0166415960d65805950565405920d648059201648058f0d63c058e0563805871d61c0587016085582015fc3572355c80572015bc356f015bc056c0d5b0056c0159c55670159c05670159035640159005610d584055b1956c055711550355305534654d01534054c0551c55470151c0547015181546015180545054f48539114a115270549c052605494151f19478151b0d464251511450151401448250c19430050c0142c150a0540495000540004f91d3e014f50d3d404f4053c434ea1d36cf4d90935c24d21534804cd1533014c42130c14c2052fc34be052f804ba112d454b3092cc04b3012c424ad112b404ac052b004ac012a824aa0128c74a30128424a101284049f0927c049e052780) (pickBlockF p 7 0x6aa01aa416a511a9406a405a9006a305a8036a001a8006a001a80069c11a70069b05a68169a01a50669401a4c169301a48169201a2c768615a0456723d9c8066f0d9b0366c019b006690d9a406670999c06640d98c166205988065e11974165d01968365a0196416590196406590195056540193c564f01934264911924064901924064511914064501914064015900064001889e6220188416210188016172585c06170185c061701858160f1d8381608198200608018104603057e895fa017e415f9017e405f8057c475f1017c405ed117b405ec057a435e8057a005e80179435e40579005e30577075dc0176c15da0575065d40174435d10172c65cb0172815ca0172805c90570875c20170805c10570405c10170015c00170005bf056fc0 0x8360e0b8881b4e05c481119ff547fb09fe817f611fd417f309fcc07ec1dfac17eb01fa037e50df8057e001f8007e001f6867b1a5eb837ae01eb807ae01ea457a709e8c47943de44379101e3c278b11dfcc77d09de8377809de0077801dd4377501dd0177401dcc177301dcc077205db0676c01db0076619d98076601d29c74515d14074405cfc573e05cf0273715cdc073605cbc772f01c94a72501c90172305c84271f09c7c071d09c74071035c40070f05c38170d05c2446f359bc426e921ba406e805ba006e50db9406e501b9406db29b6c06d711b5c06d701b5816d601b4456cf09b3816ca11ae126b705abc86aa15aa80)))))
  (pagedUnpackF 24 7 (fun p => (pickBlockF p 8 (pickBlockF p 4 (pickBlockF p 2 (pickBlockF p 1 0x11445611035a10c3561082391042310f82340fc3560f434e0f02560ec2460e814a0e41461a445f19c45b19445718445317c35f17435b16c35715c35315434f14c34b14434713c34313824a12c24611c1561001460e013e0d82580482480d02480cc1480342680c42600442480bc3480b83440402580b42480b01480a82580282300a023809826009416008c35c08835408423808013803c25807824807414806c23806425003824802423005c23805813801424a03414a05014604434404845e04045203c34d03834503415a03015602835e02434601024a02015601c14601425a01023200c12d0d445f0c845b0c04570ac4530a435f09c35b09035707c35307034f06834b06034705434304c25a02c24a01823200814afa034ff9434bf50347f30343f1da4fecda4be61a47e0da43d91a3fcf5a3bbdda37b89a33f1c14fecc14be60147e0c143d9013fcf413bbdc137b88133af592faf412ba841278d812384404f6f404a6280472ac04623803f1ac0370dd82f0058270dc01f00401700001f 0x3b801b37c0172b00132a435429c14427013829436c29026c28c26026c13828415428014427c13c27813427025026c256261a3e26815626034825c14424c13025434824812024c2382482342441542401442a83562a1a5f299a5b289a57275a53265a392a015f29815b28815727415326413925992f25812b25012723c12323045d2284552304682284582204581ec14021815c21046020c26c20826020015c1fc1441f813c1f41341ec25e1dc2461c82361e81561dc1401d415c1cc3501c9a501c81501c01201bc14c1bc1241c02341b815c1b414423445a22c35f22435721da5f215a5b205a571f1a531e5a411e1a3b1d9a3721c15f21415b2041571f01531e41411e013b1d81371d192f1d012b1c41271b01231a81541342541101541a014413024419816c11416410c14419034818c34418814418015417813417016c0fc13c16835c1643541601341581440f413c10815415013414815c1041541401341242560e823e13435a1303561201560e412e12835d11435512413a12013611845a) (pickBlockF p 3 0x3480203942583ac25034401034002039413a39c13639414833c02038992c38802c38803838c14838402c31c0103b034d3a83453a42523a024a39824839023a38194a38004a33401035001434c124378044359a3435813434412437005c2bc0542b80342f00442ec0442e804435c3503582442e40443500343481402d80342d403434c23d34423534014233c12a32403d31c03a30c0363000352d003433801d32c03431803432412431404431803431801431c12431404430c0143041403001242e00322dc0302d80222d401a2f824d2bc2452f59422f193e2ed9322e992a2e59262f40422f003e2ec0322e802a2e40262d00142c80442c03502bc3442b824437434d36c345369a5e365a52361a3a355a3636815e36415236013a35413633412433005e32805232004d31004a3080462fc0452cc0442c403a2b403661c24f60c2435fc23d5e823b5d423759423557d94f55994353593b4f99374ad92f47992b4259273f192357c04f55804353403b4f80374ac02f47802b4240273f00233b981f 0x509a443141443d80285140405102352f593550004249402a3d801a31445050994050805050015053025d52423551c15c51815150c1505041354fc04249002a3d001a4d01244f024e4e823e4cc1244c403245c0254e82444c00324bc0424d01364cc1344b80244b81344c43444c02444bc1284b40244f43464ec3444e425e4e02464dc2444d81294d41284c81244b005245c0344941504a835e4a43524a034d49c34549814a4901463e192e36012248c05e48805248404a48004647c02e2c402244434446834d46034a45434644c34543004a35c01246835045c24446035045c24445424042c03844c34044423244004235801243814443035042c24447435247035046c34a46424d45824a45024644824543c2443f423d43413142804a35401240804440404441c03440004440823e40403e40003242035e41815e41415241005e40c0463fc0443f802e3f401e3c40343d81503d405c3c42443140443ec34d3e83453e42523e023a3dc14a3d01463cc05e3c80463c00363bc01e3b424834c010)) (pickBlockF p 6 (pickBlockF p 5 0x5740434a002b4640273ed81f3ec01b3b00173740135f42445f423e45d92545c0255f835e5f02444599355ed9294580355ec0295e19245e00245281445e424e5dc2424859595d99515559395259354f592d4519254840595d80515540395240354f402d4500255c824c5c83425c024e5bd9245bc0245400345a004052c25c5ac15c5a815059c0405a014059c1544401345d03435cc23f5c423e5b82325b594f5b194b5a594759994358d93f5719334ed92d49d92b44992743d9255b404f5b004b5a404759804358c03f5700334ec02d49c02b44802743c0253e981f3e801b3a801736c01358414459024d58c24558823558013954c04a41802236801256804456c0344c413c56403456c35056825056424457835157434d57034554814a4fc1464b013e4141323e592e36412248803a56003655c02e32802242c13454003438c13454435054024455434555024954c15e54815249813a4281363dc12a38012648403a53c03653802e31002252c24451414052c24c52014c510140528050520135 0x7d813b7b01377a013377d92f77c12b7681277301236f80466e835a6dc356689a39671a316881396701316e43456e846c6e43545f40446dc35c6b1a3d679a356b013d6781356b825669024e661a3e6d01466bc1506bc2506c426c6c02606b81506a02346981506a02446982386941346b04546ac36c6a83546a423869c23469016068846c68416c67c46067835467046c66c16c66815466036065c16c64813065436065035864412063814464825063414463c14063813063412464423464016c6301546f035d6ec34d6e034b6d83476d43456cda516c9a4b6b5a4768da3f681a3b675a37665a336cc1516c814b6b414768c13f68013b67413766413365992f65812b64c12762c12362404460034160024d5f824a5e42465cc2455c42446219394899314a99294219216200394880314a80294200215e02365bc2345dc3465b83445799514a59396199296159286119245780514a403961802961402861002460434d60435c5f423460834e60024f5f023559194f5759434a192b46592759004f) (pickBlockF p 7 0x79412a82035d81c25c8182518142507e813a78c12a7fc23472c0447280447240467200347fc24671c04680c4568083568042398002387f82347180567ec2507f025a7e825679da3e7642327e415a7e01567dc13e73c1323f40567c004c45c0447bc03c7b804c7c024a7bc2467b804a7600127d445a7d035a7cc3567a434d7c82417c415a75c1227140567b404c7100447ac1567a813e7a412e70c05679425079015c79c34a79825a78c25678815678414678012e70805670405475813077013c74c12077835a77434a76da5a76c15a7501206fc05676004c75823a74c14a74414675412d70004674c23431803474412431404473804c765b4a75db4676424a75c24675023474815a74015673c14a7341463bc05672012472013472c34472824472412871c12456c35045c2447100443180347042487000105f023571992f3f592b71592770d92371802f3f402b71402770c02370981f70801b6fc0173bc01383c34b834347825a4b811a477f5a3f7d9a3b7b1a377a1a3382414b8101477f413f 0xa5c453a4db5ea39b52a1db4a9f1b46a4c25ea38252a1c24a9f02469b42349a415f98815a97c15793815692814f91c14a9041478e414684805f73005a62c0572b005623c04f1b00478dc0178d445e8c1a3d891a358c013d8901356e40455f00448bda3d88da358bc13d88c1358882468642368c81468ac23472c0448a82347280447240447200348ac2548a824471c0448c04648bc4548b83648b43548b02388a423471805489c1543f405445c04489445889036488c35488815871405471004488016487c15470c05487415470805470405486c368868358865a5886415885c1206fc05485815485014470004431803485812431404485012485c23485416484c1543bc0548d03558cc3458c5a498a1a3f899a3b885a37879a338c41498a013f89813b88413787813387192f87012b8601278481236f80447d1a45841a397d01458401397e5a59839a5180da3d7cda357e415983815180c13d7cc1355f004483004c7f024a7c424679823a76c2367e414a82c14682813e7481327941387ec13a))) (pickBlockF p 12 (pickBlockF p 10 (pickBlockF p 9 0x93012575804a33c04691823a9bc23675404a3380469e434f9dc34b9d43479c43439c023a9b014f99814a98014793c14692c13f9101379b812d85c04f75004a64404733404624803f1c00378e00179941443240549ac0449ac1249b02349901543200649a805499c23a99414674c04a31c0463180349941243140449a1b469a024699823499015698c14674805a3100563040449842503000449802342fc0542f805495401495012497404495da3495c13494c1242f40442e804496035095c2442e40449540342e003463c0352dc0342d403495023d94c23594814294414094012a85803d74403a30c0366340352d003497835d8fc35597034d96c345969a52965a3a959a3696815296413a95813693c12485404d74004a3080466300452cc04493424893023892c2349201442c804492415692014673c05a2c405691824891423890c04c90c12491023490805c2bc0442b80448ec05490045a8fc4568f835a8f435673405a2b40568f004e8e804224403d1b40358e0344a7845fa7045ba68457 0xa9db5aaa825aaa4256a9c15a9c013077405a39005699c130a91a3ca9013c38c054388044a9014a77004a384046a9c34aa9825aa9413da8c13c99812076c05a380056ae045fad845bad0457ac0453aac35aaa034aa89a5aa8815a9b412086005f76805a64c05737c05625004f1c40479ec1243780549e81249740549e4234970164a80154374064a7c054a19b54a182549dc2348f8154a74144370044a15b44a142449d4234a6c16c8fc16496c1548f414436c0549cc1249c81249c4234a64144a60044a11a34a3592aa0d92679004a3d4046a58345a31a3aa09a36a54145a50144a2da38a05a34a4423aa40236a25b4aa01b46a48246a3c244a34144a2c344a28234a3035ea24352a2034a9fdb4696415676405a36005695c144358044a10244a0c144a04234a1835aa14356a0825ea002529fc23a9f82369a015a9581569f414d75c05a3540563500449540449501549ec14434c0549e80449e02383480449d825094c1443440449d02389cc1349c803499c14a94014693413d91413591812d) (pickBlockF p 11 0x3f4056bd035fbc835bbc0357bb0353ba0156b9413eb8c12e87805f7a005a6640573f005613d83f055837b841543ec064b80054b78348b10154b74144b6c360b6816cb14164b0c1443e8054b60348b5c144b58044b50346b4c344a8d934b3c25ab30256b20156b4413679c05a3e0056b3c34ab0824679805a3dc056b0413679404a3d8046a3595cb34250b3023aa5015cb0013678c04a3d0046b2425cb2835db14355b2023a78804a3c80463c4044b04150b1845ab14456b1035ab0c356b0815ab0015678405a3c005699015692014678005a3bc056b7c45fb7045bb64457b54453b48352b4034ab3825ab2c256b1c156afc146af812e87005f77c05a6580573b805625804f1d00473b4054aec13c9e8010af0358ae9a58ae81589e41203b0064ae40549e0130abc368adc3489dc1209d81303ac054aa8368ad43609d41203a80549d0130ab82589c8010ab4368acc348ac9a48ac81489c4120ac4044ab804439c054abc459ab4451aa824aab024686c05d77805a3a0056650055398054394054 0x89004d7cc04a45004667804543c04413001da10120c9c340ca8458ca4354c54240ca0158a08120c98054c0c04cc90568c8c25c9a0120c0805cc0404cc84460c80160c0004cc70254c70358a04120bf803cbf404cc64140c78568c7425cc6c244a00130c68128bf005cc60024c58244438044c5435ec41b46c502569202467c805a4340569fc130c48128bec05c920450c41a40c401509f8120be585cbe404c42c044c2c14cc3835ac34356c3014dc2812e9a01227c405a428056c1c344c10344c04050bfc144bf8134bf4018be834cc20346c1824fc14247c0c14fc0814bc00147bf0143bec12bbe4127ce045acc835fcc035acb4357cac356b8c34dc9425fc8825bc7c257c5c253c4c241c4423bc3c237c2415a9f012288405f7b005a674057424056be004c1d803714582f06182712c01dbac054ba8164bd8154bd4054bcc134bc416cba4154b9c13cbbc354bb8134bb4034bac044ba824dba424588004d7ac04a40c0466680453fc044b9c356b982567a805a3f8056059835b901567a405a)) (pickBlockF p 14 (pickBlockF p 13 0xe00356df025fde825bddc257dc8253db4239d9c238d942348a005f7f405a68c0574ac05615582f071827d181644a0064d8c054d14154cc414449c054a30230d80154d7c054b3da4cd74134b31a3cd6c16cd0813ca2c230a28130d64354a24240d60134d5c034a20240d5013e7f005a498056d48124d4023dd3c235d381267ec04a494046d44251d34250d3015d7e804a490046b90154d28054b90156cd81467e405a484056d1834dd143457e004a480046d08356c49b46d042567dc05a47c056d8845fd84457d7835fd7035bd68357d58353d5434bc45b47d4c25ad2c256b41a3ea1c232d2415fd2015ad1c157d10156d0c13fd0013ecfc13791c13289805f7d805a6800574780561e004714d83f06983713802d008025cf8017cf0254ce8054cdc45dcbc455cd8346c90259c782517d405a46c056cec03ece4032cd0340cdc468cd8458cc4354cd4158464064ccc054c1804c45c044cc4356c3815aa181227d005a45805613401dcbc458cb8160448054c1404c440044cb0152c3414aa14122 0xddda3fd69a3bc7da37bc1a33d2c13ab2c12a81004a6b40474f804628803f20403716d82f09182716982f08d827dd9a3dd65a39c6da35bbda31b5192ea4812228403d1fc035a44130c71c58a40120e4c04ce5423fe5023be48237e44233b4d92ea3c122e4003fe3c03716582f089827dd1b4ec69b46e34246081835e2804ce2c23fe2423727c03f1f8037e2002727803f1f4037cd8146dcda3fd5da3bc61a37bb5a33dc9b4fd59b4bc5db47bb1b43b49a3ea38232e5c14ce58146e38144e3013ee1c13ce18134e1412e27404f1f004715d83f07d837e100144f0044e0835ed98234cc41358c004d80c04a4f40466b00454ec0448b804d80804a4e00466a80454dc044dc4128dfc454df8354dc0238df4054dec244da8238de436cdbc238de0160dd8254dd4244dd0128dcc024dc4044da8150dc035edbc356db825680405a4d8056075835db0044da8150dac24fda42478b004f80004a6a40474d4046da00278ac03d7fc03a4d00366a00354cc034d982468a404f7f804a69c0474c8046e04456) (pickBlockF p 15 0xa5827c38254ef8154c34244ef4144554054a98244550064f0c348f08344cd8144f0005c540044eec054ef835aef435682c05a53c056ef004eee8042e71b56edc246d5014ac2814682805a538056f1845bf14457f1035be6db57de9b4fd71b4bc89b47bc9b43d4c24ac24246b3823aa88236f0414fd2014aefc147ee4146ee013fed813eed413798813282405a6c805753405629804f21404717583f09d837ed0017b90456ec435aeb835682005a530056e98250ec446cb9036ceac26ce94260ec013852c044e90250528044eb835cea825ce8c250eb4160524044520044eac24bea824781c04a6c404751c04629002f20c027e69b56de1b4ec81b46990256ea0246d4414ab3413881805a518056095835e98138514044e90150510044d40148da9938d3c138e8404ce9434be8c347969a47e8823fe80237d3413ab3412a81404a6c004750c04628c03f208037e7c027e7415ce70128508044990560e69a50e68160504044e1445dec835debc34beb0347ea425ce9c251e78250e6c24be64247 (pickBlockF p 16 0xc982719c01f0c8017f8c1685b4044f70154f8c26cd14154ef41445b00545ac034f741505a8044cbc46ceb836cf8426cf80260f6c150f7c06c5a40445a0044f74250f7015c59c044f6c264cb0244598054eb4256cb8246b6da3e83805a5d805622846c6dc36cf5da6cf59a60f5c16cf58160f91a5ff89a5bd21a59f79a57f69a53f65a51f15a4beb1a47e05a3dd85a3bcb5a37cada35f9015ff8815bd20159f78157f68153f64151f1414beb0147e0413dd8413bcb4137cac135b6592fb6412bad0127a68123f6005ff540578d004d83404a6d80475d40466d404559404422403719582f0c182719401f0c0017b61a3eac82360b0025f4812ff4412719182f0bd827f4001718d81f0b9817b5981fb5801bac4017a60013f4da39f3da38f39a34f4c139f3c138f38134b5592fb5412bac0127a5c123f3403418582f0ad82718401f0ac017dfda3dca5a35a58122ca1b46f28246df592fd7d92bc99927bd5923f2c345f24249df1a3fd79a3bc95a37bd1a33a4c122f200442a003f21c03717d82f 0xcd4246ae8236cd8146d8d92bccd927d8c02bccc027b8181fb8001bae4017a7c013f9c345fa9a49d89a3bcc9a37fa8149d8813bcc8137b7d92fb7c12bae0127a781236ec0555fc054fa404422c0371a582f0d58271a401f0d4017cc5a35cc41356e40455f0044ec0256b79a3eb9015684005a5ec0560cc025f9c356f19a5bebda57cc1a45f99a39f1815bebc157cc0145f98139b7192fb7012bad8127a7012383c05a6e00575e805619d82f)))))))
  6 11 7
def m_60190 : Nat := 0xffffffffffffffff
def s_60190 : List Nat := [0x5555555555555555, 0x3333333333333333, 0xff00ff00ff00ff, 0xffff0000ffff, 0xffffffff]
def g_60190 : Nat := 0x11555577337777ff
def bds_60190 : List (Nat × List Nat × Nat × Nat) := [(m_60100, s_60100, 6, g_60100), (m_60101, s_60101, 5, g_60101), (m_60102, s_60102, 5, g_60102), (m_60103, s_60103, 5, g_60103), (m_60104, s_60104, 5, g_60104), (m_60105, s_60105, 4, g_60105), (m_60106, s_60106, 5, g_60106), (m_60107, s_60107, 4, g_60107)]
theorem kn_60190 : KnownBin bds_60190 := by
  intro b hb
  simp only [bds_60190, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_60100
  · exact lb_60101
  · exact lb_60102
  · exact lb_60103
  · exact lb_60104
  · exact lb_60105
  · exact lb_60106
  · exact lb_60107
theorem sub_60190 : ∀ b ∈ bds_60190, m_60190 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_60190, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_60190 : ∀ b ∈ bds_60190, canon b.1 g_60190 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_60190, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_60190 : dagCheckRootsF m_60190 g_60190 bds_60190 (dagRefPermF m_60190 g_60190 63 1003 (dagTraceF m_60190 s_60190 8 f_60190) l_60190 0) s_60190 8 = true := by decide +kernel
def picks_60190 (j : Nat) : List Nat :=
  forceW ((pagedUnpackF 8 7 (fun p => (pickBlockF p 4 (pickBlockF p 2 (pickBlockF p 1 0xc40084cf0232ff870a0f0096002016200000202b5f4243028e000b00000c8f101300320496000044c7049e022b121300be8f00028f430202ff020200020200ff80008004130008efdf424b00000e0406000808000f10130022100016003040007708000e0032101b00000f427f0200060402020277020212126f0200040f5f01 0xd00005f001800004010101000040000445f00400404050000050040000000405f00400008041218000404404004040440404541004940004040000044540000540050041010040000000004550040010100425f43ff0407028700000407004000004b000000ff000013000700040102bf5fff024b0243040700820000000648) (pickBlockF p 3 0x4a000049085f420042485f430a005e00001e04000000030001444b00040200405f09000900030102005f0c04000200000a405f0800040c004144040445440404045f4000140005000d000d0000090000000000005f0206000008404002000000005f020f0300020000000444040e02005600400000005f0000000a0900000008 0x95d0800000000005d0600400000000000065d0000005d00400000000400045d000000005d180004000045000040140000015d000000000040020040000040404241bf4b00090b024b4b07bf8701450000470002050500010000004702028b060207000209cf00021302054700450200000021f75f00085f000b0f5f430001)) (pickBlockF p 6 (pickBlockF p 5 0x40c04de40006500440404004040654400446545400075040064401403ff0064f400000008501400040400000400400064ff000004bc0003e30000250000bd031700e0010002ff2023ff004afe06fe00000000000000084e0086060002020f00004a0096000020566040004000625e085f405f0001405f004104455f0000000d 0xe0000020e5f004059003804dc004400cd000008bf8004ef00ffdf0400d5000018101018000c009d007074107e00d45400d4030000ff00040010000000ffffdf0000200055044c04040820405d040014071f00005f0004900090d45f14407503bc00fc0c00bd10044454100004c4d400100000040cde04440000040044) (pickBlockF p 7 0x1004101d0434141014304430307d000104146f00010004002d081d5f00c5c400009508b40494040c00cdb400de00100000005400de00cdb7cc0002bfbc8004efbc83df00010002bf020300000245405c0201cd005c03100000021d040465140515044b00710100027d0000146f0135001d0040500008de020002020002000004 0xff4a5fffbf5f84008400040285000001c4ff030203035fff008000c94d4a5f7f037f465f8c8cb40000cc00cd0002010002fff400ffb483dfbf00000c02048c000055277f00040404040035006500203454145fcdff84000085000084c543ff84000100e5d5ffc6df005c3f))))) j) fun w => (List.range 8).filter (fun k => w.testBit k)
def node_60190 (j : Nat) : Bool := withPickedBounds bds_60190 (picks_60190 j) fun cuts =>
  clashNode m_60190 g_60190 cuts (dagTraceF m_60190 s_60190 8 f_60190) (dagRefPermF m_60190 g_60190 63 1003 (dagTraceF m_60190 s_60190 8 f_60190) l_60190) (fun _ => none) j
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_60190_0 : treeBlockF 0 48 node_60190 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_60190_1 : treeBlockF 48 96 node_60190 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_60190_2 : treeBlockF 96 144 node_60190 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_60190_3 : treeBlockF 144 192 node_60190 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_60190_4 : treeBlockF 192 240 node_60190 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_60190_5 : treeBlockF 240 288 node_60190 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_60190_6 : treeBlockF 288 336 node_60190 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_60190_7 : treeBlockF 336 384 node_60190 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_60190_8 : treeBlockF 384 432 node_60190 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_60190_9 : treeBlockF 432 480 node_60190 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_60190_10 : treeBlockF 480 528 node_60190 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_60190_11 : treeBlockF 528 576 node_60190 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_60190_12 : treeBlockF 576 624 node_60190 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_60190_13 : treeBlockF 624 672 node_60190 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_60190_14 : treeBlockF 672 720 node_60190 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_60190_15 : treeBlockF 720 768 node_60190 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_60190_16 : treeBlockF 768 816 node_60190 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_60190_17 : treeBlockF 816 864 node_60190 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_60190_18 : treeBlockF 864 912 node_60190 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_60190_19 : treeBlockF 912 960 node_60190 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_60190_20 : treeBlockF 960 1003 node_60190 = true := by decide +kernel
theorem nc_60190 : ∀ j, 0 ≤ j → j < 1003 → node_60190 j = true :=
  (joinChecks (joinChecks (joinChecks (joinChecks (joinChecks (certBlock nb_60190_0) (certBlock nb_60190_1)) (joinChecks (certBlock nb_60190_2) (certBlock nb_60190_3))) (joinChecks (joinChecks (certBlock nb_60190_4) (certBlock nb_60190_5)) (joinChecks (certBlock nb_60190_6) (certBlock nb_60190_7)))) (joinChecks (joinChecks (joinChecks (certBlock nb_60190_8) (certBlock nb_60190_9)) (joinChecks (certBlock nb_60190_10) (certBlock nb_60190_11))) (joinChecks (joinChecks (certBlock nb_60190_12) (certBlock nb_60190_13)) (joinChecks (certBlock nb_60190_14) (certBlock nb_60190_15))))) (joinChecks (joinChecks (joinChecks (certBlock nb_60190_16) (certBlock nb_60190_17)) (joinChecks (certBlock nb_60190_18) (certBlock nb_60190_19))) (certBlock nb_60190_20)))
theorem lb_60190 : LowerBin m_60190 s_60190 g_60190 9 :=
  lowerDagPickedF (top := 63) (picks := picks_60190) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_60190 sub_60190 gl_60190 rc_60190 (by
    intro j hlo hhi
    have hj := nc_60190 j hlo hhi
    simp only [node_60190, withPickedBounds_eq] at hj
    exact clashNode_sound _ _ _ _ _ _ _ hj)

def m_2298 : Nat := 0xf0f0f0f0f0f0f0f
def s_2298 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_2298 : Nat := 0x10505070307070f
theorem lb_2298 : LowerBin m_2298 s_2298 g_2298 9 :=
  lowerByCheckedRows (unpackRows 64 0xefae78efae78cf2c70cf2c70aeaa68aeaa688e28608e28606da6586da6584d24504d24502ca2482ca2480c20400c2040) lb_60190 (by decide +kernel)

def m_2302 : Nat := 0xff00ff00ff00ff
def s_2302 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_2302 : Nat := 0x1500570037007f
theorem lb_2302 : LowerBin m_2302 s_2302 g_2302 9 :=
  lowerByCheckedRows (unpackRows 60 0xdf6d74208208cf2c702082089e69642082088e28602082085d65542082084d24502082081c61442082080c2040) lb_2298 (by decide +kernel)

def m_2304 : Nat := 0xff00ff00ff00ff00
def s_2304 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_2304 : Nat := 0x100150013003700
theorem lb_2304 : LowerBin m_2304 s_2304 g_2304 9 :=
  lowerByCheckedRows (unpackRows 60 0x20a24b00000030e34f00000061a65b00000071e75f000000a2aa6b000000b2eb6f000000e3ae7b000000f3ef7f) lb_2298 (by decide +kernel)

def m_2300 : Nat := 0xf0f0f0f0f0f0f0f0
def s_2300 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_2300 : Nat := 0x10105010303070
theorem lb_2300 : LowerBin m_2300 s_2300 g_2300 9 :=
  lowerByCheckedRows (unpackRows 60 0x10614700000030e34f00000051655700000071e75f000000926967000000b2eb6f000000d36d77000000f3ef7f) lb_2298 (by decide +kernel)

def f_1806 : Nat → Nat × Nat := fun _ => (0, 0)
def l_1806 : Nat → Nat → Option Nat := fun _ _ => none
def m_1806 : Nat := 0xaaaa0000aaaa
def s_1806 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_1806 : Nat := 0x20000222a
def bds_1806 : List (Nat × List Nat × Nat × Nat) := [(m_297, s_297, 4, g_297)]
theorem kn_1806 : KnownBin bds_1806 := by
  intro b hb
  simp only [bds_1806, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_297
theorem sub_1806 : ∀ b ∈ bds_1806, m_1806 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1806, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_1806 : ∀ b ∈ bds_1806, canon b.1 g_1806 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1806, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1806 : dagCheckRootsF m_1806 g_1806 bds_1806 (dagRefF 0 (dagTraceF m_1806 s_1806 4 f_1806) l_1806 0) s_1806 4 = true := by decide +kernel
def node_1806 : Nat → Bool := dagCheckNodeF m_1806 g_1806 bds_1806 0 (dagTraceF m_1806 s_1806 4 f_1806) l_1806
theorem nc_1806 : ∀ j, 0 ≤ j → j < 0 → node_1806 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_1806 : LowerBin m_1806 s_1806 g_1806 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1806 sub_1806 gl_1806 rc_1806 nc_1806

def m_60000 : Nat := 0xffff0000ffff
def s_60000 : List Nat := [0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_60000 : Nat := 0x30000333f
theorem lb_60000 : LowerBin m_60000 s_60000 g_60000 5 :=
  lowerByCheckedRows (unpackRows 48 0xbd0b50ad0a509d09508d08504104104104104104104104103d03502d02501d01500d0050) lb_1806 (by decide +kernel)

def m_60001 : Nat := 0xffffffff
def s_60001 : List Nat := [0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_60001 : Nat := 0x333333f
theorem lb_60001 : LowerBin m_60001 s_60001 g_60001 6 :=
  lowerByCheckedRows (unpackRows 32 0x7e07606e06605e05604e04603e03602e02601e01600e0060) lb_1761 (by decide +kernel)

def m_2026 : Nat := 0x2222222222222222
def s_2026 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_2026 : Nat := 0x202222222
theorem lb_2026 : LowerBin m_2026 s_2026 g_2026 6 :=
  lowerByCheckedRows (unpackRows 32 0xf40740e40640d40540c40440b40340a40240940140840040) lb_1761 (by decide +kernel)

def m_60002 : Nat := 0x3333333333333333
def s_60002 : List Nat := [0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_60002 : Nat := 0x303333333
theorem lb_60002 : LowerBin m_60002 s_60002 g_60002 6 :=
  lowerByCheckedRows (unpackRows 62 0xf42082e42082d42082c42082b42082a42082942082842082742082642082542082442082342082242082142082042) lb_2026 (by decide +kernel)

def m_60003 : Nat := 0xf0f0f0f0f0f0f0f
def s_60003 : List Nat := [0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_60003 : Nat := 0x30303030f
theorem lb_60003 : LowerBin m_60003 s_60003 g_60003 5 :=
  lowerByCheckedRows (unpackRows 60 0xec4e44104104cc4c44104104ac4a441041048c48441041046c46441041044c44441041042c42441041040c4044) lb_1947 (by decide +kernel)

def f_1871 : Nat → Nat × Nat := fun _ => (0, 0)
def l_1871 : Nat → Nat → Option Nat := fun _ _ => none
def m_1871 : Nat := 0xaa00aa00aa00aa
def s_1871 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_1871 : Nat := 0x20022002a
def bds_1871 : List (Nat × List Nat × Nat × Nat) := [(m_566, s_566, 4, g_566)]
theorem kn_1871 : KnownBin bds_1871 := by
  intro b hb
  simp only [bds_1871, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_566
theorem sub_1871 : ∀ b ∈ bds_1871, m_1871 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1871, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_1871 : ∀ b ∈ bds_1871, canon b.1 g_1871 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1871, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1871 : dagCheckRootsF m_1871 g_1871 bds_1871 (dagRefF 0 (dagTraceF m_1871 s_1871 4 f_1871) l_1871 0) s_1871 4 = true := by decide +kernel
def node_1871 : Nat → Bool := dagCheckNodeF m_1871 g_1871 bds_1871 0 (dagTraceF m_1871 s_1871 4 f_1871) l_1871
theorem nc_1871 : ∀ j, 0 ≤ j → j < 0 → node_1871 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_1871 : LowerBin m_1871 s_1871 g_1871 5 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1871 sub_1871 gl_1871 rc_1871 nc_1871

def m_60004 : Nat := 0xff00ff00ff00ff
def s_60004 : List Nat := [0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_60004 : Nat := 0x30033003f
theorem lb_60004 : LowerBin m_60004 s_60004 g_60004 5 :=
  lowerByCheckedRows (unpackRows 56 0xdc8d48cc8c482082082082089c89488c88482082082082085c85484c84482082082082081c81480c8048) lb_1871 (by decide +kernel)

def f_60090 : Nat → Nat × Nat := unpackIndexedForestF (pagedUnpackF 21 7 (fun p => (pickBlockF p 2 (pickBlockF p 1 0x1e1a70f0d08784bc3e0341e1270f40d8784983c0250091f0e8970744a83a23c0091d8048cc636bc3803418da90dc0d06369435a4c1aca00c6d18634bc31a5218d270cc4c06568831a4218c950048c86106829b5114d288bc8f8534a02da5c16d260a68f8590682bb5015d280a68c85325a2a23014c92804548504c0281600082f8949244a2a22613c12897094488020bc2284c1142208a0f0450580105310c1a0829304104819a3e0cd190661743307c1e04c0cc1e8660f0380981c0440cc1a8660b8350681982d0cc0e804148314800103f0bc9c044d38226841125e08929044938224841115e088a904c530222721113108ca80441480207c0d14c07c1e0341701a0a80d03c06816034070020760c2300081b82c0f0132880983c04c160040cc1108801a5e00d2901c940032a40185e028260140b0030a40184e01c2e0061080305c0182d00c0e8040c8010260001f 0x3fc261fc100ce46e773603e5a81f24c0f9060773443b9301dc0a0f44807a0203bd1a1e28c0f1040782343bca01dc090ce46676360338179d4510e44747223639d261c84f8e546872132338171be4f0df0d86f82c37c0e19c0acda6906d34036da01b4980ce04e6ba3035c1619e4d0cf0d86784c348981a4480d10486784433c1619c08c0108665a5832c2a13cd7cc90684f3533191c18c0d09e69661a5030c2e13cd1cbf8a8603442fc1a13cd0cbc47c5e0262792915cd78ae6a45734a2dd2615cd18ae4bc5a0242b9291640d0ae49c583442b92115c0989e46455a492ac9113c1789f6bc4fb5227da514c9309f68c4fa5e27d2913e938a16884fa4227ca913c0f8010364d2582682c134150026be4b83825c1a004d4c934704983824c1a004d2c8e4a0471502382e11c1400268e4594022c261111508807044034009a190a9248508a0125e009299028f88125401252) (pickBlockF p 3 0x5f8a62fc1051148cbe14c5ee2a22290d78290bc1445ada7aec8e16b686b9b415cc14ad69096e49cb723d5b91aadc0a56b25ab604e5ac10a228d1664c0b3a5059d202cc8d1112beb1349588a8ac4125112bcb013c579a22bc4f1112a6ac15d560a72b04b95825aac019444a92a896155470aa234444a7a8ad79456a4a8244514af28a5494d288a29495149d28e50947254a392851c08a8a491450728894e50c9e27ad113d4b8a014c4f49e27c8d13d2588894b4ed1a22251d384989c14c4c1aa26c4f13068899a344cca6260951316889813c444a1a3c9791e4a493b4e49da1254d01274849392d49c10a3c8d11e2bc92018478a9244d111e25c9034447896a3c065112848d93046c18234d11110368aa5e4552922a1791509c8881944c1e224d1111026009234392721c4a8ce4a28246041136214d41044b88225441da82084a104050820243391d9fd180fe2807f04c (pickBlockF p 4 0x7fc14bd84f9f9498fe13c7e4ae3f2551f9278f613b7b09bbec4f1f4488fa13c7b099bd806df107cf60197b4263da111ed078f6013004a1bd2961e92a8d9c5f799a43cc511b38a6f193678c1cb66d49e1298d9a5377d29366939b3496ecb49764a8bb24f9d9092d995e7422f3a1149d06bce835274d1a3a0949d0292e80396cca7384d3dcd470e13437291b3940a5c2484e424e7091d38c4f1c2286e11337081db840cdb3298e01436cca2374949ba494dd15e6e8a9374065b325cda3526dd1c368939b40bcda04e6cc0c8024adaf6b0d813c6bcac33f17dad690cfc536a628b52939a9052cfb5268e2f347149a34bcd1a5268c14b3ed09a00bcd004e67c1880249d9c2b0ce1544462fb3092198290cc14444629b2a5159509288a5e44529b208f59046ac80294452922292d888a4c435e62d1a310d49884bcc4029445252fd1497e4bcc24505f9292fc5358029cc0142 0x8192740c0a6034930203e80c2480253dec27effa4e))))) 11
def l_60090 : Nat → Nat → Option Nat := unpackIndexedLinksF
  (pagedUnpackF 17 7 (fun p => (pickBlockF p 2 (pickBlockF p 1 0x2060102048100404120200fd107e803cca1e408f20079003b061d218e900740239821cc00e504728039011c218e100700238001c000df046f0237801a070cf04658832c019600c320618030c018210c1006002300017c10be005f002f0215a78ad0056802a8315400aa0055002a41152009f284f8027c013e009f004c0e260012e0897004a84254012a0095004a8024c2126009300498023c411e008f00468423400f6907b003c061e000ee0877003b021d800ec0076003b001d410ea0074043a001d000e6086538318418c00c4086200310018800c4005c182e0016430b20058042c0016000a8205400298214810a4005008280014000a0004d0c26801340098084c002600130007c701a9000b20001 0x45612241d110488414400a1f050d0a86024300217050b028484424021201080483c141a12003500007f043f801fa08fc047e003ec11f600fa827a8b3d209e900f48079c23c621e300f00678003bc11d620ea04750039e29cf00e78073c039e01cd08e58472c0386419f90cf8067c0336219b00cb0a658032c019210c900648031639880cc40061c1306218300c1805f072f8017c00be005f002f4117a00bd005e412f2017804bc005dc12ee016c2cb6005b002cc316600b30059802cc016408b20059002c8016400b18258c02b0594a38a5005280294014514a28050c2276413a049d004e4126631330098064bc125e01281c938249c02481924009200468a234011a00898e440321e090f00821640c1) (pickBlockF p 3 0x6d2135e2daf00d6c36ae235701ab80d5036a803510da802d400690434801a400d200690034219a100ce886509328019400ca0064c1322119100c88064403172d8b80c58162c0312118900c4806240312018900c10e6060b03018084bf055f802fc017e00bec15f602fb017c84be405f202f9017c80be405e632f3016f2ab7805b812d90d6c80b6015b002d50d680ab3825961acb016580b20359002c50d6280b14058612c3016102aec75740ab9055c80ae0157002b7055b80ad8155a4aad015680ab0155802ab055580aa815540291654880a44051e128b114580a2c0516028b013f989fc04fc0a7a11295094414a202423d20048fc147e023c0d1d828ec04740a39051c808bca45c0a2d0516808b40 (pickBlockF p 4 0x98c74c40a620130c198604c3025e8d2e8397404b9065c812d449641cb2025319298094c04a6024f8f1ee48f6047b023b891d818ea0c6f1a37811b818c85463062e8d17018aa3c50162801140089e0c4f02221711008860c4302218110c08840c420221010ccf86604330219030c80864042e1217010b02858042b0614850a408500c1c320e0106438320419020c810640832040d32060303008160c0b020581000b7d8a3ec01f600fa827c63be205ed8ef6037b003d705e712f38079c03ce01e700f38078c43c505e280ef097625bb005d782eac475603ab01d580e84a74203a101cb94e54272a039501ca80e1ce7081b8401c200e1007060b8301c180de896f0137609ba82dc836e20b7101b880dac6 0x13e809f404ee32770139889b074d50e6a813501)))))
  (pagedUnpackF 24 7 (fun p => (pickBlockF p 5 (pickBlockF p 2 (pickBlockF p 1 0xdc0350240320d802e0d002d0cc01d0c42400800480118400bc138029a4808c05009814c08c1500b834e0b43420b025e0ac2520a824e0a424206823e011a3d0a015e09c15209413909013108805205183107c04c05803407c03c08014c07805c07405407003c06c02c06801c06023001584c05403005803c01194c05414405003c04c02c044044038150039b5003825002c04c02983c02802c01c05c041b5e03db5204025e03c25203415203005e02405202004e01804201583e01183d01402e01002d00c01d264c5f258c5326435f258353248b4f24834b23434721c34321025e20c2532002521dca4e1cca4b1c8a43188a421dc23e1cc23b1c823318823214815213c05f12405e1100530c80520c084f08484e06484b05c8470488430088420c003f08403e06403b05c03704803300803280934f7ad343809a4f7ada436c923f6ca23b67923744123380814f7ac1436ca93f6c893b6789374409336c992f6c812b67812744012333404327503b00503327582b00582327401b00401300001f 0x13004e1080421e80361fc34e1f83421f425e1ec24e1e424c1d023e16815212c05e1000521e002509803c1d825c1d42541d023c06c12809404c06802804c12809004c0680201640401601501c00341b80341982301b024c1942301ac14015c1501981301943441c435e1bc3521b434a1a83461a425e1a025219c24e19024215815218c12a12805e0fc0520c403d06003516413016024015c230039840184034178a4e15ca4217823e15c23208c84e03884208c03e03803217025c16c24c16403416035015c250150a40150230180c5118035117c251174250168a4e158a4216823e15823215412d14c12514005d08884e03484208803e0340321442601401600f806013013c0f845d138b490acb411382490ac24113415112c93e12893212c12e1281220f816c12085c11c85412004c11c04411803c11402c10c03410824c1040240f004c0e48440e404c0e004402983c0d402c0d48440d4034100a4e0fca4210023e0fc2320f805d0f484e0ec84d0e884c0dc8450248420f403e0ec03d0e803c) (pickBlockF p 3 0x2cc23227c84e27c03e2f00262dc24c2c02302d00242c80342c03442e835e2e43522e034a2d83462d425e2cc2522c424e2bc2422ac05e2b80261d001e2b0b4928cb412b024928c2412ac9322ac12229824c2842302843442a435e2a035229c34a29434629025e28c25228824e28024227c152071831068021328c5f320c5332835f320353314b4f31434b3083472f83432ec2522b4a422b42322a805e27884e27803e2702581c423026c0582680540418301c01301840501bc2401a023018016003d8400ac03c26003825c0340240300bc84c1b81301fca5c1b42402542380b885c25003824c0342303401aca401ac23022c2302283402442501a8a401a823024015023c05c23805019823019423023014022c04c2284541f8a5c1f824c1902300b485c0b404c0a403c224038220034018030218b492182492140450a083e0408320a002e04002217c16011412813406c178150208a4e1a0a4220823e1a023217415020412a14405d09c84e03c84209c03e03c0321b02341701501f003416c142 (pickBlockF p 4 0x3b03601541303880380d00303a814402812410413c39412039c24c0281283942343a4a4a3a0a463a423a3a023639894e39094239813e39013237c12e0d012d11802135c02402a84c02983c38813c38406c38002c37c01c36c35015013036003036cb5036c340374b58370b5037434837034036826014c1200d803c35802034c834348024360a4036023034484434403435c02c34c1303481200d402c3440240d013c35813435406c35085c34085435004c34004433c02c435451435b5140d34f40e34b3f53473b534343425140ea4f40ca4b3f4a473b4a4340da3f40c23b3f42373b42331491421499321481223ad04f38d04e37904b3650473390430c90423ad83f38d83e37983b3658373398330c98323ac02f38c02e37802b3640273380230c80223302582e823032c0542a403c2e42402cc2302a004c28c03c3240342e024031c23829c04c3180343043403102502d8a402d823030c05c29484c29403c2c023028403c3000343003443044542bc23028003c2fc0342f4a4e2cca422f423e 0xc01d44c03c44834400c12809004c09183c66c45f65c453651b5e64db5363db52639b4b61db4a5f5b465e9b4365025e64c25363c25263824b61c24a5f42465e82435a823459415f58415e57415355c15254c14f51014e4f014b4e81474bc1434741423b40532f904b21d0432b58391c98331898312b40291c802318802146401b450019444013008011178120432b5e3f0b52431b4e3f034243ca5e3dca5243c24e3dc24218295218194217c13217413043812a3b003d36803542825c41c12817193042835016d9301098303a802c41c35002802c43046042c26c42425c4202541699404181281018403a403c4140284100243ec2403e82303e42303fc04c4084603e023040414040004c3f80403a183c3a002c1619400381203d40243d01243480243ec3503e81303e403039402c3cc02415d94015c1303c81303c41203d42403c01303481203d00203c82303c40203c02343cc2343bc1403f1c603f03603e03443dc2601599401581300341200fd8400fc03039002c3d80283b8024024020))) (pickBlockF p 7 (pickBlockF p 6 0x55825855023450415847d15054024453414450193c4f823e48123d52814252412a52012851c01154835e5443524f434e47d34d53da5e539a52531a494c124152da3a53c15e5381525301494c294152c13a5181245140392250312c582919d8212c401919c01150c13c4f812c4cc14450193c50012c50014c4f93444f8a444f823450834450425c4fd94c4fc13c4f412c48914c4d01304ec23448515c4c81404e424c4e014c4c593c48124c4d02444d813c4d02344cc14c4c43444ddc544dc3544d434447d25c4c82544c194c4c013c4b12344ad3444a82404a83401991304b034e4ac3424a424248913e48113d4a012d2c103919503149c0214900184883444803444b945e4b54524b9b5e4b5b524993444b825e4b4252498a4449823449415e48c15248514e47d14d48593e47d93d48412e47c12d2bd0491910412bd8391918312bc02919002147801901801147013046c03046834418d94018c13000c120461b5e45db5246025e45c25204d93204c12245805e3d805245404e22504206801e 0x62425e55814d1fa8412e18391b58316200296102504a494060413c4b09204a894061045060014c4ac9304e41304e423a60414e6001425f19212dd8191b181149ca401ad93061845261425e60c2525eda3160814d5fc14c4dc1314989305f80412d98291a98215f0a4c5f014c4f91205ec4544c1a4c4c295c4f41205e41485e01444b01305d02505d82384ac1404a81405d03415a014d52813e4a413259c12d3ec0415cc0293e40215c424e59c2425c023d5bc2355b802946c02151c23e49c2323e814223113247012a5b004e3e404246c02a5dc34f5d43435c824259814f57c14355013f51813e50813b4ec1374d41334981325b412d3e004330503b2290335ac02146801b4480135a025059c2405a5b605a426059823457016057045d59034954434158da5158c1515880493d80412d58291a58212d40191a401158013c57c34457026c57994c57813c57015d56c14e48c14256993e56593d56812e56412d3dc0512cd8391a18312cc0291a00215600190240114e0244554238481140559b58) (pickBlockF p 8 0x7a045f79445378835277a34a78025377824e77424b638a4361ca4276015e73c14e70414c6fc1446e412e40c05331684b24a8431dd8311cc0236cc0196c013c5e41206c435869c3406bda586162406bc1586149405dc1205d81306ac3606983506b434869034060e25060c9505d41206123506109505d01305cc2306ac45161a3426a824e6902426189425c81304080516a40293f802169c45e69845269425e69025231104924504168c0292390215b01205fa3425f8a425ac23040415224114268405e3f805268004e2390426b845f6b04536a03526883425f62425f49425a81203f405330904b23504367c0315e42345e01245dc2346741586701544b9140635b58669b486342586682485d42344b515054414c66414866014448c140631a3a615a3665814553c13e4b81326540492e98291c5821460019040011579a4c58c16c629b4a60db4664823d6442355a415d53814e4b41423f00512e58391bd8316400290fc02145c01903c0114fda4c53015c4f412862c23463445263035e628352 (pickBlockF p 9 0x2000217c801b7c00197b00130c80117a8258630a407a415475c14c73414c62c94077e35879c348628a5075815c75014c79814472824c77c24e634a4274814e72414c7901366f992e43005178c0391018316e001971814c76c26c71425c7002546f823c78414c6ec1286001346f4b4e77c25271ea3876815e5fc1341fd8216d801974425c6f423c74494c6f493c48412472292877034975034176c1515681496ec14176813e62493242c0517640494140411f582173423874c23475c45e75845275435e75035274825271c2487441494fe9414841394f413131e8492568417400392528311ed82173423872c23642804172802910982172024e6de02971813c4f8a4450293c0bd03c73834f73034372424271c23a71414352d13b71013342404370c03b7080331e58211d80137001434200431d40136f9b526f5b4a6f82526f424a6f015e6ec15248514e4f41421d18311d00216e801906801141c1506dc2386e03526d824e620a4241815206c1226d405e4140526d004e25284201402e068022 0x7e5b527aa34a6be3466f025e6ec25281c24e67524233183927183181802926d821218011654a4265423238015237c05281084e26e84281003e26d832814b498142497a123f7a223b6b923766d23365093265012280c04932a83b26683332982b2658232100116482407f414856594002983c7d1b5279d34e66a34280024e6652426ec23e565a3d78413957993143c0517fc0292618212f40192080117f014c7d81347f013c7f424c76c16c7ec15c7e81547e413c6ec12c64423056994c7d41307d813c565a4c7d424458c16c7d013c4381602041300cc12078ea4e640a4278da3e64023233c1521141227c484e2628427c403e26183237c01e0cc01d0cc12813406c7bc85c7b88547bc04c7b80447b403c79534f79634b6b134765d34378aa4e780a4b64ca4363ca42789a3e78023b64c23363c23280494f7f894e7e094b7dc9477cc94355c94280413f7f813e7e013b7dc1377cc13355c13243405132284b25a84332183b2598332ec02920c023))))))
  6 11 7
def m_60090 : Nat := 0xffffffffffffffff
def s_60090 : List Nat := [0x3333333333333333, 0xf0f0f0f0f0f0f0f, 0xff00ff00ff00ff, 0xffff0000ffff, 0xffffffff]
def g_60090 : Nat := 0x30333333f
def bds_60090 : List (Nat × List Nat × Nat × Nat) := [(m_60000, s_60000, 5, g_60000), (m_60001, s_60001, 6, g_60001), (m_60002, s_60002, 6, g_60002), (m_60003, s_60003, 5, g_60003), (m_60004, s_60004, 5, g_60004)]
theorem kn_60090 : KnownBin bds_60090 := by
  intro b hb
  simp only [bds_60090, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact lb_60000
  · exact lb_60001
  · exact lb_60002
  · exact lb_60003
  · exact lb_60004
theorem sub_60090 : ∀ b ∈ bds_60090, m_60090 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_60090, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_60090 : ∀ b ∈ bds_60090, canon b.1 g_60090 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_60090, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_60090 : dagCheckRootsF m_60090 g_60090 bds_60090 (dagRefPermF m_60090 g_60090 63 520 (dagTraceF m_60090 s_60090 8 f_60090) l_60090 0) s_60090 8 = true := by decide +kernel
def picks_60090 (j : Nat) : List Nat :=
  forceW ((pagedUnpackF 5 7 (fun p => (pickBlockF p 2 (pickBlockF p 1 0x200040360dc01094e00001200a0028851a06cc0180e0000001004011c2638020043e00042404018c040080000000010fa13001000040000001013e00401108200980010c0002108000100010010bbe6 0x66e000103100000000007ee43800002000f8063c0c43010e0000620000218fe0044310a72006421084003842102400000210a76086c01080000440007ff004220345080a5010016102702c800738027) (pickBlockF p 3 0x4e320ce4084812103409001205bc00406a0083e0004810002072009c82200c400400000241f08400484084a4200802102401c8781085014240010421083e0406600001f0005f118e09024305001b8ca0 (pickBlockF p 4 0x7c0080230a800181c1f00022fa3390230007414067000801f4420102230fe001003a048201c06e0fc300003e000000ffc000640d0801f0040007c00ffc094c004ca61dac010ee61806210ce1210a400 0x883e0dfea1))))) j) fun w => (List.range 5).filter (fun k => w.testBit k)
def node_60090 (j : Nat) : Bool := withPickedBounds bds_60090 (picks_60090 j) fun cuts =>
  clashNode m_60090 g_60090 cuts (dagTraceF m_60090 s_60090 8 f_60090) (dagRefPermF m_60090 g_60090 63 520 (dagTraceF m_60090 s_60090 8 f_60090) l_60090) (fun _ => none) j
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_60090_0 : treeBlockF 0 48 node_60090 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_60090_1 : treeBlockF 48 96 node_60090 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_60090_2 : treeBlockF 96 144 node_60090 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_60090_3 : treeBlockF 144 192 node_60090 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_60090_4 : treeBlockF 192 240 node_60090 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_60090_5 : treeBlockF 240 288 node_60090 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_60090_6 : treeBlockF 288 336 node_60090 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_60090_7 : treeBlockF 336 384 node_60090 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_60090_8 : treeBlockF 384 432 node_60090 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_60090_9 : treeBlockF 432 480 node_60090 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_60090_10 : treeBlockF 480 520 node_60090 = true := by decide +kernel
theorem nc_60090 : ∀ j, 0 ≤ j → j < 520 → node_60090 j = true :=
  (joinChecks (joinChecks (joinChecks (joinChecks (certBlock nb_60090_0) (certBlock nb_60090_1)) (joinChecks (certBlock nb_60090_2) (certBlock nb_60090_3))) (joinChecks (joinChecks (certBlock nb_60090_4) (certBlock nb_60090_5)) (joinChecks (certBlock nb_60090_6) (certBlock nb_60090_7)))) (joinChecks (joinChecks (certBlock nb_60090_8) (certBlock nb_60090_9)) (certBlock nb_60090_10)))
theorem lb_60090 : LowerBin m_60090 s_60090 g_60090 9 :=
  lowerDagPickedF (top := 63) (picks := picks_60090) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_60090 sub_60090 gl_60090 rc_60090 (by
    intro j hlo hhi
    have hj := nc_60090 j hlo hhi
    simp only [node_60090, withPickedBounds_eq] at hj
    exact clashNode_sound _ _ _ _ _ _ _ hj)

def m_2293 : Nat := 0xaaaaaaaaaaaaaaaa
def s_2293 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_2293 : Nat := 0x20222222a
theorem lb_2293 : LowerBin m_2293 s_2293 g_2293 9 :=
  lowerByCheckedRows (unpackRows 64 0xffff7defbe79df7d75cf3c71befb6daeba699e79658e38617df75d6db6595d75554d34513cf34d2cb2491c71450c3041) lb_60090 (by decide +kernel)

def m_2295 : Nat := 0x3333333333333333
def s_2295 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_2295 : Nat := 0x111111313333333
theorem lb_2295 : LowerBin m_2295 s_2295 g_2295 9 :=
  lowerByCheckedRows (unpackRows 64 0x2042102142202242302342402442502542602642702742802842902942a02a42b02b42c02c42d02d42e02e42f02f42) lb_2293 (by decide +kernel)

def f_2297 : Nat → Nat × Nat := fun _ => (0, 0)
def l_2297 : Nat → Nat → Option Nat := fun _ _ => none
def m_2297 : Nat := 0xcccccccccccccccc
def s_2297 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_2297 : Nat := 0x404440004044c
def bds_2297 : List (Nat × List Nat × Nat × Nat) := [(m_1765, s_1765, 7, g_1765)]
theorem kn_2297 : KnownBin bds_2297 := by
  intro b hb
  simp only [bds_2297, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_1765
theorem sub_2297 : ∀ b ∈ bds_2297, m_2297 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_2297, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_2297 : ∀ b ∈ bds_2297, canon b.1 g_2297 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_2297, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_2297 : dagCheckRootsF m_2297 g_2297 bds_2297 (dagRefF 0 (dagTraceF m_2297 s_2297 7 f_2297) l_2297 0) s_2297 7 = true := by decide +kernel
def node_2297 : Nat → Bool := dagCheckNodeF m_2297 g_2297 bds_2297 0 (dagTraceF m_2297 s_2297 7 f_2297) l_2297
theorem nc_2297 : ∀ j, 0 ≤ j → j < 0 → node_2297 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_2297 : LowerBin m_2297 s_2297 g_2297 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2297 sub_2297 gl_2297 rc_2297 nc_2297

def f_2294 : Nat → Nat × Nat := unpackForestF 0xe9498cea7c5334a72508a4601f 3 10
def l_2294 : Nat → Nat → Option Nat := unpackLinksF 0x288a06986121c1 0x3a52921a9f24c9a9c942d19c4cca4601f 6 2 10 3 3
def m_2294 : Nat := 0xaaaaaaaaaaaaaaaa
def s_2294 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_2294 : Nat := 0x20222222a
def bds_2294 : List (Nat × List Nat × Nat × Nat) := [(m_1761, s_1761, 6, g_1761), (m_1806, s_1806, 5, g_1806), (m_1871, s_1871, 5, g_1871), (m_1947, s_1947, 5, g_1947), (m_2026, s_2026, 6, g_2026)]
theorem kn_2294 : KnownBin bds_2294 := by
  intro b hb
  simp only [bds_2294, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact lb_1761
  · exact lb_1806
  · exact lb_1871
  · exact lb_1947
  · exact lb_2026
theorem sub_2294 : ∀ b ∈ bds_2294, m_2294 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_2294, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_2294 : ∀ b ∈ bds_2294, canon b.1 g_2294 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_2294, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_2294 : dagCheckRootsF m_2294 g_2294 bds_2294 (dagRefF 8 (dagTraceF m_2294 s_2294 7 f_2294) l_2294 0) s_2294 7 = true := by decide +kernel
def node_2294 : Nat → Bool := dagCheckNodeF m_2294 g_2294 bds_2294 8 (dagTraceF m_2294 s_2294 7 f_2294) l_2294
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2294_0 : treeBlockF 0 8 node_2294 = true := by decide +kernel
theorem nc_2294 : ∀ j, 0 ≤ j → j < 8 → node_2294 j = true :=
  (certBlock nb_2294_0)
theorem lb_2294 : LowerBin m_2294 s_2294 g_2294 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2294 sub_2294 gl_2294 rc_2294 nc_2294

def m_2296 : Nat := 0x3333333333333333
def s_2296 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_2296 : Nat := 0x111111313333333
theorem lb_2296 : LowerBin m_2296 s_2296 g_2296 8 :=
  lowerByCheckedRows (unpackRows 64 0x2042102142202242302342402442502542602642702742802842902942a02a42b02b42c02c42d02d42e02e42f02f42) lb_2294 (by decide +kernel)

def f_2299 : Nat → Nat × Nat := unpackForestF 0x1d1e323064b7cac18edaa3054b5aac14ed0ab21460a4628d4495882b1888204c223001f 5 10
def l_2299 : Nat → Nat → Option Nat := unpackLinksF 0xb9b8b1b0a2a099988a81806b6868686861440f01 0x30891919f2b14566a8cb55882b0c444aac851842b0c44346a54ac8158813968f092dd1db14b5276748c223001f 8 3 10 5 4
def m_2299 : Nat := 0xf0f0f0f0f0f0f0f
def s_2299 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_2299 : Nat := 0x10505070307070f
def bds_2299 : List (Nat × List Nat × Nat × Nat) := [(m_1986, s_1986, 6, g_1986), (m_1776, s_1776, 5, g_1776), (m_1745, s_1745, 5, g_1745), (m_1828, s_1828, 5, g_1828), (m_1963, s_1963, 5, g_1963), (m_1947, s_1947, 5, g_1947), (m_1978, s_1978, 4, g_1978), (m_1984, s_1984, 4, g_1984)]
theorem kn_2299 : KnownBin bds_2299 := by
  intro b hb
  simp only [bds_2299, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_1986
  · exact lb_1776
  · exact lb_1745
  · exact lb_1828
  · exact lb_1963
  · exact lb_1947
  · exact lb_1978
  · exact lb_1984
theorem sub_2299 : ∀ b ∈ bds_2299, m_2299 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_2299, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_2299 : ∀ b ∈ bds_2299, canon b.1 g_2299 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_2299, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_2299 : dagCheckRootsF m_2299 g_2299 bds_2299 (dagRefF 19 (dagTraceF m_2299 s_2299 7 f_2299) l_2299 0) s_2299 7 = true := by decide +kernel
def node_2299 : Nat → Bool := dagCheckNodeF m_2299 g_2299 bds_2299 19 (dagTraceF m_2299 s_2299 7 f_2299) l_2299
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2299_0 : treeBlockF 0 19 node_2299 = true := by decide +kernel
theorem nc_2299 : ∀ j, 0 ≤ j → j < 19 → node_2299 j = true :=
  (certBlock nb_2299_0)
theorem lb_2299 : LowerBin m_2299 s_2299 g_2299 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2299 sub_2299 gl_2299 rc_2299 nc_2299

def m_2309 : Nat := 0xffff0000ffff0000
def s_2309 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_2309 : Nat := 0x115000013370000
theorem lb_2309 : LowerBin m_2309 s_2309 g_2309 8 :=
  lowerByCheckedRows (unpackRows 60 0x41245300000051655700000061a65b00000071e75f000000c32c73000000d36d77000000e3ae7b000000f3ef7f) lb_2299 (by decide +kernel)

def m_2306 : Nat := 0xffff0000ffff
def s_2306 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_2306 : Nat := 0x15570000377f
theorem lb_2306 : LowerBin m_2306 s_2306 g_2306 9 :=
  lowerByCheckedRows (unpackRows 60 0xbeeb6c410410aeaa684104109e69644104108e28604104103ce34c4104102ca2484104101c61444104100c2040) lb_2298 (by decide +kernel)

def m_2135 : Nat := 0x5555555500000000
def s_2135 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_2135 : Nat := 0x115155500000000
theorem lb_2135 : LowerBin m_2135 s_2135 g_2135 7 :=
  lowerByCheckedRows (unpackRows 30 0xeb8000cb0000aa80008a0fbc000db4000bac0009a4000) lb_1749 (by decide +kernel)

def m_2307 : Nat := 0xffff0000ffff
def s_2307 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_2307 : Nat := 0x15570000377f
theorem lb_2307 : LowerBin m_2307 s_2307 g_2307 8 :=
  lowerByCheckedRows (unpackRows 60 0xbeeb6c410410aeaa684104109e69644104108e28604104103ce34c4104102ca2484104101c61444104100c2040) lb_2299 (by decide +kernel)

def m_2301 : Nat := 0xf0f0f0f0f0f0f0f0
def s_2301 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_2301 : Nat := 0x10105010303070
theorem lb_2301 : LowerBin m_2301 s_2301 g_2301 8 :=
  lowerByCheckedRows (unpackRows 60 0x10614700000030e34f00000051655700000071e75f000000926967000000b2eb6f000000d36d77000000f3ef7f) lb_2299 (by decide +kernel)

def m_1902 : Nat := 0xff00ff00000000
def s_1902 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_1902 : Nat := 0x15005700000000
theorem lb_1902 : LowerBin m_1902 s_1902 g_1902 6 :=
  lowerByCheckedRows (unpackRows 32 0xdc0d80d40d00cc0c80c40c009c09809409008c0880840800) lb_1761 (by decide +kernel)

def m_2305 : Nat := 0xff00ff00ff00ff00
def s_2305 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_2305 : Nat := 0x100150013003700
theorem lb_2305 : LowerBin m_2305 s_2305 g_2305 8 :=
  lowerByCheckedRows (unpackRows 60 0x20a24b00000030e34f00000061a65b00000071e75f000000a2aa6b000000b2eb6f000000e3ae7b000000f3ef7f) lb_2299 (by decide +kernel)

def m_2070 : Nat := 0x3333333300000000
def s_2070 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_2070 : Nat := 0x111111300000000
theorem lb_2070 : LowerBin m_2070 s_2070 g_2070 6 :=
  lowerByCheckedRows (unpackRows 32 0xf40f00e40e00d40d00c40c00b40b00a40a00940900840800) lb_1761 (by decide +kernel)

def m_444 : Nat := 0x666600000000
def s_444 : List Nat := [0x222200000000, 0x60600000000, 0x6600000000]
def g_444 : Nat := 0x44600000000
theorem lb_444 : LowerBin m_444 s_444 g_444 4 :=
  lowerByCheckedRows (unpackRows 16 0xb6e000a6a000966000862000) lb_15 (by decide +kernel)

def m_439 : Nat := 0x606000006060
def s_439 : List Nat := [0x202000002020, 0x6000000060, 0x6060]
def g_439 : Nat := 0x4000002060
def bds_439 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_439 : KnownBin bds_439 := by
  intro b hb
  simp [bds_439] at hb
theorem sub_439 : ∀ b ∈ bds_439, m_439 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_439] at hb
theorem gl_439 : ∀ b ∈ bds_439, canon b.1 g_439 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_439] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_439 : dagCheckRootsF m_439 g_439 bds_439 (dagRefF 1 (dagTraceF m_439 s_439 2 f_15) l_15 0) s_439 2 = true := by decide +kernel
def node_439 : Nat → Bool := dagCheckNodeF m_439 g_439 bds_439 1 (dagTraceF m_439 s_439 2 f_15) l_15
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_439_0 : treeBlockF 0 1 node_439 = true := by decide +kernel
theorem nc_439 : ∀ j, 0 ≤ j → j < 1 → node_439 j = true :=
  (certBlock nb_439_0)
theorem lb_439 : LowerBin m_439 s_439 g_439 3 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_439 sub_439 gl_439 rc_439 nc_439

def m_442 : Nat := 0x660000006600
def s_442 : List Nat := [0x220000002200, 0x60000000600, 0x6600]
def g_442 : Nat := 0x40000002600
theorem lb_442 : LowerBin m_442 s_442 g_442 3 :=
  lowerByCheckedRows (unpackRows 47 0x2eb4000000002aa4000000000000000000000000000000000e34000000000a240000000) lb_439 (by decide +kernel)

def f_1798 : Nat → Nat × Nat := unpackForestF 0x41340c7ee13031bb2340a7ea13029b8527384824f449a9124107a20d421f000f 5 10
def l_1798 : Nat → Nat → Option Nat := unpackLinksF 0xb1a2a092897a786a686861606059583c0e01 0x70f209a184c709850f081632341898a13041e1c24224864f4a9a8c3d106af8fdb1bad3f4a6e849c21f000f 8 3 10 5 4
def m_1798 : Nat := 0x666600006666
def s_1798 : List Nat := [0x222200002222, 0x60600000606, 0x6600000066, 0x6666]
def g_1798 : Nat := 0x44600002666
def bds_1798 : List (Nat × List Nat × Nat × Nat) := [(m_444, s_444, 4, g_444), (m_439, s_439, 3, g_439), (m_442, s_442, 3, g_442)]
theorem kn_1798 : KnownBin bds_1798 := by
  intro b hb
  simp only [bds_1798, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact lb_444
  · exact lb_439
  · exact lb_442
theorem sub_1798 : ∀ b ∈ bds_1798, m_1798 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1798, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl <;> decide +kernel
theorem gl_1798 : ∀ b ∈ bds_1798, canon b.1 g_1798 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1798, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1798 : dagCheckRootsF m_1798 g_1798 bds_1798 (dagRefF 17 (dagTraceF m_1798 s_1798 5 f_1798) l_1798 0) s_1798 5 = true := by decide +kernel
def node_1798 : Nat → Bool := dagCheckNodeF m_1798 g_1798 bds_1798 17 (dagTraceF m_1798 s_1798 5 f_1798) l_1798
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1798_0 : treeBlockF 0 17 node_1798 = true := by decide +kernel
theorem nc_1798 : ∀ j, 0 ≤ j → j < 17 → node_1798 j = true :=
  (certBlock nb_1798_0)
theorem lb_1798 : LowerBin m_1798 s_1798 g_1798 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1798 sub_1798 gl_1798 rc_1798 nc_1798

def m_2149 : Nat := 0x6060606060606060
def s_2149 : List Nat := [0x2020202020202020, 0x60006000600060, 0x606000006060, 0x60606060]
def g_2149 : Nat := 0x4000202060
theorem lb_2149 : LowerBin m_2149 s_2149 g_2149 6 :=
  lowerByCheckedRows (unpackRows 47 0x614000e34001654001e74000000000000000000000000002694002eb40036d4003ef40) lb_1798 (by decide +kernel)

def m_2139 : Nat := 0x55aa55aa00000000
def s_2139 : List Nat := [0xaa00aa00000000, 0x1122112200000000, 0x50a050a00000000, 0x55aa00000000]
def g_2139 : Nat := 0x100150200000000
theorem lb_2139 : LowerBin m_2139 s_2139 g_2139 7 :=
  lowerByCheckedRows (unpackRows 30 0xaa3000ba7000eb3000fb7a21000b25000e31000f35000) lb_1749 (by decide +kernel)

def m_2041 : Nat := 0x3003300330033003
def s_2041 : List Nat := [0x1001100110011001, 0x3000300030003, 0x300300003003, 0x30033003]
def g_2041 : Nat := 0x1100310033003
theorem lb_2041 : LowerBin m_2041 s_2041 g_2041 7 :=
  lowerByCheckedRows (unpackRows 30 0xc70082860082450082040f7c082b6c08275c08234c082) lb_1749 (by decide +kernel)

def m_1861 : Nat := 0x66006600660066
def s_1861 : List Nat := [0x22002200220022, 0x6000600060006, 0x6600000066, 0x660066]
def g_1861 : Nat := 0x4004600260066
theorem lb_1861 : LowerBin m_1861 s_1861 g_1861 6 :=
  lowerByCheckedRows (unpackRows 47 0x36d40032c40026940022840000000000000000000000000016540012440006140002040) lb_1798 (by decide +kernel)

def f_2292 : Nat → Nat × Nat := fun _ => (0, 0)
def l_2292 : Nat → Nat → Option Nat := fun _ _ => none
def m_2292 : Nat := 0x5555555555555555
def s_2292 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_2292 : Nat := 0x115155511151555
def bds_2292 : List (Nat × List Nat × Nat × Nat) := [(m_2135, s_2135, 7, g_2135)]
theorem kn_2292 : KnownBin bds_2292 := by
  intro b hb
  simp only [bds_2292, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_2135
theorem sub_2292 : ∀ b ∈ bds_2292, m_2292 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_2292, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_2292 : ∀ b ∈ bds_2292, canon b.1 g_2292 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_2292, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_2292 : dagCheckRootsF m_2292 g_2292 bds_2292 (dagRefF 0 (dagTraceF m_2292 s_2292 7 f_2292) l_2292 0) s_2292 7 = true := by decide +kernel
def node_2292 : Nat → Bool := dagCheckNodeF m_2292 g_2292 bds_2292 0 (dagTraceF m_2292 s_2292 7 f_2292) l_2292
theorem nc_2292 : ∀ j, 0 ≤ j → j < 0 → node_2292 j = true := fun _ _ hj => absurd hj (Nat.not_lt_zero _)
theorem lb_2292 : LowerBin m_2292 s_2292 g_2292 8 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2292 sub_2292 gl_2292 rc_2292 nc_2292

def m_2303 : Nat := 0xff00ff00ff00ff
def s_2303 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_2303 : Nat := 0x1500570037007f
theorem lb_2303 : LowerBin m_2303 s_2303 g_2303 8 :=
  lowerByCheckedRows (unpackRows 60 0xdf6d74208208cf2c702082089e69642082088e28602082085d65542082084d24502082081c61442082080c2040) lb_2299 (by decide +kernel)

def m_2152 : Nat := 0x6600660066006600
def s_2152 : List Nat := [0x2200220022002200, 0x600060006000600, 0x660000006600, 0x66006600]
def g_2152 : Nat := 0x40002002600
theorem lb_2152 : LowerBin m_2152 s_2152 g_2152 6 :=
  lowerByCheckedRows (unpackRows 47 0xa24000e34001a64001e74000000000000000000000000002aa4002eb4003ae4003ef40) lb_1798 (by decide +kernel)

def m_1936 : Nat := 0x606060606060606
def s_1936 : List Nat := [0x202020202020202, 0x6000600060006, 0x60600000606, 0x6060606]
def g_1936 : Nat := 0x4040602060606
theorem lb_1936 : LowerBin m_1936 s_1936 g_1936 6 :=
  lowerByCheckedRows (unpackRows 47 0x3ae40032c4002aa4002284000000000000000000000000001a64001244000a240002040) lb_1798 (by decide +kernel)

def m_2145 : Nat := 0x5a5a5a5a00000000
def s_2145 : List Nat := [0xa0a0a0a00000000, 0x1212121200000000, 0x5a005a00000000, 0x5a5a00000000]
def g_2145 : Nat := 0x10105200000000
theorem lb_2145 : LowerBin m_2145 s_2145 g_2145 7 :=
  lowerByCheckedRows (unpackRows 30 0x9a3000bab000db3000fbb921000b29000d31000f39000) lb_1749 (by decide +kernel)

def m_2154 : Nat := 0x6666000066660000
def s_2154 : List Nat := [0x2222000022220000, 0x606000006060000, 0x66000000660000, 0x66660000]
def g_2154 : Nat := 0x4000002260000
theorem lb_2154 : LowerBin m_2154 s_2154 g_2154 6 :=
  lowerByCheckedRows (unpackRows 47 0x1244001654001a64001e740000000000000000000000000032c40036d4003ae4003ef40) lb_1798 (by decide +kernel)

def m_2190 : Nat := 0xa00aa00aa00aa00a
def s_2190 : List Nat := [0x2002200220022002, 0xa000a000a000a, 0xa00a0000a00a, 0xa00aa00a]
def g_2190 : Nat := 0x20002200a
theorem lb_2190 : LowerBin m_2190 s_2190 g_2190 7 :=
  lowerByCheckedRows (unpackRows 30 0x34f00075f000b6f000f7f043000453000863000c73000) lb_1749 (by decide +kernel)

def m_2155 : Nat := 0x6666666600000000
def s_2155 : List Nat := [0x2222222200000000, 0x606060600000000, 0x66006600000000, 0x666600000000]
def g_2155 : Nat := 0x4044600000000
theorem lb_2155 : LowerBin m_2155 s_2155 g_2155 7 :=
  lowerByCheckedRows (unpackRows 30 0x9a5000bad000db5000fbd8a1000aa9000cb1000eb9000) lb_1749 (by decide +kernel)

def m_157 : Nat := 0x66660000
def s_157 : List Nat := [0x22220000, 0x6060000, 0x660000]
def g_157 : Nat := 0x2260000
theorem lb_157 : LowerBin m_157 s_157 g_157 4 :=
  lowerByCheckedRows (unpackRows 16 0x79d000699000595000491000) lb_15 (by decide +kernel)

def m_402 : Nat := 0x444444440000
def s_402 : List Nat := [0x40404040000, 0x4400440000, 0x44440000]
def g_402 : Nat := 0x44400040000
theorem lb_402 : LowerBin m_402 s_402 g_402 4 :=
  lowerByCheckedRows (unpackRows 16 0x8a6000aae00049600069e000) lb_15 (by decide +kernel)

def m_355 : Nat := 0x222222220000
def s_355 : List Nat := [0x20202020000, 0x2200220000, 0x22220000]
def g_355 : Nat := 0x202220000
theorem lb_355 : LowerBin m_355 s_355 g_355 4 :=
  lowerByCheckedRows (unpackRows 16 0xb69000961000759000551000) lb_15 (by decide +kernel)

def f_290 : Nat → Nat × Nat := unpackForestF 0x32d32592c21a424216007 3 9
def l_290 : Nat → Nat → Option Nat := unpackLinksF 0x82e5c3160a4601 0x81841492c424d2db2561a216007 7 3 9 3 4
def m_290 : Nat := 0x60606060000
def s_290 : List Nat := [0x20202020000, 0x600060000, 0x6060000]
def g_290 : Nat := 0x20004000000
def bds_290 : List (Nat × List Nat × Nat × Nat) := []
theorem kn_290 : KnownBin bds_290 := by
  intro b hb
  simp [bds_290] at hb
theorem sub_290 : ∀ b ∈ bds_290, m_290 &&& b.1 = b.1 := by
  intro b hb
  simp [bds_290] at hb
theorem gl_290 : ∀ b ∈ bds_290, canon b.1 g_290 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp [bds_290] at hb
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_290 : dagCheckRootsF m_290 g_290 bds_290 (dagRefF 7 (dagTraceF m_290 s_290 3 f_290) l_290 0) s_290 3 = true := by decide +kernel
def node_290 : Nat → Bool := dagCheckNodeF m_290 g_290 bds_290 7 (dagTraceF m_290 s_290 3 f_290) l_290
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_290_0 : treeBlockF 0 7 node_290 = true := by decide +kernel
theorem nc_290 : ∀ j, 0 ≤ j → j < 7 → node_290 j = true :=
  (certBlock nb_290_0)
theorem lb_290 : LowerBin m_290 s_290 g_290 4 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_290 sub_290 gl_290 rc_290 nc_290

def m_440 : Nat := 0x606060600000
def s_440 : List Nat := [0x202020200000, 0x6000600000, 0x60600000]
def g_440 : Nat := 0x4000200000
theorem lb_440 : LowerBin m_440 s_440 g_440 4 :=
  lowerByCheckedRows (unpackRows 43 0x2598000000002db8000000001558000000001d780000000000000000000000000) lb_290 (by decide +kernel)

def m_1799 : Nat := 0x666666660000
def s_1799 : List Nat := [0x222222220000, 0x60606060000, 0x6600660000, 0x66660000]
def g_1799 : Nat := 0x44602260000
def bds_1799 : List (Nat × List Nat × Nat × Nat) := [(m_444, s_444, 4, g_444), (m_157, s_157, 4, g_157), (m_402, s_402, 4, g_402), (m_355, s_355, 4, g_355), (m_440, s_440, 4, g_440), (m_290, s_290, 4, g_290)]
theorem kn_1799 : KnownBin bds_1799 := by
  intro b hb
  simp only [bds_1799, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_444
  · exact lb_157
  · exact lb_402
  · exact lb_355
  · exact lb_440
  · exact lb_290
theorem sub_1799 : ∀ b ∈ bds_1799, m_1799 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1799, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_1799 : ∀ b ∈ bds_1799, canon b.1 g_1799 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1799, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1799 : dagCheckRootsF m_1799 g_1799 bds_1799 (dagRefF 1 (dagTraceF m_1799 s_1799 6 f_1820) l_1820 0) s_1799 6 = true := by decide +kernel
def node_1799 : Nat → Bool := dagCheckNodeF m_1799 g_1799 bds_1799 1 (dagTraceF m_1799 s_1799 6 f_1820) l_1820
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1799_0 : treeBlockF 0 1 node_1799 = true := by decide +kernel
theorem nc_1799 : ∀ j, 0 ≤ j → j < 1 → node_1799 j = true :=
  (certBlock nb_1799_0)
theorem lb_1799 : LowerBin m_1799 s_1799 g_1799 7 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1799 sub_1799 gl_1799 rc_1799 nc_1799

def m_1750 : Nat := 0x33cc33cc
def s_1750 : List Nat := [0x11441144, 0xcc00cc, 0x30c030c, 0x33cc]
def g_1750 : Nat := 0x1304334c
theorem lb_1750 : LowerBin m_1750 s_1750 g_1750 7 :=
  lowerByCheckedRows (unpackRows 30 0x75c00065800034c0002485d60004d20001c60000c2000) lb_1749 (by decide +kernel)

def m_1862 : Nat := 0x66006666006600
def s_1862 : List Nat := [0x22002222002200, 0x6000606000600, 0x66006600, 0x6600006600]
def g_1862 : Nat := 0x4004602002600
theorem lb_1862 : LowerBin m_1862 s_1862 g_1862 7 :=
  lowerByCheckedRows (unpackRows 47 0x36d40032c4002694002284001e74001a64000e34000a240000000000000000000000000) lb_1799 (by decide +kernel)

def m_2045 : Nat := 0x3030030330300303
def s_2045 : List Nat := [0x1010010110100101, 0x30300000303, 0x30000300300003, 0x30300303]
def g_2045 : Nat := 0x10010310300303
theorem lb_2045 : LowerBin m_2045 s_2045 g_2045 7 :=
  lowerByCheckedRows (unpackRows 30 0xa68082860082248082040f7c082d7408275c082554082) lb_1749 (by decide +kernel)

def m_2196 : Nat := 0xa0a00a0aa0a00a0a
def s_2196 : List Nat := [0x2020020220200202, 0xa0a00000a0a, 0xa0000a00a0000a, 0xa0a00a0a]
def g_2196 : Nat := 0x20020020a
theorem lb_2196 : LowerBin m_2196 s_2196 g_2196 7 :=
  lowerByCheckedRows (unpackRows 30 0x55700075f000d77000f7f04300024b000863000a6b000) lb_1749 (by decide +kernel)

def m_1937 : Nat := 0x606060660606060
def s_1937 : List Nat := [0x202020220202020, 0x60606060, 0x6000600600060, 0x60600006060]
def g_1937 : Nat := 0x4040600202060
theorem lb_1937 : LowerBin m_1937 s_1937 g_1937 7 :=
  lowerByCheckedRows (unpackRows 47 0x3ae40032c4002aa4002284001e74001654000e340006140000000000000000000000000) lb_1799 (by decide +kernel)

def m_126 : Nat := 0x33cc0000
def s_126 : List Nat := [0x11440000, 0xcc0000, 0x30c0000]
def g_126 : Nat := 0x13040000
theorem lb_126 : LowerBin m_126 s_126 g_126 4 :=
  lowerByCheckedRows (unpackRows 16 0x5d600075c0004d2000658000) lb_15 (by decide +kernel)

def f_1787 : Nat → Nat × Nat := unpackForestF 0xc7e18eeea65d40b88018de6944d24985018cdf1c3e34787014fd69e2d34583014ec29b85330a5e68f029590300a4e2060291800f 5 10
def l_1787 : Nat → Nat → Option Nat := unpackLinksF 0x1d0e8743a1d0d1e8341a0b9dc2e170a1d02814089c422101803c5e0e1703443801 0x654cc2817102a945124985118e211a3c386a78c4d160c1938347840c040c6e3fd47768de519b93f527694dd0999d2f2a56349c291800f 9 4 10 5 5
def m_1787 : Nat := 0x33cc33cc0000
def s_1787 : List Nat := [0x114411440000, 0xcc00cc0000, 0x30c030c0000, 0x33cc0000]
def g_1787 : Nat := 0x114413040000
def bds_1787 : List (Nat × List Nat × Nat × Nat) := [(m_126, s_126, 4, g_126)]
theorem kn_1787 : KnownBin bds_1787 := by
  intro b hb
  simp only [bds_1787, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl
  · exact lb_126
theorem sub_1787 : ∀ b ∈ bds_1787, m_1787 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_1787, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
theorem gl_1787 : ∀ b ∈ bds_1787, canon b.1 g_1787 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_1787, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_1787 : dagCheckRootsF m_1787 g_1787 bds_1787 (dagRefF 28 (dagTraceF m_1787 s_1787 5 f_1787) l_1787 0) s_1787 5 = true := by decide +kernel
def node_1787 : Nat → Bool := dagCheckNodeF m_1787 g_1787 bds_1787 28 (dagTraceF m_1787 s_1787 5 f_1787) l_1787
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_1787_0 : treeBlockF 0 28 node_1787 = true := by decide +kernel
theorem nc_1787 : ∀ j, 0 ≤ j → j < 28 → node_1787 j = true :=
  (certBlock nb_1787_0)
theorem lb_1787 : LowerBin m_1787 s_1787 g_1787 6 :=
  lowerDagF (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_1787 sub_1787 gl_1787 rc_1787 nc_1787

def m_1797 : Nat := 0x5a5a5a5a0000
def s_1797 : List Nat := [0xa0a0a0a0000, 0x121212120000, 0x5a005a0000, 0x5a5a0000]
def g_1797 : Nat := 0x105212120000
theorem lb_1797 : LowerBin m_1797 s_1797 g_1797 6 :=
  lowerByCheckedRows (unpackRows 46 0x79c0005946d90004d1000000bac0009a4ae90008e1000000000000000000000000000) lb_1787 (by decide +kernel)

def m_1802 : Nat := 0xa5a5a5a50000
def s_1802 : List Nat := [0x50505050000, 0x212121210000, 0xa500a50000, 0xa5a50000]
def g_1802 : Nat := 0x50501250000
theorem lb_1802 : LowerBin m_1802 s_1802 g_1802 6 :=
  lowerByCheckedRows (unpackRows 46 0xb68000960bea0009e20000007580005507da0005d2000000000000000000000000000) lb_1787 (by decide +kernel)

def m_1812 : Nat := 0xcc33cc330000
def s_1812 : List Nat := [0x441144110000, 0x3300330000, 0xc030c030000, 0xcc330000]
def g_1812 : Nat := 0x41300330000
theorem lb_1812 : LowerBin m_1812 s_1812 g_1812 6 :=
  lowerByCheckedRows (unpackRows 46 0x7940006907d50006d1000000ba4000aa0be5000ae1000000000000000000000000000) lb_1787 (by decide +kernel)

def m_2146 : Nat := 0x6006600660066006
def s_2146 : List Nat := [0x2002200220022002, 0x6000600060006, 0x600600006006, 0x60066006]
def g_2146 : Nat := 0x4000600062006
theorem lb_2146 : LowerBin m_2146 s_2146 g_2146 6 :=
  lowerByCheckedRows (unpackRows 46 0xba2000382fb2000792000000b61000341f71000751000000000000000000000000000) lb_1787 (by decide +kernel)

def m_1751 : Nat := 0x3c3c3c3c
def s_1751 : List Nat := [0x14141414, 0xc0c0c0c, 0x3c003c, 0x3c3c]
def g_1751 : Nat := 0x1034343c
theorem lb_1751 : LowerBin m_1751 s_1751 g_1751 7 :=
  lowerByCheckedRows (unpackRows 30 0x75c00055400034c0001446da0004d20002ca0000c2000) lb_1749 (by decide +kernel)

def m_2131 : Nat := 0x5555000000005555
def s_2131 : List Nat := [0x1111000000001111, 0x505000000000505, 0x55000000000055, 0x5555]
def g_2131 : Nat := 0x115000000001555
theorem lb_2131 : LowerBin m_2131 s_2131 g_2131 7 :=
  lowerByCheckedRows (unpackRows 30 0xeb8041cb0041288041080fbc041db404138c041184041) lb_1749 (by decide +kernel)

def m_2262 : Nat := 0xcccc00000000cccc
def s_2262 : List Nat := [0x4444000000004444, 0xc0c000000000c0c, 0xcc0000000000cc, 0xcccc]
def g_2262 : Nat := 0x400000000044c
theorem lb_2262 : LowerBin m_2262 s_2262 g_2262 7 :=
  lowerByCheckedRows (unpackRows 30 0x18700038f000db7000fbf08300028b000cb3000ebb000) lb_1749 (by decide +kernel)

def m_2308 : Nat := 0xffff0000ffff0000
def s_2308 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_2308 : Nat := 0x115000013370000
theorem lb_2308 : LowerBin m_2308 s_2308 g_2308 9 :=
  lowerByCheckedRows (unpackRows 60 0x41245300000051655700000061a65b00000071e75f000000c32c73000000d36d77000000e3ae7b000000f3ef7f) lb_2298 (by decide +kernel)

def m_1827 : Nat := 0xffff00000000
def s_1827 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_1827 : Nat := 0x155700000000
theorem lb_1827 : LowerBin m_1827 s_1827 g_1827 6 :=
  lowerByCheckedRows (unpackRows 32 0xbc0b80b40b00ac0a80a40a009c09809409008c0880840800) lb_1761 (by decide +kernel)

def m_2057 : Nat := 0x3300003333000033
def s_2057 : List Nat := [0x1100001111000011, 0x300000303000003, 0x3300000033, 0x33000033]
def g_2057 : Nat := 0x100001313000033
theorem lb_2057 : LowerBin m_2057 s_2057 g_2057 7 :=
  lowerByCheckedRows (unpackRows 30 0xe78082860082658082040f7c08296408275c082144082) lb_1749 (by decide +kernel)

def m_2211 : Nat := 0xaa0000aaaa0000aa
def s_2211 : List Nat := [0x2200002222000022, 0xa00000a0a00000a, 0xaa000000aa, 0xaa0000aa]
def g_2211 : Nat := 0x20200002a
theorem lb_2211 : LowerBin m_2211 s_2211 g_2211 7 :=
  lowerByCheckedRows (unpackRows 30 0x14700075f000967000f7f04300065b000863000e7b000) lb_1749 (by decide +kernel)

def m_2150 : Nat := 0x6600006666000066
def s_2150 : List Nat := [0x2200002222000022, 0x600000606000006, 0x6600000066, 0x66000066]
def g_2150 : Nat := 0x4602000066
theorem lb_2150 : LowerBin m_2150 s_2150 g_2150 6 :=
  lowerByCheckedRows (unpackRows 46 0xea2000682fa6000786000000e61000641f65000745000000000000000000000000000) lb_1787 (by decide +kernel)

def m_1946 : Nat := 0xa0a0a0a05050505
def s_1946 : List Nat := [0x5050505, 0x202020201010101, 0xa000a00050005, 0xa0a00000505]
def g_1946 : Nat := 0x201050505
theorem lb_1946 : LowerBin m_1946 s_1946 g_1946 6 :=
  lowerByCheckedRows (unpackRows 32 0xec1681e41601cc1481c41401ac1281a412018c1081841001) lb_1761 (by decide +kernel)

def m_2136 : Nat := 0x5555aaaa00000000
def s_2136 : List Nat := [0xaaaa00000000, 0x1111222200000000, 0x5050a0a00000000, 0x5500aa00000000]
def g_2136 : Nat := 0x115000200000000
theorem lb_2136 : LowerBin m_2136 s_2136 g_2136 7 :=
  lowerByCheckedRows (unpackRows 30 0xca3000da7000eab000fafc21000d25000e29000f2d000) lb_1749 (by decide +kernel)

def m_1993 : Nat := 0x1111111144444444
def s_1993 : List Nat := [0x44444444, 0x101010104040404, 0x11001100440044, 0x111100004444]
def g_1993 : Nat := 0x111111100040444
theorem lb_1993 : LowerBin m_1993 s_1993 g_1993 7 :=
  lowerByCheckedRows (unpackRows 30 0x6b80004b00002a80000a07bc0005b40003ac0001a4000) lb_1749 (by decide +kernel)

def m_2256 : Nat := 0xcc00cc0033003300
def s_2256 : List Nat := [0x4400440011001100, 0x33003300, 0xc000c0003000300, 0xcc0000003300]
def g_2256 : Nat := 0x40013003300
theorem lb_2256 : LowerBin m_2256 s_2256 g_2256 6 :=
  lowerByCheckedRows (unpackRows 32 0xfc0740f80700ec0640e80600bc0340b80300ac0240a80200) lb_1761 (by decide +kernel)

def m_2125 : Nat := 0x5500550000550055
def s_2125 : List Nat := [0x1100110000110011, 0x500050000050005, 0x550055, 0x550000000055]
def g_2125 : Nat := 0x100150000150055
theorem lb_2125 : LowerBin m_2125 s_2125 g_2125 7 :=
  lowerByCheckedRows (unpackRows 30 0xeb8041490041aa8041080fbc041594041bac041184041) lb_1749 (by decide +kernel)

def m_2096 : Nat := 0x4444444488888888
def s_2096 : List Nat := [0x88888888, 0x404040408080808, 0x44004400880088, 0x444400008888]
def g_2096 : Nat := 0x4044400000008
theorem lb_2096 : LowerBin m_2096 s_2096 g_2096 7 :=
  lowerByCheckedRows (unpackRows 30 0x987000b8f000d97000f9f883000a8b000c93000e9b000) lb_1749 (by decide +kernel)

def m_2027 : Nat := 0x2222222244444444
def s_2027 : List Nat := [0x44444444, 0x202020204040404, 0x22002200440044, 0x222200004444]
def g_2027 : Nat := 0x200040444
theorem lb_2027 : LowerBin m_2027 s_2027 g_2027 7 :=
  lowerByCheckedRows (unpackRows 30 0x1a50003ad0005b50007bd0a10002a90004b10006b9000) lb_1749 (by decide +kernel)

def m_2094 : Nat := 0x4444444422222222
def s_2094 : List Nat := [0x22222222, 0x404040402020202, 0x44004400220022, 0x444400002222]
def g_2094 : Nat := 0x4044402222222
theorem lb_2094 : LowerBin m_2094 s_2094 g_2094 7 :=
  lowerByCheckedRows (unpackRows 30 0xe99000c91000a89000881f9d000d95000b8d000985000) lb_1749 (by decide +kernel)

def m_2113 : Nat := 0x5050505005050505
def s_2113 : List Nat := [0x1010101001010101, 0x5050505, 0x50005000050005, 0x505000000505]
def g_2113 : Nat := 0x10105001050505
theorem lb_2113 : LowerBin m_2113 s_2113 g_2113 7 :=
  lowerByCheckedRows (unpackRows 30 0x698041490041288041080fbc041db4041bac0419a4041) lb_1749 (by decide +kernel)

def f_2347 : Nat → Nat × Nat := unpackIndexedForestF (pagedUnpackF 22 7 (fun p => (pickBlockF p 7 (pickBlockF p 3 (pickBlockF p 1 0xd15bc3da590f69603da550f6950345630d09bc342630ea9f83b2540ea9c83425f0e4db43936c0d096c342570de99034b7e0d2dc83626c0d2d943525c0d2d90342530ce0d0013430ca1902e26f0c60902e2630c20902e23b0be1302e2370bad102e2330045780545d0a6d7c2c46c0a6d6c29b570aad702a4640a6d4c2947c01493c2535f09f1b02535b094d5c2636c097190253530929f00524b082d3c2345c082d2c20b47086d3021454082d0c2057001491c1c35f07b1b01c35b070d5c1d36c0731901c35306e9f00524305b5b41745f0675b01745b05d15c1846c05f5901745305a9f00523b0571a01056d042d7c1446c042d6c10b5704ad7012464042d4c113520420d8104700148dc0f2640275b40e45d026d100a45f0335b00a45b02915c0b46c02b5900a4530269f0052330225f00592b01e9140737001649c0623401648c0504e00419801a6f00698c01a3b0068dc023440068cc0105e00204c0003f (pickBlockF p 2 0x1fe1d87ed741fa1d078c7f1f21b87c86c1f21987bc641ee11078c731eb1907936f1e6d50793631e21500135f1dcdd0770741cb5fc75b541d615072d731d29907346f1ce910734631ca0d00135b1c59e0710741b31fc6fc7c1be1106cc731bb5a06d36f1b6db06d3631b21b0013571aa1b86a86c1aa19869b741a61d05957f19e1386784c19e11866b5419a150595731929a064a6519299059c6f18a92062a4518a91059c631669bc59a6317e9f86024417e9c859a4f178df85e35c16692c5ca7e1729c859a4716e9905a37e16a9305a35416690c59034004d4c57b7415e1d05367f158d905606414d9cc5526414f5bc5425414f58c53034004d2c5104e144118510441415e05007412d9fc4f04e1395a04e06412d9cc4d46812f5bc4c45812f58c4b05c004d1c4906e1241b049066120dd0480740cf9fc47056118d90460640cf9cc4506410b5bc4404610cd504305410b58c33c541009a44026810099440264 0x2fe138bed682fa190bce732f55bcbd5632f217085b472ec1b8bb0662e8dd0ba0742c79fcb90562e0d90b80642c79ccb70642d35bcb60462d4d50b50542d358cb1c542ce9a0b256f2ca960b25632c60d085b432b692cb05702b691cada3b2b68dcae3442b68cc859662a6d7cac46c2a6d6ca9b572aad70aa4642a6d4ca947c22693ca535f29f1b0a535b294d5ca636c297190a53532929f089a4b282d3ca345c282d2ca0b47286d30a1454282d0ca057022691c9c35f27b1b09c35b270d5c9d36c2731909c35326e9f089a4325f17c9a56c25f16c97c572631b09856425f14c9727c2268ec92b5f2571b092b5b24ad5c9435c24f19092b5324a0d8924702268dc8f34f23cd2c8f34723cd0c8f03623ad808a34422b17c8d56c22b16c8ac5722f1b08b56422b14c8a27c2268cc858662189bc862632188ec8623721ad10862332161780081b2121900156f20e1500156320a1900136f2060d0013631fe1f87f87c)) (pickBlockF p 5 (pickBlockF p 4 0x3f48d0fdb603f8940fe1503f6490fd1443f20ccfc0143ee48ce4166392574fa1643d71b4f635f3e31b0f635b3d8d5cf736c3db190f63533d65f0e492b3c11b4f0a4f3ced70f0a4b3c291cf224c3c6d50f0a433c2098f037039249cef05e3ba590e546d3a6d74ea23f3a88ecec14c3a88dceb3443a88ccea0263a6980e5234396d7ce846c396d6ce5b5739adb0e6464396d4ce517c39248ce406600210ce30642175bce205421758ce1064216dbce0034216d8cde87e37a1d8ddd743761d0d947f3701b8dc06636d190db0443651ccd9b6f366d8cd9054216d7cd7b7435e1d0d457f358d50d60543515ccd4c6f35318cd4034216d6cd2e7834a1d0cf47f3451f0d104433d1cccfb6f33ed8ccf06c216d5ccd86e336198ccb743321d0c857f32c138cb046328d50ca0543215ccc8c6f32318cc8034216d4cc6b7431a1d0c367f314d90c506430d9ccc3d6f30f58cc3034216d2cc184e306118c0d783021d0bce7f 0x4fed213f4634fa130e42374f05b93c06e4f01b13c0664ec9d13b07442b5fd3894e4e21393884c4e211937a544de1510ad734da19132c6f4d04f93403e4d00f1340364cc911330444cb18d0ab444be5a52f9684be5953005e4be5910b46f4b25252c9484b25152d03e4b25110b4634ac5652b15549ed7d281394a04e1281354a20b92813449ed4d0b23449a8d10b16f4960b92513c48ad112423448a5712323448a5510b16347a8d12112447a5f91f23447e4911f14447a5c90b14f4749511d1544615c91ba4446e5111b462460d111827e4609c9193444609751825c42c52d162344585f91617242c51d14a644525910bd7e44e55112c6e44a4f10bb444428d1111244425910ba7e43ed110ba72436d110e2344365710ba554308d10c14c42e9510b14342a090e4233426050fb92b3f08d1081503f249105b7c4189b106160416490fc83f412981042343f20ed01c70408d8102160406490fc8374009810002c) (pickBlockF p 6 0x5b698d7f3645f29f97ca7a5f6df17ca765f29c96da4f5e0df97b2345e0de9783765e68d1783725e0d757835c5b692d774685d09f97625c5d09e9754705d09d9742725b691d732645b8df9722345b8de96e3765c28d16e3725be9716e3555ba9316e3545b690d6d36054649d5267a5a79e16a56a5a95896a5605a65d15247f59b1f16736d59cd856736059a5115247b58fa016457a5915e16457258e631524775831f16136d584d85613605825115247355d5a95f56855cdbd5cb6c5749755d2515728e15736b5695c15ac6a56b1895a17c55cd9d57b6c5609755825155e4d1573635488d15646854adbd5535c54adad5447054ad9d5335c54ad8d5216c54648c00847542190e426f53e090e42635389d14e0745275fd4ca5453215149d7352e5914a46f52a5114a463526090e423b51a4f94683e51a0d94702e51a0d145c785161d13ed7f50a4f94283e50a0d94302e50a0d141c585061513ed73502da13f46f 0x6ba98dbf2746f75fdbe2546f75cdaea3b6f00f9bc0366ef1e1b957f6e80f9ba0366e7161b95736ba8ddb786e6de199b72746c75fdb584e6d6119b52546c75cdb246f6cc0f9b30366ca911b24636c6d11aea336bc4adaf1276be8d1af1236ba1980084b5475a9ad5685465bdac16c5465adab57054659daa16c54658d9be7a6a19e1a817466f1fda547c696db5a5b61696d81a514466f1eda268068b5e9a2d7868b5c9a218c66f1dda0c7c6825119bc7367f1a19c36f67ad719c36b6771c19c367672d719c36366e5b15192b5b59e9986786629b598a6c662985983785b51fd9547c6569b595a6c656985953485b51ed9268064a9b592a6c64a985923805b51dd8f47c63e9b58fa6c63e9858f3485b51cd8ca696329a18ca656329916dc6f6289258a2486289158a2445b71ad87a7d61e9f187a7161e9c16dc6761492585248614915852445b718d6da6f60cdf58337c5b69ad6da676069f1803756029b180374))) (pickBlockF p 10 (pickBlockF p 8 0x7fad9dff3547fad8dfe15e00248dc14667f3191c116f7ee551c116b7eb1f1c11677e6551c11637b75d9f7d747de5d1edc7f7d5191f5b597d6d55f51447b71edf41647c9631f2c7e7cb1d9f218c7b71ddf0c647c2511edc737b8dbdee36b7b8d9dee3637b6551c112b7735d9ea5747aa965eaa557aa089ea3787731fde7c647a0965e825579ed21dcc7b79ada1e4d8c794965e5255792e01dcc77787191e2259788955e2022786d21dcc73782991dd46f77e911dd46b77a9f1dd467776911dd463772d61c112770f5d9d95747671b9d9c66766189d917470f1fdd6c6475cd65d735575a511c3c7b756591d3d8c7511f9d447674e631c3c77743191d1359744d55d1032742511c3c7371b199cf46471adbdccb54734925cd2457328e1c6b6b7291f1cab6e72ad99ca17c71ad9dc735471e925c7a4571e089c713471ad8dc3a34710dbdc436b710d9dc436370e551c11237064adc223470648dc106a00213daea6f (pickBlockF p 9 0x8fb1ca3f36c8fa1da3b83b8f11fa3c4728f2d823c0768ee0ce3b1447f914e3a05482117e3934782116e35c5e8d88ee374688d88de3603b8d6512084538d298229c668ce1622a35f8c91b6323668a8d6e2f3598c35b22f2628be9822f1628a8d5e2e36c8b51962d34e8a8d4e2c0668a80ee2b1608aa19a2a0338a65120834f8a2d9a0834b85b5aa1825f898db62626686096e2525986095e2426c886d9621a5c8868fa218288860921825388299a1802f876dba1db628764fa1e26c87619a1802b872daa18027862dba18b6286a0f2189368649821925086219a1802385a9421685c85a14208347822d9a1515482497e1416484cdb61326682496e1225982495e1126c83ad961025e83ad920ea3e83a0a209253830dba0c36283019a0c0248240ae09b6e826d8a0a25082619a090238228e2083437f88d20747c80ed3e0637c80ed2e0557080ed1e0437c80ed0dfe1667fb59a024647fadbe013547fadae0047c 0x9fe1da7c84b9f55fa7d5729f71827d0769f210e7c1547f917e64476992dbe78c7d9e6d9678c7c9e2dda64b6b9deda664b679dadf2734759d4dba7536c9cd1d27334e9cc0e273034992d8e723449c31ea70c769c2dda6483f9b31fa6cc729b253a6c94c9b4df26d36c9b21da6483b9ab1ea6ab7a9aadda648379951fa654729a21326514699e0f265144996dc265b609960d2650769920ce641447f916e4b67a9881a2620649335be5fe7d9831965fe7c97f1da4cd6b97b5a64cd679771f25b6759711ba5c46c96d9d25b46e93358e5967a9659da5957693217e54e7e9539ca5496e9525b25557c9555b25505c9521da4c85b9499ea5257a94b5c25257693215e4d67e9359ca5006c93459a4f05c9345924dd709375824d07693214e4b16c92c1b24b0607f915e4a17c8ed1da3bb6f91d1f64836591d1f2473768eedae45c7e916da63bb67912df24147590b1ba42b6e90adb241474904d3a410388eed8e3ec7e)) (pickBlockF p 12 (pickBlockF p 11 0xafed72be464af8dbabe36dae2d4ebbc6aaef19abc368aeedbab883fae518ab936aae6d42b9366ae20deb81447f91aeb7154aa55c6b6054aa71beb3d7ead3156b3d7cacf17aa9c6baa719eb247cabd5dab0c6dac31b2af574abd17aaf45daa718eacc7dab31d6ad57cab31a6a986faa91c6aa46daab182aa465aa619ea917c7f919e8f46ea42d7ea5c6da9ad5aa5c6ca96d3a90b5ba8f9e2a386ca8e18290b57a8adb29fc65a84d76a135ca7f1929fb6ea7edb690b53a731aa9cc66a74da29d358a72dba9083fa6e1529946ea6518a9914ea645329906ea420ee96462a58daa96b60a5ad4296366a420de9146ea5211291462a4e13291146a48d4a9203ca445129106ea420ce8f144a3c1228f0447f918e8e17c9f15da8d0689f31be8ad7da2f1968ad7ca2b1da7cc6ba1d1a68967ca1cdca87a70a1e5f28717e9f319e8647ca095d68346ea0d1b283362a0e9828316ea095d28245e9f318e7fd7e9ff5ca8046c 0xbfe0ceff144bf114efcb6fbf2daefcb67bf2d8efc15e0024aeeb35fbe91bafa46cbacd6eeb357be2db2f7466bded72f7464bacd4ef6564bd4db6f5365bac17ef4044bc91a6f2461bc85baf216cbac16eefc60bbed76f0560bbed56eb057baf1a6ee044baf186ed06cbae59aec05cbae592eb053ba6592e9868ba6191fe56fba2512e6c5bb9e5b2e6c57b9a551fe56bb90dbee4363b92df6e406fb8e5f1fe567b7f5bae034bb875e2e0347b83166e004bb7e551fe563b1d5a6c7c5fb715badd455b715b2dc45eb1f16eda87cb6a1c2c7c57b671f2d6d66b611b6d846cb5b592d6c5eb5b176c7c53b4f1b6d3c65b515b2d446cb4f166c785fb4a152d0569b41586d016eb405b2d005eb1e16ecd461b35176cdd70b37142cd455b1e15ec8569b2e152c8561b2a1b2c8166b25146c905cb20592c805eb1e14ec71647f91bec6154ae11bab8b5fb0d1b6c4356b0d1b2c334eae2d6ec206cae2d5ec136caf9196bfb5d) (pickBlockF p 13 0xcff1933c353cf91a73e461cf016f3cc69cf31873c053cee5932736fcd893f39b5dce6d733624bcd891f3825ccdad573724ccdad5336243cd64d32736bcc8d9f3437cccb1db3336cccb1d332363cc65f327367ca493f2fb5dcbed732924bca491f2e25ccb2d572d24ccb2d5329243cacd7b2b352ca40af29b5eca6d4b29023ca04d328038c9cd8f2716600250f25964c96192fc56fc925b323c57c8e552fc56bc895bb22154bf158f2117cc495db20068c4b1bf1dd7dc7b1971dd7cc771db12c6bc711a71c272c4b19f1b47cc615d71946ec651b319262c615d31845ec4b18f15d7ec575cb1646cc561db1284bc4d5fb13572c4f18313076c4a10f12154bf117f10c76c42512fc45bc399eb0e16cc381b30e060bf115f0d17cbfd1daffb6fc291f70b365c291f30a376bfedaf09369bfed9f0837cc151d706b6ec1adb305474c14d3b05038bfed8f02c7ec0b1cb0336cc0a1daff83bc011fb00472c02d8300076 0x36805400317f6714700316f6645e00314f61466d88d5f6436cd8b19b6335cd8b19362353d869536126b00253f60164d56dbf5724fd78d775e35cd5c92f57247d729735ab55d6e4db5b24cd6ad5357243d64d6b59356d5c0bf57a5ad5e95b57027d5a4d355b6bd565980094bd135ab54568d129bf4bb4fd4917b5245cd2ed2f4bb47d42db34f456d3ed734f454d2ed0f4db5dd36d574b84fd30d374c345d2e11f4b26cd129af49a6cd2697344a63d1c57f4715bd1e55347153d121734525fd1609345253d1214000947cf0d7f42c6ed0b1b33c35bcf0d5f4137ccff19b4036c)))))) 11
def l_2347 : Nat → Nat → Option Nat := unpackIndexedLinksF
  (pagedUnpackF 18 7 (fun p => (pickBlockF p 7 (pickBlockF p 3 (pickBlockF p 1 0x11200448011200448010e10430210a08428010a0042411051041011030440420ff083fc00fe043f800fe003f410fd003f010f8103c080e91c3a400e8043a000e70439c00e50839400e20c38410df0835890d21034410d00433c10ce0433800cd0433010c81031c10c60431410c40430c10c30030810c1042f440bc042ec10ba042e410b8042e000b7042d810b2102c410b0042bc10ae042b410ad002b010ab0429c40a60429800a50429010a30428810a20028410a00426c50980c26000960825410940424c10920424800910424010900023c10891821440850020c2083002042080041fc107e041f4107d001f0107b041dc4073101cc0072041c80071041bc206f001b8106a10170e05c00170005c0016c105b001681052200f55001f00001 (pickBlockF p 2 0x1da1076411d60c75801d60075801d21074411ce0c73801cd0473401cc0472821c61071411c40470431c0046fc11bc0c6f001bb046ec01ba046e021b4106cc11b2046bc31ae046b411aa0c6a801a9046a401a80469821a21068801a200688019e10674119a0c668019a0066801961065411920c648019200648018f0c63c018f0063c018c0c62041860861801860061411820c6080181045fc217f005fc017c0c5f0017b045ec017a045e02170205b0416b045a811661059411640458431610058011600057c115c0c558615600558015600544514f08528514a00520214608508414200504114100500113d0c4d87136004d80136004c4512f084a8512904498312408480412000478211e00474111d0046c2116144580116004580116004484 0x2cc04b2c12c710b1c02c700b1422be1caf802be00af022bb04adc42b604ad022b304abc42af00ab812ae00ab412ad00aac22a614a9802a504a9402a404a88229b1ca6c029b00a68129a00a64129900a60129020a3c128e04a34128c04a30028b04a28128610a14128404a0c128204a04128100a00127f049ec427a049e41278049dc1276049d80275049d01270109bc126e049b4126c049ac126b009a812690499442640498c126204984126004980025f04978125a10964125708958125408948225200944124f089381248189182246009180246009180246009045240048fc123e048f4123c048f0023b048e81236108d02228308a00228008a002270489c02260487882095481441ff187ec41f6147c451ea1c79451de1c77801de007780)) (pickBlockF p 5 (pickBlockF p 4 0x3c204f0803c200f0023be08ef023b714ed423a930e9443a500e9013a304e8813a104e8013a000e7c139e04e68439808e5c139508e50139208e40239000e38238c08e2c138518e08338200e04137f08dfc037f00dfc037f00df4237d00df0137c00ddc537508dd0137304dc8137104dc4037004dbc136b10da033593cd09733e10ce4533510cc0532c10c98632210c70631c00c70031a08c6803170cc5c031700c54231500c48331200c48031008c30430c00c3003090cc24030900c18330600c18030408bfc52ff00bfc02fc0cbf002fc00be432f900be402f708bc852f200bc802f008bc002ed0cbb402ed00bac22eb00ba032e800ba002e608b8842e200b8802df0cb7c02df00b7032dc00b7002da08b5062d400b5002d208b4412cd10b340 0x4ca0532024c11d2fc24bf012fc04be052e064b6092c454af092b814ad052ac24a51928c249f1127c049c0d26c149b0126c049a05254549405244348b19228148a012202488012182480191fc147e051f0247b051e03472191c80472011bc346f011bc046e051b8046c0919c545e2517024571515c04560514454510114014500113c14481d11044440110c1442051080441050fc2439190e01437050d03434010d00432090bc342f010bc042e050b0242b0509074210d08404210106c641b0106814170d05c041605054140e1d034140d01030140a0902804090502014080101c14050901014040100433fa1cfc0a3e91cfa403e708f9423dd20f6053d704f5c03d700f5423d308f4c03d204f4413cf08f3813cd04f2833c70cf1813c600f0c3) (pickBlockF p 6 0x5bd016f015bc016f005bb056e815b4196d005b4016cc15b2056c805b1056c015af056a465a9016a015a80169c15a70169815a60168065a00167c159f01678159e01678059d05674059c05670059b056546589316087581055fc257f015fc057f015ec4577115d42575015d40575015c4456d115ac256a055a8056905590556011578255d05570155c0155c55531154c055301548155201548055201540254e09538054e01538054c09528254a01528054a015202546095045541015001540014fc153f014f8153e014f41539114c8751965454450d2141c65001d3f824fd053e444f8053dc14f40d3d004f3053cc04f2053bc34e9193a014e80139c14e70139814e11537c24da1536414d90136014d80135c14d21534024cc1133004cb0532c0 0x6b401acc16b301ac816af0dabc06af01ab426ab09aac06ab01aa426a709a8c46a301a8c06a109a7c269e05a74169a0da60269801a60069801a58269505a48368e11a38068d05a34068c05a00c66d4d984c65d1196056541193c564b119185642118f4563d018f0163b058e03637058dc0637018dc0633118c0362f058bc062f018bc062b118a036270589816230d88c062205888062105884062005880061f0586c461519850161209848061201848060e1182846080981c1607018181601157f445fb097ec05fb017ec05f7117cc45f1097c405f1017c405ed117a445e9017a405e9017a405e51179405e50179405e50178445e10178405e10178405dd1177405dd0177405dd0176445d31974815d10572c65c51971405c40571005c3056f46))) (pickBlockF p 10 (pickBlockF p 8 0x7d501f5017cf15ed1b7a831e90479d1de64479415e40478b15e1c47801de00078001e00077d0ddf4077d01df4077b09de0377801ddc177701ddc077509dc8377201dc8076f0ddbc076f01dbc076f01dac476321d88176105d84076101d84075e0dd68475905d60175705d50375011d40074e09d38074e01d30274811d1c174701d1c074701d10374011d00073f05cfc073e05cf8073d05cf4073c05ce0472f25cb8172d05cb4072d01cb4072a0dc98472505c94072501c8c271f11c7c071d09c70171b05c60371411c4c171205c44171005c30470811c20070801c1c170701c1c070701c14270309c0c070301c0c070109bfc26ff01bfc06ff01bfc06fc0dbe826f31dbcc06f301bcc06f301bbc46e625b9806e601b9416d931af1d6b811ad04 (pickBlockF p 9 0x8b8022dc18b40e2d008b3062cc08b2062bc38a72228468a10226c689b0226428990226408990226018980224c588f1223c088e06238088b0e228188a0221848850621408830a20c0882061f0687c021ec187b021e42879021e01878021dc1876061b8886a121a8086516194086112180186002170485c0216048580215c18570215c08570215c08501e140084e0a134184d02130184c0212c18461611808430e10c08410a1040840061000840020f8283a120b8c82e020b8082622098082506080582002078281e02068481a0205458150205018140204c18130204c080d1a034080d02034080d0202448090202018080201c18040dff087f811f8187e001f7c17df01f7817de01f7417dd01f7017d811f6007d801f5c17d701f5817d601f541 0x9a9126a409a8066a009a60a68849992664c699206634598c06630098a0a62809831e60c097c1e5f0097b065ec097b025e42979025e40979025c87972025c41971025c4096c165a8296a025a41968065a009680259829601a58009600257c19591a56409570a55c09560655809540a55009540255009510e5305940324e08937064dc0937024c0792f064bc092d0a4b409261e498091f1e47c091e06478091e02470291c0245c591606458091602440690e0a438090d0642c290b0242c090b0242039031640c09030240c0902063f458fd023ec28fb023e818fa023e418f9023e408f70a3c468e53239018e306364a8d90235c28d21634418d10233c28cf0232858c90632408c31a30c08c20630808c20230808bf0e2fc08bf022e468b8062e00)) (pickBlockF p 12 (pickBlockF p 11 0xad50ab540ad502b405acf06b3c0acf02b381acb0eb281aca02b280ac906b183abe22ae06ab802ad82ab506ab87aac0aaac1aa80ea9c1aa11aa6c6a9a06a602a9802a600a960aa541a9406a386a8c0aa2c1a8a06a202a8412a082a8106a040a7f0a9ec4a72269b06a6b0698c8a610a9840a5f0a9781a581a95c1a56069541a4c2692c1a490a9240a490291c2a46069141a3d228e83a39068e40a38068d43a2e1e8b80a2d068b40a2b0a8a81a290688c6a1f128781a1d068701a190e84c6a130284c0a12068441a0f0a83c0a0f028342a0c0681479f8367dc19f6067b0a9ec027a829e90678879e00a78009de0a77419d71a75429d40673c59ce0673809cb0e70899c1066fc29bf026fc09bd0a6f409bc066dc59b6066c069af066bc09af026b42 0xbd722f485bd202f480bd202f480bce12ed1abb012ebc1bae06ea84ba612e980ba506e940ba406e804ba002e7c1b9f02e6c4b9b02e681b9a02e641b9806e504b9402e500b9402e4c1b8e16e380b8e02e341b8d02e301b8c02e2c1b8712deccb7a06de41b7122dc40b6f0adbc0b6d0adb40b6912da01b6802da00b6706d885b5c1ad6c1b590ad601b560ad580b540ad386b4916d201b4316d081b4202d002b4002ce47b3902ce40b321ecc80b3106cc40b3102cbc2b2f02cbc0b281ec982b2602c980b2602c902b1e1ac780b1d06c740b1c06c6c1b1b02c585b130ec4c0b1302c4c0b110ac305b0c02c300b0b06c2c0b0a06c280b0a02c202b0802c086af632bb88aed06bac2ae616b941ae502b8c2ae302b785ade02b606ad802b5c1ad702b5c0) (pickBlockF p 13 0xccc133300ccc033282cca033280cc80b3008cbd0f2ec2cba072e41cb70b2d42cb5032d01cb4032cc1cb10b2b44cac072a82caa032a41ca9032a01ca60b2884ca1072744c9c0726c1c990b25c2c97032581c96032541c91132440c910323c2c8f0323c0c8d0b2148c85032044c7d131a93c66131980c5f1f17c0c5e071780c59171640c570b14c4c53031481c52031306c4b0712c0c490b1240c44171100c43070f46c3d030f01c3c030f00c3c030e43c39030d05c33070cc0c33030c81c2f0f0bc0c2e070b80c2d070a83c22230745c1d030644c121f0480c0e130380c0e030149c05030101bff16ff81bfe02ff02bfc02fdc5bf702fc85bf202fc41bf102fc40bef0afbc0bef02fa46be806fa00be802f9c1be40ef900be306f8c0be206f7c3 0xe04337a9ade6137512dc8336d53db1136bc2daf036b81dae036b41dab0b69c4da60764d3d8f136285d880b61c1d86076084d7e135f80d7d075f40d7c075ec1d790b5e40d79035dc2d77035dc0d750b5b48d6a0f5984d4d6751c6d43134f07d38134dc1d36074d02d30134c00d2f074bc0d2e074b02d2c034b00d2a0b4a80d2a034a02d20234704d18134600d0d2f4340d0d034340d0c07400cd00034000cff073dc8cdc6f3682cd9073601cd4133482cd2033441cd1033401))))))
  (pagedUnpackF 26 7 (fun p => (pickBlockF p 14 (pickBlockF p 7 (pickBlockF p 3 (pickBlockF p 1 0x2c11500c856c02a11400b046c02a15900d045f030116c0b8457028114c0e856d0360d1009827c016017808817c01e0914070370018048006023402024bc08012b01a049c0581230b41174288b4f0902d2c1f8b4706c2d0c28824f090092c1f824706c090c160a3f05808ec0f823702408cc05004e00808c00203440102dbc038b6301009bc03826300c28fc03023b00a08dc01823321015bc83056320831bc810c631e0317c720c5b1b0315c588c532080dbc8103631e00d7c72035b1b00d5c58835314a2d3c52834b12a0d1c3303430b60578048066004017b67845fd9a116f65b457d96114f55435fd830d6f26c357d110d4f60934fd544d2f441347c9a4d0f554a5fd83296f26ca57d11294f609a4fd54692f441a47c9a690efb923fbee88edfdc2377f648cf55315fd82c56f26b157d10c54f60814fd54052f440147c9a050efba93fbee24edfdb9377f624cefb992fbee04adfdb1277f6048dae305f702c16ce3b057544c14dc0804f6b8012d51004738e010c85403f21440ec00c03700240cc85482f21460ac00c827002608c85301f214006c00b017002004c00003f (pickBlockF p 2 0xd209403782640d809b035025c0dc0df83683720d60d943483640fe15bc3d05630f209bc3c02630e8097c38825b0e0095c34025311e19fc45867310811502e016e02401d801806e0ce00d03280640c600900800760c200902e823001a01d82f804c01801982e834401601d8320b6f0c42d8c32026f0c4098c300a3f0c008ec2f02370b808cc05006606a28fc1a823b05408dc0e82330b00da02a83540b011b02a03500aa0d702a04640b20d7c2b835b0ac0d5c2983530a411f02783680980d5027846c0960d4026036c096119028035f09c0d6c2683570940d4c24827c08c0d6021834408c11702103400860d3021045408e0d3c22834b0880d1c20834308015c01e83680740d501e846c0720d401d036c07211901f035f0780d6c1d83570700d4c1b827c06611a018045406615b017845006011b0178564068117c19045b062115c17045302201381a856d05a09f008005e05611a00e02300500da012835405011b012035004a0d701204640440d4814835f04e0d6c1303570460d4c07005e04200d815056d04011c00d823001a01780e034403c09900e045d01801380c8468 0x1780d705d027e17209c85a024016e09905a824c16c0df85a035419011bc62046318609bc61026317c093c5d824b170091c5982431a415fc66057306c01d859003415401905502641600dd01a808415e01d0548034150015054025415a0d9056006414e00d0550264150095054856f14e158c30805e15c19fc5586730c005b816007600c01b853003405601d052004e134013051804614401104d046811408c05085781120d0015008414001d04c805c13c01384c004c130116043023013a15a042834013801904b805c13411a04c045813215bc4b85630be01784f867f13619cc4203400bc05b80f807600a01b84b005c03c01d04a006e12601b0490066100019045034410009904484541220dd00e808412001d03f803411008d043834411c01583d805410c0d103d825410a115046836411801903d003403801d0450064110011843835410c015044856f10a158c2e815e036019802005e10609a441026810209944002640fc09643e82580f809543d82540ee09783702520ea0db83683620ec09503b827e0ea09c83982690e409a03602640d4095039836d0e40db0358251)) (pickBlockF p 5 (pickBlockF p 4 0x2120190560a3f15808ec4e023711808cc558b4f1560d2c4d83471160d0c8380541fa2d3c770b4b1c42d1c698b430ca01387e0c5f1da316c708c571a4314c32015e20a019004005e1ee317c758c5b1be315c668c530c601787b0d6f1d435ac6f0d67198358c31016e00e01b881803420201f880007c1fe01d87a80741ea11907f05741fa01d07a00541f601b87d006c1f201987980641e60d507c04641e401907b80441ea11907983541e80dbc7903631f811fc7b04730a201d87880541d201907482641de0dd07700741d000d07380441ce09107603541d601507300341d209907382441d011bc7304631da15fc75057309001d87280341ba01706e85681c619e07100741b801b06d805c1b60db070047c1b401f06f80441ba15a06d836c1b80dbc6d03631c211fc6f047307e01d86c806c1ae01b86b006c1aa019864806419209906a03741a601d06400341a2013868004c19e011862804418a091067035419a015062003419609a0650265192099063824818c091462824418209385e824a17409185b024217e0d785c8356180091060827e17e09c85e025816a09105e837e 0x2961190a8035f29c0d6ca683572940d4ca4827c28c0d60a1834428c1170a103402860d30a1045428e0d3ca2834b2880d1ca0834328015c09e83682740d509e846c2720d409d036c27211909f035f2780d6c9d83572700d4c9b827c26811a098845426815b098045026211b098056426a117c99845b264115c97845325c09f0958368244090094035425611b090825024e0d409002402500d7093846423e09408f01402580d7c95035b2520d5c93035323a090092803624811c08e02302440d3c90834b2400d1c8f834323c00d88e836023411a08b845423415b08b045022e11b08b0564236117c8c845b230115c8a84532380d108a027c2a22d3ca40b4b27e2d1c9b0b432a2093ca4024b27e091c9b024325a28fc96823b24608dc89823321a08c08683442222dbc880b6322209bc88026321e28fc87823b21c08dc86023338a15bce1856338231bcdf8c63362317cd38c5b33a315cc78c533820dbcdf83633620d7cd3835b33a0d5cc7835330a2d3cc2834b2f00d1cb103432b405988900662160178578a3f15e08ec50023712008cc570b4f15c0d2c4f834711e0d0c2d0074) (pickBlockF p 6 0x35000d0d3067834a01d0d0006c34611f0cf807c3440110d0036f33e0d8cd2047f34211ccaf817627e01d8cf006c33801b8cd80663340dd0cc807432400d0cb804e32c0118ca83543280150c8803432411bcc8846333015fcc9857326c01d8c8003431c0dd0c6807431000d0c583643140190c3803431015bcc3856331819fcc486732bc05d896807621e01b8c300343080138c180462dc08c0c105782da0d00c080742f60170bf804e2d408c0bf05682d20d00be80642f40170bd856f2f4158cc0067f2f819ccb403402ba05d891807621c01b8bc805c2ee01b8bb00662dc0d10b684542ea0dd0ba00742cc00d0b602342d60d10b900562d40d10b484542e20d90b800642c800d0b700642d80118b583542d40150b6856f2d2158cae0166238019886805e2ce09a0b282582cc15bcb205632e619fcb786732d01150ad817622601d886006e2c600d0b005702b808c0ae03442c22d2caf8b472c2092caf82472bc28fcaf023b2ba08dcad82332b00da0aa83542b011b0aa03502aa0d70aa04642b20d7cab835b2ac0d5ca983532a411f0a783682980d50a7846c2960d40a6036c 0x3ba0590eb02303b00530eb03443b408fcec823b3ae08dcea82333a80098ed835d3a60980e8036839a0d50e8046c3980d40e6836c3981190e8835f39e0d6ce703573960d4cee046d3a408d0e5017c3ea4d74fa9a5d3d448fcf5223b3be48dce492333ea0574f5293f3d424ecef893739224ccf5192f3d404acef8127392048d50146f53c518d501b6f53c6d8d49134f5248d2d3e13474284d0d50026f53c098d492a4f524292d3e0a47428290d491a3f52408ed3e023742808ccfb01662b50538ad493e2b4c4b8e4006631a28fcc6823b30208dcba02333182d3cc6034b3000d1cb9834338c0190c50a3f31408ecbe82372e008ccc48b4f3120d2cbe03472de0d0ce200543762d3cd78b4b34a2d1ccc8b43374317cd70c5b348315ccc0c53384019088805e36c317cd60c5b344315cca0c5336a35bcd58d6b342359cc98d6322001b8e0003437c01f8de807637815d0dd80743680150dc806e3700198db84643660190db00443680dbcd9836337411fcda84732a201d8d900543600dd0d7807435400d0d683543580150d4803435411bcd4846335c15fcd585732c205d8a40076))) (pickBlockF p 10 (pickBlockF p 8 0x4480d1110027e43c09c90d025542e0950fc80764bc11bd2c046349c08d126016f488058d1e014f45e052d15814742c050cfc00664ea15fd3705734c80d10fb81762bb0578e4807642a009109c97c426005107b26041e005104b12f418c4ad00b127408c48d06002f41200ad020027402008d08015041600bd04002b406009cff802341a049106826c418058107037c416049104826041008d10281243fc0100fe80303f800810283604080580fd802040c11c10181243f400c0fe01344020980fd813440000b0fe81243fa0940fe01503fc0d80fd81243fe08d0fd014441e049105003f40e00ed0100373f200cd0882343f0005109123f42488ecfbc2373ee48cd09293f42424ecfbb9373ee24cd09192f42404acfbb1273ee048cf9923f3e688ecf492373b848ccfa01643e20da0f703543e211b0f683503dc0db0f684643e40d7cf8035b3de0d5cf603533e611b4f5817c3b60480f382583b404c0f202443ce0d70ec81403c60900eb81303c80930eb01303c60d50ea81403a800c0f4024f3cc092cf282473c4090ce981303c20098f4846d3c00dc0e901203bc0178ed8234 (pickBlockF p 9 0x4a80d112982344a408d11d81584a200511d83494a004912d003e49e08d11c81594ba05252e01484b605152c81444ae05652b015544c04c51c014847008e528802e46c05252a01394a604e12901354a004d12a835f49e0d4d26815f492054d21813f46a04ed17013744804cd07805648404f911813249a08d120814e4680529168146440050925802e48009390f8242490053123014449404f124023448c08d124834447a097919825a45809590f025248e057122815448405b9200162464052505806648404911f813447e049120023447c051121823448205f91e8172462056518015841401d91c023446e08d11b034447609511d015447009111b814446c118919024d41001990e01444640d110d815443005111c857246a0d111a027e46609c918825d460097103807643a04c50c8130406019917023445a05f916017243405050b814040401d913823444c0d111502644520591138154400015913046e44609b90f826243a09150c824444a04f0ff8066444055111012444608d110816443e0d110e014c43808d10e83444360570fd805643208d10c014c3f4019914057e 0x3e801d14b806452e05914e82743e602114e007452c00914a804452a05114d025453201514a002452e05914a814452c11bd4a046342601994d857f53015cd0901762bd0578f50076526009147003451c00b147002e52204f948003e50200f147803651a00d14083684da04814604784d808c0f4808451601d140004c50c00d143002c50c00b944813e51000f93f803c50e00d94280344fe0d21330120508116132823050601513f004c5020da13f834850011bd3f046351415fd4105734c808c0fbb1762b70578ef80764fa0130ef00744c0019130005c4f605b8ee80744f401b93c806c4f001992f80644da08d12f81644d80d113b82743b802113b00744bc00913581244b401113501244d204913401244b400f13382344e8053939804e4e401313880464b201113302344b205113283444e009513780544b00090ed80744da01912a80244a200d128802c4d604f935003e4d200f13400364a000d12801344ce091133004449e009136046f4ca118d0881662b90538e9006649c00912b83444ac08d11501404540d4930005e4aa08d13181694c405a13081654be0591140141)) (pickBlockF p 12 (pickBlockF p 11 0x55805716b056a55815a16a85625a815816b867857a08d169817455605b15e0234554057168036d5540db167836159c0d8168847c57008d154817c59a05115b823455005715b012456a049165057a59215e164057255015c15a01245961a0159823458e063153816c56408d153015c56204915801245880db553036c5860d8561036055e049162847c55c08d152817c58205115f056857609755d02515780db15c823856c11a95a846256e15c15a017c56209755802515640db157813457e15a95e836f5700dad59836755c0d8d5604685540d7154047054c0d7155836f5520dad53836754a0d8d6c067a5a411fd66047b58c11dd60047355a08d152016c6b615a9ac936f6ae4dadaa93676a64d8dac9a6f6ae69adaa9a676a6698d9b123f66c88ed6c923754648cdac816f6ae05adaa81676a6058d9b293f66c24ed6c893754624cd9b192f66c04ad6c8127546048d4e123f53888ed4592374ec48cd4d934f5368d2d4513474ea4d0cb0d94e2c324f8fa807454201914c934f5328d2d4193474de4d0cb0584e2c120f94c145f530916d4114574dc514cafd95e2bf25394f8024 0x6260dc1950348570048187835056e048193826d64c09b192826161e09819406806480e018703605660481860350564048190826d64009b18f8261618098191047c6120dc18f034855c04818e026963609a18d026563209918b824962c09218a8245628091189027d62209f188027161e09c18682496180921858245614091183827960c09e17e824e5ee09297682465ca0909818274602099183837d60c0df17e035e5ea0d697583565c60d4981026160009817d024e5e809297482465c4090981827c60209b18103756000dd17c835e5e40d697403565c00d497f03645f60df17602445fa09f97e027a5f409d97c82725e209657802585ec08d173027c5e608d16f82545ba09117b837e5ea0de97a03765e40dc978835d5e00d717704685d809717504705da09f975827a5d209d97402725bc09056e02405cc09917202345c208d16f825c5ba093172837e5c60de97103765c00dc96f03555b80d518c046f62611ad870467612118d84026f60a09ad8202675fe098d7c024f5de092d7382475b6090d9a867a65e11fd94847b64611dd8e84735b40d8156812057e08d15f0234) (pickBlockF p 13 0x70051bdbf94637006dbdbf9b636f44d3dbd234b6e24d1db1134370009bdbf82636f4a93dbd0a4b6e2291db10a436f468fdbd023b6e208ddb102336ba0199a9123f6a488ed9a92375b048cda9293f6a424ed9a89375b024cda9192f6a404ad9a81275b0048da8923f6a288ed9a12375ae48cdad056869e48fda7a23b65e48dd69123369c48fda7223b65c48dd6892336924d3da4a34b6524d1d6613436b005b1a4123f69088ed94123759648cdab057068648fda1a23b64648dd63123368448fda1223b64448dd6292336804d3da0234b63a4d1d6013436a805b19f815c67e15a1a886786a005d19f016c67a0571a6836d67a0db1a603616960d81a7047c67805f1a501446760571a3857a68c15e1a2857267615c1a4068068806319d016c67205719c836c68411f19c017c68205119f846867a0d719d84706720d719f036f6780dad9d03676700d8da9067a69e11fda4847b68611dda0047366e05b15f81206360d415f012066609b599026c66209858d826066819e19803786300d815e812062c0d415e012057604c15d014065a09b596026c65609858b026057204c197047c 0x72805f1c882497200915c780227240d51c7013473e1199ce836f7300dadc9836771a0d8dc2006a0ba40c9c5836f7140dadc483677100d8ddb857676211fdd6047b74c11ddd0047371808d1c3815470601e82e104270808d1c2923f70a88edc1c23770648cdc2a93f70a24edc1b93770624cdc2992f70a04adc1b127706048dfd04667f04dbdfb136b7e84d9df913637f069bdfb1a6b7e8699df91a637b448fded223b77048ddc312337f005bdfb016b7e8059df901637b4a4fded093b77024ddc309337b464bded012b770049dc3012370401a82d90320b660882d80126fa4d3dbea34b6ec4d1db693436f6517dbda45b6e4515db494536fc09d1be02546fa15fdbd85736c201d9bc803e6f000d9bb84786d008c1ba803e6e800d9b984586c808c1bb057f6e415cdb182306c001d9b8006e6de0199b403446dc09d1b381246cc0491b282346d80139b580466c80d11b502546ce00f9b300366ca0911b4046f6c8118daf80666da15fdb485736c60d11af00766be0481af82346c248fdb0a23b6c048ddaf12336c2a4fdb0893b6c024ddaf09336c264bdb0812b6c0049daf0123)))) (pickBlockF p 21 (pickBlockF p 17 (pickBlockF p 15 0x7e015d1f781747be0551f603597d60d55f684647bc0591f501447d00591f3047e7ca11d9f3858c7c80631ee81547c41191ee01647c20511ef836f7bc0dadee83677b80d8df885767dc11fdf4847b7c611ddf004737b60551c2807a0c0a109cf812073c0481eb82597ac0955ea80227b015d1ea03787800d61ce81207380481cd814073404c1e882597a00955cc81307a41191df036879e0d21cc012079a0da1cb81207960965e502557981631e483807780d61c981207240481e3025978a0955e2002278e1191dd03687860d21c681207820991df824477a09f1dd824478011bddf046b778119ddd04637b215d9e9847f79c11ede4047778411cddc83587180481c1b07a0bc4109cf823473c08d1da846e7681199d9806276c15d1ce823476405d1c5815473808d1d7835975c0d55d8046473008d1c5016475a0511cb82347560591cb012472a0491d4847e75011d9ca01247541631c9823474e0631c4815472408d1c881247200491c781247480d65d1835571c0491d1003274a1191c682347100591d0814473c1191cd82497340915ce035473208e1cb036e72a0d99cb847c (pickBlockF p 16 0x728c16d5a305382e00ae0900238560d9a088238726c1ad59b0638e6117e38845b8d4d15e3504538a0cd7e29335b820cd5e1633538a40d3e28034b8580d1e0803436c6c17dc6305b4c8c15d56b053718013db1804b55a011d3200432d100fcb4103b10900dc42103381c11f206037c81415c204037c81a0d3e05834b8120d1e038343808119201035480011f1ff035480a159a01836f8020dadff83677fa0d8ee9056fb9815aee30567b7c158ec6846fade11aea88467a3a118e7b845f98e116e4a84578ea114e07823480c0599fe015e6e2c1bddc306b4f8c19d6cb06370c017db1005b546015d0a00532f1013cb1104b12b011c3310437e248fdf8a23b7b248dddb92337e2a4fdf8893b7b224dddb89337e264bdf8812b7b2049ddb81237e048fdf8223b7b048dddb12337f21191f7123f7dc88ede9923776248cc3228320c86089f6923f7da88ede9123776048cdf4934f7d28d2de713477584d0dfb81547ce48fdf3a23b79848ddd512337ea11f1f1923f7c688ede4123774c48cdf1123f7c488ede3923774a48cdf0134f7c08d2de113477404d0df981540c4a108311832 0x8c40d662d83518c0098a2f01628b80db22d84658b40d3a2c00668ac05822a80668cc0d7e31835b8ba0d5e2c8353732c16d5cb0538ae00ee2a00338d0119a298144730c1ad5c30638a20d99b4306f73ac1ad36306757ac18e26826989809561f802986e008624026489a0db6250365898099a25026589415ba22856d894096623825189009b223836588c097222823e87c00e61b003188800a2218024882099a1e803a87801521a802487809b21f836e87c0d8935b16687a04fa1d80668720da9c7b06a868008a19006486600d21a803c866098219025086e0dba1b036286804da18806689c097e25825b892095e2102536cac17dc7305b4cec15d57b05388000be1d002b870009e18002389e15aa1782506c8c1bdc6b06b4cac19d57306385c0172168050850056613826984c095615015483600a60b0021844099214016484e0db612036584c099a12026584815ba0f056d848096610825183e094211026c840097a10836583e0d920f023e83400e60a803183a00a20d836e8340d8a0c806683000920a006482809420b036e82a0d8a098066852097e12825b846095e0e0253)) (pickBlockF p 19 (pickBlockF p 18 0x94815da4f805293a01424d8074938015250006c93c01724e0570936158251067e94219c944b17693e059a4e816493401da61856f97c15ae5e056796a158db9b06f786c1ad42306763cc18e58805f950016e518057932014e17012485a08d263067a85808d204817693005b1b9307f784c1ed41307763ac1ce4b806c92c018215823492805f248837991e0de247036590000e63d80319120dd248036590a0d9248847d91e11f245847591c0dda45837590e0d8245867e90619f646047e9160da64403619080d8244837c90e11ba43036e90a0db244047590811d241834e8fe01263d004190400e23f00748fc0db240047e8fe11ca3e80768f201d23c83608f611fa3d04728f001da49036f91a0dae4503679020d8de4b06b648c18e3e003b8ee00ce49847682008d20381768ec0511e4307b646c1ce3a30588e80150b6c03f2da40ec44c03711240ce39334b8e40d1e3704688de08ee3682378d800ecb5902b10e408e38045e8d60510b4903b10a40ce3482608ca0da63203558ce01622e03648ca11b63104658c80d9a3103658c2098230856c8be05822f82608c415ba2d056d 0x9d80d867483609c400f66a80359da0df275836e9d40db27604759d211d274034e9bc01266900419ce00e27300349c80d1271847a9c411da7083769ba012a6e00489b401d26d80649a200d26780349b60df26d036c9be11fa6f0472522c5da6e814e9b805326c80765c8cdc26b847a9ac0dea6a83767aac1ea68003299c00c266007499a011268804c996019a67803c99a0dc266036099600d269847e9a411ca68014699c05126500769ea0dbe78036b9dc0d9e7283636eec1bdea306b518c19d9830639c000fe6c003b9a800de6480339ec11da28023481605da6401446ecc1fde9b07b514c1dd97b07389e08d261057998015e25f856598a01a2620064960016651005197611d2608465970119261067d98019f25e867597e11da5e847596801b653006597a19fa5b067d97a15a65d056196e158259805d94801565d847c97211ba5c046c97419d65b867496c11ba57806994201857b346496819ea59867696415d9e2307a95c01aa56806895601d2560064940015255006693c015256057c95615b255005c96019fa57867295c05ba56816c95201da52857094e19ea53057a) (pickBlockF p 20 0x742017db5005b582015d380053a7000fe98803ba5600de90803385cc8d216b124aa011ba1632347fa05ba90014474001bdb4806b580019d370063a3e01228f00448d008d28e017c8ce04928c0479a2c11e28a84658cc04928d0068a0401267e8041a1811d2328124a2e11968484648c804928c057da2c15f2898575a2a11da8984758c604928903708c40492308124a2419f2840460a2069f288017c8c00492838350a0c0d42880270a1e05f289867ea0819f6898469a161186828460a220dca871a7ea1c05fa2e81248b8049286047c8b60492839a6ca0e05b2838260a1411ba84846ca100d8a831a6ea0c05ba2d0124a1615d6828574a08117a2c8124a0201667e0051a0001d280046c8b0049281057ea0215ca2b82349fe01da7d80749f611822a81249fa15fa7e05728a808d27d0076a3211be8a046ba1a119e8184638a60491e7b06b654c18e7f004b9f2010e8d85768a408d20681769f00551e7307b652c1ce2882349e80de67903789e20d966f80399a600c67683749e60d967503649e811f679047c9de11d67883769de0dd671804d9ac011677867e9d019f6778369 0x836c492ab8471aac11b6aa046582ec492b5846facc11aeb28467aba118e08b124ab001bea9806774e013d638047ada15c6083234aa405f1ff815e74c017d63005789ec8d2a5856ea7e15b6a70369a980da29f8361896c4929b0039a5400c6a2836489ac492a68356a840d52263124a9c11b6a6046ca960d3a273124a7a013697804588cc492223014886c492a48678a800db6a20351a820d42213124a9001b2a38060a7800f6960035890c492a2836c88ec492a1835da840d7222b124894c4929f846da881196a08464a800dba9f836d892c4929a8049a5001069d846ca740d121fb12487cc4921e3124a760da29d0358876c4929e846aa78119a9c836e874c4913a0062a68012a998048a6e01521eb124a4e00d2920034882c4929b046ea6a118a203234a68053a99814ca6401ba968464a5c0d1218b124a4a01021bb124866c492193124a5c0d8296835086cc492980462a5e0daa960366860c492930032a4600c294804486ac0521a3124a4e0132928352a4800f21cb124a5411ba940462870c8d1d1016ea4c051a918144a4401baa7835fa940d6ea30357a7c0d4e17b124))) (pickBlockF p 25 (pickBlockF p 23 (pickBlockF p 22 0xb68115ed60453b4c017ecf805bb32015ec78053764013db7004b5a6011d3b8043b7a15a6283234b1c059201815e762017db6805b5a4015d3a80538d2c492343234b180552c3056eaf815b6c48369b0e0da2be0361b040d92c40356afe0d52c4846db0e11b2c3034eaf40136ba0045afa0db6c08351afc0d42c2006caf200f6b90035b040db2c0035dafe0d72be046db021196bf0464afa0dbabe036daf011b2bc0368af411aabc8466aee0dbab98464ae60d42ba8462ae80daab90366b140d7ec2835bb060d5ebd835375a017d668057aec00feb88037b1611ba29323480205bab8014475801bd660067856c8d2b7015483ac052b3857ead411eab40478838c492ae007daac01d6b60054ac8115210b124840c492b48455ac211520fb12483cc492b5057ead015f2af0572ace117aaf045d846c492af867dac6118ab00460852c492ad806daa80196113124ac811f213b124ac411b6b0846c84cc492123124abc15eab18576ac015d2af845eabc117612b124ab411e20ab12482cc4920a3124ab415f209b124ab811f6ad8475ab211a6093124aaa15d20cb124834c492aa8460 0xbac014cc1403f2ea40ec50c03712240ce3a32348e80492398234baa0592ea0068ba60190c0404f2e6412c4fc04711e410e393234ba20512390234b9e05b2e8045bb9c115e388234b9a0552e4807db920df6e5836fb940d8ee4006f2fd00fc4ec037b8a19f6353234b8e05f202815c2f9013c4dc0478e008d2378124b820166370124b8615e2368124b821166360234b880d2ee103478d60492e0004b2e240ec469033b8a15ba350234b7e0550b7904b116410e28b234b7015badd846ab7211a2d5806db3a0196d98454b741156d80454b7615badc856cb5a158adc045eb5a1176d20069b300186d7057db64114ad78450b6c01f2da8070b540176cd0055b6611f2d8846db6011b2d6856ab64159ad78564b5c117ad6845db4601a6cb0061b501592d48468b5215b2d4046cb5611b6d50465b4e1166d1006ab4201a13d8042b4a0152ca8054b240152d20569b461586d1016eb4205b2d0005eb361592ce0464b260182ce0570b361142cf0461b3a1176cd0455b28014ac88050b2e0152ca806cb261146c9005cb3015a6cb0561b28059ac88164766057ac8005eb78117edb845b) (pickBlockF p 24 0xc0600c7080374c2c0d97068364c2e11f70a847cc2411d70a0376c240dd709067ec1619f7090369c1e0d87060360c200df307036ec1a0db3078475c1811d305834ec0e0127010041c1400e3030074c0c0db304047ec0e11cb028076c0201d3008360c0611fb010472c0001db0c036fc260daf088367c120d8df2486b689218f02003bbfe00cf0c8476bf525daff01447c721eda1c873bf80dbefd836bbf40d9efc8363c9415bf23056bc87359f218563c4131bf11cc6bbfb319f0dcc63c46117f10045bc36115efe8453bf1259afc015e6f521bded486b525219d9b48637b4017dbd005b66c015d49005330b013cc2a84b14b011c52a843bea0daafa0368bd601b6f08065be20d52f78354bea11bafa046cbce01a6ee8061be00d4af70350bd40176ef8055be20db2f7835cbe0119af70464bcc01a6ed8061bd81592f5836dbd40d96f2806abc801a2f40044bb40152ec0054bce11a6f30461bca05baf2016cbc01582f10460bc20d76ef8355bb2014aeb8050bb80112ed006cbb00172ee8469bb61186ec8166bae0592fb035fbe60d6ef90357bda0d4ef4805fbc6016eef0057 0xc3288eeb6c23792648cf3b0c6fcd431af310c67c9e318f3b036fcd40daf310367c9e0d8efe934fbfa8d2ea8c3478ea4d0f2701667e8c1adaab06331ea12c58a84331e60ec58983331d00fcc7283b16100dc582833c98059325c868c960190c6404f318a12c57404715ca10f24816cc91316f240457c8e0552e2b136b8a04b8c5a83b15aa0cf22856ec880550c4a84b156a10f21017cc7c11e71e0478c761197200068c5c0127148041c6c11d31e8465c6611931f057dc7815f31c8575c7611db1c8475c6411831c867ec6019f71c8469c6a1187188460c7009cb1b047cc6811bb19846cc64098b1a8575c6215d318045ec5a0167140051c5801d316046cc5c15fb168572c5601db138074c4e118314857ec5015cb130076c7e11bf1d046bc6e119f1784637d521ada54863c54012f128043c8215dafdc976c480551f4c87b69321cdbf486f7df21ad4ec8676a1218f110476bf925db1081446fb21fdf7487b53721dda7c8736f921bdf0c86b535219da0c863c3e19eafcc976c3c05b1bdc87f7c121ed4c487768121cf0e806cc3801830d017cc2e0de70a8378c280d97040039)) (pickBlockF p 27 (pickBlockF p 26 0xd160093460b5fd142d4f46025fd14094f0e123fc3888ee8f423792c48cf54856ad4e2dbf4a8b6bc9f6d9f490b63d4e09bf4a826bc9f299f490263c3648ff0da23ba3b08de4a92336fec1bdf9306b53cc19da9b063d1a017344805037f60fccea83b20560dc6c283337f20bcce982b205209c6c1823d0c0dab428368d040d53400354d0c11bb42846ccfa01a73d0061d020d4b3f8350d040df340036cd02119b3f8464cf801a73c8061cfa11a73e0461cf411a73c8461d0e0d7f42035bd060d5f3f0353cf6016f3c0053334a0ec6a2833cee0590cc284b1a4a10f3a0259ce60963380254cdc09133a035dce60d73378241cda090338025ccdc0933378355cda0d533a824fce4092f388247cd8090f358134cce0d8b328360cd00df333036ccce11db328474cc92dbf34cb6bcd20d9f320363cc605f3300259cbe09632b8029ca800872e0254cb4091330035dcbe0d732d8241cb209032e025ccb409332d8355cb20d532b0039ca600c72b835ecac0d4b2a035eca60d4b30824fcbc092f2e8247cb0090ccaa84b19ca10f2a802bca4008f288134326a16c662853ca000e30c923f 0xd6400b7578025d7209735b8136d6c09335c0355d6a0d5359835ad640d5b58025ad5e095b5f024fd76092f5d0247d68090cde404f1fd011f58802fd5c009f568134375017c7e4057c4448ff11223bb7b08de7b1233d7e31bf560c6bced719f53dc63d7e0dbf56036bced2d9f53cb63c404d3f10234bb1b0d1e639343d560599c0306f7f0c1ad5030676b2c18ce0d84f34ea12c8258471c8a10ce0c83f34e60ec8248371c860cf49db61d2729870f923fc3e88eea8423798c48ccd6c03f34ca0ec7640371c6a0cf540568d22017346005035700fcd2283b1d500dc70a833d4a0d6b520358d3801774c8055d420d134f8344d4a117b52045cd400d0b4f0340d3601374c0045d420db34f835cd40115b4f0454d380d774d8355d320d374c0345d4c0d3f51834bd440d1f4e8343d34013f4b804736f00fc7c4037d2c09b348006c36b013c7b404734700fcd1a83b1c100dc702833d2739e34a026cd26097347006cd140180d0c04f342a12c6f40471bca10f474828d152093478154d22297f480a5bca1695f470a53d22057f48015bca1255f470153c3a44bf0ea12ba3f049e4b9123) (pickBlockF p 28 0xc94a4ff25093bba4e4dee90933c9464bf25012bba4c49ee90123da0c16368005438b00fce2903b21100dc84103338b20bce2982b211209c84182338ac07ce2801b210c05c840013c9048ff24223bba108dee71233d9d0d2f671347d9d292f671a47c8c48ff23223bb9908dee61233d9cc52f670147c8ca4ff23093bb98e4dee60933c8c64bf23012bb98c49ee60123c8a48ff22a23bb8b08dee29233c8aa4ff22893bb8ae4dee28933c8a64bf22812bb8ac49ee28123d98117b21923fc8688eee34237b7c48cf21a93fc8624eee33937b7c24cf21992fc8604aee33127b7c048ce1903b20c40cce1982b20c608ce1801b20c004f20923fc8288eec5c237a3648cf638352d8a0d4364036cd8c0d73638466d8a1193624b5fd932d6f648357d880d4f618254d94119b565b6fd842daf355b67d2b6d8f564a6fd8409af354a67d2b298f11923fc4688eeb7c2379ee48cdfb306b6aec18cd8a83b1e0a0ccd8982b1e0608cd8403f360a0ec77c0371dea0cf60016435d013cd7284b1db011c76a843d7a09675e0258d7209535b0244d7a0d775e035cd6600f7580035d7009075a8240 0xc9644bf25a12bba9049ee99123c96a0bf25882bba8e09ee98823c96607f25801bba8c05ee98013c9448ff25223bba508dee91233)))))))
  6 11 7
def m_2347 : Nat := 0xffffffffffffffff
def s_2347 : List Nat := [0x5555555555555555, 0x3333333333333333, 0xf0f0f0f0f0f0f0f, 0xff00ff00ff00ff, 0xffff0000ffff, 0xffffffff]
def g_2347 : Nat := 0x11515571337377f
def bds_2347 : List (Nat × List Nat × Nat × Nat) := [(m_2311, s_2311, 9, g_2311), (m_2310, s_2310, 9, g_2310), (m_2302, s_2302, 9, g_2302), (m_2304, s_2304, 9, g_2304), (m_2298, s_2298, 9, g_2298), (m_2300, s_2300, 9, g_2300), (m_2295, s_2295, 9, g_2295), (m_2297, s_2297, 8, g_2297), (m_2296, s_2296, 8, g_2296), (m_2309, s_2309, 8, g_2309), (m_2306, s_2306, 9, g_2306), (m_2135, s_2135, 7, g_2135), (m_2307, s_2307, 8, g_2307), (m_2301, s_2301, 8, g_2301), (m_1902, s_1902, 6, g_1902), (m_2305, s_2305, 8, g_2305), (m_1986, s_1986, 6, g_1986), (m_2070, s_2070, 6, g_2070), (m_2149, s_2149, 6, g_2149), (m_2139, s_2139, 7, g_2139), (m_2293, s_2293, 9, g_2293), (m_2299, s_2299, 8, g_2299), (m_2041, s_2041, 7, g_2041), (m_1861, s_1861, 6, g_1861), (m_2292, s_2292, 8, g_2292), (m_2294, s_2294, 8, g_2294), (m_2303, s_2303, 8, g_2303), (m_2152, s_2152, 6, g_2152), (m_1936, s_1936, 6, g_1936), (m_2145, s_2145, 7, g_2145), (m_1761, s_1761, 6, g_1761), (m_1768, s_1768, 6, g_1768), (m_2154, s_2154, 6, g_2154), (m_1765, s_1765, 7, g_1765), (m_2190, s_2190, 7, g_2190), (m_2155, s_2155, 7, g_2155), (m_2026, s_2026, 6, g_2026), (m_1799, s_1799, 7, g_1799), (m_1750, s_1750, 7, g_1750), (m_1862, s_1862, 7, g_1862), (m_2045, s_2045, 7, g_2045), (m_2196, s_2196, 7, g_2196), (m_1798, s_1798, 6, g_1798), (m_1937, s_1937, 7, g_1937), (m_1787, s_1787, 6, g_1787), (m_1797, s_1797, 6, g_1797), (m_1802, s_1802, 6, g_1802), (m_1812, s_1812, 6, g_1812), (m_1771, s_1771, 6, g_1771), (m_2146, s_2146, 6, g_2146), (m_1751, s_1751, 7, g_1751), (m_2131, s_2131, 7, g_2131), (m_2262, s_2262, 7, g_2262), (m_2308, s_2308, 9, g_2308), (m_1827, s_1827, 6, g_1827), (m_2057, s_2057, 7, g_2057), (m_2211, s_2211, 7, g_2211), (m_2150, s_2150, 6, g_2150), (m_1946, s_1946, 6, g_1946), (m_2136, s_2136, 7, g_2136), (m_1770, s_1770, 6, g_1770), (m_1993, s_1993, 7, g_1993), (m_2256, s_2256, 6, g_2256), (m_2125, s_2125, 7, g_2125), (m_2096, s_2096, 7, g_2096), (m_2027, s_2027, 7, g_2027), (m_1749, s_1749, 7, g_1749), (m_2094, s_2094, 7, g_2094), (m_2113, s_2113, 7, g_2113)]
theorem kn_2347 : KnownBin bds_2347 := by
  intro b hb
  simp only [bds_2347, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lb_2311
  · exact lb_2310
  · exact lb_2302
  · exact lb_2304
  · exact lb_2298
  · exact lb_2300
  · exact lb_2295
  · exact lb_2297
  · exact lb_2296
  · exact lb_2309
  · exact lb_2306
  · exact lb_2135
  · exact lb_2307
  · exact lb_2301
  · exact lb_1902
  · exact lb_2305
  · exact lb_1986
  · exact lb_2070
  · exact lb_2149
  · exact lb_2139
  · exact lb_2293
  · exact lb_2299
  · exact lb_2041
  · exact lb_1861
  · exact lb_2292
  · exact lb_2294
  · exact lb_2303
  · exact lb_2152
  · exact lb_1936
  · exact lb_2145
  · exact lb_1761
  · exact lb_1768
  · exact lb_2154
  · exact lb_1765
  · exact lb_2190
  · exact lb_2155
  · exact lb_2026
  · exact lb_1799
  · exact lb_1750
  · exact lb_1862
  · exact lb_2045
  · exact lb_2196
  · exact lb_1798
  · exact lb_1937
  · exact lb_1787
  · exact lb_1797
  · exact lb_1802
  · exact lb_1812
  · exact lb_1771
  · exact lb_2146
  · exact lb_1751
  · exact lb_2131
  · exact lb_2262
  · exact lb_2308
  · exact lb_1827
  · exact lb_2057
  · exact lb_2211
  · exact lb_2150
  · exact lb_1946
  · exact lb_2136
  · exact lb_1770
  · exact lb_1993
  · exact lb_2256
  · exact lb_2125
  · exact lb_2096
  · exact lb_2027
  · exact lb_1749
  · exact lb_2094
  · exact lb_2113
theorem sub_2347 : ∀ b ∈ bds_2347, m_2347 &&& b.1 = b.1 := by
  intro b hb
  simp only [bds_2347, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
theorem gl_2347 : ∀ b ∈ bds_2347, canon b.1 g_2347 = b.2.2.2 ∧ b.2.2.2 ≠ 0 := by
  intro b hb
  simp only [bds_2347, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rc_2347 : dagCheckRootsF m_2347 g_2347 bds_2347 (groupRef 1745 (dagTraceF m_2347 s_2347 12 f_2347) l_2347 0) s_2347 12 = true := by decide +kernel
def picks_2347 : Nat → List Nat := unpackIndexedPicks (pagedUnpackF 20 7 (fun p => (pickBlockF p 7 (pickBlockF p 3 (pickBlockF p 1 0x82340820108108080e107fe807db207bb007a0d0796507960079030774e07702076c20750e0731007300072e1071e8071e0071a2071a00712406fac06dee06bb2069ee06793065af06391061ce05fb105e0d05c1005a6d058700570b055e90554505540054e3054830548005480053a7051ee04f9304f0404f0004ec204e8204e8004e8004dc604bef04993049420494004902048460484004840046eb0450f042940424204240042020418404180041800410403f6d03cd503b6b03ae403ae003aa2039c7039c0039c0039060372f03495033c60322d0318503180030e502faa02fa002fa002e0d02dc202ca902aee02874027c50260e025080232f022a4022a002262021c5021c0021c00214401f8e01cf501c2601a8d01a80019e50184d0170a0152f013cb0124c00fb500d3400a57007d4005d0003160016d0000b00000 (pickBlockF p 2 0x14f2114d6e14b70149511492114809147e11462e1443014211140e913e9313d4a13af31392e1373013530132f21307412e3212bd312973128491263112509122f11210f11e9411c52119f311736115111129410ff510e8b10c3310aac108341064f103d4103a1102a810281100af0fe910fc520fc210fb090fae10f8d10f6b10f4910f3a70f3810f2690f0320ef280ef010edca0ebb10e9b00e7ee0e7450e7400e7020e4f10e4a20e4430e2ad0e2050e1a30dfb00dfa00dfa00dfa00df240dd6e0dbae0d9530d7500d5120d2750d0510ce120caf90c9e80c7360c5ea0c3170c12f0bed30bea10be810bd690bb510b9120b6370b6010b42f0b1d30ae9a0ad880aad60a98a0a6d60a4d00a2d00a2a10a16a0a14109f1209cb3099b80998109733094d3091b90902c08e1108e0008c6d08aae08853086eb086c1085e7085c1084a9 0x1ef211ed111eaf11e7d91e4d81e1f71dff01ddf01ddc11dda11db911d9141d6371d6011d3751d1321ce191cc6d1ca511ca401c8ad1c74b1c5121c3ab1c2c71c0351bf471bcf31bb2e1b8f21b6741b48f1b2711b0321ae4f1ac8e1aa711a90b1a8271a8201a7c31a7251a7201a7201a6851a4ed1a2b21a2621a2601a2221a1a41a1a01a1a01a0a819ecf19c7319c2219c2019be219b0719b0019b0019a081984e195b5195621956019522194661946019460193e41926c18fd518f4418f4018f0218ec218ec018ec018e4418c6f189b6189241892018885187a7187a018781185ed1848b182ce18073180601802217fa417ee617e8317d8817baf17ae617ae017aa217a6217a6017a6017a221786e175f41746c171b616f1516c18169751675116477162ae1614b15f6f15cf415af015874156cd15473152ae150721504114f48)) (pickBlockF p 5 (pickBlockF p 4 0x2aa042a9e12a9c12a9822a9422a9022a8272a64f2a3f32a22e2a0cb2a02529e3029de229de029da229d0529d0029d0029c0829a2f29795295ce295442954029448293862938029361291ec2908b28eaf28c7228c4128bc4289ef288c9288c028844288402882128801287462868628588283ce283822838028342282a5282a0282a0281e627ff027d7427bec27a6c27870275d5273ef2719326fed26d7426b8f2693326901268e12670f26510262f1262c1262a1260cf25eb125c9125a52258122562f254302523024ff224d9324b71248f4246b224453242122401023d9423b71239132367523470231d522f3522cf222ad1228ef2267422641226212244f2221221fd221fa121f8121d7121b13218f121693214332124f20ff320dd120b54208d420654203f3200d91fdf71faf81f90f1f6b31f6811f6611f4701f2131ef56 0x319a931791315ce3139231361313413120a3118430faf30d7230af430ac130aa13092c308a430691303d6301733000b2fdd22fdc02fdc02fd632fd032fb8c2f9af2f7b02f62c2f5c32f4c82f4062f3e12f28b2f0142ef842edce2ece72ecc12eaef2e8742e8222e7c32e62d2e5c32e5252e4662e4602e3e42e26c2e1872dfce2dd162dd002dca32db2c2da852d92b2d8662d70b2d4f12d34d2d3212d2662d2222d2202d2012d1462cf122cee12cec12ce632ce602ce602ce602cd0b2cc842cb4a2cb402cae32ca262c84f2c6cc2c5e72c4e82c2d12c2a12c2812c2232c2202c2012c1c22c06b2c0412c0402c0212bfa42bf432be482be212be202be012bda32bce62bce02bbe82ba0f2b82f2b5f22b42e2b1762af8f2ae692ad0b2ace12ace02ace02aca22ac432ac402ac402ac022abc22abc02ab822ab422aac42aa822aa80) (pickBlockF p 6 0x3b5503b5403b4a53b4813b4803b3c63b3823b1ed3b1c13b1c03b1253b0c33b0c03afc83af823af423ad503ad403aca53aca03aca03aca03aba83ab433a96f3a9603a9603a9603a8c53a8823a8803a7883a7803a7423a7403a7023a4f13a30f3a07539db639b7239b4139b21399cb397ef3957439313392e1392c1391a93900d38d9438b5238b21389ea389c1387d038573383513832138301381ab37f5337cb537acf3794c377123758c37580375803742b372303708d370803708036f4a36d5036bad36ba036ba036a2c367f23666c36568363513620a35ff135ec935cd035ba935972357ae35534353ac3520d34f7534d8f34af5348b234653343963415233e9633bd633a8a33871336cd33492332ce3305432fe332fc132f8232f6132e2a32bd3329d032735326c3326a1326623264132529322f23207431df431caa31acf 0x473574715046ed446cef46a74467d5467a146781465af4633446301462e14612e45e9545c1445be145bc1459d04573545701456e1454b24523445011450004500044eab44cb044b0d4485644596443144416d43ed543d4c43bad439ee437f0435364334f4311242f2f42cd342ad0427f7424f8422b2420ee41e7441c5141c2141c0141ae94190f416d2414b14148141369413414116f40f1340cb340ab040815406ca404734030b400f13ff8b3fd713fc0b3f9943f7af3f5153f2373eff23efc13ee6b3ee413ec8e3e9f53e7b23e7813e64a3e6213e4113e1d23df923df613de493de213dc6e3da133d7b33d7813d64a3d6213d44f3d1963d1613d02a3d0013ceca3ccd03cca13cb6a3cb413ca293c86e3c8413c70a3c6e13c58b3c3713c3413c1eb3c1c13c06b3be133bc2f3bbe23bba23b9b03b7ee3b7e03b7a23b7a03b743))) (pickBlockF p 10 (pickBlockF p 8 0x53d1453b1053875536cd5356b533cd5320e52fb352dee52bb2529ee52793525ce52373520b651e5351c31519d35177351741516e3514f051293511a750f7250f4150ee350cf050a74507f4505f050374501514ff314fcf24fab24f8cf4f6924f3f54f1d14f1a14f1434f1024eed24ec164ea104e9a34e9814e7904e5714e4874e2714e2414e1e34e02e4ddf24dbd14dba14db434db024d8f14d6364d5094d3104d1e94d00f4cee94ccb24cb894c9334c76e4c5134c2944c0714c0414bfe34bfa24bd914bb144b8f14b8c14b8634b6ae4b4534b3674b1704b1034b0e14aef04acb24aa534aa214a9c34a9824a7334a4b44a2cf4a18a49f7149e0b49de149de049c8b49a90498ed498c1498c04978a49590493ed493e0493c1493c04926b4907048f0b48d1048b10488f1486b2484ee482b24801547e4e47bf347a2e478cb47635 (pickBlockF p 9 0x5af655af605af035ad2f5ace25abe85aba25ab245a9ac5a7915a5525a40a5a28c5a0ce59f0e59d6d59bae59b62599cd5980e597085952f593ea5920f591a35900d5900058f8458e2b58e0158e0058dc258dc058d6358bcd58bc058ba158ba058a2c58a20588cb588c0588a15874b586295848d582ed5816c57fcd57e6b57e6057e2257d0957ce157bc957bc057bc057b8257b8057b4257ac45796b57960577ec577e0577a2577a0577a0577a05764b57640574cc574a1574625746057460574605744157440572cc571c85708a56f4a56deb56c0f56be156a8b56a8056a8056a615692a568e2567aa567a0567a0567a05676256760567225658d565615654156521564e25638b563805636156360563415620a560e955f4d55ec455d2d55ad35589255633554115519454fed54d5554bad54a0d5481054594543ce5415453f8e 0x6162461430613c3612e7612e0612076106d60e7060c32609b460791607426074060702606a3604b0604626021360200601c2601c0601c060182601235ffcb5fe6b5fcae5fca05fc055fbe15fb455f9cc5f9255f8a45f8625f7a65f7a05f7a05f7625f5705f5035f4a35f4055f22f5f2015f1655f1605f1225f1205f0855f0615f0415f0405efe35ee4d5ec505e9f35e7745e60b5e4ab5e32c5e2e25e2e05e2835e1c65df735dee45dcd15dcc05dc445dc215dc205dba45db435d96f5d8c55d8445d7e35d60f5d5655d5415d5025d4655d4415d4215d4205d3c35d22d5d1855d1615d1605d0a65cf2c5cea45ce055ce005cdc25cdc05cd065cd005cd005cc465ca6f5c88f5c6ce5c4d05c2735c0325bdb45bb535bb025bb005bae15ba455b8505b8025b7c25b5545b5405b5025b5005b4e15b4e05b4645b4035b2e95b0b25b005)) (pickBlockF p 12 (pickBlockF p 11 0x683c06836368303682c2680d06800667f8467f8067f2367dcb67d4467d2167d0167c4667a8e678716763267411671946700c66d5666d0266d0066c6566c03669f16679366780667426674066740666a5666436660266394662e5662a266281662046601065fa365f2465f2065e4765cad65ab065872655f465336652e2652e0652c16520664ff164f4564d8e64bce6493564920648e2648c1648c06488264823647e264574644e4644076440064400643c26420e642006416564122640e26402663f8563d7163d0363cc263c8263c4263b29638d36386363860637a6637a0637626376063760636c563663634ae63291630af62eee62c9362a52627f36266c623b6623626236062322622286201161fc261fc061f4461f2161f0161e6561bb661ba061b4361ae361ae061ae061ae061ae061a45619e3617b261705616c2616a1 0x70f2c70d1170ab370872705f470355700d46ff0e6fdab6fb726fae46fa266f7956f5146f5006f4c26f4c06f4256f1766f1606f0c56f0a16ee916ee806eda76ed816ed426ec866ea526e9676e9226e9206e8666e5f46e5836e5806e4e56e4e06e4836e4806e3c66e1d06dfd06ddd06dbef6d9936d7906d5526d36f6d1326cf306ccb46caee6c90f6c8466c68e6c4526c1776bed56bd0e6bc656ba8f6b9c66b80e6b5b36b2f66b0746aeec6aea26aea06ae816ae236abb46aa4b6a8eb6a6f06a6e06a6a26a6a06a6a06a6816a6236a5e26a3f06a3646a2e46a2e06a2e06a2a26a10d6a1006a0656a0416a00269f8469ee569d0f69ca369c6269c2269c0169b4669931698c3698c06982569820697e2697e0697e06978369723695ac693cf6917368f3268cb468a5368a0268a00689c2689636878f686696841368400683c2683c0) (pickBlockF p 13 0x7acc27aab17a9e67a9c17a7d07a7827a6a77a50d7a3107a09479e5279dc479d0679b4e7991279900798c2798c0798257966e79451791d47902d7902078fe278fe078f4578d3178b1178894785f5785837852378311780377802077fe277fe077f4577cd477c0677bc2779b17796277868776ae77491772af7703476e6e76ccd76aef768d1766737648f7623375ff275d9375af5758d175616753f1751937500c74d9474d4274d2174ce274c4574a31749e2749a27471574700746c2746a1746a0746a074662745c5743b174305742e1742c1742067401073fa373ec773ec073e2573c8d73a9073833735d37340e731d272f7372dae72bcf72a0e727d2725b172353720d472082720617202271fc371db171d6271af471ae071aa271aa071aa071a62719c57184c71631715857150471500714657128f712427114871121710a4 0x813e58126c810cd80f0e80dab80c0d80a4e8081280800807c2807c0807258053080311800947feed7fd4d7fb127f8947f8047f7847f5af7f3917f3807f3427f3407f3217f2a47f0727ef877ef617edec7eda27ece67eb0f7e9107e6947e4ce7e34c7e18e7dfed7ddb27db727db227da857d8527d66f7d6607d5e47d5c17d5447d2d47d2067d1a37cfcf7cfa17cea87cd2c7cb307c8957c6ed7c58b7c3337c14f7bfad7be4b7bc6f7bbc57b9ef7b88b7b6ce7b6067b48c7b2af7b2627b2227afd37ad547ad407ad027ad00)))))) (pagedUnpackF 7 7 (fun p => (pickBlockF p 65 (pickBlockF p 32 (pickBlockF p 16 (pickBlockF p 8 (pickBlockF p 4 (pickBlockF p 2 (pickBlockF p 1 0x32003981a54d9a0a4088a182008e1e2459332003993034e1a284c8831404d8c1058a8e1640789001cc98284469c1e28097182081a165448e001cc982e48501105858e2a34189001cc982a6cd14262809222304031e2c80e1a2400732606951e6808816284800e50305080c1011624500 0x1e240181054d1b28043922284619143c1901c3448030484010080c0d367c016103880c121c09800210013044f0d1e0080818243811c604123e246001c58098226c69f3c00908182438e2004c081a3c60014444810e604151a687810e6448a0060c110a40e8d2a3cb812630508343848b) (pickBlockF p 3 0x4854c072860295100cd091484001480009534910803224c1b24203a0202871534644803020a1138347810e84b8c322881a2a24700304452030011901c0c50918803882258c001c0c5071260016105c9010e651151a287031200c071000087101c40d1e60394302091b101d0101438c8d 0x2e800073020a8d3698a05204409a1430c8e1e250800e607031424620101cc002c1c400021c40710547810060396302078e2e4840744805101c64a8f1200c083834d11060439b4230ca2145470f202401822283a030011901424620221c7082c600071004021101d200021c41a1424080)) (pickBlockF p 6 (pickBlockF p 5 0x4200398486091c247091c247078e0005227384900a1c6438f4224400305469a3614390186408a1e388a11220018247091c302091c14249184220e033424001489089c24807073228d2112200182a348052e3d307186409114690891c20018247091c2470520247000110709251484c8f 0x21c00a30208901668a891c000873c2868f2230410342ca891c043801430f881c2ca8d2c24087007898a3e44608164078e1234087003028310285911204380461d08a22244003048e21000491c4248e212470391420008838493a51468da132800073020a151a14817023c60a3238d09) (pickBlockF p 7 0x1a840033064407140480e163c48d004c31534048a11850503164078e123400c302068a222cd090038c810e7c81d0a3c98a3044608342470b0264380182068a226070b1e24980320439f201451818447081e2498b02643801a28c081c405952c24780021cf133e2868c1038a8b205848f 0x4cd951a68798322060902485a10e9401852248a12a6899948307811a2c0212261499483c0891a2c980226440b0e3400128444092a6838c1e0458d42004074244a130e05424103c8891684680281d4092a69208183c5a11a048800044c881a04587001c4112c8401426444010e3c48b))) (pickBlockF p 12 (pickBlockF p 10 (pickBlockF p 9 0x2e48a8d1824c071c0c0991620b004448717022cb183221287002d10e0660ba32404b2510003a22e480951824c19103818d2c945a10e0111602285951a0c7090020da024603a50020e122e6d501301c01336a90951a68798321d28c1248091162000736603a024212800e6039b0221292 0x5480ca5302038020381931470b9b3204620304839610440101c28da11e2501206940953430c07322cb111a20025164071c365c08d1e895203248c084a1c021203819c2e6cc8154811982421125001c80e386cb812a6878c12a9003242cc1910351214a1c0110628b8e2404c072c2000a) (pickBlockF p 11 0x2e6040e322caa24a8438022a80980e48d8036495174e84c190e5469a1e94609024458e1000c1b245c0a700212870a6c192306440d1e30497029c715342d287008478d306440718280901668a891c008861a3c0a1185051016684951c01291301c91b5405288009488a2454d9a022c68f 0x423050b2a384901e012a5301ce175405288002d0911470b815480c8d1e94c080e014101464e1236046201c44c072e584002028e2134250252e0468f186088732385962a200252470d811e35520325cc084a1c021202ce123605520328c7182e21125001c2832048e1b023478c12a901a)) (pickBlockF p 14 (pickBlockF p 13 0x67091732055202c60d8844940070648e17025469a1c304aa406c596306440f42892870059501301cb92004cb9236a95951a68798321d28c124008b10580182e48d8156004250e389972458a8d3460c881824d81563c80b42943801a60c880e305011c2ca8f124001426441a22c34d01 0x581c01012016102814e0142485881e256070060c951a280881c2c7a1121c02626408843404614101450e163c4a10e0051c36680955480c8d2c94c080e0098e0628e122e6408c4044c1b0e200161c0c51c2a2501b4a0469a1860399163c416005891c2e04a8d5480ca236604250e0118e) (pickBlockF p 15 0x5871000309439932710975404c080e0129a1e60e1258304a10274c8b101c0053a61010343c62110052ac161c00520600a1402078b1294007584881816640072874b1c426890f18200891641607007438512b0a120284e0b10407890eb00180a705993a003940a48d1c1e310880224590 0x20b8a8d0230498321c0214c4409d2034a8f3430498102cca10e012882458daa02640074a986951e6808b2ca90213094c880e01311105cd951a756811824c0732010a622046951e686093020e8b3284380364900030943993248baa02604000e94e9a1e84c2c38486090240c8b101c01b)))) (pickBlockF p 24 (pickBlockF p 20 (pickBlockF p 18 (pickBlockF p 17 0x445191048daa026038020445185874e12343c6090238c8b0e200114828c88386d501301c0210644518384960f1824d0e026458710740113064a8d021c521166848e1000a104c9020f06308870a0450b426848e1001288386d50132003a54234a8f34045aa4061299101c0262220b9b 0xe1408a16388a11e24400167488a2454d9a02a90244a60c880e0130a5c403951a5cd8c12440a11060719001530a067489002347a11824c072a6858e32200111434e1b06a901a029129832203804c3c5151ab439b182489702847083074c80209851106547811824c071a84d0b1c74c88) (pickBlockF p 19 0x385c10e54807814894c19101c01a141cb951ab4609364408e426041d32005021a54d0142304980e4470f1674c8800644122ea80980e00e9a1e608af384860902405990e200191070baa02603801c68c1c244578c123c08b321ce880060c951a280871c8458f2224400284d204340880c 0x343d08c120471916200073270da15404c08001c8a5307090e5e6878c12050993a2c4000e60c951a0450816690891c1c010083c08c282028a1c2cd09421c0111448a8f2e055204894c19101c00a0e5cdae2a34609220480e4260419002811d0234a9a1c84609304038f222cc88004450d)) (pickBlockF p 22 (pickBlockF p 21 0x2ea8099001d2a11a5479a02a90253064407002082e2a34b9b1c0460930643804204e8e2034a8f3430498102cca10e01288245d0aa02640074a34a8f34055204261299101c0151a20ead1c5cd8c1204c0732010911c046951e686093020e8b32843803248daa02604000e412985e74e12 0x12648880074984044070c301c2830229091122cc880060a8d343c08846285a140652870040713080808c1260405062900b328528700203951a04c0a166848e32008903a9020f028498c301451a122c71900203951a04c0e142c789266402122412043430c05023850f122c999009441c) (pickBlockF p 23 0x1c3c6131664007326069c345099106c009b12210962a385901e300073260a111a707b0025c4884240d0b2a307000e64c1724041b01084b0b2a3868c001cc982a6cd14264409206c0488423c5901c306800e64c0d2a3cd0110845b018003940c14203040458c1400a8d343c0980e8450b 0x2a318181a300014488c00620d1301a30018105c9010e641a2605470d1800c14301c400021c407101c41236203aa20c07191e346003020d810e54d12228449906c07901c306803020a8d343c08732c0600306088520746951e5c9896004421343860b32003981a54d9a22148216024401))) (pickBlockF p 28 (pickBlockF p 26 (pickBlockF p 25 0xe6038800043880e203881e38b92101d52260388192a3c6003020e1a28441810e34da16024ca22a387901800c0710010880e90001305438818c120c0e50c052a2019a6031081005480e34910804430c9836484075441815346470c006041138347810e84bb0126481a2a307003000098 0x6038c87423c6080060a8d346c2810e41809323c88e42304003048e12382091c3431818247019a4830001487092a60383a132686080060a112a348052e3d30712c0c81348460e1000c123848e1238607aa6048e000220e126084c971ea83803020a8d346d3140a408816024c8e1e31080) (pickBlockF p 27 0x4cc0490322d09a1838a8130004b01c6511f422c6951804c002a688b0127cc8b203c7211834098002420232c108b1804c00286091c4200092388491c3461092388400110709276068da132a83803020a8d0a40b8f02258193438621001cc123848e1238607924860e0f1c000a44e7092a 0x301c9084a0099b025469a1e60c881825825242c3a10060c880e240901c2c78c1ac00130c54d012284494140c5901e3860d007d91008693071c25819222c78c42044180011030321c7011684d0c4c20c00207c20712398191668626420441800c889f34c110932385a12a4078c0260011)) (pickBlockF p 30 (pickBlockF p 29 0x18255200604c191034592448438022c05b32e389012c6038800ccb922a34609306438e060440b2c011211c5c0963064407242c00e6060ba32458088001d1172a3049832207030234916161d080445808a165418c1c3401b16a89180e0099b4084a8d343cc190e304920295811102c01b 0x4430d1e05089282880b3430a8e00000332454d9a02347aa406580b3020380203898b6670b9b32c00aa12609072c44400203999b423c62a240c0953424c190e44b0d162000020390b04e70d9702347a2548059930484070040727385cd9960050233049508441c0101c70d974e54d0f) (pickBlockF p 31 0x1c58a8b100000b4248e30360478d5480c9730203806040c9c246c701408cc2a105d10700141902470d8d1e304aa4004d181038c972a885a10e0181b5648ba04260c872a34d0f18248814e9458e1001805360c91832206ab1e3048e2a685974e94380423c6983220389600480b345460e 0x2a34d0f306438c12055a52020b0b00398132e480962a34d1832206091e40dab4a2c3a10034c19101c48160385951e30800284c883445869a028448a165470c203c000008599c2e05520166580d1e6040700c080b6664e1236055092238c072e5840020cce213431517024468f1260c87))))) (pickBlockF p 48 (pickBlockF p 40 (pickBlockF p 36 (pickBlockF p 34 (pickBlockF p 33 0x2d9b0386cd012aa90192c34c080e018131c0c5b33848b9902a8491306c38800587036670a8c546c08d3424c190e3c5882c00b0b42c1392385c0951aa9019446cc080e011b04e3819c245cb190280c1b5421107000c91c2e9ca8d34386095480096306440b363d1210e018132e4901b 0xe000004c34a8f3404b2a408580b30644070099813222c41736546811824e980e650804c4408d2a3cd0c126041d166508700418134274d0f307090c1205a19102c380604d5a1343cc1c24304b40274c88161c01832546b00220734163d08c0e01313204421a0224a080a2870b1e31087) (pickBlockF p 35 0x423859d32200306660e9c246878c12400990e2c70800c19983848d0f182408e321c59d1001a1832546810ec108b343070800508904cd12041e24385022859a423070800000211a5479a02a90301660c880e013302644417365468118248180e640214c44e900234a8f3430498102cca1 0x284da240868090121c28a222c70f42304003acd8122a6cd2a402c0a4306440700c08854c1c69736304902a05088306470022153333a4068f340508c12603951638c88002d9b01a70d9a54800a4306440700448304ccca872e6c6091a2c0a1106071d32008904c0d9951e04609301c69a)) (pickBlockF p 38 (pickBlockF p 37 0xcce910234a8f343908c1260390166440016cc69c603cb811ca90243064407004581316cc397365468118247213020e9900cc8811a54d211824c071e3859d322003026cce9a1e60e121824881206438b1001813666879838486092204c873a2c4006860c951a0438e608458f2230400 0x2e6c609027439832010911c046951e686093020e8b328438020c11983a7091a1e3048168645880e0182b4260e12343c6096804c9d16203803064a8d02c040e688459a181c010083c089282028a1c2cd0c421c00b66c09151e5c0aa4090c19101c011604c397365468118247212060419) (pickBlockF p 39 0x4481d669020f424c4980a0451a182c71900cc4072a34098603878b184cc8042448334810d09301408a1c3c60b2664000002d08d2a3cd01548181832203806020a8d2e6c701182480730640213a388011a5479a1824c081665087000000b1a5479a02a90304260c880e0180b2a3440e 0x30546a02814c863430d90100c7b61c243803020a8d343c60932180073050085080c135142c30700cca8d343c0980ec108c1644c8800749b3080880e1260385060452122305991000c151a68781108d80b426550700407130808609302028302285aa3284380101ca8d026180b3430719))) (pickBlockF p 44 (pickBlockF p 42 (pickBlockF p 41 0x38483196c6870c0e00c151a4028f5424c862e21b1a183838030003990060e8e6c0cd0c10548191a1dc0030746b8061c6370061c070004c3770240010edc6386e1c01818e41896e1c018105469736647090631b800e6091c247091c1e24c12281ce000250d974a20e123219b0e1e24380 0xa381813431b8832546870061c123848e12386849824e039c12d80012e6d2883849b191c24d370e00c151a310140a40199023cbb61069b891c1c0183a41b082a687191a1c6380060c12387cc1c281c93a0004d123831d1828609033471a8c3e000872839819747cd007030398285cd88) (pickBlockF p 43 0x26000718004816e84c07160c4b74238600161c0980260198067019c3804c387060a033861c1806e0c003061c187060a180650c0f12703bc064cc95608470b1e00498021c284343081f6020ca116f070f12000980e141b50808508328458100603bb124070c4865b07006038c3200c1d 0x2400389202c492206008b321c000247000e702c290005018e6c2c290005099c1cd8908062c80f0a243800630c192a343086c3858f121c013086860820500850c0c5b61c3c4870031837325509a1638480021cc051e0cf90781060a60dc419422cd091c040180e142083239bbc422c48c)) (pickBlockF p 46 (pickBlockF p 45 0x103c805161c4803000e9200ddc130a2440e0e2c800380009d0a7079800044871664e120050e90002c283284c2921cd8e081e2c4900e002811c25c0718dc40b2000c053804580327429c1e0448700501852404d0e6c706081e2c3892000c0020700381201c136e2c40e121c80500e0c10 0x160029d1cd8c24405009034e0999363c608121c580166c037121481b0220707164c0371638d801cd82b83249007166c0106e38d8b0039b107064e200e2cd801cd82903005c19103d009362c98700e0e811c1c609102c8370a00592206058032248191248800021ca1d067009a1cd890c) (pickBlockF p 47 0x32240801cd8da0163dc1910704980e00585320440900207361e24c87386d5382e2cc080039b150a4c09a7060e12183c4993a2c407000400b02209906e044880e7460e702c0090201c0b1c2400b0a044090039c8016149b70224407183859d002470c16dc3800a40e811c2438c26ddc08 0x7a406951075b98020c70c7024c87160071d1654c006e75e812a30c191a3858006f4689305db8e362c4190e7403d2a21b98023418e18643891674038021420316386096e1c0190200da032209180e0059920044005664407246d50b00acb981cd898d0274d383048e0c1e404991620380)))) (pickBlockF p 56 (pickBlockF p 52 (pickBlockF p 50 (pickBlockF p 49 0x126400e6c0c98b2ea90151a6001036e0c880e39b3d3a0c08d2a68608303dc101624c87000038e6c2cc072481c003620c95301c00e6cf4a9a10e008d1e2c6180e24c801cd81937a3c0975480a891a6059b7020e990e007367a0c09534304181a3dc0b3a24c87004018b305c71b6e64407 0x6a04a8f1220c0d1c69c0b1874c870064407245d0005660d903a60e12343c48c1638c880e00c87385d000306c4036a04c1c243c71a1230599101c01d1260c951a19b08166860e0e008041e0c4b510500850cd859a1838380001cc073848da016004190e606807a40695342008f1630c07) (pickBlockF p 51 0x1c380102cc073848baa0020c8b7a407362a3c1b51004d0d1230c073201b0b2a34daa4040c001c5dc19101de836a75b011a54789106081a702c70c321c01a180038700205980e495170020c8b7a39b151e0da880234d09301c619003c4bd0254da06ca86981639c082e6439d00f5b03 0x1c80c0b1a5c4190ee0e806c401bd14dc7012a3cd0c106068b3ae0c890e00c880e48baa00acc1b6e04e9a1e60e121c30499702058700ddc0b126439c2ea8c1b1001b377004d0f307090e1824c88161ce801860c951ad840b34dc7090e00a3b200dc041e305080215b0b34dc7090e00d0c)) (pickBlockF p 54 (pickBlockF p 53 0x6c2cc8700f4a8d343cc36109048b766438020747137a1010c106008506d9209762cc87002de901c34a8f342840118e0c0712640051c0c08b36a90371a40a982e644000ee02837a4051d6e3808d1e686083054589321dc006e2de8e2a3cd0a100468c7060389320061006f448136a9b95 0x166041236a80192e1cf1d327091a1ef06090200c07102cc88386d500305c39d3cacc1c24687bc1824599001c09f1030c192a35807423c4bc00044140a6861e2c18587087d837423de090020094081410314d432100200951a68798109060b6c643803a4de8404244101cecc010a0d20c) (pickBlockF p 55 0x460c8b0005c1d2a34c8704dc6097820c00160413c7ae0b9f36dc088301cc95083013d306458d6e0009d2a11e981a1c13c6e30589322003802e02056e09e0c42240080248daa00acc170e58f183848d0f1824f8b0201e190e20c19107159b5400b870428c9c247cd3c1e304810060388 0x1024c003204e843cc1e9a1e30abc166038d6e7c480322008d2a2ccbc6e1cb82426c0080260f0202f4bbc36dcc080e64f8d0af4c072a09e37182459910e0001047c5992ef4dbc6e1cc082a3449f6e60cbc16000951ae0c87047dbbc1230418002c0820264bbd36dc03c161cc082a35b8c))) (pickBlockF p 60 (pickBlockF p 58 (pickBlockF p 57 0x4298043430f951e6438d78dc0091060581607cbaa4034a8b0265e007a6db873020401167091b40012873020a8d343de30161db8c1220c803004f1d607cd0f1834c872af1b89002059802c1e975481e1c1a00098106db873e6558802f4c19104900036ac39508acd0f78c1e8b1a1db8c 0x1824f16082cc9f60843a06ef0d801004c302cf4baa40549003c05e18106db8732204017a6041c246d0000e64685343de8716546091060019021583d3c6878c1a7c5980e55e371200c8802c0f84165d5202a0403c1a65e9b6e1cc08102008b2480025361cc151a6878b0e304883200c01) (pickBlockF p 59 0x264e122c11092687059e343c2090e7c60010045982c70c993c70b1a1820c1d00050923ed059e0e70d160830008024821e5660e8824105985600099247021f427821c684859a1e584873e300080225a1832546b00ef109a18000882814b1f1e2430b3c1c23004dde2134300080234a9a 0x56f4d0f3070909182cc803e1c0883e10b1842f43993430f0b0020098327859f0868f195460b8f182438010045843e78caa0e68c0c2e005880264c1e022d08430f4c9f343c4871630f0010049041660c9d0848c9e10600013c10e0b0e7c91a1800b080274f1f3864c1a182059f3861580)) (pickBlockF p 62 (pickBlockF p 61 0x2ea9e990e480180221e9a1e60e121230f8b3c000990e20c183220e2b2e8001b0e60baa301ce00320441f343cc9c242460002603881660baa1660392006408830045981048ba00064d873c75e301e64e123424600026038816ac0bd3220e174000c1b0e64baa7a644073800c2b0274f16 0x6e1cc084a6441c245d5000e60415343d28b0e3448c10640180278e8278c0a8d1e24c8734dc00c10605812c09e307a7069b54800013020bb70e7cc8830644124ea92802e1d59508687ab7a343891030c003204e843cf413c6054789166038d34dc600327c4013205e922e8002b306c399) (pickBlockF p 63 0x3220c1910709174ea92800e2029a1ef4a871a246083000c810af183d0434d0f127c5983c1cab71800c880209e30165469b548008032f4bb70e60425022cc8824a80170e604151a687a578c05876e2440c3200c0178c0f822a34d0f12643b7180040b300413c605469b54805813201e97 (pickBlockF p 64 0x1664d8770745193848d0f6e3048002603881605e991070baa0060d873a54b2b7a60e1a1e486091665c000edc0881860c951af180742684b700044380a3c61e3ea0b02161c2307884d3712004011a54616087c7891664f30780908754dcb801004c0278c1e95246d5200004c083c5db87 0xedc00910605812c09e3d706d520383401f02604170e65b951aacd0f7a1dbb81820498006409d1409e3d086878c2a2cc071ae04803221b8102f49175401598361d41f1af4c12343ce0c12e058002643b71060c8816715975400d873ee1e1938487b7343048002603881604c08245d500))))))) (pickBlockF p 97 (pickBlockF p 81 (pickBlockF p 73 (pickBlockF p 69 (pickBlockF p 67 (pickBlockF p 66 0x18345980ee0a8900644370209e0b36a90151a040197a5c3986e2042702490001694b8730546a7343c3b7182c4093200c013ee013c1e30a8d34643896e00418160413c36a90151a2c09900f4b8730dc4271670917400128730213951a687876e30588126401802e0e8a04f0d0f1854699 0x18f4580026041f0af019e7624c870809821180040b3005e951a68798601c5a11278001106428376305286ef4c07087c13c608449e1600c880234a8f1824f1f5010b02166583c421d0176e0040130a013c7a6d5202a4801e02604170e65b951a687bd0ee06091060019021413c7a7cd0f) (pickBlockF p 68 0x1c0c3a06e84d880060a8d343c609321d0880060314021420304d450b422000d2a3cd09182cc87420040130f4a8d343cc300e2d08c3c00099107d40578dc1896af4c070809821187858032200951a68799601d0897a2c0013020283187de1e321c20242c0480102cc012a34d0f32c03a1 0x3a046951c305b7306400d2a8439802381b71824c8b107403802142371c0c5a11824400484cb107c5008434303856c381b7422c7891000a8d1e312090aa08160665b0e0e810976e200182a3461620147893291b0754dd08e2e200182a34c836e1cb8e3684400305469a18904852c40cb6)) (pickBlockF p 71 (pickBlockF p 70 0x1e24398342db8c3a644004858806280420f121c2b66e8459a1c3040010ad22b0234a8f341c5a1182049832007364804e834234a8f3430398202db8932200081039b240234a8f342c3b74230498106400e6c900834234a8f343039816dce8932200210234a873a607036ee0609322c400 0x181cc151624c886e0008d2a3cd077085b8c126041900d880e06050951e68607303459d1265b8800914102c0dc01083c6070ad87211669b8910015884804a8f34ac3a11a2460830640364804e904234a8f34243981c2db8c3220008109008d2a3cd07422461810640036ad92014234a8e) (pickBlockF p 72 0x814c887839c0c12dc080301c21a181481f3cc0c8822f078e12040180e1010a0a0da99107888100603940a101826a283000e04e9302101090e4073b30141b6488460b32200282075b8e2690202181cc010a0db2112ec5991001bab0234a8f341dc211820498320028e0604eb8423479a 0x78301096e0038130f0e12343079f1600499101c8817864e123e6888c1e00488021cc0b7878e993848d11183c00910043981674f3c307091a3e3078b0024c880e4408c3064a8d60f040f1200887025029a1879f0b1010f86603c480781c0841844f90781479e606443834dc48e0200c07))) (pickBlockF p 77 (pickBlockF p 75 (pickBlockF p 74 0x321c0380234c973e44db702203980254fb732f068916600012ae0c88047db8d7830487006058104f008b325c89b6e2000730046956e0861930005817074695106413718f048730005811a24c173e6dc372220c870204a8c7060c8b1a09b800274a9810f068c6e08599121c03802e0284 0x18f058732240180278e9f606860d3220a8f7824007302c0bc603cbaa407ca891a00c1b7020c87220438722048812a69e303c9058822e068f181cc09006409d6090f1a1855e0b302068f707c480321c0882a34b9b323013c12dc0010e60f3c305c89b6e20c873e34a841061e0c6e08589) (pickBlockF p 76 0x24408d2a68f24082088b1e303981200c81609021a185469f166041e1ef1c0900643817e5d5203e718001a64091106de07301c38b0254d08223458f181cc890060082141181a187ca9910347bc002438b3004e1b5404b8730fcbaa40549300264400226de07301c5810e34a9a602088f 0x2ea8c082400c810e78ebc603cc9c24688891800c01101c597546441c00600873a79e301e60e12342458c00640883e443893064a8d6021e1a18008810e5028f122859e1010f8634c013c18003812a34d0c4078219367c430223c48078043986078baa40f0a8d0200c1136e04190e1c391)) (pickBlockF p 79 (pickBlockF p 78 0x3a08a8d1e24c8834f180c001cc0b02f181f2a6d5201a00c177020c87024438722048812a3cd1e4808508223448c0e60019027520a78c0f151e24598106868270300193e1c097546441200600873c68798384848c3e2c08022644072ea8c083800c810e7cd0f32709111230080302038b 0x1044689181cc003205e3048105151a3cd093e2cc0804e0f0c00643813e70daa400069978c0088225c3980e2c0872a3cd0822f180d122c6073200c013e08a9a1e24c8878c068c001c5980270ba0026c398042ca9236a901978c04010044b87301c38b025479a1044689182c399006009e) (pickBlockF p 80 0x240880e605b070745193848d0f22300011220398167580a307091a1e4460b0024c880e05c0c3064a8d78c041a6e444800e05c051e3059e1010f827869bb012003812a34f041ea84993e5c402226983c180008730f181e2a34daa4004018225dc08321c38722048812a3cd1e481010a 0x44b87301c38b0234a8f34dd8082230399162401802e0e8a04dc79a18546bc3221809001cc0b027c2027824daa4055b8030348971064381705488f34084371a30398702401902745047808d0f1855b8b302068900643b802c0f983848d0f2230589006440702e0fb07064e12343c88c)))) (pickBlockF p 89 (pickBlockF p 85 (pickBlockF p 83 (pickBlockF p 82 0x5481b8d2254018025c4190ee088d2a3cd37080840c701cc0900640bc087c10f34306b716604151200c87700598236a90373e718007834c812220b87301c38b025479a6ef04111a305873224018027dc026e3c615346443078344800e60581385d501361cc33046d5206e5490160f0c88 0x321c0951a6879910c05890044087301418c3ef0f191010106602400b301c0951a6879910c058c0044087307c2bc0679d8910642020cc0600302c3812a34d0f30c040b1200c91021c2837630c08087c13c609048b3c00c87025468f1880f0404645973e20d3c6ec0480021cc1e3e09e1b) (pickBlockF p 84 0x4060d870a64a0d3828d0c10000a104545841e24c07306c5244010080100868f32250873048a861500a1a103008004106851e844990e64c0d2a000881408789421ca060a10080143c1031220a8d343c60932440010e60a8d343cc30102c6000244c870a0c48a1060f847809824182cf00 0x3020906280ca9a3230501000820d0a2c7890e604151a04007322810f122cc19283c486140908b406cc07306d22014100801008a8f32250870a18c0d3828a1a182000104550841e24c87320400a100909c1a2d018361cc94245451a103008042082841a2c789301cc8100284024254592)) (pickBlockF p 87 (pickBlockF p 86 0x42301096e1c60906084010028c822a4901b161cc080a7030a1a68c8c0200115082c7890e60305369100a0804007320868f10245982a4830a0e68c8c0200105083478b1220c06369052002002073208a881e245980a7068614f439a3230080045420f1624418100400a3208e0d402cd87 0x18544b71001c0100101032a246086e20c97360400206304b71a2c398700db881834b8902003b87034a8902004036e1dc077025b881834181001dc0770de0022e341a12a2408010dc3b842050a100ddc0d180418812843804285bb81a54089101d08004302036e350890ee00800a1018d) (pickBlockF p 88 0x1060609061c6810020ab86ee04951034481001dc370e1ca8d12040086ee03b980ddbb242046051a040080e24ab770e06956425e086e1d08002dc0b81a540890685b871001c151af04b764843880004ab72adc1b81a140894220a876e0010c080ca8910dc20278dc6212a24401083818b 0x1034637182023702004872a09c071009c3718242050e340801031c1504dc2846e3041b0200a82121dc37700469518383884200637700449518207210e001890809b954230385700401506090841825b8732040030e09b97363458830e028100101031a304886e64001061c1372e54d8b))) (pickBlockF p 93 (pickBlockF p 91 (pickBlockF p 90 0x6e060b1261b871a55c0002081b72e6c5980e4813872603842e0401910dcdb83009c98321db8100202382e6c5b86e640850884c072e6c40004ddc1b4264b870a1060100241823685b992ee0384700dcb712545873020c9736040020625b8c2a2c3986f00715066d0871a301010021bb8 0x60890e84c982c40a1534305811a207a1121c0410e0009842944990e004990084c16205058802347a1121c0030a60c8c020050808090961e344873430a082a1808014110851a08783121c13c6e31c0942644010a10080040dc0c12644371a08603125cdb702005a4301c2050201082) (pickBlockF p 92 0x34310140828d9c100400f060868b121cc182c3d49532691094004021103461b281cc1928544193050b190414c1c10845810034a0f121c4180e502192c08a98386828100845881e30a0d121cc980ad41852850c1944a45991a8038036611296a64420020018f0a8469b12503800261099 0x2a3d080122008003044800261599000458f1200381326878c126108e4834d0c16400872a3c4090060c8318040070c282022a3c4883c11e871ac10b71e55e091004324261038d06d8737163ca891000a0534312071a040066e28115063c484105031b2e284192404002083c48d161cc19)) (pickBlockF p 95 (pickBlockF p 94 0x1890d89101c78948641826a603a0020058f0890a893620c981e2520f70252243064c192434d1e0200395183c4094890c8002620800220c9e30906a634c861e421ca8f00204810004c093304001023c4870064019006108e2290590021ca8f1220019022cf1882652010020c244cc8f07 0x308480e482c88702347891000298320c601001c30a080878d1220a1a1890395020033714082051e0c6891064d0c12105241a0c080041dba02a2c41b31007101664a921e244004299924325490f1204418321c90100787951221218326d024326120f1220c82086018d3480581001ca8f) (pickBlockF p 96 0x10010a25290c9c1a3c4811061129327039e020078d1221224320009882645813c61226847838d1e8400910040015660c800304480022c789001c099308480e2290a9a182c08d0e3c4090064f18820402b48040184854d261908f210e3478010240c10004c0932000811e243803200c80 0x1804003102821504847890e14d0c282068602005212a08783082439934312090828a8302001076e8068b106cc1844a4a9938680803c1c68f18244243065207326120632082980e3d00b02006a4126c40748647820a54c033425001002c38d1890d8832603a44860cc044a45993834789))))) (pickBlockF p 113 (pickBlockF p 105 (pickBlockF p 101 (pickBlockF p 99 (pickBlockF p 98 0xe50c0806d410c126020c04642b5303491a0828080422c40c0650a8f041c49930142036ad4a0d080ca183260519100c7a070090810010a9b1250380026109982240190084c102834d0c1639b0110547a1121c00003040013085289326509a1e30498205058e6c200951e250870018c19 0x603dc2178344990218d0c3090a810051c0a04107831a144992818e171420c9b02001042a3c48b0e60ca0343020a3648401000c10f2a2c48730407361664aa07100d8700612031e105191a684a070080801054621361ca183248a19305040d34246191460412068458100101142a3c487) (pickBlockF p 100 0x42008871cd9215343089d70046981e2cc8900200871b0cc083204c87563c48100206a42a10d0c78c0f21706059f1a3c019120408086000a41064380023c49800044110e39b242275c18023478b12640080e0c605700401828105021e3449908608c02a0db0e163dc0d12640144810c15 0x32085086e60b2878c042138347b77a240992c747361090e0d1edc58932002072ca0a883869b821404011303068f12652071091ba4481c41848504036a2839840e0121020078d481449b321c00110646c31e24080101d23c6084c38163479f0024c8100052080f0cc80023c4a13000088)) (pickBlockF p 103 (pickBlockF p 102 0x102c3c30004c074a2c080106031f6065095783c00b12600880e50601000cc8a085410b1e24c1a18643051a50080142c1151e0c2093020d0c121121514600800609c201a84c9b0e5040f145438334242a07008080426068c486cc880e903a4103c4990e594021420e186e440801a3c4a4 0x481c18f082840d34804b704040192a3059b30183880428c370c1c308101050732481a116040020c54789301c1b514644206e08080163c2151218d980e203036a602060e20c0610105072434d03422c080325478c04184980e2c001110cc0110045870c7c69a18c10992a3de091600c01) (pickBlockF p 104 0x310c080162039f0c84c8d1e0048b3004401161e181301c58100203153e686213234789002cc010614407180400a32111021e2c68930686190c54a01002820b0a0878d0624c1c145ca1b02001080884a8f1624c0734806080828c9b2404021060878b2a24c073ef180842550377a04d98 0x423c5891a6039a40304041464d9c02010831e2c10d12603a210082950e70d0100845991a3c60612604070c60386101cb2810647a0160400d1218d982c2108d40f409b301c7a82a8841a2c25001006468c166cc060e20d980c183883019108041439c3284581003430f12603a51600088))) (pickBlockF p 109 (pickBlockF p 107 (pickBlockF p 106 0x284c0010840110e388241a686110260a8f1624c8010043c32a615810eac080105520d0a7cd3c187908b303ca890064081010c00148203800200c01104438e2090898025478b12640080e0c6010060a0a0808a8f12642863430c241a040147028115063c209326cb8328485010020202 0x24440802a3c499481c4240e9040828087870634d0440250810060a8c486ccbc3c21095243de8902647101090a921e2c499001c2881a48d010044c0f1854499481c424481c4184820a020e607844084080485449b321c001110ca8100203a43ef0c213c2ca8f0024c81000522b0f0c001) (pickBlockF p 108 0x2001036e8059b301ce2106602010064417248039b388039b3048e1042601810020b99088039b24110ab0200805085c5a53004c88401c01b300c3151a304b8020041414090a0321cda20c6878c302028402004b814081a04250c9b0e20d0c12105241a60080040dc202a84c9b0e1cc08 0x423c598129039a18644240a100801484a06042c7833024392382cc8308040072e210183670f8b0610c81001cb882480c1b16ac29c00045a13e14217321c4004060d81320ca8d2830481001838a042d008306da963430c871e1420100504b71408320160c41b3034a9a18204a40a5820a)) (pickBlockF p 111 (pickBlockF p 110 0x12202962018c076c0c70b1edc4991000b04286039f60847b77824c880258d0c301c2840201b86140878332504881a64e0f12a90122e2c0803690c071e2869a1880595246c4830404018481ca8f5480e09246c080165d2180e3c515343100b1a6c49c06080803090399105468c1404002 0x406039f1e8459912004011e2490456040440004da000603811c44284366900c2004799301c5891000c1e7c3c487031042b10702810084205346d30c4108f1f322cc071e00488023c4c424595810001f0136803980200705086d0101e44c010e2c49910001951a30080301c3141408799) (pickBlockF p 112 0x22010a34250872818284060400a34241052461107381079b40a080100644882c48e1650154073430b1c2848d0236305203e04019301c18f08204850a48a033868d8f18800802064c07082441624702050e686040c714140648c071e08d8a407c0803214b0910ac29c00062050898dc2 0x234d21121c00530646370200508080941a423448728e078c105418a02002844234d3704243981a7010f1821b840004a9a42e04990e64915043c40518dc0804211c0d16684980e14c8d38287821821b800285c151610d09301cc122a141401e2020c6e0400d34844b8321cc981a55b80)))) (pickBlockF p 121 (pickBlockF p 117 (pickBlockF p 115 (pickBlockF p 114 0x30e0cb73070405422c0805009c1a1a2438770642b72a60e0f0404021162140d3431c090e64c3770e0c0d12660296ee140b3235007005cc0252dd419108008034846892e1dc00026109900060872a3509930ddc151e3058e023441a1284380821c001329cc214a1c0190084c37702c708 0x16dc4173060c8c020038a0808d151221b9e0411e871ac1e213455b89100422406d838d1c685951221b80709028f181c68314040020868a8910ddc17046c41924100806e6848d161cc191e31004065ce080200d3704345890e60c1a04dca991e254a0020108850346170ee0c197091c19) (pickBlockF p 116 0x608002653984294ca1343cc37702c7080258a9a422438030646370200508080909a2c544870a501b81e3040d14040213455b8404243991e30224120ca8202003a01a2db882e60c191804007141011a1a2443770152031e303951404002086868910dcc8f18104834834101001d015 0x306823732347a212800801058a8c425c3b83065c247064c38183ccb73020904422c0802c09c1a2a2438770606190611b981a4878100845882c546027068487326013804e0c191254c2208dcc882c690210200a892ee038002610998200c951a010986ee068f182c7012c20a9a4224380)) (pickBlockF p 119 (pickBlockF p 118 0xe3c61910905050804021702cd3704604871a5478c12902a8085818a04040206e2cb980e60a8d182408004284374281c192e1d4a2066878c3020284042808012810b7325dc0738e0d88325c2020200d3712545873064620080c79724200806e6810b2a2439880ddc0b32551202c5c380 0x2a34d0f320400614245873050205040c0800c25aa1141ca8d18040180e0853834644886e7d4042c098180ef1c213425b991005416063c6180e1420a020013834644886e54d2a40704922e0400b3661207341418f1881b951634b8938040024860399105468c04280807091ba1342cc09) (pickBlockF p 120 0x381028f50a4a35501011c2421b8a42040291e0c289321c90442ac08088661050868610260479810245a1321c0440e494a156643810108284204c401122c7a1321c0352a34c0302004140429b8f4224c870aa48110460d361624799801c0291030c043415a940200524043d0890664388 0x38151180e10e1b04a908b02002993424412081cc352a343191004014148411a1624c071030c831e1820528040216a2859a126010728d4e02344850c06040213015408121078732707920a3d4820a48e0808dc52120040091e643a90651a852408d1c6e286010084818101048f0e65492))) (pickBlockF p 125 (pickBlockF p 123 (pickBlockF p 122 0x5404021166428824107890e60e0f24242981e0c48404149211604003383c4840e60292040cbaa020108b3220e0f12103982470205303c482380d08b02002921e10487300ca8d32284010009c37423c589301c40c32683040a500804229a8b043c483301c292020108b047049a0860392 0xe642926a50e0f0430080424021834204a90e6491c0815aa80870a121084080521411a126439208855810110705083c6100284c1a12205990e0220724a50ab020038e0a10801108449a16643806a546980200414149011a4224c8706a440c30107856a50080149109a1208c873808197) (pickBlockF p 124 0x7a600b6789c0a11ef48991820f16081cf8a12847bd18f0419022908c10042902c1c9891490d0c1c2c419010920a1c0058f184cc880a4038a129070f184c588320030b143040028d4205040c0800c3040a0a481083811090020049a321d49238154b55070a121e310810014c1a0424404 0x300622b167029810040040a9839f1e3001816200951a64181001838a049078b18604146a58c9a0e242840c04003480878b18284182a34080301c5021e30c88481048a04a840f329108752581b530683850824080140878c322121f0858389147909a78f46083204f840e284a1783c608)) (pickBlockF p 127 (pickBlockF p 126 0x4859483301c2051e240801408d0c3221205247121a06245810010c8718587883048e040a88d0f4410e120e901033e2c0800a5878c3020292061ce04480400b1e30c082c48e0f2c5879a0a58e3524681093e2c0804464187083040f30145ab0a7000188604050898d093e6438c1e0040b 0x566000188982843e1c789002cc080310c2b1670281001029a4c30f990e247801620c012a34c83020030714e010f1624c082c1c61934102860201a8a069010b1e244182a34d0f32040070c284881660a040a08181001848a6a206951e68c80021c30a18205982a34080301c5023430c88) (pickBlockF p 128 0x40c0800c310871454681006038a04684991090b296a1c6180a10781002811a1264424447010a34486030200f8b323c3840a20c09384850918242960a48503381c58100107892c604052468e0c060400b32107872c244182471a840a304a20808e0a241c19f16040161e144981014e0b (pickBlockF p 129 0x20108630505871a5479a123000116603840a0818a6a040063284394105469a1e640800c2860b0e60292040cba0020108b323c40c3810398247022232202940c70103422c080241060f0a603951a18c831004014140908f1630c076a64d0812142062804021042c78c0628c0728d4205 0x2884c8802102820629a8100643082824205040c080143120b301c205040c535)))))))))) 5
def routeMeta : Nat → Nat := (pagedUnpackF 30 7 (fun p => (pickBlockF p 7 (pickBlockF p 3 (pickBlockF p 1 0x5b75073000000005a3c434c0000000591dc30d56781c4525ca6913af19d44e5c610c00000004e4480692d151844b3c00452cd081147f4669111d51c400000000000000043d821ac000000043d04044000000043902108ffc39d439908cd0be00d0c29204cd07f434ac19512d103e864dc09612c900006cb45300cc91274bc9c4420ab70ea864c435612a90be41aec2f5440ac00000002f3c0068bc9181a0000000000000002ed080ec9ec13941be017b06f02022000000006ee08111bb020440000000000000006da283314180eb02223dcc0880204400000000878004420c50330000000000000000770219000013bc36c81710db0001100000000dae081136984088000000000000000d9e00222f89adf08f605dc20e985f083200220000000083018112060010c000000000000000806383319388dd03a25d5c0de041cc2a419ac0a54c0ac00000000a1820ac252086c000000000000000087861b021c2811070082f00004b84819076d204000637de2a651f3310bb755daef1d4f002200000001d4d181174ec00cc000000000000001d3308226dfc8db18c3457c6265a1cd7bd49bc00000001790107b5ab1e73163c30e4553287913b83b2c4860ad10f78254432d0f630a040d641dc0b4b059c13ac0bc1557015ca32c0000caf00000000 (pickBlockF p 2 0x22c411d486d00891ff82b7c00000001f9018d400000001e9809f47621e891b9c1bdc6cd0c351a4011ec6720c3d18a822445b71ee71448252c4d00085122c0a2c41502ed0f38523c38304970c200bdc2f000310ad409dc29d043109641a241ea1edf0504554c1021e7f02f8322404606f100001a345f7948f15ba244c552a439143a1a244ef803f1282327c42a88ed0e06554c00000000dbe00c300000000cba6a0c2eeaa810a022b740000000099210e40000000088e8a0c1dd928d05aa439c1570a34c000000013b003903e8020c0e52638c00000000c7003d020c9a2404802770018a2140000010c000000063d0206580c19d4602820457fe00325c18e7d16ee08435b9820895fa31dc000000000000000000000015ea0042540867513466b7c42f87450fb602143ab86850cea838c2fa9c810ae61a0c25290cf08fc58d3202047b079810e41ad04730500236c0a01941000000000000000022010c4045028700000a2c6281cd3000000005ea007d169c121c53824df149220d34e89a79133ab8d448f867f106e03a43789d470000000035c80390000000031d927f0b722a0c26d86df0000000022c828307aa22141868ac9058e091c1198c95000000000f8804303527924091848700ae3b340000000006010d30000000000000c4 0x20860a0c7e2827f1dba0ba47338e771bce22046808ce71776551c00000000000000059e927f15762a0c4f686cf000000004b3808711d669f440daed10faa111c3a6848900000000387923f0dae28e432396910af61b342aa0434c9ac29fc2591230c8643a041a81ae3041c050c070072f00003b8453a5f371295acac4106b2b0ec91af431643390b0532ac2bc040ec00000002ba80068adb282b0000000000000002b3020ac90c7b8419903550662001100000000660081119604088000000000000000640084312322db01e8454c079820440000000079000441cc184300000000000000006d0210c000836c393275f0e4a001100000000e48081138d840cc000000000000000e2e002231ea2db09ce255c271800880000000271060449c2181100000000000000026e800887fe6b7c1518f5d053e00220000000052f082b146820ec0000000000000004e2207411e923502ae4b9c002835300000000002000440002822b2d0010ecac2022afb0280ea141bb4a80820cc0000000a80060469fe1811000000000000000a7f00046848236c95d056b23e44324844096b1e5065846eb1d5318fcb5645c900ed148c65344b72ad9118c7aa43ef10e90d08056c2cd2aeb08c494e41c422db04941cfc0b204e70048a5040000000000088c3)) (pickBlockF p 5 (pickBlockF p 4 0x43a820880000000000000010e80811439820450e408114330210cf10437c31f094b0b2052bc26b06bb09824873227ae73089c00110000000089a0811222040cc00000000000000087000431a70aeb03bc5dc40bf046102f40022000000002dc58430b10010c00000000000000028c3074080124700000c046ae1367000000006a5042499c8199c66004250000000065e0008800000000000000000000006580a10d942405361c1c8cd6840bdc5a08004400000005a00204566e1033000000000000000597000cd4a88b6c4752d6b1038133c3b30eb70cfc73a429c134708a4339c184094b045c836c0741547000093a494b214900000000000000024282a0c8cc2c7d215813b400000000000000081604811f487a2475e16e91c8841e46e2068119ccb37c5d21b43164812045560a79139cb37c4a602831194220c3f002eb0eb4a21c3691c890be44b842600f3308743a1c1da168705807bd411c2c890334027c04a170700002a548e9269121bc13d47cb25490000000000000001e2c120474f12791b74a39400000000000000069a2087196052145e50ae7167c5234559028d13a4b3844470745102041fc3c70a830d5cab843190e7d0b7859dc26f0cdf08d451d41f72a7d06186b8c0ed0f3300000000000000002b4ba04068008b00004344 0x57c883514c61a5c4c288df10261dcc0000000000000003eb863d0fa4182a3980ca30d600a042dc16f90000000000000000af820f42bb820a89ba626c21f8a9f068243fc1848a3904d6027c000000000000000133820884c8001a10d0a4b037449840891ca90068b37c0180408801200d3000060cc00000002eec4410a876a6c29f4c0a89e9912c275200ec000000024b1a5507f85a6c1fd800447f0181a1d91a47075c00221d10210c73238330000000071e08521a0884f05c20a0314a864d043671ec0000000042c002a0dc025f035808430b1104b02a01863083044b00c00a9c0080c51000000000008614c0003811000000000000000160ca0ec47b521400000000000000011d4406800000000000000000000000fa404703df082a0e8e81f000000000e74406838508430a4627b01f9b9340760616c1b7385b02ad68700000000000000000a5301a0000000000000000288206400a013400000000000000000000000000002a375c0068dad787300000000000000000000000da7101a360021ac00000003536a22cc2512542904ef3077d258c17550d50351b50c06b4cd301252914007408500000000000000000000000006c0044015081a000000000000000004c004401108110000000000f081100304064002082a000020440000000) (pickBlockF p 6 0xc9406d000000000c4060ec0000000000000002f5004b0bcc204423309840000000000000000878a0ec2160022000000001fb104b07e420441f7101104dd46100000000048840ec00000000000000000000000405816c0fb001a00cda65000000000000000000000000078e0ec01b081900000000000084b0000000184608110000000184400115e00c6315e4933c4dd133910d0554c3f408810000000000000000f6828d439714870ca8436c2e704870000000000000000b34b8d42930475087493b41d8008b000000001be2c3500000000180047d0444237c0d00c8300000000000000002d810d40752e8300002bac61b18e717fc90e45bb0689167448f4000000000000000581063914e80a3c5160c4900000000000000013f000d44b82689125c190c000000000000000479063d10b84a5c3cd14c30eec70c337f10790d9c70c432314890c2c70c42cb04810acc70c4271068508108b6c167133b046442740aa1adf000015547c186f91c52256c6c69c9d19fe0a3c5f9830d16a61a8455594a913220c6c4b0803111aa2a3444c883d10022a6438888f10b560d9c2d38208800000002d2c006400000002b4d03d09ab725422bc27f06a774141a7c208800000001a7000640000000189103d04f8925c0e520b301682c5c040083500002204 0x862113920840a0c7b124e11db8121c6f61ef11944152c000000000000000615287916b40344000000000000000571287913ec43b445b1141000000000000000107409f43b302d50000000000000000dc0021c3011edf0b0831fc0000000000000002a8183509780a541f806cd057874d40af015f00002d7caa71ce727f47d5499a0ec7251832a48e018cd21b4639c7cd19411d682b9c6be1339192c639c5ac0b3f14e80b9449b113f0fd0153c3b920770df8b1dc30c0ae50b3811f40000000000000002b0003d09c801f42020ae107009a140000000069818d4000000005a069f40fe16d502fc21fc07d0485000043ec66b043918acb2046110635173c72145b30e3915c49a14555043914480a1c4a62cd9102804e435e01590c8439ec00000000c2470c400000000b2c39f425b00e1087829ec0000000080810e400000000714a1ec15904d904601a0c0000000040070c400000000318a9d405722df0060a1fc0000000000070c400000000baa21f427486ed0000000025a8a3500000000240ae35080649fc000000007a680c40000000074610c419580790000000017984390000000015d8239045e1234000000003ee20e400000000386b8d40a4827b01d25984074080441ce08110418665001211ec000000000101011000000000002042))) (pickBlockF p 10 (pickBlockF p 8 0xbcd83552d72038caa5896f28e2036c9e88aa126125324917a0db21ba154c7faa4e91d2245946d794e318b25d5c5b296f51426954c45e9157106202343cc98990d46b3dc3108a830000000030e80088b0ab2642438aff08c090d31f3267b000000001f102088688327c1200305033812940822c9900003c1473a088b1be4120c6b5268919b46a445f806eb153c654c4a1035d119019ec00000001188002246140065071322c3a658ed0d8da21c3614008800000003154a990a653be4285c034c8fb0a3c000000008f300221f4c49105b3044411eea9d0000000011cc008847000190d6028d0154340c03d0031000039ec72504311ba071ec6d02e311a08027466a043118989a245b916db14444544462015f10880a0400000001080282241f46064f511a5c35844f90c450a3c00000000c3d00222c7609108f13c5c228c634c79f1a0c1e5c00880000000199ce9904573c240c9ec99000000000c7c008831c081907d2295000013ec7bd10df1e8400e47540c9b1cc4291c00000000000000070f0e451afc8a8469d144500000000000000019ec091462802a71804093c00000000000000000000001778291c5900e9d14982b544d80c9d1244323c44802930ffc1a4c38906ed0b909d2c246093d07907b14144194103bcbaac09a02ab00002cd4 (pickBlockF p 9 0x553460ec0000000550c00a946f41ac51b04065445306b51080065434183a4cb0485118c23443bd074d0e0011ec31914cf0b646a0426e02d708044b6c1dd0649076f00291b5ca4d06571104166847ec3de4b7c0b59885010e239404180088082290c0000000007a08220008a3d0000000000000000000081100000000c66381a2f58449000000000000000000000002cd8c51000000002b282370000000000000000a46210c254827b07a6935c178a4e3045e330c0a484e7021a88f400000000218101106e043100000000050043d000000000000000013c082100000000138082104b060c8078b96c0000000000090f40000000088208110000000000000000000000081628dc000000007aa58dc000000007a8101100000000000000000000000000000000000000720291419f806cc58a11ec1278677030613340519ee1000000000308243000000000000000000000000168a35005800110001c2d0000000000000000000000090a000e400000009098604639a691c0000000000000000000000239600218c79a3d00000000000000000000000000000022a230fc870887120162b5c7f40a469e0c038c6d60f5b1994038c5bc1153151843b449a1f5910a4038c3722d6f0c24434c2ac04bb08ec838c18d215d04742b8407303550000139c 0x376000e8cfc29bc33d88068cdb284b00000000cc0284b2f30e7b0a18836c1eb053704f0057c10c1e61042e00110000000042b001910942068369497c0d9820642b67164000000002b400110000000000000000aac41242a5281a091443101e510c403e647700000000039040ec00000000330410c000019c2ea0c0ccb9e082a2e702044b7e18530000000000000002de80084a9609cc2a2880c8a84181a29bce0ec99731b40000000097f10430000000097d001100000000962204b00000000000000000000000958182a2230e67070433141260b3701bc2dbc057003100fc70c400610730016001100000000000405a16dda0ec4f7098413b420a841d71a4000000004151022000000000000000100c21283fd001a0ca5e6b0314283b0c2820a82fe10320898e6d020e28430000000020c181107c4412c0000000000000000000000079c40a811b119c040da10c0000000000000000e8184b00718670012002a000000cc000000043540044000000042dca14c00000000000000109f18433f3d4690e3b032c324c6d50aeb1354214df4d0697537c0f7cd5d032f01640cb4004400000000000000031e102b0968c63025810110954206419d21740000000019b001100000000000000000000000183086205f4a06811d10c400550850000203b)) (pickBlockF p 12 (pickBlockF p 11 0xed4183a3b380068ecb0019381cc630df2083b37a820880000000378020a8cf809d433a840e8000000000000000cd218432ff9e6b0a6a5b2c1ea836105e203940cf995302ce80e407c806f01f00011000000001d5084b073c00680ff91a4005de75000000000054c044000000000000000000283b37f02068df9181934c40650d1c083b346460640000000342c40e8c2771cc307400a8c13002a00000000bf2485b2bb8e83093a836c1ac814503ee258c0ce825b033808110000000000000000c8c40ec23f09cc086da18c1a3b8f404ac83d0017122c000000000152011000000000000000001861e4000001a1cc4006464d39cc190480c862c203b00000000000000018a00084548a1c400000000533103b14c0006452e08111440014c4f80043102067903fe002a0ff000443fa00110fe000443cc305c0b50e7d02ce001a000000002b3104b000000002b100110000000000000000a40216c2841832069067100002b4c33604d50b3013542330d33071c7b64117096103ec10e40c90e65032218110000000031d00290c09212c22aa9b4089c00640000000087ca088000000000000000210002b04f006b0000000004d80068130001a0000000000000000000000000000000449014c10c081a006147b0003203b000000640000000 0x5e5247f15e4b3644d80743109c0d8c37f09510b5c7544220056f06d03b6416408a104b019c412a0408848438630f00263031011640000000030e0811000000002f6004308b8665000000000864a0ec00000000536e670000000004c8012c000000004c06044112185300cac7100024083000060440000000801c610df2321cc7c74206800000007c2020ec00000007c08406800000007b78618de0611b471a94cf1ac21354649a4cf16aa8cfc5638a8f13d613744b58881111e23743d288eb0ccaa5042f782770ae201fc2b28210c9de21dc20f86d105ba050c0c89f4d022a41f4080041cc10449fc03b0010c000b9dc29bacd3080e0cc41508167046a01b411a02044000000000000000462081a0eb8a5b033e00e40b5863501f271cc000000001f01811000000000000000000000001ea001a079c006412b197c047c80c81170022000000000000000044c008403b39b400000000026103b000000000241811006000c8000104335092670d38082a34d84044d34001100000000d1c50433132a690c46001a00000000c31103b00000000c2f0011000000000000000308420e8c1500322cf546d09a1433c1d04f31055d0bcc0b4554702198174085c204400000000850006420e001a054ac5f00ea20d4000827500000000000080440000000) (pickBlockF p 13 0x58cc404556f418c555c010c000000051dd471147400195158814d356ba0446aa6d70f32bcf439488710e4a08223898418cd3671e431282770000000031202044000000030c0010cb6019a426c10d907284d141920c710000000019184044000000018b9010c54611d40e18ce100d605640018a690000001a9a8800ca5aea9ec9338471000000009330204400000009288a1ce3b201e48e68010e39700198a8c07b22a0001989f0218e168222c7ec1cdd1e0813546e20b4119c003946190caf16b0236c5430cd312884d0c464267d0fe8b35438906e30bb424e424b1b45077c8b64141053d033c139401c0167000010e44078869101c1811000000010170829402060acf2801c43c940064f230011396d46500000000396460440000000000000000000000395c8044e48382b35b006f0d57203b00000000000000034f0212cc58b1cc31488068c3d083b00000000c28003b2cf04770988136c1b90153043cbd540a220db00009d1445687710f9e8b7c37d9ad50c4e135426ba95107ee7b84150a5570486597c1210004400000001204206447b081a0e6d271039808190b60461000000000b5800440000000000000002cd00490af800ac24e50e4054907f013d203b04cc40a80000000047860ec03259dc00bc406400e085b00000000000183a 0x12a611ab45582a90eda34fc35e94b10c0242f42aca8a909027b64210a6610000000021002044000000020a1010c73829e416302d703102cfc06d10af0000236c5584941149101a45224208947520524e54e7112bd29b4000000012bb08110000000000000004abc40c91d301bc46e2012c00000004361c7110d6081142f8810cfde11c439188cd0bd204ec28896d908ea82741cc9add0576b37c0b7814d020e71a4083020441f42843047126d0008022c00000000000002200000001ca938826f05e751ba938436e842089ac189c400000001aa0105b670087118142b5c561074913b02bac4890ac70f60bd8c36e06d50c1013542c62c7d0954238c2312860c71c2b54189227d0470836c0f39a6cc2827a9c066807501980011064800c40c201a4000986100000000000020440000000))))))

def routeDeck (p : Nat) : Nat := (pickBlockF p 27 (pickBlockF p 13 (pickBlockF p 6 (pickBlockF p 3 (pickBlockF p 1 0xb05527afea34490a5f60729cd678a256cd05a97d95d05c9829f800c3ad05290b050ca05b12e24ec038b5ff6c3b701dfa4e9483d3da04b9a39634de794af01a49cb5cae175077dd2fdcec2da04b3208712ef07906083987610e0000a5829542d1960ab6f64b8c00538ab49ed1557520d081971cfc991700dad5a2b3ea3cf16d484777e54ee021fe26fa0ff7ac9c81f91d5e0f8cb366b34304518506ff62b6de29203bbbe0f62a2934af619780bf1f2977d0b5aac6f84c307d84a41086837b133ac621758785017f8abfc849d130c87aef20306e17546831c578f29b82c28c3417c25da017066ce11ffbfd1e99e73705e14116ba19af2a684005a5215d9507df393d27259661393f4f3002c33cb2b41bcf7b48bbea4487b158da416e8ff8369bb58d9f34cb4194a25cc41c15970487384e0b1d83d28eaefa304de7756f0f8533788f93414084720701986b879116f802814758aa29839fb3a2d530aa533b8dacf3868a2016f32395c0c73a99dcf23f85c18e7869af07a01aeea7100442c28f309ffb2cadac00213503f0f97a55a30069560b6200e4cd5ccfc14cc340f088933d63b26a4d8b25d9ca30558c9f461059a90fdbc1ccc5d0081d8f5490e350df0b2efc3d17dbc942e8a3c5f2731a0bb568397ab609823c0948a9cc60109952c7c28d76d1a0890012308c54831a4878ec494bf00c01e30fca06306e4321d3e30fe1c6112503023e241bcc3ec33d3f2dc1cac23211d1dffaef3200ecefd2c0cfdf13c8ce3e35c6380ba4055fe0906aa4804d65fe2347a544bab3b55afee5ca738dfe1220c2f01239c804a16abb88e40d8c360116fc241844be8e21a329027bb2049f6d7602765c4fe35731eee3fe6fae637bd3550c16c632d0f1088404a302077cb61545411435b034b017741501006418b9943040256eb40561d852456040600d60bf73b5631658773fda00341185414253d581306262f6ed70ee0fea105ae05b7d77fe405104cb1f555545201c35a92a514c0407bb0508598de246a33e8f148a9930a2818970e51f06cdbea7e988082b1f8d7342601276c60585f0f00891016d7000b0030260fde281116007550c439ee5fc3708117a08009b0129c5617caef0005533a23db0c534b83b5c8a59dcce9d8a135d11db7c1aac78c9259d0e0c98b000a04c58e2834047a8ff78192cb0100ed1801cc601818a65e6078d2b3a940661a69403a0adb00e3acb1ae1e516766aa1696fe6501d89ab90bacab1012f0bb4a1e4f409c4dd52947cb47c01302cb4391c46fd04009235ef0c9b006d93409af08c104457f54bf234480fbf507080fc8df02eb50b8c4c00307abda0ca1a9bd3ed55d94fa039ea025603edf204dca8866ed48b1f70f88409d5561ea78568026b2014c9b52330058e0e599f0709bcf80b57ce975d38406ba103da1321abb3d48cfda081b007a6227fff3f0f2620506305029a2bc75aa141227e01a7cc433e8350b978fc37d3edbc3db99b99fde85c84903a06f4945ba6ff8af7e6a7bf17ab108cd05e7da40638c87ff05c90a4a28b62f460ce08e540b010010aca814c1fd20ad022e5faacf8a61ab048a484200 (pickBlockF p 2 0x3a1bacf32905f7f2b6e2b7b266a130867c157950124f358d069e5a709d46a9252bf5fe0002972a47d8404c6c308308588277f9f31bd8c451e214113c7e24e022be3c04acf0218dd95994bbfe6bc72ff914d2635a1673886c0c1800002b8b5049ec41e6789055ec2f9f5d3415eebfb005b72b47d409cc7b0815a1ec347c0533013c266af21fbe4a519174940a0118947ff06a8c2f81f431e67fce7915dca46e3fcd1a05e3804543cf0079ca4f03de9cc091013c47675a6962c744343a31c8ddd9a21fb5d00ed6f94b19f5438a43e8525242995e9c28b438620289f3743d9251b811256c3cbb5f4e165b17e4aa0901a9b2908bc80301c954001cc8dc91510dd815811d458f1058dcdf4d90445bd6310a816393241e6d59dcd74802e74c313eee3ace0ae30e8dacff81dd2f33e784bf7cca40001ab4ed33612e401b7c3444fdf268da4f1482ab36a7813bc1b3aad128399f316b50414b635c58c849a51b0c78722834c40c9bd9d24b7ebb751fba9cdb9def3ade17f4a36a1c2b7387b8cfbfefc40f6da8d8cd13dece12d14e1a4185030be9b5d9cbbab02d81e728a48c08240007e2659edeff62e464a6f2c8a9398a71689ff925fa861a2c43a0c007700140004fb12b09c01cb44ece560be36a2eb17fc21a648ccdd964bd160f84be95f4dad404449b4f11908a39ae365c2c38f1575458a25d1f03e83b1e98d65b9b19c0a9e46b0c6604ab47c009790b88003f88690af00f24382 0x592768ece0de63e44bd1e11ad52f0202c5cc0ef27f8402e860a8d021c1d31eef65c1420f2d43b731ec402a02222d00906d2e16d0ed5bca0f41b27f71a0a06ec0adbee02081775041a62375524d6187048594e98e176e5faf385264b61eb3a300454a63e357c17e11d65cf180078a419a881bea58b831694d549c45fae8c018ce5de38cdcf224e4a140b29542007437bd5567038280f455aca0e49298cbb6743599080c644240b20741814291878cf00e700dc9e3660f9120eb5ff299a406b989a0ae71fa10523c43d913ec3303e05460c0f79197fe0add94f2a13272c6b5a7b8f0a4f6b29e08bc902f7d10699b9b202125e7352a004a382146db2ab0273b3325d33f2ced29f8f1401881822cff326d6d20e71efd3d5a05e33ed702f93f5f4073a242077777572a02630e27005061110485b46344361769a8f3305441d76623f7b3008184c54327230e13132495308e231c031a010b18eab5fb7a5403b878580553e35d81d5618b6f92f71e8c6d6ff073d5053bf448f505429b7dffab1e93e57a5cb01b87a54bd060a034e2896605908c94a475ef30aea8de8053a08eba438373fd2138abf8208e8d5c659cb0f9cf1e4ce02c281fd06b9c3c5fbf42ecd50b0b4ade563c94785ab320fc4fda081aeff813ec03149355bfd430f4b9671a3af85f69b8709c6335c140b0950000529ab4002f1e1967a90e41dc9b821ca1c8302d1ddf7e871718a01833bf7e85855444844f25f001312ade39d6e6b73e293e594363eaa4352d31dad032cc01b9946e723668b67cb1c0a67ff0a8dde60993b115c0035e1959cb964bc29e202c55f023cb2881abbbe82dac58a9c8386340a577140e1282bba57400da189c2437d68db023b3a517d459d0b0ffc3c317c4e69db6b9c1327f81e9c982f8154a08c651acf3745310c714a7fa85104a8aced2a308220d46637ad863b6a26c68f1a962a28bf47fa96c2ed50653164f1ff84f7d29abe99018640aef614257de3120426410)) (pickBlockF p 4 0x13ab84982bfda794584fc3b7bd3f5df7c099e2141ec2cf7a055f6960c6d4ea8e18c3080869d225d9dd09680201ee0b6432838197bd1c7104a82c186d2045a41d5f0a9ca10996c3b4029b818eeb42081f3d884f93adbdb3ad6d440d9683427b9e1f50b9acfe87617aeea1aa6eb0125f13794cf5b1d8d7ff5fbc1b7a2e29b9f201706bc1b15321261c6ae6bb78452a35153264b0153b058ec3e41b5a2e61866aaf56eea598a53910f72b612f68a067b7be8027dbf6985801cbc0ec41397d662f4e9d3be96274146997ebcaa0ee3743717252d5dd801e090ea8102e158c622a1b866370bf3545c1efeabbb483107050be00ea354d6a306f90b03e5ac0bc5384407493083a2e3aa8e6a9074ba189f74375be24a8a9433e05de621b30251a58954e0b85c06f91b97d9d3cc0ed564efc704a0d307f4f08df6c8393cfac03f10783b636cc7fe50ccac6d9b5fd70ae93a890a395dac7a0f77010550fc393e5010dba4253b3821a4068820956102b0c3e90d0a6b4a8a63c8a8033f6d99149ac3d87260ceeb3eff1948c6a93ef1c6e306057ffb485bda44347c315a03fe3023388af629ba9be9069f2cfb6b0cd1c52d9ea26e9850ae0a86b05b527c01b00b71f4a64a6a19a8ca2e49a18335b05f509039716d806b65b760c244505008a5c4f906a252ed8e38786c5677ff3467f2fd8064eda32688acb00d0eb7874bc02b9702a5bec373a860ed0325be4b3cc76b0d48ceaa03b4f9ff88db8fe2ff00a3438ffe2510d44779fb8fde0da286426f3049459395f0000a16bd70a4c02891de58cecd17fe0ce7042525209c6ab8e89b27e2db6c1f2f813cee576119627ff6807162fbb81b24163691eb54ebfd7eb6e4f63201ab7d218bdca4bd33704645b605f54060000065521138910f9c96fff9db9efacc8f2f251b4b3301b135bad283c96b71f005100a293eb15a5e3b20ff0236f492c1052407866061985c24d4f8779c037277704de49d48594b61b53ba7d942e9d669d253007f334051d3e772b818c03aeb0100504fbc9ec74e360d1d65a69a7ad467994ef1ac0da9d8d6f2f60da41170 (pickBlockF p 5 0x9681eb6d498d4f0fefa9e111a519bbd986214d8a2c9fb6a0089937100368d6d5d7ce0d1ba7efe254d70fbb1fcacc26596fdbda00d1f29a0010d406311510307c709972c1133c19e09c45501e88450665d4171b168061fd4662c83433bc41cee79df3f419b34e599b85b3e13cf07c6fc0967d5910d7e0dce9d2a00cc74a3f0368d2bcc1239777119839bd5080b8572104b9e9182e8f45ee8dd2ee896f192769d2ed6372957ea6b0c80faaeb80d964201059dc648944c5c4957848220903fd816c389111f02eeff3f79fb1e8de7b1b6ebc6bf166bd9ba14b6edb1282724792ec52c05f7f1792c8ddbc362964fb4afd0c40ee8ec037fe4d7592b0c016ca69d71a83bcb3e77237d60719ba695bb1eeb4813a4308bdbb9c3c30db6d3b157dd4d5bbcb3f7041fecbce6e3dd388f7d812feaa63114465481dc8076c0028005a99ac505f8136e1cad8020493727c3eb01d13e9449dfa255dd9555c37d4175d45a00b0a84133721d7edf8315a01f770ccedc98ac1c90c99fa580b2102346d3007d1046a4e6c17a28cc2c831b0f985a8172ed109d92c9837e7e49f37adfc2d04b7f6cfb7ba1c58308a4b0bd0fc036673c23a4d781251fad19015681a14ce11b2bdf8a25c37c5f834100fcd7e579ed66ec6e1b17135c0c978a7aeece7327531a458e3fca747e2024ef202aa80348d4de8d5e291f00163cd110055f61a9d13e4022d0b32e993ff22417181f25385da9246e42c8ed8c0003c5f5cd6a7ecc44ada05290c8fda457cbad2971a2f50a4a315f2e6d22b7904c4004d759e1949241780394d8f0005c79c80b4f6268ff214ba99cc3755804045bafcefdd73037da7c3039a8df51977e55f2acefa2ca2001c903cb4bcbac1a51b8f05700525715b296564a301ec9f8b6a914a96f40b9bb3e5562cdadca483e6de6411f3be65857804377e03e5243ec3a6f031382893eb066c38088b7487415be7ed7b640ebfb3cdee23e22be202e8881356c3e2d26c245ada76494303de566cc8ff1acad7e4c3011b12833f3539cdba69ecf3a5aef5ea11c0dd771321da99f3e7648082e19592cb1b01f4b94e1e105849cefab87777c8de001f56c2d7cdfa2759f8cfac200125c2f32d150e52284f52dd3b3df484954a18c0198aa0166bbfd41fcff92383f074684141169c40f44ece141d3be57319ebf446 0x59db93cef6a0db88f477fdac133870734f921d447d3a28c7266a17017f273d4ecf1a0cf399b5ae814075830ac1ada5bcaf58144c0dfa7cab8a42403ec96b16d05087bd74a8032efe514cc1ac554e9e99c11d555c7c105a41b6f39aec0a4dc75a335a194b217859b1943e75f569390d6a0752df4603cb65aa91486a371d60823b40ccb787707d7ac06284ae80527fbc21bc7eabf4d3d2f57343b2f32e59f41891e4300141614c596d9e7135b722f8832390a66ee885e038379302ceedf29668c45f85f1aa8fbf6ec54ecfd607af00a3c2e36d5bd15fb442e42ccdf916bc7f3817a69030028ccd748f0ee3a982b349a7ee437f8974a4228dc4d025f54d781e79f694ddcd4232094c12644fe1e13debec5f78f1410ce8423f84aa827fe10f4359383081c85f1984803811eb2c510257681279b28a21b1bc180f3023090ae83f63059727229e70ad5d574b0cc01446005233588c3a3ec8cc016b701f62ad0cb2c65e7c434844ce7c823f8eb435559bed405bfddd03980732bfb700381e902151ce3f7c9b4ffee1d8a0426ecd1a5d758006a7f91e520cb424614097f183850194ff0e97311cc3a313d952f34aab70d6bd6f3d46d3576cf70a7626754a6bde81f5cbea17742f6fb62d31aaaef40a1ed813acf7a7195d329cb354795f39705bdca4d69e6f7702d1d731f0b341daa360c2df444f302f00a8140149c0b81345c387f2161a503c1c4fc8a77a6a2e518209a502bf5d3d030fad3f95bddbc3620e1a55d38b5e31e03fcf7554778a010b0e0e820dc8a7a022a773770827727c3260353db12baa192fb4fea2173fff0ed0a76aa8e296e66b7cb4fe1904270604d07575df7f3761eb3f3a7bcd63db25053bc82dc6b87d171a0d112c0b5c271aa0bf1a971bd0dd2173a74d2f078ff244cf08db9c55450e6e0a0f15ece0002e86315c897a8d64708674319ee59be5205a59bb54030b7a1cca5a3fea19ecd6ae8ce7b61ee03bae2ac0a0d8c34a085847bbdd39ede5020500843f8886871e98e566b22363cba437c536da21ae092f0ee605188ad110b1c949edb4c99b76fcc86f4b416d0b7e01878711a30433852810b7649f00fd224b7a5cd653d06ea0cdf63e2da700d570280110))) (pickBlockF p 9 (pickBlockF p 7 0x2c52747654cea7af41f59e8ba4918d748388dfe5990cc046bb252048d1e748d7a9523802868a592fced8cd5421cc92f4d84e90ad8398237fd009b8db1a506b403388d956d242f72e859f0f6cbc0d61fd10291c1eb82214644182031998000c20303118adb1cb302affd58fdd6a3ebefef7f5c4c4a78913ec0f7fd818817ebe220003d1f8e03712363f8ad0485e6d73e24af136d7e01f86103936ea4ca0b4a3434e0405c5fca6207bcfd4011081bb4c974eeb0aef72a277d22facb8373e3141d356a8b002aeee65d1d53a12689b24403d1439c13ca223ac2ad31a2b64883ef292cbf38ff087b338dbe8a3d8cc3aad5c7d27d033839ff73a563832af78923f43d0d071980fc236503b1c18c25c061ddeb5fc7c00fb8ea794a970f84da2f6007a5315248c28eedc394042b8da5ffcf1c3aaee8cbf6eeb946a50286c56050011bc4c48ae964f35f93d5397fdc01cc80e36c188847439a94765c21560d1d3ab7a689e4310120ca51682f01744490cd036a86a2d97fa82024026e55a1f629430429222175c5802e03d468114f1d23caf00e35a1164ad21203ab70bd90e3278b9f643f2be22f42dc4104f43d01a336d26d2ada9efc8ec91100316b08fa8b008bc93c8a09c474733915965b410c219b5809e97a5e553561eef240030f9cc8b36df8d4812b535919fc350c49d47cd8641c03ca8068f023bfabf6ec2c909dfcd1aeaa9264a2daa41005a240b879d57c6202f94725c3eaab88c3456133ccb71a7a103edb81a2a53cd436168008040c24dfb291f424027c75efb6b7dbfac780a97cdf0918da69d4cea5c133761c5b9ccab25dbdbf02c0761362b517bb5d1f90125d3de116dbaa4282acf1a2439202002c2e537a046830020a7c3cd25a2084c680a858021def9b90c965f1548cb03dd04b71e7bbaf71aa0341ad3a47fd711362220c0b2e2a3300dec840b3fc331238c9fd370b91d0220a824e961f22013907c3c00785685473738eb452504aea7a0476da921605e5a5e07fb49c433f7e9cc00403207fd7b5043ab50cb9f022a79004d03e5bbec56838e2e0db3182d650342e56860095d7a8174b55b60741b902a1525d4e094c3ea16d5d2b4c4bd38d81e739c156b04358c239 (pickBlockF p 8 0x24620e33ef915615ae4847bff13cf32185b9d7863f6162bf46e86c31acbc8042e6d0b838f530d40fe19f740d8957a2635462f0b4101476fba650cbf609620886a60da9b790355aae0d14b4b3cc193106d64a0843db0cbf7a4e053b893c1290105d02c75d82296eb00902903ac023a5f080b0434c121d17ee61455b1a0c202f5a00f6bb76007223f9dc003bfb0d1925c48672023308a416356e75d30d1dcd3b9b5a324709ccd6ef411af2866d5aaad1bf5cbd561475482050526b3e77fa1d4365e9cdf05b04c6caaa4b64d0643444e50bc8c03ed7d8e67640f7efc0048a73b8bea922edaab3e2cb10cf8636e0faaebb08e7de07d029e5876d45ac070d3b8eba0000c0cf4013efe7fc2af20c0cc99d0b90fa18c05bf792118a2383201be02c3a8e9663770b1c003f22a6a6c51cf8e0fa6167b0949260241027505021725d70a4711bbe96e7c2a7c0e89963b136aefc2bbf45004f7057354a50810c2bf537df5065b940806b72958402b6e9f0b0ac2277a9ab0f00c31593200200ea202b23c9c78933e8912a7f304f8d60c56f4004de94ca88b47d0bd5ab784f1af0e68d1bb0fa007c7aa9882d78c11dc54c0d57026348c74c8f84858e0580d14686438688746608d575d305fd2f12f403478028d7ca9a851a991628460e2088705d14689b1d408b89e49bec801b53bb4202b3000dfba437bf18dba9408c4e30248122fe66f920bcae24a9c20c280da61aebc0500b00299e97557d0262d2d34c79381a763a33664704f28fe905001bbbe48b0d08f020044023a0d68f175787c881d801099b68e59cc509608552300fc245211161910e056bab195075b448923c8052c66cd14cc88dc2c25a7de382df6004be00de16351ceecbf382ff350f3decc90debeb49db02ea679655846453b4f72f52206b30de0cd1ee332240063a5d12171d5b250f5f11fb3c001aeec66c7310bf55f1680a3c0d74c5a8a1042fb4df449e5e9b091bcd43cd503e9c43002d4b9840ed1afb3ca2e8dfcebc60f09a06e0c7ddf5ccfe4bfef94054105964f00d50ebd3ad22fc82046c005a11102401451c2de3cc42435dba0f40340a73c2f22d4de1657a28221adb464c0b716c3faa1be03650cef04d5a4e13d8149b863a42e033d7fb9d92a47601e357f9bfd9df9e1055892abfad24364bed02ac4b139fbe8d84bfb8af0535b4f11f2b7002b07a537c815b11240b09b96abf05549a38dc83ecfe56890e0a6f9283e0c9338e70261009b40ebbb90a50b0688f25ae90392b9aaed5de2f22bfccf7ffbaceb63de2a5252b055d652c0e3844b2000038e04f3910a3165792d1410d140cabd94346d000e97a08de00c3c7ca57b95a2da2043e013d204f90e067ec409b4838502e2e8d9b60be0208502b6ab8becf2f8c60bec0a4ac06f8b9910fe18ec2402531b9831050f3930a4beedd0bd1906a71ee05786ea08264845827dc8200e90c1e07f154173058504c035a2fcbc294017fdb2fcf66b083a064a4e6cbb34227272833005724ca85a8036416bc0f9893d8a6907d53b5a70fb0f1ec0c6bb967eb4070dac9090adc311fc612fc6b6daf4156005fb022fd7b64e1d80eb510b188ec9244097264fbb0dcd 0x3c6c91c227b0e366dd8840fd9817701ba082204e2fdb79ac85cc8cc0e8c164f0d5350c186c1d133e4e8b0044e0e19100c7f1f4fe0cfcb305dc7d1357b1f90f344fe1ddc58dd2c86050904ae883d04f701d4b062b9b7a60a14e55fbc288030b29e40644a6c4f390d0efd0f08d46e749fd9e1fb990bc44d1b0268024c91a040fd96275bf607a84fe8d149e27fdfbc3c780206b492fda7e560144a20f30a87d1988a49969e05e8248fc7ba00b3d6b90f13600380f9ce81365b975e4c038189cdf685eaff6452da72a6b0a040c7f39fe0546872af99300d17950acaa9b879a09dea480b03032b9c6a8678e3082ef016fa9e8c497029a021ba44f5d5331602d681915c86da320359eb11d44146508650bc336c071ea03f5eaa9bd232a7000e5f53c0e4674c4ab6c207928de3c4f9766b015ff2fd8b11a23140fa70bce523aa7e9c5d268cd2a156dcef7f5bd223744429bf21cea08bdd449eb003d06cce16d9100456ffeb452ed93957ca9acf4cb21a9e0ce199e47fc00400e00077edf96dc71372b010e0d2b31a51ecaa4ffe2ccd689bad99f5d806ba4624b14a43de931e9beea3eeb7a3504e95005921041e310f390956999b35a8c9cfb2c8d084f40e40c22038b8af83511aa854b206e5f27537c0be70005aca370a336fd031bb20221904f10537220e14d82ea9724e3db1f580249b8f2d21a331fde34b98f84a58349a1016bc089901013b2224b33fcaa04dc1938800525ce0ee6996dfcc033fbb1170ba71ca3df0d100fa082cf9d1f28966c881c5a6e57fd425542692a1c64c3585f49132154686cf130085883ec0025297b7a715f481c0150ad016593043df55534dc2ad780c0f42d810df1415c317fc7b76004f8551cb302470e1d0c2440fb046131015907875061015e02015506147b09dd07b5e0153cc281b5e260755012050c309f4856b66e102f5e907de5027049300905108d1e50610a7000d4c4eea0c004a09df708c16189f9fbffedf0992bceac735a1df56d28a6696637656e71734933916b4a97a97ac18610ffca958164c12b0270e06f016e5951c4339d3b4e32bb9c0fc639bb65f478a729a7e313f74d20e10344149ccbb7a6d7c03713af59ef88ecdd2a29934004e6bb688a4cb51c53378bbb73599f0b9b265750f7005630f7d70388706828f08a09a53e0df9c16cb2399ddf3f2c0b33a2a11019e40bd73335d2958290146f1e5b0202a583d5d0bf67bd17ad4bc8108a7f06a533eee5fc58cae97c480f6d66d5b0bde3ddb524471f330cefd3bd3014cfbc6ef2ed2c392189350458204b5bf90eaa82a01906534789900107961f009f004e59298f408eba436d2ab70c8b9f39062cbc60014c41b4a15fd7ccbf66c405f12be0df035519b3b0cb30edf9af2f9efdc758efe7b77bc60c1f95281e0627b14d0509317d0918b0003006b3993a685426710a7092b44f8e021b027da0484bdd4f319473d6633902e438fe05a8b739fb0b2a031e01c3ea3a9043bfdd582f21918b57018c0b826c7300681c68bb2493c7055ae1e4720e5e17e497c9a026e0f1afe26cb16aae5d7acbe4535389d238ac12e42f020915c09599b965deddabe8223bd31b534637b843cfdae6fef3200761f54a680aef89549b4f2481b537c41818f5762f33297596c56cd84f0db720b2be4ad593551c853410a09125350cc7caabd5867c842609c64984060d97f44a9b108a8fe48bb1c114b1b79f453379c1d26590e70ca6b0fb12979a58892ebabced573e7e8acf606c56a700d1ccb72e49bcd0860e0743d66c9526171dab2170a7d22a0c479b01bde902f7a009438bfa013332741d7f010d48c0293ad12b5919671c84d058e9b54cffa5436756dfa030f89e92f45c716a980ae73da0d5a6e4d11768978f4500ca9fddc13141ebbdc171f3a14213ef87f8a11019ec622b2bc0a0dc5c192f3756fd94f3163f47b06fe20cab0a2801e6581fa0d69fdb0cba4cb55d26b200327db7d24c3c124f5e086e2e4fe5b26ab3ce0c06a922464088b8100)) (pickBlockF p 11 (pickBlockF p 10 0xfa1a9885f62ccf25c7e3f37bdc42e1bd1215a000997b89487f90e6901c24dfb10e6fe20472b679bc6694a84053db7b08f6a9616fd00917056d0c976950612d618cff69e480ee685808f05cfea69301eed2d125484f69000a06bf350229c97dc9b57b865a4dddc40a63683ed1a385821b243f2c9e038ba8fa8c0ec1bda6019a28b81dc75cb75989394a90649fcac4ec02434059da8023ced3971c9630192424241e89e363c91f4ddff3a4d4b6c2b38b85cc9bdb8aa456c1cb53826aa657f988519dc455b0cce88e08f2484f751c13717e640d806fbf00480a8e93a28716e9d453c0a087b5daa3941bd640d2d0939577d4249de08b5080c1ce89c19d5dd8fd399828dd75ea011a0f0c1dc280201d80ec0fc2452a41ec402ccf661bd01dbcf47042f83ee67b430744df2742020a62be057b6a861c14422e2e7f8e3ab0ad39eeb59d343dd7cb2e9588a5a3562bda374c49c6f685911814129124450b903c94801fdab4c3684dad00e1897b43742dfc1bec015ad3cc25a437030ac92561414ea03b68f9e4945b089c098d19a008003c51d348098e643483f4505d607468f332f6fc3c6205886f858ccfe0683bcb005edd5b364ba04bb0fa4894152d6839a033933477dbe2e7d45f20280d865361abbba1219e869210890c010e8dab2c81d0475f6c241482569d0b00b2a66817e01b06f440fd76c078701daee9dc69dfcf02bba83c275af8080d5769e9b712cdb099d0e4203fa6583f0eec16eb7f60cdd4ff67fab4fa64 0x10a93de1450fc542265841a20cab790636a2f2d987d44da0112098ba995e6a4e04596165830006f0ddc6a96e6f6eaa052daabfa032a3ce5781ffc41f408226399384028657b9fe19f1089c10200f6933c7254f4706407e279186c364a0518dc42193422baa7ed4672dfa13e3335f95bc8a57e2fc200f53ae3ed15f80ff8e3142a1b4799f0a9e40153d2fa80ca5208b475b01fbf14a07d8a43b68debfd4949cf8006a16d720d28957db60981930ce555ec3294334dc099428623fde5a8f501513ec0cb80ee119e0fecfcd4e23c16cbe069c1abbffdd282e54a1daa528020c44c36c7f819941342156fd4072c5598c54d0c38fe002661a8a5740215579c4746446c40204537eb841b16875d60fd37125679d096246ef61df3d8209b68f581e000389d84609cec3c6d69ac94d06ea7eb3177b268c56453232447dc7a59fb01c043c185622b7d702a9261ad8d4babcca141b73e274e438616082f0199f052600a0c19e8c61a1baf7b315e011b1474d051e3f3ac43698f716fe11e0e470584a75e494fbd6578662381120f8012f8b6c180be0b87869c245d2a1fbe1f2fed8a4632f0824c006351fe6c4bbd8463dc241d84c0f08926711601a1c5e28e2806402c025179084e00bbcee1d000be86a2b8e800bfad0a04607ced079e83b751288e20ce4f918e4dec7b0ed28f0b1eaf9b704061a780889e498a8f70658fdc6f3bf246c40b69073321da5f7c05366b91304d5b34e8b7a47a3906fc1834b1b32ea4d9ab00ae2913bcc093252a068ccaa61bf38281b9f7b4ceb67aa5ee94dfb23b61c39d978a1423ed0c4983519a9b7c25367882564a6d848f62ff06770080b039a60a3b101f900277c9a38e499ad2e10e004d0d137fd24180a30231a01fe07673972270c15a9da648d0516913279bfbb10130c092a302c1320e61f2aab03bbc1f4acb04ed3a121b7123d40ab90707f635d261a0057f5000435358f10a30ece4ed804083a2a641f20c02cd799711b70cd3a1c14a67ca0858704f05caa11157a62579df9d2603594b0c5bfe00978757357f0) (pickBlockF p 12 0xec071141bdf03f805319ed085d3829a2c12fa9ce81c1d501c525d68850301bc30d8d5dd171c5e61b6d387186848b07355f3daebac17417bca73c2e3a62c12ccaa2dffd5c40a1872ddc557f2c249394181659ad6d7310c962aafc5e14354ee7c0c3bb966b543bc4103178fb002ae9c21198044016df81589910083ee52e13e10019a9fca6628dcac7f86b40378977f59423af34b263b401baa8cc2afd21c7562f51f3b1b8fb6554edfc10d587c616ce8be5e3c03f81b643a5251d0cf6cca41961fec013d848f6f4c74854c0b2f50eb96a9038634b4e4b42d71b3a56df42d90e54cdd176753601f8db8207543e41540fc02cf07b9f6ffe87b012d5f9ab2e51cc35997ee90d8e01e3fe3f010402358474f834364acc041883ea7514ff705ec25be06c2cc25cc7bc2879da012c941f9c0741e8c2aaa1d88e7c29001b8b1e1e35f823ec752ee425eeb3c83088038bd390c2d0070cd5b548c5e7820c787b70172aeaec00024ef3f48dfd2b0a841cc0078c5fc695082f340c214ae9165540c7972883ec0788ccfa9cf5caac0b235b91844349b8b0c64b61c4c675ea747840f9f5e912a5172f495171243b80478223eae67edbc009980aaf03ce68f281a72ce3683018435f03fac1b974169f4864639348e7711d7c16f1c768b70b8cfe598974242157255a51082ad624343b5e284b029e5f5825e34a86cec096d0bbc3fc7700ac9147f4a920f3ec6bddc6720280ddfac62e7205a8b2b70c0f3ea1921bee9d6eebe6fd226cb4c8c315b4303a540286eb72a32653f68ec12382e1cb5ffd1303dc3f553641b22e7df8d5cc767608e173f5a56ab1882bdab432e4531176cd178cdbc53b39a6e31c06f9c8e82ae123805da8b5801e7c50a043b845debc1e263b71eac3a310fb4dddfb34d80c952a44b6c056b84a23c6ae92cedea36b5019770545b3034341123441a2567fbab64ad6e361cef4f982d931f5312eee82681b016075b9113443bb5c19d0be00100119f3798fa7683a70037db628315f33406c01e3a070098a7539a75e933317692540da2c072f92aa7ef48c049de40409b4cde0ea4dac2522606d5175eae8b3a2f2b33a6084d516cb261784304e20ee526942bfe2078427b9eb912ddfcb856cc0c8fe723ac1a10660341498511587701bc0fa075f01bcffcd5021f13b581c413bbe2ed0f8efdedabb01268acb484f1dbcfe0dc5fd473f0bf28f66a945f371953a5b28435302cbbd15407a37afa8b5faee1bb836bc831deb5cd14405351dd0c199890b93bae0a650aef0f019bfad22374be7c21153282970b0ecf78b2a99b2d0c0ba0e56b312000b05a1f5567352d079b424a7fb7a07f9452092607c05cd4b601551126c92012bbec05300ada15128b203b7049d7fc60458c9d0cc8764ceedd67ce93fedfb388703b645de9b6eebf6605884a0a2c09787f59e0803f305c0f8ed9761259da1b76952092ce5aa277ca00f7ff93fc4a5c5ded4babbf440ec2f3a887c84b95b54f09b800e73674 0x24918aac5f2ad2925b753ac358c762930f4e90a651f60eef102452f47bbd3d81d114f00fff650096e8f0c5b8b503dda50370a694d8da002db7b4d4e75a80dcf00a75e72cd305fadc1aec0cbd474007d45ae6a830921e19438929e13a3e3089b167dbe2d0e5fca2d47050e7019e272f6e5e569d0b9289ad57f42002be5823e3a0cd746c1607b4ec4732b2b9fc2072f57000d9ede36188a201761d44dd0a6a49bf0c90b91f3b409913a5fcd6da8ac790d1e85aad3e385eae7556d0b7f9648b5a50413d6a73a7d4093510db72db404cf1adb8bae03d6e54bacc63efa0cdecd9255605dd86fd356003b841eda6aecc785561e758df9a390cefaeb4fc929f8b80c19d4388a578de7d46d260a098ffff8e9b4825fe8304dd3c9a286055181bf6994703a9d19ae62ba008000c3d9007084216d7c50c8901167f300d6be15bc971db2ce4af737a25a88f6014701b66cba276575109064c6dfc49d2c7d9766bc6f8004a4290d90838f798208ba6a6c3707b907008f0db2373d2b8e27256afdd0113ff07244bd3428acd0a74a084f2738f4b5fb621adcb7d476512ff32c074eff53bb22ace4e19462800950068e0d57b23feb1bbb1ce14810f934830c10a60edd4e189fa3b08c26e19f4008255006cd9b271ba3f42ecd2005d922146289aaa0767b837b792aeb23d32b06f55aa1c8e04074051816cae12306d31a0c4c7ae105a91bb69e37c6d939619b9dd66f402ba0d0c8fd81db50d6e2451000f97ff7bb081b714758f12813bc5e20f3900bbbd94940ffea928748517d56ca31e596671f9992461aeba73afaa56c9b176a6afc6238d5c5216620303f08aac1cf0ccbec2386689d9f0f46b141f4403f1de032fb78d67fe75382dd490fd7979063f30346773dd90f46edb520be476131be6ec3d2a981872fcf0e79b57c2110c85f13c29804a6e33700f30af04d07989907a52644f5d391744bf4984536ff289b18d7140759c0b7c0a650f01c324d50808e5ad1a59c9a307859d14a1b40b18a1a070cf6567a4e909a10831e737956dbf8db08ad302396580aa020a7ffad3132d0fa271834b909bb82061fea8ab250bbd30ed3133282133065c55d7b8d89f6293b4acbdb310e73b7bca758f028f67c86481f8f711058398e80558f05f0fe503399083ae7c50f15088e93c03ec3d06d3089ffcd615360160fe8903cb0b185f54b77ad071b3cfab178db349400482a15e31140f035724efe7cacea64cecf2de103b9aec4cc6162f1785eb5a0f53ee9c5663600b52bab45325d857e07bd5e8c60177a1b506803c52f0ad0ea8d3e153a71ca6c6a10f7eb07cdc94bbb3790c10b565cce0d6004293c083d6cb39c7375b78f96aaa1acc3bb01298fc8e22b2e0a07b121660fd36f07c1be845fe9387c78b2e974428e9060428d6f8d937ef535733f0481df003b2e2066d36dc5f4e0476dd02d2c6469746ebf0f6128a6d0dbf9697707422fc9918c6ab73bda253706d7b58798b5cb6b41382088ffccbda37b9e13c90114d74e183fc340cf5aeff16809210430d4acb1ff995130a5b76cff05732d3f64a11acb02b7da01e4d661c620840f0ac09b423442907cbe72ab300cbd2650c813b0fcaf9a288ec38593551d40de156800adc47bb5c8b0447dbcae2084002d1c616e79c223265)))) (pickBlockF p 20 (pickBlockF p 16 (pickBlockF p 14 0x78fae141c1b4054a89dd00e9f1fa1ac070f16ac39ab0f79e1e567f08a0823097150e895c36dfa630be76f48f75bf5c0cafde69b2785adaf680360402bf2e64bd07159e3a69f32aee2f0f734517b42fa10007e4d6e29460646fcd3fb1bf65ce3f0d660a6d70c81028adcd5411ac42702a20000a9fdf4d181cf2127b387882977b198dc85c6cab0e63f8b26c08173080e11f09f66388c1123d88322100065edac80c95fee05406ef2fcaed76c81542d6899aac4640f0b064100bd7cb21004c3bc29d7019b4cea0b7c319a0f0200c3b7c1aeb755281f8f8209eea1044286e23e3c10834109b379e001ce5eda8bba77f8a3286c56d80a962bc5fd4568dbb402008332e79c1ea0581688884736a2210ba0bf0c1e522e4fac6ba585639a7fdb4c3b7022b41c71797c849aaf140e7642e5074f4e213b3b1f2b4b2e4a9874af99890754b0ad4f4d0c5b4c9482186d1bc3e8a9650def02cf24ba4cb26c0bf2f8beb0d686c051320a054b6c3029df8b9f2e5c4c71c4360eb79ca47c83cc8c6cf2bad0667c30a8630a7ec89a4c8780b3932a97998f5843c61a40b635eff14cbd8e83a51bb2372ccbc76225e4979bf045dd4017e13d31c41dc782062bff70234730230084670a3434fde1f4525ea083d4199b8c1dc06d6b475d6e1130bd8c928fff962a853c9a07796e6af398b901f6cda406cad504112fa77367f7da9e61fa15505c50d35035a2e4865087911ebd1ed3813f33903e1aac9e780efce8b43b916f0808109fde3d161036f1024b356c5182d9c7a1898e6621e70ad095448a3e0661c982d4be231afd27646aacaf4fe68805d0c08c4671e41036de6614d53acd45331058db6cab931f3e81a9b839b07cfd24e3bf0856102add7725779c7119a80af960998b22d001364d6dd5e0701ec7e4787a2d53ae84671d95553c40e4a8260df0f241a512d132110d2a5884247d9ea1252e026b3f82e19734f3e2abbee604c1042eeb5c9ca458057147780aecdd5b8ee69dd34ab6bb2d02238602e7acbb1e21b7c050b62dcce7100d80f97e3e61f6c48a59a4ea021cfaea0988e4a31bba0eb9de85b65e700adc3c8b0fb10999e3668383e98962894140b6b4be6f03ced14477f58ea1d0453d9a082aaa30025d5ee21ff73f7807506f6f6008fe0fb03e59a2667d3e74f6fde44ca772965d8c49fdb21e65c0fc4dcb76a500c8024bec50774be4a3ea3d790cd86b7a2a52ffce4818a0704ed2a617f630256601a2ddfcf00d39ca0c0686b99b75509431abdcd5a4eabfef6bfa971b6ae80c320d829314cf8306e7e6efd55380e94b9553b497bbecaf0dea78c2aabe340b8535c14811f61bca0dc9dbce99c65415d2a5d6f2720b47dcf23f77fd36bac06608e799879c85ac14d78831e458062957646af2cabd88b4cd1b11406071bca8a4952e27efe0c7a335956590907c9df182c00b15c31c48b58402f51275d0ff0ab7a53e2f401bffb68459e218fea87255358f32c207760eb89805d47a881384a0cab840e26789ced94f9cc060000cab0c692eb70e2f764130db5001d450b88c1254073e51151a33e0532c176919be4b4beaca20603c970f3b502a75047bb113aeb0772868ad5027223777728d60445afd47b01590766714c62174e5d3bd0ea6203500047717fb4569096a466371348d8169b41350ec82b8b058eaf980d3e0e8de5b9080c1cc8cbf4c049fd0471a77323b8abca33b83c5193bca2cb897b48f8ad0069b400d0f093e389270cfe905919de4037763adff8510ae830ff3574755609a8e7c2fb29fffc8e800 (pickBlockF p 15 0x41a09d0134b02423310a872dde2c689d3846b49a4a2d127da3f60f0790ce2eb7d5325a946ed2faf7c261b1299ee0605fc60b07a39d6e5712d22d8f214128c9c70553dfc8f09d8ffc0e14404dedc8a6df8456691202482f0a5001ee0b3412c005598d008d9ce7c89f3466ad9616a088960f0f0c4207e8bbf311345631084135000e8a40a78be641ce6e56bd7856802c05c000157d8843ff810501a7078a0f1e3e28040aa048e73408b4c0875b39b461b61c85931b71e04d9a3edf74036540a9e04265faec5296e1dd07c92721398de0e8f33580acd685716f7eb35061d6200001ae0d3487780f14582d8bd7cad68d6585ad636d389ca3a27f188721dce8273de7c88909c6ae667d31f2f4fb11ebe99633f8f5cc252820e6a990080604c44e6dcf4180761f4a8a3a3ec21fc35e32827d30c2cd8d4fe04061e374d83e4c14f14c128138545e84928b11fa989256b2226dabf89b8a8c4d7640249d0d6db9c91a8e530232c25d29bf7b2d56f04b1aa371f33bb815d9940e0042406ba36da1d73b172bbbb090423e8e3e6d7d5100ad02c3d7f93d9f0abbc76fe8821c68d62de0b85e01a7c19296554b8a3e9b15ece43e0d2938a01009168e6e058f04e3065089120902aee73654532a2013efcf0bbc28778494618101086d2e0d590dd7170d3d4e112ccd331c0caac75970f3f962cf37235a8e1567f5face5b1d34753579080a74a9fe102076f09b49691bdf63cf33d6b9d3a297c63bb7b0638301c8f065ec251f8042c146164dd205130b376d80b5066732820d2405f53a552f66fa60804961a45564629496ec79904173f5101dafd0a01abba7fe23007afff49c14d69617624794e29416f86e2683a884529c024fc4c044022e1ed148825007bba07e35c370153e46194af4d1989f4d0b0dbc73973d68a8f450077b5f449ad30900d07ea0d847c3b81509e209d91e82ac83f89fd6970a0fef8702eb5075d64d89e05f483e0a5a1a0dd95efe1f9cfb919e29dc07528070110b517b256b1f657b0029c8b1045cc36d330423f422dbcd923bbe8b226f2df0db41670bb81703a64bc807c4ce6aa48d678a11972c6989fce81c047dd0161469b926507b6df88967173b09c7dc81dd72477910008f7da004d681080cb4397ecb9ddae50541f8fb8ad6f49513024f523e0bb0f2115a243446cd18013f5956b994db8969a064320f5893e84290f00ec3b306448488999c131e840c5e8c4def9fa0b28829cbe4fe160007c2f0ab48769aaef92dfcb00a5a4ee6e2d35979bd981e1a4a215d38b0aad0226e0a38b18a96f8e7666ebfe44b70200ad710bc202403f665cb000 0x7150f14ba6506585a381db6047a5d480c5be76a081fecf607505b47a7e89b0faf94764e9cff8b447a1b01fd00001211707265e5a00dfe3986208604b45afbe640ac0e3493b94fe02328d0189d52ae40e465efd80c1b606f6ade08fa3cea1b0ba2e0419de6bf6a0bfd2116dfba340115e2d0c2f8642ff669e095a82c2e3f95149da5e7d5e5463606c8031b980480005e8a855d61ebb66d6e53dade8cad90bf55c156dabc8bab2a5dab2e675257be0dd7f7ec5ab7c871e8b0ad00237857d0759654e109a6224d17826c39db7206922752470a22ab4404f7109c456406b2009ff709a784102b66abd100f43a8a4c32dc27abd6775f782bc4f0a3122ba8ffdba26d456e612a3109750e94a6c2b83dd66eb8d60b4a526c09b0e4f8e070096a726a4757580ceaf516c01893e1da8c826ca563dc67cab0032a61780822d491b9befa0f052cef5675104f3960b00087c48e0fd6c5e0fcba36ff556fbab3c88b1cf0c5376a476bd15ba24b0b09954d1e0590073f8a8f1207654f05a3a3714c8cdff5d5449c43e17211e266b4f048aa2d4a61ce12669874c0540020ddba2e600f5dcf7e407bf57decbd07000b8ba7ac56af81919a0d39168f90d6a6886af1506c3d7fe0ada519c249d22ae4ca62370dc638c30aa271e0b6dbd2ab3811fb39440a10fc4c701957b52e883388b3d272051865e79c106a45b1a6a98600df8f04c9b5fd56d7f18e48003b0798e0748e058838aefb6901b236f8c54b3a0207d9a0000410d20)) (pickBlockF p 18 (pickBlockF p 17 0x9ba985efd7ab24201cf4120af8b6ea01550218c083a01774161b5645004d2156c81dd79820edf07d15545ede80a9b563b2639754c04089faf169d10a6cd1a662c0658ba0e4f39fde0757e0d78e2705537f124bab2b32b30a89106ae7648e0ce4bb0a31aa81582b5c0a27961290cb6ba00100017bffbb7b565e6ef40a08d678fb0380ac20d81e010e8f8900020da351b7b6c05fe79dd278fb6150069b1ca761331fd133460a4130028860eaf28e4bdd9f7fad870dd284781b731dd2f7b5f4a847080ba3e1a6c24db21561a12017010a1e04f7a39e3ca626e1d49a36831713a78b872c561fa30064ca10bed7fea51b672f4116f29eab07ec811e5ac0b0b2cb16b860755fbd7f53072f743d59494f2baf8332bb7d78772452ca5c334f8ac505b020565bb6e5486095547282a95464bea1d00045ba83d6565252636739b36be022f12414700748d6540c9600705000f610d47560e6467a66369d43926390a43005e5866e0918793226b3f81e63966e5539dd6c097ca0b73ddba9ae8c5fc1843c5861ba83194caa01a3cbc4bf73c6e07305f0cc06bc0866f0a0082c0f04e0e8aeb562bbeabf220b20f448e576feae2a23ce2de88ea0623461800136d1d41 0x30881a961b82a2174fbde4059491d6b02912e33af4c5111a581807aba29ce6123681b3d49ec3646a9a7b5eb2c3dcc08c1b7fa684210074734d66229109e7849782c6c5c98de8c7ebb3c7bcb8de3cbf90552607dc121e4e83ac9dbfa1b127617b47dca39f28620c06266c8e7ae232e0c2da7caf0300bb4918ca51c6f69c3c2711e0c0f0d8b941c911ff7aa2adae281d2948786730350b1f7c3a2326ce8c870f325808814ffec34280c90883db856cadc7401784) (pickBlockF p 19 0x4db2fa0eccdad9a5d7de914f4c4b4802c623e5f0b7486e48d09fb98a1090d1d6d1d16b4a98b9f9c31f759b815d641e802a59b5d050000244a06ba3f826f22f010e2bf55fdd02584e13d3826a76f6549054acf5535b824530d802d8bf0ba0c25f18fa0635d1a4512d160230801e8a8c124e0c8983c33663689252566b1a10e7f60aea97035270400705c9618b26aebc2540ec5ee05ab9ca4ecc85c4854460a44721a80e441ade30cf60f7366d546650a91bcd101504277d411c6725f866fd1789ee5c61ef4c0552faaefd1f5025180de19bcc1ad382947c5d09a003b8149e8b81e48181237bf14af1c185ad3c49d8324d81cf8e0184359872877134ef6a4c102016e039a29e2b0e593cf803702a2f002b4c48766072bfcb6710b4460a40be453f1d85f550b81a86e2c1e195a59d0454ec870672305293c803a388fc9705b32d3a0cc3300115a3717ba3c5bf4027e501ce2ec8fca8102506f2889a20ac89c1fa9a8bc25d0de2289508203a31a201e050629e1a91ac8a44d1a49556c7bff0462d517dec0c906009986 0x1c8e4948c09117c18b805dc80aeaf0a875c1c224f0107b5cb7e423a6125543282d38397c3857b0b748480b0c812078092205e5f3c93875be029a1d1d80409e5071316cb63dda8002caf605dde2a51e4999e578f3c4505c535a956732a103a022d19c7151c88dc6a87c0008ec08098984c6d31a025a3cb64fb7347511fd4052635423b89aaf9188be7d04a232c26a4c1f3031017bf6221fd9f11c8298737a501466833678934fd0ad41811fa8ecca435308cff43a03d82dad68426ae2ce3c88093efaa43c09c00096216257b003a694a283831aae1a0817aa79e6153c200404b30fcf038490a43cbf07527d5327eb0039e000f87530d549c195c063f4b050b007c00d330d5b03b627712d898808a006fd51cde34a960077f05c8eabdd873507e029c786217a26e6e96e7fc9d33272071109c5c2a404820820f6890a7de1b27208516f85564106ff28423f15fcfb883b21b3a9393730b85c755c889ba0a29e74ff4de7074017074b40c4e51b9c4f4f40d1b5ccd9c03da75d468000eb8024d8b01889f3349c95ec1c0034c942041fe871e1b3c610b9e394754ff1770eb01bde6c3bd9cd9226e0cd0745db3b4a77e0e1edde002702e38cf571d9643d948382b3110b16a581c8918b9d1db45c5b8c46aadef480f5a32d4e4f3014a605cf4d998881a29d01000a7b1147efebc021fee84a2fe0c9f6752911f842c308400028286c20411f8b07fd61ed20c867bf001f2e63e995c44c714846d22c22a2f2f790544ec4f65f9318a1be1b8ffd8a1241c31ea3e4135a46c6e224f48efe01d5c302ac5d0c830bfa6e4684aa09dcb24cadf3199e06b441572b17d3c941a20121106bd9a7007cca67bf92a0615f36900e996d60637400dc65a9cf6eda1303a4357aff5b0050d0f1f2b653f1d500305c005c02ad48a54bf2789c7c6938030acff804602dbc3ed5c0203221bc523ba06d4ad092819e36658dadf0f6d8b34fac0992ad087cfc99733dbf807f4479e9000f9e27f))) (pickBlockF p 23 (pickBlockF p 21 0x30583a2c0943a971b6107978606246085da265e7bf0045f3795823f35b3eb35bb528f28fd245c800e4778c136f37f586a40ec0be47536aff60ad1819944321f5dc200303a9ade17fee1e30f481b6391c5253b753bd43f6a02c1b5cc4dc25b7a4ddfbc061fe77642db54af42d2380e835633c33bd631841c136b9ee4fe39dc4d098def20bc435a3742c0a83c8026002820f19403c03fdb4a3de1edbc2ca2dbef76311a69c1548b252e802dd00904ad4519388b8be242227096cef7f0048a9c4c8041531be8de09246a38800879e015299a23ef6c25e797dee21e1c9436bc028214ab7a6ded7faccca2e9fc1011fb9002a3f1ded43e8686f469fadec0a13c3b2be9adafb4f9cc020eb88823be053303b31046f207912c1cf3f325bd37c9322881aebb465039bae41acd2ef3fdb175081d9cc699217f0d8f38b47a36f434e436fdac303deab0fbf8122404430d53730a483c153ef897c5664623bad7a4998231293168ce025d41ae2edba9b5953ba1682e6fb0e81d6d7f58e871ac7edcc64a89202ca18e93c4032f90fe9f86b5346e540a95d501943d40f003208c8309e58287044bb4c19892f895dde444e8be9b54a3854e9ff8cbfd746aa01400001264c75d1d530e2d27dcd90d1fade065bd652cd4a653cfb55b3f141739fd0efc3fc1cc3a452bbe25561f699c9af72c3df29c22b5dc2f612f392668286f3f30dc31c40e420ea808e590f23e7e24337f6ef2d9085aba7d15740554f02b15941302fb5ee24c0016d83480f37ef9803df8eb639898171d43880015435ee4f7b0c07ed8dddb198878027487cf9ef4954648201ee68dfe623e4410dfd403b5cbc8bc01fc01eb58ca9a9b4b408bf670573c819bec145deebd4fc06601401e94d0d14210ad15dd5eeac2df5b548e1a43089a21c21b6fae85f836163760a1693153365c190061e3c37002e420a6607ad0e9e0872c1fac2076e517442d6dee76128acf034ea180410f8c81ea2a84a271f014a7749a4593438c424728a2359930986ba49d852d4c48c91a0fff987cb49f73c090e86cad5036ee5d2520dd09af8a64b559237f6e48a983f04f44de5d8f1c93d4c80a41dc99983f92c3a4661606d07f03b559dd82f8fb7f4371528a2918964815d5ae30b971b4f20665703db0b5c2610da90d5110373ad501cf038bf0c0019e65737004ec7512b22350740141531141036602434674dad0984a9034802d06a0a43804bcd7fdfb81771199264e45b23d82e5a3e4dd0508c70ce3c64a60ffb03be59a8d00afc3100ecde7e774fda1892a093c5ffb190c46cbe90435249e163f028fc66d851a0fdc6d6b223fed5904b13adc037d0d053287b3700985f5ff637c0859fd52be7781b0dbda8dea8553003daf8604fbe2300606079eab13c5b858723189b9fee0645192eae5f20c00cc64b1356e6247d9900e0900c8da529bd410642f8b11eb93e98a010baa24607d9275c1ead21089a97ee245060 (pickBlockF p 22 0x18d64cbbbfbf56e53c2a208c2385f032c4002090a99275103bafe096e15f2633c4683e00c1b7c00902f1e7f5fbccd00510b763e489f344c962023d3f22b2c233fa2f512b21c9ffa4af52b9e47a33007da0005cabbf7a0cfb24450f99793fe3b92dba8afe861bf900f3b33fd3b9672400d0082560173535bf3e171b0e29abbb7399930fed212a0488b038b892befbeaecbeddf239500bf5d13039ffec267d5de567b0c44f43003b0e70100970198c00a689eb707436159208ce4060761051800378b43f24276476805060e7f1002ed10a640991b4fba71e4be5cf33473b7fa404400572b45a222058ba7490c1212fff408227c4d42340a7e140ee420c369ae8db6f046f5e15376c4943edd5c7aa5772c3cc8107e03810c0535ddfbedff00603d505dd5325ce9f81713003349ec8ddf060966358c6f33389866b2abb2fb2d4f3072592ac6ba560aa71ef304b971dc0f1271bb8d073691ebdd1100a7375ba73b30cf4838cfb938d58ee1ec190b00a687ddb10681031502fb78500eef1fe0e2377050c60ad0da2dad09660727153b98d79328c4facd646124c7727f02f95136c930a8ebb83880d978a500241aab7ccb5607bb4fb305d11f4007731460c647727081e336d162a569d30e2140bc03efaaa99860c8d10c79abe7d7e5d7318686cfca900650000737142a28a7923e654ddc7399de1ba0909cfcfa022c2ea6cbf9197516331a9ceb27d26509d7b04db0d57b9b8d430542b072a15d4651384d73f0cf294e5f2bda0387deddc4f87d2110e71d52eaed6588c79305e5e7890b0de9dff5226d110ea1fa06c3c0b72ee567bb00eee42c0ffed6d20d711dd9be1c2a6503863d2e434cb88ce4bf6e0f9efe5ea000b1651b4007be901c07f0f1007a9bd11706352d6188b2fd45060c5a75494969a1a7a7495c05e88087e237f00190464b2a3607db9ffe27f0ecfbfce8f0f4af61caf495ade39497688148ff8406cb97076eab199e029d12ff0291ae5e9bd75e122dde354e914815bf567fc26e380ec699730190677cf10b9c36d01cba6b33abef02c5afb63f160b8c894560625e0b9d56c0282988bca1a9217cb249bc7f66252033102e71fda7090eea396b71d4fa0b1e405c7abda1d25ea34d699f2f8c1baf8c0503e80f8f54e336b3c5608494d53d8d062e20200d5091a63080017 0xa7f47d901659dd0d201e4fb60f736bba176b12dc14e7b7d4bece2f35d279bd326eab034014a73432e154380471418f2e90078dd00b0f3c49adb2784e72db0c0711ed80de29331d1a136c25108d4ccfa0f0a53ebaa49c9ff8d8fc80c3d80363f9b2c0bdb1429fb0b10bfbcb52e6ab089150e500ffb00071868747370b317a431bd3527e00882a00e67f1b5445d36544390dd53167ddcf4892b4b560923d7205f8dead4d4c799e64844de4e9b3c7991ee2024db0a22a2d6e9a64c8792dab5060098da468e4a9c008d81641d6009d06d5fd46370ae0e7d4079674b886724c42b680c906a1b9358030aceee009ce050d0e3d61bd16ddbb8aac5015bc90291af2decb3c5628f201bc48dd2441d4090008407142325637220b71a5555890077014fac1c7da120c43f7f79ecba74f5ca959cb1ac663bfdbfe7d042e95309800b00ae5e9dfc042b221d9400756ebc008164b8a93c43c040599a9ba5426b18499678c21b0da4f5ea8258dd70c5dc9d147abdd0c2682c508001d55840837290089c308c127971ec00e14a22002e372d9f42e5083c9a45e0d3a600a56733764257180be213c93146bff32b5057a3218019121d348bb75ba25d4c194385d29b335b13110850629c2583a2530ae754b9481c7e06c1d63ec9b92208a1cdaa3280430e26c0c4ed755835b73857a8ad1043a16308f026923fa6dc6fdecedebb7acf71bebd628cd3f5ea876fb0a1a0318637e7933b2c453aa72e8e814f1806594eb932cb20394eedf0370a124af3673394c0081e02c1a249405fa7164abfd2d7634d01850c10426e44090c7129582e94a703560f30b925e56753bd8dd7a26ea30823137aa385290ea82e2448aba9389f50a042b1c86ef631017a847b73677e45f15a2f3a347e0c6030c8a09cc0d193219dbb8a7709614302720e3c9de55cf43fb5f9045b0f1ebe34000950ed13ef300f1c2880b341ab30b068c0c239c2d02e1378ee4560a3b4db0116b436c2d5a60820a65060baf2476e956905979225bb7e19fcd7a20972205104d8540b15d40af9689303d90bd08ef37eadecc5dc023f07f2b1fc56068b3faf1b3607b00b0af276b4609)) (pickBlockF p 25 (pickBlockF p 24 0x17de016e908dde8456424a53f711e3ff582211db3a0d5c58134415e656074dc8c8cf6d8e86510346a5bd0f89a29701d72bc8340235fb541525d53c40922a760ac539466a5936f8c72f073d4c71013b5e30a659b9de5c3063607084ec718e1c4a359d7bdbea9ef47145a631ab6b0da260102aef32e07d5833b1845c60a76f0386 0x642ce94969e39e980be25c81f80f032d93a522ab40c90750006cc905fc01a7b1ae4a20c7fb8adfe5b43c012b18db6a9f023ee6ce0d55182f01bcfbf24c2ea8339feb08ff8bde2ed953df6429ebf804c5b8483ee0e2d158ffeac23e4ce74f05e6c1a154c0dd76528a6f4c53dbc5be818bda67a43c9140411675058e1a18f11a70c05cc3378e1c9bb28a67e8407f9c2e45816c205fcec2e47f50480115b2336bffd8b48082038e4ae356f2822813e4c675ca890539a368614cbc64a85c8af6bf75c5a724dca8272f9824183bef7158d037a735ba2764e680400a845ccd3c19a854d44c140da014359603469d08351519cbb08e7c10e81ecbe2f84677bf5fd0164a084e53082c0981002c0213284a00eca8264478902933a59b05bd138295d8c47e66c410d63a4f372596a5aeb065d0832d29cc71046e8c75587562a82f378df3c4834020787cc47f9f95157aeed56cc01971789aaa90032e95a8ee69d6a800c181b9c622b7239e756652dc20308f35c5f35c414db57d34a8fab4136cfc2791f4377c8731af6fbfb973f46338794b434da644022540) (pickBlockF p 26 0x209f20cfde29200edc5f0109770080422fa6c323d543927d5eacf74140824bd27c52229d01a9ca036fc00724c12ed897dd701941994ca1bc9e3c64056da30c3385362f70831dc9b9ca6844e637a2d8ed939fb6b274a3fd3d80f170d3e5e2a935dd69b4a51f26dd3e468d27d6d0415840aedcca90cd62defc599a73d8614ef9bd628db1cb03c3259061eb516f566d8fde61ddd7dabfb10af404031bddb441bf2f049e33ee4678ba1ddeb4b71e2c38b891271c00da0c07e04f39a1936c79741bc5bdecf7fcf7be3e10f2e5db929d62314eb331d3f2d9c26cc61355b642ba44e2403dce5402e06ebca08a1817ff0754e9f75c001e2305db9bd546eaa034d0290b1caf63c2ce86f1e4fec624e87fbf55ace54adfbdebd2915e7ffdbf03cc3d99ada81d5b7a993002b6107cb0077ef40f50309d89b0476c05cac20e2768a560488c78aea57bc70071d84a0d27f8ec663429041d503d6b1253bdff8af43497f7742eb9c70e495c3928f4a419df8458c780ac071a69b3ed17614d1e001750b45528f361d1002001c298e292d32ad24b44005c770c8b3570a39bf2a1a07f5fbb340227c06f91713f239b586cdcab4cd83ffdfe103cb3ec250865264fded74b4bbba50f137cafba503f8b0b4fcf4b0a8134a7b7ffdf78ae48f3a60d0f7c866068143700b3c63ecbffe6ba2001bd7608da5537021df034186ad97306b53cf486403c19932fd66b2e60114e4b3585d980db547c9263d784f7200000aad4738ad6d8dbffc5533acc5288d0a36017c0a6e02fd771b7c7ebc89ef2f259f61ebb83d366cba68600a410528f9f4a10f610330c951980ebb78165dd1d7a179983c7c613d0c719241a701bb9184cdb956f5756480048c94dc9cc12dda7c32b89a277684d23589e33a814764dbdfe1790ecbcc610be23065a5060407e982bc2f055086ef3bba95603d53dd6b4eae0bd400022db0b04eae9c27cad90e8fff504c0d331727013f08d2823d017b9821bc7104ccf7860d8a718a80ba11cd6dde4f74db1d24d0934af67067b257ebeb3da9a1da16647fff0876b8d37912aedcda27ff9210614f0d489083a10c1586758f2bcf13ded4065f346e3a59e773257a806f906f7694906a7de0254c302aeb6fd184e0d8dc3efad1bc7ce0cbb25d11a9dd05e36f5207523668efd4d06b83fa8e 0xed42150ecab48a1722283323d38aff2c4c1e48e15f6fc6fd4513130e307c70e0443fd30cba640aa7d9510236a808ee150640d5b0e3244e9ef8b6b013c5a69b55d9a3656dfab5d1058455c791506117f0b28498f63f66d866293c7fbf0d070a3cab05fc39a7c6f38b7ac0b9adaa7ec7176bd25b92e9900584e3ebc0880f6ba9774483a3feaed3b58778a00502ed0039f05349bcad8fc99bd39b7b7aafc88cd63e1536b67cabf6d920c582de60629275ebab06029de6b400a616b36e5151686648b09156fe15720cd2a3f6eed2e87908e101adf3e241dac0c5044f079ef25724756910a086e7c68d40cf06e0109bfb8bc090e69b40b5a0e88a2a2cc5ff10975f29ff7a5f903ec70240b64b4314515f11818cae0c7455499767c5791e1400beb11735e126745582a9035867e586f2eff118afdbb621b3efebe05e711d08420074bbcf3b7025370766a713c68cd09ce08576ea20747e505000659e60950f7705bf9843e9d1fc828831c01be4fdb0a483c4ef109fdcfdc2eb0247b700150a25b34f565b207031921f85cad862a519d939f1eabc3f27d4c67070e2cf098afce823efad245592c6254531482af1eb0da96576200f86e7c643a9cfeace8f19e1d52fa8fa5292b6706942c3401030404cc958404404812f67c469d2296f2f3b0b42ee43409718c044099ddba92bb08b7d218d91135a68468e6f9599b52adf0d2a0d7ebddeb10e6c8d5b5963d0c00056ed55dcc3a6366952b4c6e4cec3aba51f243d552f4f4342b5124de220ae495eee71b0509b9bc032691edcdc3b72039bf0a96b15f1d346e33a639b8b99dea034f955ac63047cf5101c279c06066b9b948428b0ebe0fde07a1af4b6fe06f6c24635f47b2ee58cd1f644300377c22a97fd795ce69298dc140dc9faf29f68f7c0bcdb7c3a5cc210ad503e49710a8c5c9f5db6abb246960be0154175cf26a4beba11cd0e200fc762e964cfa0908c002a8482970a6465076dbbf23df1629eb1d086fa705a26d4577081b603d91bb780535c0f2449614ded6a040fea70fde941956a61c0115663b64fcf9944e639742dcce3064aec90dc93efeabe818863343f0fa18a7dcd34dfe6902b9e84ae6ea5cdc8f5617b7719cdf0d632b5cb3e2ddd2afc3a9f112803875e8f740c4fd0b815db4a01bf5e905334700a1b58a7fe20cc78e4c0c7bccf01b8f80b10071d8071e68540cc0e1527457be65d3368b324cce9f1478f2a08e6b3049b02388887f00df3c7177084031e0a6daccec0b08b19c0234a828463546459ce88c7e23d5b7e95311c33a2ff43cf19c5459ffe2c1c16054628384cf83c5e2174609786e0ada6fbcf1265e64c71ed8df6f10697ac1ff945e06c08dc1b61e386a9db600c70b0a070151452a4bdebe59000e595ec771a5f653e5f85137793fd1eaaa6f8c438e2ff16ceced6831c9fcf6df03395d768541cfe80a109e70e5e63395529c2359ceac9aaac3870f465807819051b8ab047c9a5e5f0b05f026c61dedccb80b7d1a65c1e02290809f597298b404f9ca45cdbc6f85add61307cb9829909d61f01fddaec400638b1601df020c82170824f269ac4bbd6294202ca0c12ac0340760610e78a417792dfa74e5213b1dee673f6422cc73501c78b861604e812f8fa96392760b991bd2eabd53e580aa28d65fe8f428ff3fea559713870559d664063545d0136535d924664674631f9be9feaf0a0f64fe86d5bdd0000e2385129cba1000ad9a192e25eff3002279631fd0bf2cefe4a78c8bfb4d2fae8670ed40cd1e5e69f42c1e924044f6654940423eeeb3fc3d956e0b1d7a6d63dc68a299aab8070f10981bb0a0f0c0726007e8531fc817b22ed591022151755076210e4af9c9f0e08b27cb9f13384260edd0c1198ec8e308069462b9743d86d096c70766859083204c8a2028b2bed3ee05c6a3e559102ebdc4d9f108b90af9f6d48de2a80774c796c50af52cfe06552000b4646840ed676c6b0360d5043b66b6015b0beb8f107))))) (pickBlockF p 41 (pickBlockF p 34 (pickBlockF p 30 (pickBlockF p 28 0x3e89063e3ae182791004230d0520619f86516091fae8aebd50483b02bb08de44e02573fb00a045b7aee060aed67c7bdf44090121803b8e7a04f0250e1c08fdd505fdaa79b2d999636c90995d9a2a755e28060c6d8c06753b230c9eedd5f30130e2fa69bd05dd56aecb9c1d80f5070bb809a5163a6a01d715a8b8b0c4f33994f2acf6678c188fe47f3a67dc8193746a00d04e79b313a5904c80fd0fd2095dc7384edf606ef2691a20612fc7a963e4c5de65aee7030304f4c2ef417e30022000c6271ff7407f1fe0005ec3c739902fb910158067dea9c88f58303e73aae0993b38960cd8f8504900d177e13b207504b6b607b8907c0fa61b376838bd8f03e60b8b8a390adc7bd711d34b2520501bdd33e6092aac3f4dcd5013bf71b68dad48b0ed576202fcc85b8bf5602b5580bbf0137004c96be295006000014703a7d29d6e871904782eec73bb35d5c131ea0303717692beb1ac104103fd0137d4bc767b73b267759da0b01be6dd2d1bd909267e875a80080645d9029a0b49c41cc702650bd900d84cd630ce386ec0060afb3bffd0ccbd6d37d950f1048083243b00c84b85301c4940ec08344550c5bc6992a24e772448c2cb3dbbd3d828903b739ca80a3e770b2dc10b0fa6f74b4d272aa30f3b4fd509c9c4303a674fa0ff0087694262603621c3fdbe484fa99102e10d4a2d5fe5bb9dce9e8f052efe69ce4fd05b87be71a0507f03079120d4fbb0f147581bac00cde9b009be7486ce78816b4a8e2b1de68c378018ca59a71d8c0cb446465ea423446e15c0da67ecbd8fc5a5130c8d063d8252290f9b988fab1a6a23f48b0c51b482057600f129625210668e044b31936db3ca7201b80575b7646e556099793f4df10f792a01cad38cc22a38333b8d747ddaeeb209bceb07c261669bc1b70fa52c89c05451fdd5da18448f14a2b8f148e3c610806e14a001c7bce18e7f27dadd21209b07039b56a27a508d0d2f79edf45770244e00b5a6cc0b7976ce9e12c269615503d81f0a503fb42079c3067cb0d4f0e0c9a7b28a1fa6d90ac5389355895f478f348a5686deccd489555e68b5de0b27c80103045f80d158c58e471f2b2f227c6494e2d602b68ef086be1c0887050eec07fec873dff20233d31d7e1c3e3b06c7ad0d1a167890720056af913819081acc8d0e105d30c7bff4538c3000301854f6b11785910a1b6bfb4e591714d2bb54a68ca1ed943c9d5dccdf442c26c824b93d90164945799010559d08bcbc8004d958bd280100ef70dfae7296cda9270d6c3e30ff5b0ec518b455e8a4e3148ab4598f12a9f58aae2bc5cab0edf3562e5037511adff736d40f42a261b25c3c2ec396da95d0f199707befedb71fd9cf9bfbf98d994ccd0bdbf078404003e121214fcc33f00805597aebb761304c1f30554028175d63c06d99b405664e2ac045700fd284df5d502908db1de01a1b374297226100bd4749a6b01e2611d07c1b1bf80afcd684de7b1d0b0300a0b17d5d640cc00091115a0646b36044c333148ab3809715351621ad3f7854aad2d22f71ad9058beef0be6adedb63c6e88f9e0f25b273ce9098c1fb4f247a70ab7473c707c43d196365aa45177a603166ca2d302b610106026 (pickBlockF p 29 0xbeb141ae5f441e074df5fc0d86f9302220e927674a5ef509d9c42b55b24b32046294640710e342530e9500947d1607106351a97a66ada548a1260d87b724d1e20813a03ab4297eb6c7720c08c50050967eea01d607c20ed0703b55fdfba6b3abfced0dae5d8b444dbbe0b09fb3b78e9b6235ab281b90bb839dc8a009e002364fa0b60859998d8382019aba05259ac71c1631837eeb40d7be5c7f826dd74f44533f5677c3bbb327456c3abedfb22705fdbeeff6dd9bd30342f6cba409aff78f8c6f7a6c639ed36a01069d331270413022232305020b502626de6bae593df23be45143a007e6b9b44e0c431eecb5dcb01a3333e618ca1871e523cff4eaa9786bffa0308eb6d4f6eabe1dfb5c2904996723f6ee98154630a51df615af59c523700dec3084054016b00451185ef220a29028095307efcb2923101468acb521c3125adef00ddc481d61ca36320d78d602749cbde7e17929ce0e0abfce0ce30c06deb1385a9bd02c9b3f7fe216f9bd83576a2756f65dcc6b03e45c9535dfdfd9a370ea953ba90ace340f646a6ce4a24bffcda0225fbad7d16857cc2a9fdddbcd73091d5306803829ebc805a303f74b829956e70273e8a3739193f53870f01a8ceb78e65dc48739201a83daabc30ce2bc887ca11f755620cbd053a4e201d7dd9a3d9e86a30cac714d187092f9cf98e4efd0ebc05707e468dac5d65bade488a285e396798e3dd13160d48510f91292d5182093c33af778a7bf0cb227f16f00a6ed9be96c495fbfe9006b7f0a069c055a90a711204f83f08df9e110274d0184f4770896ac096c060382f29f92c93d017c9c87eece04688db95316f95387940c04a460421ab11940f0790a1dc736d3ad691714fe02a0bb0f56e4234156a2f8aa01c815c0ec1930c0e30def04d71b09b000104b6fe685444df1b811b1685b3fa712d3332b06980ea79142fceb703fe139f18da9ff6b470e6cd0878d002715e8bd07e0ebcc9f7940cd60da6600e7e7e8ec776298e79a013676d59ec3c680470dc80c4537dc5b216f01e860bb6f75a4729c46ab470ac0236a008afaaa3eac9002956730563f0416dd9a437be3337bd9f1179d6664124867763ccaa4404634c2ed141d00d2de5771b5261b720f7324b454af7cb2741d329c49b2363b0054707dc9b07e0857080845e29e008f0d8b75ee3eb8501a62f92dcd0bc612687241d204f2b4d42f64ed209729dd644f7f47cfbaee912237f7a3e71240c400f83e2e5d5c7c9c4f6da128273959031f4e37c3d97fa7973a60d67e4145dccc7509ec1c47d9e9671ce24fa6d1dcca8c03bd053ccdd2ea650e877270a0fe1ac5aba1ef1cc98b1d364dcf2549333cdf8e995efb9e0b00e74758a3e4dbf01fe9f38e119a46f5eedf8934496c8b0c4671b889a374760c102daa0b9ccfea7dfe789db2659343ab57fd7e5df803981c2548c78a7c107f03020fba0d8bce308414d79d32e371 0xaf3787075d0e397bd80b9a58af0d3c13ac8dff1ad2d8209b5fc3937604a308d8ee0280d487093922c810c400e50b225c9aa739180f7657c7063c6945c03935c8000e3415c2c089a4c1af44288eeba7baaf0fc190b08070d7c634fe00800eb37c747590a397bdc4bda58464f5e73f3cb3eef25d2c0eebe58cca0840d430331bfb09a56cca2ed6fb8176657250c085c0876efc1bf7803ee64da874f8a292a9104145b6ed488dd284f08377d154cb2a04e038ccf487672244bdebee525d15e315043f007b56001068c8c127024d03f5ccabfd70dc944eb9909506dca0bf5aa04b371a0c6601560481a55834837b9cef891dddc1dc1d32a43fc3550d30f528e54947769845522b080968060006fe9e1c10765a545b0bacbe82b60092e01552580e84a2e25b702830e53a37d8ed6577b261e9c0141280f305dfe6603d5f436964a7006e0500b01e4058037522757d908b0b62e1dbe94336098cb64b6a311a703961da04cbab3a9c8f3d969b052545000f00a6bcbcb1707f054d16d2f22abb3d2cc0baf30e83b0ff523754bb6a000d842bc3f8fe39f1aee3528134c23efae1e1bb8f3c3a1a918e0d327195515f1ccfdd5a0042c1824006456d300bfa1da7f855bb1415de1a549289ee8701e168f58d4d1d2de94fe9e5c5c7b57e7d690f899bf7d62e8026440e4e76e053bd3ea8d9f873326121e00000991bda193e12946a073036148b296d90ea0cf7db0a2470a791c9b5ff5abf135c6ec00ee13450a4bb58d52c413ea4574073ca28e0c3c9c0f23e1df0c036e71b83383f581c6c313209e6ee0135171ad2d7c0ffa1f6e134fc33c787b751ebdc9c2d95618e9f12bbcf221121fd99b70260e6addfd117757a10493c8a0f3e04aab1a14271ca35710f5ffbc6db49fd604d2cde887468d6719437fc726d3efe6e839f2d134c16d3f6c790bee7b1d1a052143687caf9111004acc0545ad374dc62c240150917c8f0c3657707ad678c545e6d37f05c6922fe0053d03628404134cf01804402ff2dffe790004e7505b95694847a6cd48018c84a12cff230e57a9b72fd5dbfce938cf8005774fa54e38620f664450287a980602c07ad010439a62aa8d46a49007bd17fcb8039255dde5496dc185b737e8b7d536d02196d4ce7af14b059ce7d93201b075fe4838226db20708162670490283f68f7269c33992c95fdc6c41a6b14b7bd1217ef1c2c3368a5bd0cc3442b07b52f0ec85ae6bb0ca3360fc05606dddc011221208351a713d6c7ed3fb8531226f81123702e23efcc835f9bb27f506e00601f87050af396ab181b0)) (pickBlockF p 32 (pickBlockF p 31 0x79febbd1e769e4b43de96610e1c83ebf450f7980de76bc2c9041bc76593589dda6f14f06471336231ba00361e7e596e9ff1ae69c0c01e522208e4f65d49ed45232d7b0b256a4a2db03c498efbcd5faa7e20b154a1a203a4f496a33d50ef14b1ce0537329084ad810ead79e70e79b1fdeabbacc944b6a60917beea2862b0d06c18f11a542a8a030c336c7ddd466b57989a15d930d0fe00f6b9c1a5f18910a0b75217620a20605d846db4bb069970d97a020660e39bfa034f03d7db9bcb0cd08d90a4b200fa46df4e1c00ee31574d6b5759301f7d408d5274a1940fd8c9c777b52e2010883e90300dd46a2e99d4830feb370d68499edff02403f00419a951a55c32c7f59ccc50c8ae41fc15455235074953832bb0aed006030963fce7902f1600505723242c10c0c0007b0f2ebbedb6dd7e020bd8a5c0cc0ec3a7ad200f290bd4f3ef170f006b95dc8a0cd6cbe901003ad18cea25884d640025c5009528c2eeaee552d0edc00c728071bd00a2f300000ed15f939a004fcece7a14b26d62355c9be3d8e644c3fc052b805f8301c86b1c89c76a2f5647a6788b338b5da29981ed863f5d64edd460ec2fc13fe9f27b4440172a20e10c7b20bc481ff2d217f3c9d9be6ab8b9300df8f2db5bb9e3b241d1ed1cc3c67e8af0fc96264de2422a6c7e1b3d0ddb9a977e30090da47032ce00f0f16c455de04c3c7e4bf19b88c17da1c18139fc529a30fe499a72abb2e472a8839280a0fce958a581c3c712f6a4de4531624311d0a3578516e67327bc37d456092dd2e228f6fe034202ab52040c20ff8f56af28473410f3d2975abf7a568982d5ca030910ea466ff5f05a3ac709bd02154192801d36b45f52cc793900fef4ebeb6071e37bfa188b17c11218df57a0001d2174ddb970609578f386cebc6f050e040e9d13e93f4f05d055605bb4ba02c6e4c2d980e653309c915e3de029c94c8840bad31993aacc714a5b4d7ef843417fef86b7adc2c0fb60829b541011c00091ff844c784546d193fc14faf3d1bae597aab48bd870793baf817114686e803d8efb6d25bc353188d0116befc5e80fd8d47373d6c1a350d75443f4800a004a23c3f7d838a9bacb2cf59657e94e0f75b5cff1d8b2837a415595afab5b48f2f06d1b07a6d460e4ae7454029013c3d150c005250065237b031033d10ba7030f6257202573175e0212c4ddb34ac931c02f2cfb3b7e4bc5b9e2fc15363e604b3aded8200f748aecaba12253300052b61a21c9dbca79d900fc5222b60cdf9b0e2bf8c0a9756cfaa0918c04600717500070726602268416766a55474e0b59722069b704a637347f261940622f535343e2556e78602f313e 0x3eca5b1c4c37d480e96dd4bc81e45b7dad4dfa91f77eca3171c8f580fdae32c12384301bac3324912c89296a147b848125004f5c024efbea748d1f1bcfc036a956bf3fba66b0dbf52c760507c0c3d406f378ac790004b7c8d02252b8240139f4ef036af5f7a075113ed05019c8304c1e5ec924c3be54f560c3cc01720db9fbc6bea00cd0e47ee8f7bb1a53dc0a94fe81878fb9c28b72da9c45b1a5b60dcb35815aac2aad26b0d3b8903dc49830d9f75eabecad0c2c0c028431001f6402c0319f208dc980c253cb020333d38da886001492b8b212f343f42080da2c88f5259a389d282b87a843d800a1442081085c03ba54336107baa92179781d7139fe7a0b81c0271ce838814505a1df80f26eb45d97a28fb3f97c487dc0123f827f7a8402324080184bdd6533f01f7f4562d8ec1fee5ec36bf613ae9929ed537248223b1c9b6e1427932a7854250480a04c7d01307c08040c018c80764c94355cb01148964d5b94446512c048c047d3cd01c560d14140090280896b5eb0224113dc28d2f01588a4508d9c06a60d46064e0b73333c1caef5fb6411c34f077c5db37e3b2843a1cc9641f80df68446378083228a329a621aa2fcd58d00dec6ffd911340c1f1c867e37b9fc0260a7ff00ea20e1ac1745c2101cd5af0f130458c64be707dbbec4412da6dd01b006803f4cf701d540436923528a5bdbce3a6524bf77037baf8f0cf43bc9648c83ff82329cda8289dcbc38c742650ce036ef34484970b61a65d603bba19354508b169efc5c1137f66b50eba17337a8fc54c81aba2d85e630ca8000db500e5011312ec225e8897927ddf5b25bfc48a0d58b18625a635e202ca7d83e8438104af380084f9d8901415e3342a5d002a4321434e0378c9f839a5525f8438cd37802b64e6f6353b809347c6855c288dbebaf82170294021f353aa3eda0c857414e0140f1cbbc640d44ed63d190bfea4d73d98caa83f835376dc420206a7d580d429fa88bacef5e43ec3465504e1d13b4026a80122829cc28eb574d18a80679af844e5b9044ae005dd6894736ba0da68b0338231bd136f5efd84febeafba449a203ae15c0d7c394c2050ba5c6a5673fa8d15e45fc2052231f0e93ad3b455563c45738003c710e54a4940c182f94807ea54df4c027de311a52d11f764788a27940c8bae503291e0f88f2542cdd8eccd005d4d1cd06b2ba0b8ab756fd412cc03d7184e77c6c7e5151e1c504f51779960588ba3ef32c9edb2376f016a77a6ab13989dd75027ebc1865c1056405b94e5bef25b4fe542035f1bc33f02a8a895241e10f6dfff235f72b0df59483c26abe8260641f2b60b51a4020809beba5fa49936140b976c35bc0358d7b3f4ea217f0c27b7e7d6d05994b228e8c8ef7ffaf2c02c0c2737f5a741fa43978aa459384d57472b18cd53e5c3e11a037cead78e6637782343a7d85201fa534e6a49f80c54ced70ba7a1884e22a6d0c2522e8c75de69fadce8a01b68c07400402d4fc816c09cac17d18001d4841dc100f61f750d44f6c00491f4200839548641f90d59cf84041195e01ca0d40038c9a4a3a1e1607916843c5f2d814fa83b4e96c651e16e01084d2ab84a7ee9e877ccef01ba7c843708cccc8e7a93eb32e6b0e4a45264bdc0cfac2d12099b92f84019027a031aba0841cf7a8ba59c14891d3835df801db91a130a7dbc9d7cdc0ca34301d65d4c2aec0aafe607c0ec2a9766c804d1948a0ffbe9f7c2b2bd23d9d28cad303350c64402d3311cbce86454cbdf4b388194cd3c0102e278c5c3963df7f52dc0e988b56c487f251fd040d56c80268c301419c08f333fc3ff74226342ead871cf7792db5c2d846532d73ec3d24e2b1f56c0002d743fff3ba1dc3101701c885fb7c8b0f482cdf8d83aa3006c9c18e8dc5368032203409213154c8f768b273adf0bc20ab27c06f8e499eae4940618ea0e0231ce043c5afa6f1a5b59027252a5d856317d7e4abf0727b670126d20d6423421e32ca4050ff0405ec8c1fc006020451b03d680e8b2c6bea6e2ef2b530b95e30d1063259c0df4d0cfbe88d10de7662f3887356b302207d4cada771dc1a2e214f578538263549c52061ed6a80204275eb75bbcd53902aebe5d80dddea289661f5cbe84bbb3ce3f66da88212e4a59780e51052b0200fefe92386680b6702dd5390eddf4c156dea2ddb37f1c84074e55a2057a5614de953e23555a1380c9cf9c2184ef019b1b80b5e337a9f0840d4691a4d575005d9) (pickBlockF p 33 0x4b8c20b1ad4d33a09829562725822b7721049840145810450527d0018d66d3753b24e9b945cf855d62801b73493c62bcbc7c294090928e15dcef4031c31df387443ee38025b0dc4b58bba1d23204f532f73661de6cad56087bbc09cbf37ae2c0d76b978f8d22b6b39783e6837e03b2a885e2c40c4ebcff04fc76b58008d12364be52c10bea1a41cefb620acc35ec1c01623701f0d641449b48cca0030a37db08f569175461d34875cbd9114c93d4d06390aa565c55926254ddd586fd98661395b33a01303764c3a97f2be4d23ffc5490881490f53b5bea29a6027d431a9be5f502c525a7a2f83fc8c45d49812f4160d84185f0c5e67496a70f83481b90f9e103f9bba40d3e10da60e6803a02aacd3c61c8b086417bae7e2aa2cf0ef5231001de0f0edc285276a627cf029cb41734ae4a949be703afc1761b0a1172100f304ac0116cb6e1fbb7eff86ebcb9e419affc1c910aef2cf902e93a9b5a5187a05bb76a61109e0e8b365618e896c1a54fcd781ec3296b95be4710bb4399d3cfc0c6a53eb477d36ab9728c6321400f47fee325a8b00bebaf32989ad32007fbc3890d9845acf21085d00b09ec077029c13a729ad3147cc0f32aad0bed97a1dbe4550add08dd30af7018d89b26c1800c5a1b5afa28d47dba276da07bb1d8997f1580a4350000430ec0a3806c14f5c52200c14b26285a106bd635233d03c5203c4786d09a8ecc0ca0a02559b8169164a70a030ec3892430a1f71d146871b4e51bb119e016697740ca905d4ea24a06b2a4cb5bb826c37307440a6da26705aa4f44600b149d0d5017f09e2729070dc5a78d6a62e47e769f71013e120ad4073d8eb4a0d2f07a3a8af324625fabcffb37e4e8d25569bb0c509435f1d7dd6060e78f02d186de00bae36d0050e9857ad50dd320e97260b3c68ac46126a90df012517e51a9416fb04d67280f48a8dbd3b820f8e721462d4ebd30a5328a4fc0f570d44009d1476696856d117a0f0608c800360184500d67ce36d43ba8f09261184ea0b355d568c7d0653a5c70964e253ccdeeb1d50818edf53a20722458c74ade254893ad6e1c543049202301aaee43e834064f09fb7e0652bd3b01f64770dd751e8c97d11fe48998000f3013cc23764f72e529969da4a30676e0d89e04abf648efa1e0bc0accc44661a7b5fa0612d5b5c708fd46d356827c101d57dc88cb3fae6f3b2f02bf21e834d0b0cf563804d95ed38e9d6b0a4cc408d5d057d880c4f65e3739c30750c92fccad88fd0a1d0405ea3c232dcd27b784b4aca232790a10764c1730be95479aa018dcbff133132704f5da757a17256be67b4ffe3552526f460d0c1489c0a4000060b7010de77aad126aa71b084d0a621650d1219419222d101b2ffd4c4628a306f8042ff9efac8905e684313aaf833db05d057a0f91830da051a403ee1800f85ce805220b3dc807871f03ce93e9dd0eeaecde6b01354b8b043075cce08dadd0916d1e52e31141f1b0f00c0f00c398660e6746b89e000aa4b813306a0c30d3adafe658bd6c00b00fd3bf4ecfe885040f9dd4aa6c6114b4a2c19191d350e7ad7383102efef6bd2cad5ed660ae91432f938f50096c011150028e40ac86fc0485fe2ded3cd7f50b06002 0x9c334584bbf2c1e4f16fff4085b9a8030a76ab870caba0c69d68039c54966cf0324cb3a0d224e355d02e5800fbbb44be4e61a127257bcfc3a0545b6360b70d2603c8c1604a67b9c321367381fce90a46cecd7d82edcbe011701c39556ced00ae891d9d5a8b2aaf5c0c735520a8609d59db119b1d1a0b0d7b26f68742674dcccb5f36c87fde499f5aff03d81438ea3cbd4cf9428076a175a8fb64ffdae216564048f4a379d180b83a7881ddac17dab782773e50d83c0beec80d1206c2d702e5ca848751a9070eff1145b06bd4b2f12e008e0220cdc0aa922efbd72c4d3ed252647a286fee4281393a92226b437cdf64c03c0c5797b7068005aef175f6bac47c6f607213c2cbd63b2133f0062f2a5abc010))) (pickBlockF p 37 (pickBlockF p 35 0x49809d54c60bd6d01ec1826668ea3765dc80307c4ccc31dd4181c8d82044c14e9e4a949788455020614637be4c220466aad7cbcab03e6c834241b8f4265a3d82bc62b8662189c5080418d0c040c4880c4588440085499d5518111d9014000598d498e4279b9782803893824ddc4d4f549c49dc70760c97ca0c0839356b6809d7723c09cbf5de419ec52d4bc4053675e89d4114999b4d1c8040193005950509d84d1888c90010c0085c40dc98895106150200d954c8d1008411408c0944719c0d49c819cc1100d7c51c8c30c94c204819d91c438f0b734f6f4c1639815585cab4ecf3c2b2f63b85ef99e3c343a3c99532fddb1b4d7d4860ab300c1b046d23915a890dc5866a85e88b46a53819c039bad63e46c24e29e0325b1b289724eb9578097455834ecc0d5f18a98ee40a53748700169f1f847c8a30dbbbfc1f31f90a491e2659979478c6d78162b72711262a036e2edf38d960d370006d104c26c628001e90425ad4f0699d07377d3567af008413df1b074d94201404744506e7f70961612d743746e172432354810763a32 (pickBlockF p 36 0x1cc70a09ab5b59e527602619b8010fad9d1405e08207a38086a89aa70c046475359ea01159bf0322070079750764a66383fa3656610644627b33257ca5a652fb5c30c4bef03104a0be54f6bec16ad17071a97a84e171e6e040ee3307022c59f8a1d492505d8b5a1908ed400fec01c25265356bdf2abe9708fbb000486027f7f7a7d20d1cff8be05f2c847312506a3b6560f43cb2430c879c2097f13b6e12a53a2980a68590302033de0204ce0c7e3d87009d949c774c3e05948a0b8315616dc346d6e8c0850d704c75cd4e03c573961029643fc8daaffa4f2ac99de3070403edc76ca359ce4ca17c6f8ca2a0f42000ca763e9e2207f55cd73fd1b7ab701e009fa6f54da0269985ab614ecea5b46e2110522403a03cc7711de5136e606210ace0f0d988045a9aef457eabc8250586309ecd8a22abf40ee8d7be7c097230d9007ac79d1f7bd1afcd99a12f5ae97d0aec956f8296017b7b04bbaf23723b20ba315b0e093d31202110aacf1fbb1510134938ab04fdeed00772490cce28e3fc1680ebd700f6081e943bd9cfba081e01e62ab6bd20f4d3bd0b9ddc63989b109f5133db23b8d20c785971c33b26c3007efec434a9b60198869ce109ac477af0a30596ca5685f60b410028630262d2e662f4c5cd875575a2cf1f162008150b9506bddb0706623a64d6fe7efa3701e37c2db153f882e7f894470a111e960eb5728492b9c63e72740f66e826b5b969c84422deab9f86973b8aa4daf8401989e2581f01ceb63825af65f92374bd820dc3042543f4800390dcb16d14aef1c38c3855cd916b17ce1c15420568bff17c6277a2bb1836df2408a0b2e3e8ad39065a33cead9d26abaa612c77a81581d3d378857e5412683a30855d35b4110e10111dfa82681a01e157e11a884df9ca4f3bd441c7acbf7310cab5a7c45341b79be00d3c81e36228bc50582cb485668c46feccb91ca 0x40916e2795f49829bee2742de9d8d0654f55443c522e69cfe831107e85c14370b563ca7c8177c411021436e8669202e484594b217b79a1356a23aa88dff6af9dd9f7e06ad1e9b0f3804274084eed8302cd05eb03fc2f0f49599166bfcdba5d31eb4dcecf42f2805a071792ad836be045c039280f303a0f5f7c2b6414f574ada8d83707fdeb00a54633e930cdf43f8739c4d9420d39c27074296c47f66276b43b67fdc7c9001018fc23f387d331804ddabce2fe0feb7ea539d0a1c83c000044d0066d084b06eb7501b8771aa8e108272241cd63ed46d111b7cc19a2f80f7e3fe1d48c3a9a8fb8672af5aaade9af3380850bbf03384ae714ccb6f828d76b2307c40dea127da2038d304f7990346efb80bc3609786471d1c571b816c830f55980139b97f55a03d16091a0067460d1181f618afce027c66bb9a9f36cd8102c37f1873673ac18f8de4838291d948f4a77253438e553d81b98c80d685fc5b2ab8040c5d200d7c6d2c48009798239e10a21c846614ef1556157088dfba5b9521c4aab007d1ceded21adde2c04971016af8cf07286ae3b51c25a70e4661560687eb74048297df430a29a8e9b66f718502cbbb0cebf65ec3737a230403a08098cb0c8ac43266a10e61bbdba430449cb47350c29c25c45d1e1e4db7b22ce1e02f6850527ddc8474d579ec47908403a43c9e2f64f2de100866d6ec6ec76d21b35f907b1e076a684590903fc170fb4213a0b17a461b5d13405d010e2105e53b02d)) (pickBlockF p 39 (pickBlockF p 38 0xcaa13803e1d2954600b3c2a15d08db4dc4ef9d6f8a0aeb280cb8a64080df8f99c6126d1e25aea112d9d08eeb7eb60cc2b1ef035636ee6416bf12ca0037d2a9b63a63bc64368f825500f00010e182e9884e93cc20cc62400c50d0f43143543f63a695e57a8cd2832516f7b337b1a339da02102ed06e36080e348462ac170b28bc416c37812e93b7e95c008007b7dfb0042a0708029000e02398b02bc7b247b633bb26b3d54531d624efa755573274255ac09aa11701606c88afa 0x1ed038d12064de6510ec05d902c2ebb84dedfe8164dc3b20185f5bf80908f6e402e43fd57e2d5b2214184001a017191a2ad70f42f88c149a27bf7980fa4308201bb12cf7821cb2142266f0ae049f82e00dd6cd9b02a370c12b4d5c95fb8e67f48f08aa4454608696921e4b20bc59e7a3785705ee4dfd4f4ad56b27b5ebf88ba1b3b6d34a9ea17ca9a4e4c2ee0a0be608c2cebf36f772e0600bd332e73260b29e9f5b65123a6de1981d08c620c0d1d4ed3943e360e33503709575ad3588b40499f3a1a9581f0b2526a6017d76bc97e5b9311a80004dfdfb7457ca7f8044678f011ae2510003ef2d71b4d7c035d0c33b898466ee187f38a5388000097b30da943ad4fc3e2f4b2ef596eec7c013dde21117daac80003ab952bec541eced142df107e1610705e64db68d06b261d59d676687053aba7450c50cd1f6e06cdd0d000000716422a829ff60d7e1b1e64457110a37b35475dbb924c79893f225f04de3d11454e0b1830988b3959e024b9af265d9c3fddc6ba8c460000) (pickBlockF p 40 0x267700f00d01c789030a9339612603548881b2906f572112fb35d0af2e18735ad01440de0388e4049ed687f4102b6ce596a9503e9d2df4fa203611390dc311b0fb5f4a9d6f39a2183ad8f322220e04a10f7b05cd28a657f0e3d1d435c8920b2ad0608b92fb2dafdbdbf8dc2247aa2dcf3992b44c2ec0b8a0b0f5928290e92efaf167a5d2d80bda304c70bf48954d04d52023742552d10c44eee31f715b4446501fa525fe4aaf3aef5a4da22430a307926d7ec890fd2bea9c14ead853f98d89f4d563df1d9fc520cfd20a7f990146180f3b81f6378f2bf01fd7054492fc7d608f7ff06ce6c597e1ae4ecc5ec1f995adcff0a7a00d283e335bd92f6c122bc01fc34959da5311cdd97de78609150b0ce703f0098c9febae5de64f8492d580d007d07a7c8ccf4cdcfb39843a706c5b4ea9f65ca5717b5912e6b9978e51264469e8d53a5edc0cd7b4ffb8b0cfb5454b8269883f9b42d603c47b42f8c1441126e59cae5e7318b93f0d13bd5f30bd3d3c66293bba16e32c6e42bf3f5a331d5ecd22c229511b7084f3da828d2c5471cd15ba8735a8754840c25dcc068bb90a5ff070d18babae4bde0a180eea167e5a3ec98d2a08066241a23664b33c8a2feb790 0x8445c690c83035d068785b5b5c31ab5d56502ea58be378d5649174d4540fd03784b0bffc57033933811811eac6dc61c75742db70004cfed2e234721eba5e2dde271a8418a0554d91ea17c63e89f225f73c963b95a40030704c57c6372085221066a19f00080c8350310069badb40440192b8d2f939732ccbdbf6c737ae80a7750901e4ea789d7efaae3a088678cbdde07387d2dc5a7355587ee313095d55fff84ff17615e31f4263326b226ba1d8d04db8768fe1a480681900f4e5706b215b6f3a7d214741958fbc7e78ef7072ddb8170a6d3b667144bff5203dc0d0a87cf2e95053261cb13e186c9f68819e6f3aaee01de3fcb1a7d0cf2de0a82a9ee2a062e3b15c679613b45b120d2beb3a0a97545cc03fcd1694776811808d9c74391c29746f413f0bc5d0f2a8c04503ad1a01f6b848cd796bbde170c3a10dee29d3b7d87954606f206668e02ccac3ea206896e473a3356bfaf100420c57bfc6f833bf7f36768f7c29fc0869f0a14bb9752872e358cb737e6b7bd59c0988d04ecd74f49d039803208f9094e41d31506163fa757705c6233d00526734550f211718008da6700720bf844eeafac9b863c8150d193cee2ca25c249f37af9c9d24dd1db09c8415e91fb9f67b244b401ac98086bf9d816d)))) (pickBlockF p 48 (pickBlockF p 44 (pickBlockF p 42 0xc2b4cedbe4d91c1a690f57b20c962c2393761c1b2e7a0c3b5e2bcece54951d30668cb2a2ed329c00a30e96990cee6c7222429da025330d09382871bfae9d704e34708421047b403f8d7987ecb019e9727e1993130c141dbd5ea172bd03a7f5975d3acdb10682156d3001627554eca79b3ef72ca1a9cf4dc924eabda9f6f3155717fc29997d45a65409dac380914b2d10c7065865a5b7d3c7f81a8c0217c1c8500a8b1d6c3b3f4b467cf4b11d52ad875c877a96f3a1b7a771003e1b92d22f300b87d8cd173202e732cfa83c67a0fe23c879dac976202f91263eb54000fe47d80cf54523f38be02 (pickBlockF p 43 0xd32c6c099f7b129c16c497d9bde0045fbd11ddc628dc3ce078403bf28aed5e03c8590560435aaca8220185ed1a71d5e069868274c8e0bd282cd9d08420bfed21e012a3b6c43c90d2d6e68230386891ddf234dc84d839a899ba331c25262768c5cea00b05acac7600349023b3ccd1deccb078632bb5762de93ef7b1ee4216d75e4aad9ff699a54a48d87f7c1f3703f206a1941c4f4d3e63040b427c5aeec0aa531abce29578701234a4e92759879f411feaa3a46d8a13c028e760b61af8e3ce4a707621aace18a7bedc6c083ec17ebc57d8158c82ad9bfd4e2c73a67fe845c1be1f7705568014061c2f829cc6359208697400035de0328fc31cf4965c18e7bc093882f5e394fb43a81d89aa3a8776ab6115c3a80b18e4d5c99ca126bab3aa66ea5ced3c259eddc521308a4b64fdebe2bc9da43d9b8ff71440539dc97c1f4e23f037883507d4053dc3d40f2e8dab8e412ed3ecd670733edc5956c705c153c51a4b8daad2c4b3abdb604994bdb6d58f97a01355b9f2d068000003c24a0082d74afb9554be55f9e778fb8960d98dc21726147c20ca8da5ef70d0069c21bc9d25cc7dd052767480839e228249fd800582e1d9c770f70f98813ed38072d67b87dde9d2 0x4494b1b5e65ef1c81920484867867867ca0b1c8fb6d148bc53283333491f88b0a4c9c54c075447eb00bffd0623aad0d17e0f99260a08698a73ecd4009032cc3e73c054c4471ca81b1bffdf6e94f3fa72a316f9c3be64581194c0b7e96779708ff8f8425c80abe24e560dfd81358c9777c4d2159ecb2c43417e041eb0b9c0398cb5d704e5ffae2d9ececae1735dc1b4138781c022f8270a911a2990158be2e164e477a777423e60934e490b8d9a424e43e890583a219ff5f159a408b180210b61fbc0f621e4c3cd897f15b48fe4b03fa0508001a4290bd5638202969a80a59121ec30c322817c3bf838d1bbaa93ebf60affdc3eb84651cb249d6e57298bf7d743af038792df0028340020c818eb94c7cbf4302c272a77d1664d22880a7f9ea76103b48096840571425f9ae09599006591875c1d91e7473eb85af891f9af481cfdf9e001a4e5a30ff0017570f81820bd20fe1c754e77e716a8f2bfe7c1319d840923026078f8d2fc48de400b2b0d0882f1afaa481d607de6ace840d17c9229596f6907aad35d056fceb7dcdb53c346101454c1d21f37aaa143baa829fe0002ede86b0931c55f26e68b820575477e7780485d81cc7b3922a6dc727bb0070ff5fe6dab2ac3e2b6cd002e73a1485e361af62a3d306d4e4f7dd28087c82ca5)) (pickBlockF p 46 (pickBlockF p 45 0x2f7f728455ec9f7d6d7e68bbc2736176b1ddfc0085409c0831ccb9697006f8403410cfbe4494ad0246db0c66dc4d9014d7fc730e3cd8b5be8935c1392210df1cc9a1fb23b41d4214d8be62279c4b16f61bc332fb11221a7d5cb0a65ca5350a301acd3a0d8eb4525bdb60391281d9f61500a00d279363bf0f788068195bfc31e1326800a1e00c812fcc602f84900185712e10d6f265545a4379572bde14e34d55c3b02f9e307b625d28fb66c249e955d05b8f81947c64f503efab3a294fe62efe03034f94943d396b0289613b5f97237e200815a8e0ac00e180c099de013950ec5a141ad15af138ba6365783ce1eedbfe1cbbb30ab1c031b407068f81ed9bee635de1f11e10044c41688096c3266e0985181706741020fc12ce97fca05458dbb3e6e23fb2fbe37d706ed1d409fccb864ae20f744c0ac4bab39d1b562b7e2f8dc583813aeaece0fe634b25a28818fb90e9ffd069b226417d224ed45b1fda19e02398df6699af0b594035723a10b34014bf299c6ce7a68e3a3a0704a6e933fb834b221afe2051a1fab6aef1b9ae69454f2100715402bc0587195555dccdd8010844340059401436ed0b3f9d1525d106d8fe18b4830c305fc437c99886a40c88e6180102 0x311092b98fa3a64b1ae3032b10cc12d1a30c41e85a78c520d88347d64569d1b5dbc34bb482e3814aac6892646b308a0df6b32ca5dc38b4ee861aaf9464be459f8165e902bdff3f7d1fd0135e0ac43adb3603c1fba7252f838f902cdc1723d5f38f2001a248fa6ddeba2a94e2013983024e8fb1cf098e7afbc1f40c52daa30c01a1b293e208edefb70d0a5967a1023d7fa108216614e77ba35a8a2ecca03d012598475d2e3e7adcc3abcdb086730399ac08dabf28bd5c182a4153de2d9f88e21cac10dc241ec0298dca80fc0178e6423cb3d35aa38694000028001dc233bb6dfebc4d01048798a1be4a13d02083c41bf9623c118d54171fe3a3529a8e006bbda1fac014654eaab9fd88e5c783bc725ed09c67ba7bbdec18a3005659c2118ed762c690860f4da8efee401fabbca8040a07a9218ef25db9783c7c14ccf07168b51cd8122cf716de01f547ba2e663fd544d0d110e7e71ebdd9b6c44ecbca86e210e17a07ec765c02ccaa4d38d42c0bba22d948b9c34388a0640e80901ceb82725b305c381) (pickBlockF p 47 0x514293174f51ee7a93fa1e19be3508991dff823834186886300481322ed352796a9507e4a4db1dc5b26c1d05241402722c22e82480342389df5f994d1fa379392fcc4b4e009031c2bdee4390a81550b8721d244f9800375d21e939d3c8570bdd508209c7c0798c4e78e7333b46d211c4a562c97820202d7bf855059501680639465ee4330b8586c185d4dd335d821fcda54e4d14197335544315202c05909c4e2ca740105c54383abaed80011eadbf21eb2bc84b606f5add7202836086e464196249838d4587742062b899b1adfdea8dd224a70d0c035e85d0801283a55789020c8131c9b29dde533f2636f50219cf2c700207239f807cf1a8a73f98181913c387091e8054a0266519898149b14c10d3f422acea430fea8b7e6646e07ab95de220ebb6f8d615ff1fd268aed000e06c10d6e00409ca141edbc8006039c441e00a281c82b818167a4000306dfc0c1dc2589c002afc30a50ca04caf1aad0a074c3c0a4d812d107b880913cc400060073ef0d2d490e763c3802ddd3e4448083355840284f18053074ec23c1bbba65e75c07e0b51ebf5fe70a4f0cbdfd442d5009daf133e841f1433bd75c253a972c5104900683d7cdae32906340d9d81b71e6f1debb118f9bc45a389b0e6fea85db6166f938ab2462e67b48770ace04fc025dc24435b913dcd45e42dbb33b72a9c8081416418c36a4f64f3776b83e784389c7a8e391d913247493c14e69ed46ffe130865b57abfa4b6b832baac50b3185431f3f957c79164ff0b1a69a0a9e1a01acc310294df20f9915c10180006cab1050582db6a8f257dc484083987dfcf3d1240207a476fdd2a7ffa2eb0095b9c75d919f0889601e800caba887d2e11803f34399fddaf3801c089eaf0142b99c2a0e76a9bd8112420dee6d198027df33823ebc41035afb81ba499158405437c5aa84a2834f8d4418cf30357c3a8027d2b2e3ba0b11384d2805dccc4489fc5122277527c2de3ccf070adb08078c24f36888aebb5d3c29a97db0e7a389e40392492c01ae084237874b7e4930a0ae090a4601cb535016004f709a94c437d7d15464c3f932150f124e77796c21fed61fdcc4633527642f8002890269860a3506868d2e061b448342064434c3891b1ce828f6332be8157a1000649254226b046556eba949af5cf79bd8464bf4aee1303ec40dc088002531c2fc4ac9a03809bdf5d24382206f8ccc7733570f2fbf6e23643ec29898e2b2d2bc205377470d8bfdc183101e0d643002b0751bc000dbe4e55f7f93c3b493c361511f8bb0780b9fd4f47b7bc0f135dc0405283241f2595df8483ba81d8990881c0135bc7c5817ec8ab6d640954865c1c003f61e2af473dd0e702ab6edcec9e0ef3c11a62fe8e40f27df843e3f7311ad03adc313f305a9ba0a60cc1e0ffe7281cfb9330186379940b01c131f1ae33d985a5a588268900 0xa1a96728ca966d6d6863126046e25b81acf0da51d0ffb68f28faab868894ee00003ec5f6bc626e820a141b4320f19568cecd2189b9060e8da34c3146d6b01d69ace22eedc97e748f2ae2a9b71374b400f4e0bc95f068b44e024be7abfd2a97e741145029349b91208df2ab0015490c5c954735c810be61b5aba77a6f336106c495f60a1427220171bba73e90ddb0b83ba4b94045a07c477871b0b780971c739bf2049b7ac000260b380ae3141d4702cb0e6f0d2103ffdc40d32660b3f3539cce0ab4d1c4cd8b955bdc06e520ed530efe6dde1b8ff3ce435228d500b8165dce2724b43ea0a89f3ae9b75103d3703ebc8ea0001ed4b1b7039c0e71a0d920a70877117ae9c98c307556d820d1c475b15654fe058889cc9a35da3fb274a920abfa0cf3c8707e00656324eae71adacf0e035d78283d0cdf1d1b12be1ed543182aba036923f6d6e86e407f735d985b10a6b70080c0060aaba1572252f8f947f5040d0bdf0b89a26eeed1854c3afc814c6e06f0dab64db90b8b7067b2b60894d979af628409229c0509d7132171eea7524d780bc703e90868815cdeacd50f64888604d3051ba310b59f6aa0033a411a7dd2faa750676ddb1953a6c077fbc34dc64420f152e460d1a8da73f2c9fb046536d5daef400aa1280eb12152520d7750122a7d5c5f905138911e27395062cac0128039d070358308a473b35b3d24090eedc132609000302d0eb7c2c95342622404901be2157643c03b5dfa6bd3578074bff6ec94760e00cefcb6c27640050a710ae32096060906b9d99de7433a5f7510d049a0d0712b0c2a8f701a6062100107f00a17b8370361169f513825931949e49a00060bcf0eb4e5f55fc0083df2f0eb06ea0d4701add63302c190ced347837ecba562bd5c4012a00478452cdf7de829a781753001a330a40550f25921d8f6490fb024c4e0be7a803d9354492aa30a274a2053e870c3e4248b74515949bd1dd91a81501eb5a62ee7ebd0794f2a3820ec2600e1ba6c29be43807da2fceb2c52e0b83df7228db55c12c6ee963dd9e4e09ea9a218609cb8033d985c3f167f3f2546881aee4d5282d1529b328ebc842a02968f1f0085449e))) (pickBlockF p 51 (pickBlockF p 49 0x16dfd039c2f85831d2a5726078a2e3a77c00331f59743f35f75fc4bb6a75eed431ad5b4fb56c0c11d265e14788bfadd830073cc435ae001fe6d4926e2ed7b02b46837001bb0a941d7783fae4835fbf774a1de67884e281218a82c00079f2e742ddc19880983c23ca8c254bb9a25d5b2115ec18ec88e41edd13a69c2ff9381c1932370c583aa4509ca83b81b94d04453500db4f82aa22fbf8c10c3503b6e72dc3a5da4dbf11d010d75b9137b928e07ecc8c0f5fdcc642cac81db34b7899d786bec80e41182c6db6790336c169ff3101b52d2207e553125f094f8ceef47874c81cde800c1993e83b746302a1bf132d9794d830176b26fe9480f3df00fc20003707c096309c60acb4f0c1f0ef2a0901495c791a4caa942941b01d66922900e140ca53f0788a81de92beda6c677243fc8118f6da797e112cdc2d3017c20b180db202908b2fd3f1fb4bb19c4b1c86139507fc080139ba5d21b82a1e30c1670401c7037ca12b6da55dcc8c1432a3287e17c93986eb2bda5d4708fdda79e9d9785005c154192a58aa1a0dc2c8011ee300226850b7955c026517c83d89dec93b8d537f586a5404c00c3c53f4e8b6529e63d6a20d84dd4281ce3ecb5be5c3600621cd47825d5c6303752400f5d3e828c06ccc91abd68fe4e5f5d3788371def740e70000099a60c30f7dea1e3d7d6a3eea06f8183c54a5e2c2994f4dae430047497035ad9a2f62d8212ddf606abe97068a42fb3c78d8b12009ad0561ea9bf9a0d6b326cbb28f46be135e2f93b6d7e7d6c1062880ce57a41272b509b781123ebc8cf0f60fd0c14627a230df610152ac09988c4eb556dc81471202fda36ca12cbdbeb3e7605b5e67cf8112294f3ec39007591aeaf36e5e308617f9815673f023aa3afd0bbf202c207aaaf8719bf (pickBlockF p 50 0xfc0114761cffdaf8f29406770b3ef43168b43b928167485f1c3d289d48d4d94eb0c46cd3b45c3e20682c278aab032e9b50e94820917563dab52ffad94932ee766bb3db8070d488bf0434deb6465fd340383c361d0929e347f5ca52da0f12adb34493b279249fd02c00f99f0d019df8079d8169243a4179d15d36449a7574e7571e56cb7071851b3ccad0a947f5d4160e3d030199dd8007b63c1abfa11bcd6d05b965d899a37904480edd20320db5b769f55bae1040fe40250925aa12ff9f4a67a155549460aae68b46fda77bece040a1bb0fc4280b689074e16b345b83d43a951a9962060735bcafc939b9c19ab29ed90234e70f223e957fc8ae43b842033a0d63dccc0afa7510190daa98ede75e66a76eb190fa34f51df0d3f20deed9060074321df4085d7b30e224dd558910da8bef00c98697ecef0c4c6e6330d96a48106800bc8ae7d68f050253f0576fa29708ea8092010e852772a5349b03e39309bfc7a394ae044222a0b72c8715a445adbb7961de6c2525a205e84b657d86065fd17b77703cb9bbb6b7f3facc0cd0f09e4a750930216b57f02e8c852cde89972e676a2530365f6046b281a0988589b6ad6f24ed7444101a5f31ede5203ac906ad3ed98c1d29689f7057ba5ef80000010bbea306f7ad93101f47ef2023ba978a4f29725d968ca8580d9f8ceaba3cab6c06e06f9117f8b4e52d62e88897516da31e00daad71ded35f058937b8876070aa962b4990353ef5720b06cb5a4fb292a00 0x6087f57dfe6a8764940bca4f6d1a8141d9562185fcbfc2ff988a53168c5d43d0f9fcdbbda005a6f752ba9219c3ed4e985920128d437c4206e9a302e49805024ae2ba0a7883eb6fe85e179604c73e5b5bea1a01c9744852c9f89c700025aa2ea6e82acb84866b255e5b69832dba343ecd22e9cc90c22d6a72552d54a61391266392659f036286ec5840c8f42fab3fa8a0830de8121245f8b9891536318de39a2c8df701c67e00e280c156d4633f20ef9a2cc1a0fc09755d81385190e2c3d3121058dce47c9c9af4400073cfa511c4889915a010f911faacaf08960ea307c19b5f805b0e7511017f5469515961518778b94f3ba3b47308d099be8d9a1004e4a2e47b2d81673fbbface213e063901bffa93fce500b03dff75d1426d5672cd09d6ace976022c9c3000a9a202d492f28dc76a3f81a9c0feb6b22daa1b5925a7d22c533855fa308a36becff33a70fbd70a2057b9e33b7f69e8043cd49a090ec8bd1e2f938a7cf020bc1f4400e20230b7167cebc3b65ce4b44c0902c66a4e569f0061641228c0050c037fdcb33d40594ec89785ce6e02fb076a7cf71a170e9c2021096124620d2053b6541060515c1036d90ca2d073aa311e29643bf21b00ef355d53f51334844f32d600004931bbb063ad614472dcdecd20039b033d0e0d2c70d0b73bfd10e6956cc8bdd69935ac50d2ecb97009700f21d8c1d7d06609821dcfc03329bc9c7b7d9d415eb3400592816b521ddfd777fb497a8a59432a25d1ad18507bfeb7715dc0971045a3f50f00a53c1bcf2f8600ee32cac63d77937c8c0a51df2c1252cbca15f3070f7547abab18b2d0dbc150d85a8b56825041e19aeac174c048b4fa64c76f04f3ae790a19ec18fc8d5001781c15079c6cd93c593246e744fc213c6b710008b447230057392d1ea34bed864400aa34131df085043d0eb1ceaadc12f9980d1a3eb750da177ae409464b60232cf5f31ad8756f1d4025c07663f17ee1b76c91ef4b8c06cd30e1883a5088778f708c5502f2b2c087dd3cea103a140094932d6a0cde482e324697b7f183c54ccba8cca0b035e4b6cd09b8682587654029fd444fdd04bd352e1b804270eb7705900f78c60a2f67fee814c2319a108ab500133406b691c6ebb11a72380f9839a3a255cf6d1e1977908b8627208df8a3b97baadbe3cbbe4d99009f100a929b492e34a43f73a0d153ef0801aeee26220031fe32804a2309b7ad05cc4e36d130faf8f008415f5d06d71521d79c5a28de6a1ab85f23b3de53301932b4b51020b5711956170b1bf81202642388c1a12c03716174fb74e5d0dbcc4ea9ffb7a47d73a870e3d30a5817b44ed19693b0523813d0fc5e3afacd013757045f70ee9067a96a2382798474461ae557009134b9ea391af8f8f5fe9586ac1fb07b23631de37fac02b06dc2bd75da6001c0edabc5883b01b3f6c91871f27b0a453a4124094da9acc4eea2f50c314498092e936d2509a65c700e27297c01eb66042af9d6dbb808dbc1b70a25bc0756489f5c95816c90dbf99d5971f4e18045d4502d7727d3197d18f12439e1c165a44d76c3b0ee0970e8f07f4408817e4470db255005300309a000027f13764e0467519703a06604ec590195fa7bb9f3f5f16d5565dc306453002ceb459c97557d1f78703e2b839d053e0dc517305050fa747af7f11005ba76e3c7ee67039971da1243065d00ac870f97838766065650f00c0000615276164631d0a5011710206254)) (pickBlockF p 53 (pickBlockF p 52 0x150b4d1d2b69ff7d784c25f03010a74ec689254ad3fd70bf01d4dd054e5af887d81774063e332735439cd53a1f020b3ed131652789abd187b2c861859f3c825c2eef41f1d4151f32d7d050c4cee024be65701e79d392f6ef748035c0fb83515889ed07903c655c6a420fd824f15576342a024ea62aa8047193b8bc8e4a7b7f8425858609158d311f133243ae1fafbda1f83c71a2b6c3b97307087275cae16a614bac013b68a09aa5c0bdda3590001274e4da7800a2dc00da7f4f59683068770b1c2dee664215af1fa2c8433ea5e82d7cce9385bf4800f6dc71483a1053f880e1c1fabff591bc318f18b000d8c5cadbd5cf73905fed181f8811a3157383a3d1f18c2072643aa676086ba78da6c2fe7d220ba80e6672e8281683ec4a3e65ee531dfdadc9c7f897183c025c4929adaeffc583c6541d0a0ce1a1b08f8140880a763fb33c40a979de6aa9511947d34d505bbae0307040bad6275047c7f0f2ad2ae783003398087607a9226255427144920605fc075eefc10202053f682e103b04960166de2c6ea178a8499508f913ca3ffa76d54f46b3e0887fe78b2693e20caae13ecf6dc8ed622f0a42c80324d01d181c326df448df6a5c2989550d1d844788be543a650b080a801c21c06f205cc9020cfd5d60e0a27e8b9d219a560f0e1bafb7eb05304ed1fc1057312860c3026b51d010013c37ba7bbf4f1009d3f129160850c3bcb071e3017dc0379824772641a71055c59750edd7113431658450412420029af10ef00e5439d61638acd546c4c05a418791d3b6557401521800d8e3d08181863f4202a372531900aabe0398ed0506c83980c2837dff3812c6c1d13c62d6c07df4e657f02c8afc10f6bf7b95197ac76bcb82c7ab0e800144ba7802dd34b101001ab97809c7d8e07b3d14392c1be0da808d8d8022ea9b406b0214480b6aea61219022346c29d81520902010290332d840d85e38941c6649c50cd7b178873ccbb99a88db7e827039 0x1ede4f0713bf5989f61cd5d8b52117c839ce7f4844fc122b5418d294cbf81ac184b9250435806d89b9f8fd68b774aebaa0b98646ab84803da0d7ce906a4e0d140bf1f700d33a9f15fd2c712b1fae66bbf7a42043d82dc1a13ee39906d756dd4a91d78a57400d12f8452fb60655347b3bdbdeb0ddcbf79264d17a2bb7dd8fe7799489a09e1edd09038f1048ddec3e24b020c76a32623e8b77fc7a4a5f8c6e0299a30ed700efc2f16762ec8ffe34dd60a6c8e30df30a881d5058a619c17f61118606c40eeaec0eb020552c2e93a99edb726dccd170111fbcf157bac9d60f97008069884b7609141030c061311fd035a95a5301e0c31d8b30bb065bc3a7d71e71b852d0824ce9a81f4c07043d059c1788a81d777335c8dc03103a888569e425555c0017070079bfb14e32b59d3d171027a4941a648f2b6f39ed9bafb150d7a2bf0840aa96acf7dfc600c85a577ab0d271b1834e0500d1cfedf1174f118e874532cf3ae300853a2c6fed6e5ed56cd47b241f085239b8ea42107f952b6ce617bf7135861a62d074938503d2dc4fc1412e6573f7d781983dab7d707f2c9572b2da0996ce550012a17123cc06ab0200075f319bde37e1f5ba802d71f9d069b418c5c309e98b514199a4c480d74bd7b9e8b32569bace668e2fb8a14880e93f86a4a450392007d03ff5083356b1f5bf46900c051bc420a6b1f74e9c2fbf4e7b1301eaef2b3fabdd40409f05eb197e82029f96e116051749f48ba8037128ad2f268978216257d54ab1b7910792418a2a603823bbbb81ab240ce3dd8f14690258cfdea7108432cf9e0cfc3c1896e91037df4b3602b4dcb19ffbbd15f08b0a58a07f00cde0e5f1007073c80a062557cd8edb23e42b49e5acbe7d4072623afb0374cd3a4923a2a40e872a6251210cb505f99841082a209cf501e3285a8f620ec829010a2e7b030028c4cbf1a0610851def016d2843df8a570500018cc02dd19578727b1003577c289a00e696b760f3e03c1877cbe7c11500302240236f9d2b800a84fa4b4444dccc8c4c384d8a9ab64087b948204010bad91f12a2b1c240e2450b67513de26085d104e8c4e4da6ee09d00ebe8cd648cf22f0a887719d234c3ab2181be14020a98e980070a460c48a44ae8e591a80a7b03c1d784e0f6fa4de721445c05e158944cc7d678e38035800229fbdf200c6120d890e934b7c03ff298ff35982b268a47435f6bb20abec02646be44986552e81fc05e43fe3ab7219838d91294c2bc003711d1df12999f4ead7f60305cd775e93bb2ef4a4e2d0dea9c61) (pickBlockF p 54 0x375d6e733fb654b42b1c89a198be02727b6c2e68e50c48df224f44d00180bedc018a1f7e6d65d60e9b449e49813d1ded9a48a06d04f18e7f69751ef1bc6a7a616aba90b2748a54ca35cb507c1ca29ca9e0dd33c4033b791811100825d8893785f44568165c1c43f7b243a8f58012b61e38cb85baa2cc44f933a1ade8f34cb41a9792339e0655361abeecc16f41723eef1d49944f10224605ee00120daf227dbb58d41de2d1c60443647460325ccb8813d000097fce0822051c47bbff9749284960078135f9d046a6f22508147848e4ee151d5a1610020119b763b059ca8052e4f14967ac53407292840156c4c4f1846efa706ba62eece08223415213548e2c1904819c9e9b7f1832551e45f551d85aed0bdfd46f3242cc671c1a1678dabbf4aaba0e23fae40bac354c9bfae4f6eaa20829e38037f1d1b1009dc3f51ffc2408f02f0237985ff1cc43390fb4866f6f5bc0267cfc376929911c019753f9688e9ed475aeb5823d7c026ce19e0388ffc7556c2d9d5b1c3066fc6c38343afa43b718080000325f0d380e5755d07d31d17f8a8283bdc078296cdc3663cc71e338ab0056396c3075be2d45900e47dfe4fd4957474f35f4607c8224029e9aaa796e5e0341165dc1b6ea8bf15348fe7500ebc6468d080f065646bc8d69c929983dca681a89e74c0822ecfa3ae3686f0cd4586d7664148e3bad994f7f5e478aeb02c2aacc230aa3f2f5d41a423c02f8fdefd00000cf5814ca53c23f03ebc20d9dc84eac800f0af450017145955f71e2dd1b5cdd8db2c6ffe6a46b00d5308eec0cd7b677abb89f01c8dbc258bb021b030bc24ce1976e087a2279b40840afb9ae96fc20c9c573a01d071a7a7af4b370d88da16e4872a6b56002d554c49da9fc2941c19368933e7fb83ca643c102eb9278fcf90ba5d54233e8dfb04168954a42d3d1071101691f5fef4629e3085f0e2d698b5028a7c0fc463d1ae8a0aed6b68010195fe680ead0ea11f5726ce37b124578cd68530cc07eb7ac716c7ce81097db71e250d90ef0381b05da8321a5e33fdc56f5cf0b7398a0429d76e40e430cc19d0d70c2 0x7efdda831f820f6e46d9277343281a1cec818002469fc85f824b85beadf7404c00ac7c836dce7e80febb1554380030ae059ceab334c04356fc9f2f0426d7c853a6d22360328ace9ea286f239d8758f906997f86daad11b81becf2caaec33c8c3b81064933998880ecfebcbecf42c41789feb5a7e9503f7e82debf01f0c3aebd365f7c275462974d05f0e542401580c8698d4f60d8043fa9b254f7db5d00035fd9d3684876170a93218c32601721fd0a74e15e144f22a200242c39120d504b2d2e130b50482cb8ba314a28e5e4bcc37f4004f5ac0df3806ddab00229c00fd8a997623b2cd514ee80032abbe9c4fa8f60fdcb96b6ac041a5921fc52a254f7f4a97a6801180996920fc3fc0259797379bce8e3541466d3c2bb50bcb26353065aae224515114ac1ac6c65ba4ae20aaabb82009dae839630040c23b11b3c3433550acd9133250a9e3f41c3fc211471a441901f490fd58e29e8b92074978f4783cd1f390619be65af1c243e7baed4813a142b75dc4cf3e5466082dee5494f49664d720a941272cf07970b0e527fe156732e1b123a6b9106e5ffa43aa8673520670ccf44b0df0cce120477a03c9b2b872b30b5f2d7f6c3651c6407047f94b1292cd00961b7a8149f3880dbf00d605addb7d33cc18cbc63c9a0a639ea45eaf5505c360ef8b63e98e1ad3f3fdae2a035214360ea22d6a15bcd020d79ccdd156813b97e8e98e75b0b00d1028b7a0460d6bdc0d420ae309c29a640810050be08b1f6f73a654be4d56e0cfc730847a76e207390511022e459e8472002a8cc33be47def7a304eafb28073bb41a72513d9021dd3b7065dbb5e8d0eff0cd4b62971e24917460ccd8b963de910992b082))))))

def node_2347 (j : Nat) : Bool := withPickedBounds bds_2347 (picks_2347 j) fun cuts =>
  clashRouted m_2347 g_2347 cuts (dagTraceF m_2347 s_2347 12 f_2347) (groupRef 1745 (dagTraceF m_2347 s_2347 12 f_2347) l_2347) routeMeta routeDeck j
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_0 : treeBlockF 0 48 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_1 : treeBlockF 48 96 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_2 : treeBlockF 96 144 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_3 : treeBlockF 144 192 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_4 : treeBlockF 192 240 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_5 : treeBlockF 240 288 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_6 : treeBlockF 288 336 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_7 : treeBlockF 336 384 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_8 : treeBlockF 384 432 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_9 : treeBlockF 432 480 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_10 : treeBlockF 480 528 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_11 : treeBlockF 528 576 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_12 : treeBlockF 576 624 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_13 : treeBlockF 624 672 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_14 : treeBlockF 672 720 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_15 : treeBlockF 720 768 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_16 : treeBlockF 768 816 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_17 : treeBlockF 816 864 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_18 : treeBlockF 864 912 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_19 : treeBlockF 912 960 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_20 : treeBlockF 960 1008 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_21 : treeBlockF 1008 1056 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_22 : treeBlockF 1056 1104 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_23 : treeBlockF 1104 1152 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_24 : treeBlockF 1152 1200 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_25 : treeBlockF 1200 1248 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_26 : treeBlockF 1248 1296 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_27 : treeBlockF 1296 1344 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_28 : treeBlockF 1344 1392 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_29 : treeBlockF 1392 1440 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_30 : treeBlockF 1440 1488 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_31 : treeBlockF 1488 1536 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_32 : treeBlockF 1536 1584 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_33 : treeBlockF 1584 1632 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_34 : treeBlockF 1632 1680 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_35 : treeBlockF 1680 1728 node_2347 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem nb_2347_36 : treeBlockF 1728 1745 node_2347 = true := by decide +kernel
theorem nc_2347 : ∀ j, 0 ≤ j → j < 1745 → node_2347 j = true :=
  (joinChecks (joinChecks (joinChecks (joinChecks (joinChecks (joinChecks (certBlock nb_2347_0) (certBlock nb_2347_1)) (joinChecks (certBlock nb_2347_2) (certBlock nb_2347_3))) (joinChecks (joinChecks (certBlock nb_2347_4) (certBlock nb_2347_5)) (joinChecks (certBlock nb_2347_6) (certBlock nb_2347_7)))) (joinChecks (joinChecks (joinChecks (certBlock nb_2347_8) (certBlock nb_2347_9)) (joinChecks (certBlock nb_2347_10) (certBlock nb_2347_11))) (joinChecks (joinChecks (certBlock nb_2347_12) (certBlock nb_2347_13)) (joinChecks (certBlock nb_2347_14) (certBlock nb_2347_15))))) (joinChecks (joinChecks (joinChecks (joinChecks (certBlock nb_2347_16) (certBlock nb_2347_17)) (joinChecks (certBlock nb_2347_18) (certBlock nb_2347_19))) (joinChecks (joinChecks (certBlock nb_2347_20) (certBlock nb_2347_21)) (joinChecks (certBlock nb_2347_22) (certBlock nb_2347_23)))) (joinChecks (joinChecks (joinChecks (certBlock nb_2347_24) (certBlock nb_2347_25)) (joinChecks (certBlock nb_2347_26) (certBlock nb_2347_27))) (joinChecks (joinChecks (certBlock nb_2347_28) (certBlock nb_2347_29)) (joinChecks (certBlock nb_2347_30) (certBlock nb_2347_31)))))) (joinChecks (joinChecks (joinChecks (certBlock nb_2347_32) (certBlock nb_2347_33)) (joinChecks (certBlock nb_2347_34) (certBlock nb_2347_35))) (certBlock nb_2347_36)))
theorem lb_2347 : LowerBin m_2347 s_2347 g_2347 13 :=
  lowerDagGroupF (picks := picks_2347) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) kn_2347 sub_2347 gl_2347 rc_2347 (by
    intro j hl hh
    have hj := nc_2347 j hl hh
    simp only [node_2347, withPickedBounds_eq] at hj
    have checked := clashRouted_sound _ _ _ _ _ _ _ _ hj
    simpa only [m_2347, g_2347, fullMask, fixedGoal] using checked)

theorem signedLower : LowerBin fullMask rootStock (canon fullMask (4276808360 * 2 ^ 32 + 3972581504)) 13 := lb_2347

def witnessGates : List Gate :=
  [⟨GateOp.and, [0, 2]⟩,
   ⟨GateOp.or, [6, 1]⟩,
   ⟨GateOp.or, [6, 3]⟩,
   ⟨GateOp.or, [0, 2]⟩,
   ⟨GateOp.and, [0, 5]⟩,
   ⟨GateOp.and, [3, 4]⟩,
   ⟨GateOp.or, [10, 11]⟩,
   ⟨GateOp.and, [7, 12]⟩,
   ⟨GateOp.or, [8, 4]⟩,
   ⟨GateOp.and, [9, 14]⟩,
   ⟨GateOp.and, [12, 5]⟩,
   ⟨GateOp.or, [1, 16]⟩,
   ⟨GateOp.and, [15, 17]⟩,
   ⟨GateOp.or, [13, 18]⟩]

theorem witnessSize : witnessGates.length = 14 := rfl

theorem witnessMonotone : Monotone2 ⟨witnessGates, 19⟩ := by
  intro g hg
  simp only [witnessGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem witnessEval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨witnessGates, 19⟩ (List.ofFn x) =
    Nat.testBit (4276808360 * 2 ^ 32 + 3972581504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

end PEqualNP.Outside.L_meta_48514

theorem PEqualNP.Outside.L_meta_48514 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808360 * 2 ^ 32 + 3972581504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808360 * 2 ^ 32 + 3972581504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact PEqualNP.Outside.L_meta_48514.table2_from_lowerBin
    (4276808360 * 2 ^ 32 + 3972581504) 14
    PEqualNP.Outside.L_meta_48514.signedLower
    PEqualNP.Outside.L_meta_48514.witnessGates 19
    PEqualNP.Outside.L_meta_48514.witnessSize
    PEqualNP.Outside.L_meta_48514.witnessMonotone
    PEqualNP.Outside.L_meta_48514.witnessEval
