import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_47881

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
def KnownBin (bounds : List (Nat × List Nat × Nat × Nat)) : Prop :=
  ∀ b ∈ bounds, LowerBin b.1 b.2.1 b.2.2.2 b.2.2.1
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
def lenN (l : List Nat) : Nat :=
  List.rec 0 (fun _ _ ih => Nat.add ih 1) l
theorem lenN_eq (l : List Nat) : lenN l = l.length := by
  induction l with
  | nil => rfl
  | cons _ ws ih => change Nat.add (lenN ws) 1 = ws.length + 1; rw [ih]
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
def forceWP {α : Type} (w : Nat) (k : Nat → α) : α :=
  match w with
  | 0 => k 0
  | m + 1 => k (m + 1)
theorem forceWP_eq {α : Type} (w : Nat) (k : Nat → α) : forceWP w k = k w := by
  cases w <;> rfl
def forceCons {α : Type} (l : List Nat) (k : List Nat → α) : α :=
  match l with
  | [] => k []
  | x :: xs => k (x :: xs)
theorem forceCons_eq {α : Type} (l : List Nat) (k : List Nat → α) : forceCons l k = k l := by
  cases l <;> rfl
def forceList {α : Type} (ws : List Nat) (k : List Nat → α) : α :=
  (List.rec (motive := fun _ => (List Nat → α) → α) (fun k => k [])
    (fun w _ next k => next (fun rest => k (w :: rest))) ws) k
theorem forceList_eq {α : Type} (ws : List Nat) (k : List Nat → α) : forceList ws k = k ws := by
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih =>
    change forceList ws (fun rest => k (w :: rest)) = _
    rw [ih]
def canonV2 (mask w : Nat) : Nat :=
  forceWP (Nat.land w mask) (fun v =>
    Bool.rec
      (Bool.rec
        (forceWP (Nat.xor mask v) (fun iv => Bool.rec iv v (Nat.blt v iv)))
        0 (Nat.beq v mask))
      0 (Nat.beq v 0))
theorem canonV2_eq (mask w : Nat) : canonV2 mask w = canon mask w := by
  unfold canonV2 canon bsel; dsimp only
  rw [forceWP_eq]
  change Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (forceWP (Nat.xor mask (w &&& mask)) (fun iv => Bool.rec (motive := fun _ => Nat) iv (w &&& mask) (Nat.blt (w &&& mask) iv)))
      0 (Nat.beq (w &&& mask) mask)) 0 (Nat.beq (w &&& mask) 0) = _
  rw [forceWP_eq]
  cases Nat.beq (w &&& mask) 0 <;> cases Nat.beq (w &&& mask) mask <;> rfl
def HistValid (mask : Nat) (stock : List Nat) : List (Nat × Nat × Nat) → Prop
  | [] => True
  | (z, x, y) :: rest =>
    (∃ op < 4, z = binOp mask op x y) ∧
    (x ∈ stock ∨ ∃ a b, (x, a, b) ∈ rest) ∧
    (y ∈ stock ∨ ∃ a b, (y, a, b) ∈ rest) ∧
    HistValid mask stock rest
def WsCovered (stock : List Nat) (hist : List (Nat × Nat × Nat)) (ws : List Nat) : Prop :=
  ∀ w ∈ ws, w ∈ stock ∨ ∃ a b, (w, a, b) ∈ hist
theorem getD_mem_of_lt {l : List Nat} {i : Nat} (hi : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact List.getElem_mem hi
theorem childState_valid {mask token : Nat} {stock : List Nat}
    {st ch : Nat × List Nat × List (Nat × Nat × Nat)}
    (hv : HistValid mask stock st.2.2) (hc : WsCovered stock st.2.2 st.2.1)
    (h : childState mask token st = some ch) :
    HistValid mask stock ch.2.2 ∧ WsCovered stock ch.2.2 ch.2.1 := by
  obtain ⟨fuel, ws, hist⟩ := st
  dsimp only at hv hc
  unfold childState at h; dsimp only at h
  split at h
  · contradiction
  · rename_i hok
    split at h
    · contradiction
    · have heq := Option.some.inj h
      subst ch
      simp only [Bool.or_eq_true, Nat.beq_eq, Bool.not_eq_true'] at hok
      have hab : (token >>> 8) < ((token >>> 4) &&& 15) := by
        cases h1 : Nat.blt (token >>> 8) ((token >>> 4) &&& 15)
        · exfalso; exact hok (Or.inl (Or.inr h1))
        · exact Nat.blt_eq.mp h1
      have hbl : ((token >>> 4) &&& 15) < ws.length := by
        cases h2 : Nat.blt ((token >>> 4) &&& 15) ws.length
        · exfalso; exact hok (Or.inr h2)
        · exact Nat.blt_eq.mp h2
      have hx : ws.getD (token >>> 8) 0 ∈ ws := getD_mem_of_lt (by omega)
      have hy : ws.getD ((token >>> 4) &&& 15) 0 ∈ ws := getD_mem_of_lt hbl
      have hop : ((token >>> 2) &&& 3) < 4 := by
        have := Nat.and_lt_two_pow (token >>> 2) (n := 2) (by omega : 3 < 2 ^ 2)
        simpa using this
      refine ⟨⟨⟨(token >>> 2) &&& 3, hop, rfl⟩, hc _ hx, hc _ hy, hv⟩, ?_⟩
      intro w hw
      rcases insertSorted_mem.mp hw with rfl | hrest
      · exact Or.inr ⟨_, _, List.mem_cons_self⟩
      · have hwm : w ∈ ws := (dropVal_mem.mp (dropVal_mem.mp hrest).1).1
        rcases hc w hwm with hst | ⟨a, b, hmem⟩
        · exact Or.inl hst
        · exact Or.inr ⟨a, b, List.mem_cons_of_mem _ hmem⟩
theorem dagTrace_valid {mask fuel : Nat} {stock : List Nat} {forest : Nat → Nat × Nat}
    {i : Nat} {st : Nat × List Nat × List (Nat × Nat × Nat)}
    (h : dagTrace mask stock fuel forest i = some st) :
    HistValid mask stock st.2.2 ∧ WsCovered stock st.2.2 st.2.1 := by
  unfold dagTrace at h
  suffices ∀ steps j s,
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) steps) j = some s →
      HistValid mask stock s.2.2 ∧ WsCovered stock s.2.2 s.2.1 from
    this (fuel + 1) i st h
  intro steps
  induction steps with
  | zero => intro j s h; contradiction
  | succ n ih =>
    intro j s h; dsimp only at h
    split at h
    · split at h
      · have e := Option.some.inj h; subst s
        exact ⟨trivial, fun w hw => Or.inl (subsetWords_subset stock _ w hw)⟩
      · contradiction
    · cases hp : (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) n) ((forest j).1 - 1) with
      | none => rw [hp] at h; contradiction
      | some p =>
        rw [hp] at h
        have ⟨hv, hc⟩ := ih _ _ hp
        exact childState_valid hv hc h
theorem addUniq_mem {w u : Nat} {l : List Nat} : u ∈ addUniq w l ↔ u = w ∨ u ∈ l := by
  unfold addUniq
  cases h : l.contains w
  · simp [List.mem_cons]
  · simp only [ite_true]
    have hw : w ∈ l := List.contains_iff_mem.mp h
    constructor
    · exact Or.inr
    · rintro (rfl | hu); exact hw; exact hu
theorem recipeStart_mem {cut : Nat} {stock ws : List Nat} {u : Nat} :
    u ∈ recipeStart cut stock ws ↔ ∃ w ∈ ws, canon cut w = u ∧ ¬Avail stock u := by
  induction ws with
  | nil => simp [recipeStart]
  | cons w ws ih =>
    change u ∈ (if availB stock (canon cut w) then recipeStart cut stock ws
                else addUniq (canon cut w) (recipeStart cut stock ws)) ↔ _
    cases ha : availB stock (canon cut w)
    · simp only [Bool.false_eq_true, ite_false, addUniq_mem, ih]
      have hna : ¬Avail stock (canon cut w) := fun h => by rw [availB_spec.mpr h] at ha; exact Bool.noConfusion ha
      constructor
      · rintro (rfl | ⟨w', hw', rfl, hnu⟩)
        · exact ⟨w, List.mem_cons_self, rfl, hna⟩
        · exact ⟨w', List.mem_cons_of_mem _ hw', rfl, hnu⟩
      · rintro ⟨w', hw', rfl, hnu⟩
        rcases List.mem_cons.mp hw' with rfl | hw'
        · exact Or.inl rfl
        · exact Or.inr ⟨w', hw', rfl, hnu⟩
    · simp only [ite_true, ih]
      have hya : Avail stock (canon cut w) := availB_spec.mp ha
      constructor
      · rintro ⟨w', hw', rfl, hnu⟩; exact ⟨w', List.mem_cons_of_mem _ hw', rfl, hnu⟩
      · rintro ⟨w', hw', rfl, hnu⟩
        rcases List.mem_cons.mp hw' with rfl | hw'
        · exact absurd hya hnu
        · exact ⟨w', hw', rfl, hnu⟩
theorem recipeClose_sub {cut : Nat} {stock : List Nat} {hist : List (Nat × Nat × Nat)} {acc : List Nat} :
    ∀ u ∈ acc, u ∈ recipeClose cut stock hist acc := by
  induction hist generalizing acc with
  | nil => intro u hu; exact hu
  | cons r hist ih =>
    obtain ⟨w, a, b⟩ := r
    intro u hu
    change u ∈ (if acc.contains (canon cut w) then
      let va := canon cut a; let vb := canon cut b
      let acc1 := if availB stock va then acc else addUniq va acc
      let acc2 := if availB stock vb then acc1 else addUniq vb acc1
      recipeClose cut stock hist acc2
    else recipeClose cut stock hist acc)
    split
    · apply ih
      have h1 : u ∈ (if availB stock (canon cut a) then acc else addUniq (canon cut a) acc) := by
        split; exact hu; exact addUniq_mem.mpr (Or.inr hu)
      split; exact h1; exact addUniq_mem.mpr (Or.inr h1)
    · exact ih u hu
theorem recipeClose_nil (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) :
    recipeClose cut stock hist [] = [] := by
  induction hist with
  | nil => rfl
  | cons r hist ih =>
    obtain ⟨w, a, b⟩ := r
    change (if [].contains (canon cut w) then _ else recipeClose cut stock hist []) = []
    exact ih
theorem recipeClose_mono {cut : Nat} {stock : List Nat} {hist : List (Nat × Nat × Nat)} :
    ∀ {A B : List Nat}, (∀ u ∈ A, u ∈ B) →
      ∀ u ∈ recipeClose cut stock hist A, u ∈ recipeClose cut stock hist B := by
  induction hist with
  | nil => intro A B hAB u hu; exact hAB u hu
  | cons r hist ih =>
    obtain ⟨w, a, b⟩ := r
    intro A B hAB u hu
    change u ∈ (if A.contains (canon cut w) then
      let acc1 := if availB stock (canon cut a) then A else addUniq (canon cut a) A
      let acc2 := if availB stock (canon cut b) then acc1 else addUniq (canon cut b) acc1
      recipeClose cut stock hist acc2
    else recipeClose cut stock hist A) at hu
    change u ∈ (if B.contains (canon cut w) then
      let acc1 := if availB stock (canon cut a) then B else addUniq (canon cut a) B
      let acc2 := if availB stock (canon cut b) then acc1 else addUniq (canon cut b) acc1
      recipeClose cut stock hist acc2
    else recipeClose cut stock hist B)
    cases hA : A.contains (canon cut w)
    · simp only [hA, Bool.false_eq_true, ite_false] at hu
      cases hB : B.contains (canon cut w)
      · simp only [Bool.false_eq_true, ite_false]; exact ih hAB u hu
      · simp only [ite_true]
        apply ih _ u hu
        intro x hx
        have h1 : x ∈ (if availB stock (canon cut a) then B else addUniq (canon cut a) B) := by
          split; exact hAB x hx; exact addUniq_mem.mpr (Or.inr (hAB x hx))
        split; exact h1; exact addUniq_mem.mpr (Or.inr h1)
    · have hwB : B.contains (canon cut w) = true := List.contains_iff_mem.mpr (hAB _ (List.contains_iff_mem.mp hA))
      simp only [hA, ite_true] at hu
      simp only [hwB, ite_true]
      apply ih _ u hu
      intro x hx
      have h1 : ∀ y, y ∈ (if availB stock (canon cut a) then A else addUniq (canon cut a) A) →
          y ∈ (if availB stock (canon cut a) then B else addUniq (canon cut a) B) := by
        intro y hy
        cases hca : availB stock (canon cut a)
        · simp only [hca, Bool.false_eq_true, ite_false, addUniq_mem] at hy ⊢
          rcases hy with rfl | hy; exact Or.inl rfl; exact Or.inr (hAB y hy)
        · simp only [hca, ite_true] at hy ⊢; exact hAB y hy
      cases hcb : availB stock (canon cut b)
      · simp only [hcb, Bool.false_eq_true, ite_false, addUniq_mem] at hx ⊢
        rcases hx with rfl | hx; exact Or.inl rfl; exact Or.inr (h1 x hx)
      · simp only [hcb, ite_true] at hx ⊢; exact h1 x hx
noncomputable def buildFrom (cut : Nat) (bstock : List Nat) (S : Finset Nat) :
    List (Nat × Nat × Nat) → List Nat
  | [] => []
  | (z, x, y) :: rest =>
    let vs := buildFrom cut bstock S rest
    let v := canon cut z
    let := Classical.propDecidable
    if v ∈ S ∧ ¬Avail (vs ++ bstock) v ∧ Avail (vs ++ bstock) (canon cut x) ∧ Avail (vs ++ bstock) (canon cut y)
    then vs ++ [v] else vs
theorem buildFrom_builds {mask cut : Nat} {stock bstock : List Nat} {S : Finset Nat}
    (sub : mask &&& cut = cut) :
    ∀ {hist : List (Nat × Nat × Nat)}, HistValid mask stock hist →
      BuildsBin cut bstock (buildFrom cut bstock S hist)
  | [], _ => trivial
  | (z, x, y) :: rest, ⟨⟨op, hop, hz⟩, _, _, hrest⟩ => by
    unfold buildFrom; dsimp only
    have ih := buildFrom_builds (bstock := bstock) (S := S) sub hrest
    split
    · rename_i hcond
      obtain ⟨_, hna, hax, hay⟩ := hcond
      have hgate : GateBin cut (buildFrom cut bstock S rest ++ bstock) (canon cut z) := by
        have hsub := canon_sub_binOp (op := op) (a := x) (b := y) sub
        rw [← hz] at hsub
        rcases hsub with h0 | hx | hy | ⟨op', hop', heq⟩
        · exact absurd (Or.inl h0) hna
        · exact absurd (hx ▸ hax) hna
        · exact absurd (hy ▸ hay) hna
        · exact ⟨canon cut x, canon cut y, op', hop', hax, hay, heq⟩
      exact builds_append ih ⟨hgate, trivial⟩
    · exact ih
theorem buildFrom_nodup_sub (cut : Nat) (bstock : List Nat) (S : Finset Nat) :
    ∀ (hist : List (Nat × Nat × Nat)),
      (buildFrom cut bstock S hist).Nodup ∧ ∀ u ∈ buildFrom cut bstock S hist, u ∈ S
  | [] => ⟨List.nodup_nil, fun _ h => nomatch h⟩
  | (z, x, y) :: rest => by
    unfold buildFrom; dsimp only
    obtain ⟨hnd, hsub⟩ := buildFrom_nodup_sub cut bstock S rest
    split
    · rename_i hcond
      obtain ⟨hvS, hna, _, _⟩ := hcond
      have hnm : canon cut z ∉ buildFrom cut bstock S rest := fun hm =>
        hna (Or.inr (List.mem_append_left bstock hm))
      refine ⟨List.nodup_append.mpr ⟨hnd, List.nodup_singleton _, fun a ha b hb heq => by
        rw [List.mem_singleton.mp hb] at heq; exact hnm (heq ▸ ha)⟩, ?_⟩
      intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact hsub u hu
      · rw [List.mem_singleton.mp hu]; exact hvS
    · exact ⟨hnd, hsub⟩
theorem buildFrom_mono_avail (cut : Nat) (bstock : List Nat) (S : Finset Nat)
    (r : Nat × Nat × Nat) (rest : List (Nat × Nat × Nat)) {u : Nat}
    (hu : Avail (buildFrom cut bstock S rest ++ bstock) u) :
    Avail (buildFrom cut bstock S (r :: rest) ++ bstock) u := by
  obtain ⟨z, x, y⟩ := r
  unfold buildFrom; dsimp only
  split
  · exact avail_weaken (fun w hw => by simp only [List.mem_append] at hw ⊢; tauto) hu
  · exact hu
theorem buildFrom_covers {mask cut : Nat} {stock bstock : List Nat} {S : Finset Nat}
    (hstk : ∀ s ∈ stock, Avail bstock (canon cut s)) :
    ∀ {hist : List (Nat × Nat × Nat)}, HistValid mask stock hist →
      ∀ (acc : List Nat),
        (∀ u ∈ acc, Avail bstock u ∨ ∃ z x y, (z, x, y) ∈ hist ∧ canon cut z = u) →
        (∀ u ∈ recipeClose cut bstock hist acc, u ∈ S) →
        ∀ u ∈ acc, Avail (buildFrom cut bstock S hist ++ bstock) u
  | [], _, acc, hcov, _, u, hu => by
    rcases hcov u hu with ha | ⟨_, _, _, hm, _⟩
    · exact avail_weaken (fun w hw => List.mem_append_right _ hw) ha
    · exact nomatch hm
  | (z, x, y) :: rest, ⟨_, hxc, hyc, hrest⟩, acc, hcov, hS, u, hu => by
    cases hcz : acc.contains (canon cut z)
    · have hnz : canon cut z ∉ acc := fun hm => by rw [List.contains_iff_mem.mpr hm] at hcz; exact Bool.noConfusion hcz
      have hS' : ∀ v ∈ recipeClose cut bstock rest acc, v ∈ S := by
        intro v hv; apply hS v
        change v ∈ (if acc.contains (canon cut z) then _ else recipeClose cut bstock rest acc)
        simp only [hcz, Bool.false_eq_true, ite_false]; exact hv
      have hcov' : ∀ v ∈ acc, Avail bstock v ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = v := by
        intro v hv
        rcases hcov v hv with ha | ⟨z', x', y', hm, heq⟩
        · exact Or.inl ha
        · rcases List.mem_cons.mp hm with hhead | htail
          · rcases Prod.mk.inj hhead with ⟨rfl, _⟩
            exact absurd (heq ▸ hv) hnz
          · exact Or.inr ⟨z', x', y', htail, heq⟩
      exact buildFrom_mono_avail cut bstock S (z, x, y) rest
        (buildFrom_covers hstk hrest acc hcov' hS' u hu)
    · have hzacc : canon cut z ∈ acc := List.contains_iff_mem.mp hcz
      have hzS : canon cut z ∈ S := hS _ (recipeClose_sub _ hzacc)
      set acc1 := if availB bstock (canon cut x) then acc else addUniq (canon cut x) acc
      set acc2 := if availB bstock (canon cut y) then acc1 else addUniq (canon cut y) acc1
      have hS2 : ∀ v ∈ recipeClose cut bstock rest acc2, v ∈ S := by
        intro v hv; apply hS v
        change v ∈ (if acc.contains (canon cut z) then recipeClose cut bstock rest acc2 else _)
        simp only [hcz, ite_true]; exact hv
      let := Classical.propDecidable
      set acc' := acc2.filter (fun v => decide (Avail bstock v ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = v))
      have hsub' : ∀ v ∈ acc', v ∈ acc2 := fun v hv => (List.mem_filter.mp hv).1
      have hcov' : ∀ v ∈ acc', Avail bstock v ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = v :=
        fun v hv => of_decide_eq_true (List.mem_filter.mp hv).2
      have hS' : ∀ v ∈ recipeClose cut bstock rest acc', v ∈ S :=
        fun v hv => hS2 v (recipeClose_mono hsub' v hv)
      have hIH := buildFrom_covers hstk hrest acc' hcov' hS'
      have hacc_sub2 : ∀ v ∈ acc, v ∈ acc2 := by
        intro v hv
        have h1 : v ∈ acc1 := by
          unfold acc1; split; exact hv; exact addUniq_mem.mpr (Or.inr hv)
        unfold acc2; split; exact h1; exact addUniq_mem.mpr (Or.inr h1)
      have hax : Avail (buildFrom cut bstock S rest ++ bstock) (canon cut x) := by
        cases hbx : availB bstock (canon cut x)
        · have hx2 : canon cut x ∈ acc2 := by
            have hx1 : canon cut x ∈ acc1 := by
              unfold acc1; simp only [hbx, Bool.false_eq_true, ite_false]; exact addUniq_mem.mpr (Or.inl rfl)
            unfold acc2; split; exact hx1; exact addUniq_mem.mpr (Or.inr hx1)
          have hpx : Avail bstock (canon cut x) ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = canon cut x := by
            rcases hxc with hs | ⟨a, b, hm⟩
            · exact Or.inl (hstk x hs)
            · exact Or.inr ⟨x, a, b, hm, rfl⟩
          exact hIH _ (List.mem_filter.mpr ⟨hx2, decide_eq_true hpx⟩)
        · exact avail_weaken (fun w hw => List.mem_append_right _ hw) (availB_spec.mp hbx)
      have hay : Avail (buildFrom cut bstock S rest ++ bstock) (canon cut y) := by
        cases hby : availB bstock (canon cut y)
        · have hy2 : canon cut y ∈ acc2 := by
            unfold acc2; simp only [hby, Bool.false_eq_true, ite_false]; exact addUniq_mem.mpr (Or.inl rfl)
          have hpy : Avail bstock (canon cut y) ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = canon cut y := by
            rcases hyc with hs | ⟨a, b, hm⟩
            · exact Or.inl (hstk y hs)
            · exact Or.inr ⟨y, a, b, hm, rfl⟩
          exact hIH _ (List.mem_filter.mpr ⟨hy2, decide_eq_true hpy⟩)
        · exact avail_weaken (fun w hw => List.mem_append_right _ hw) (availB_spec.mp hby)
      by_cases huz : u = canon cut z
      · subst huz
        unfold buildFrom; dsimp only
        split
        · exact Or.inr (List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self))
        · rename_i hneg
          by_cases ha : Avail (buildFrom cut bstock S rest ++ bstock) (canon cut z)
          · exact ha
          · exact absurd ⟨hzS, ha, hax, hay⟩ hneg
      · have hpu : Avail bstock u ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = u := by
          rcases hcov u hu with ha | ⟨z', x', y', hm, heq⟩
          · exact Or.inl ha
          · rcases List.mem_cons.mp hm with hhead | htail
            · rcases Prod.mk.inj hhead with ⟨rfl, _⟩; exact absurd heq.symm huz
            · exact Or.inr ⟨z', x', y', htail, heq⟩
        exact buildFrom_mono_avail cut bstock S (z, x, y) rest
          (hIH u (List.mem_filter.mpr ⟨hacc_sub2 u hu, decide_eq_true hpu⟩))
def flatStartF (cut : Nat) (stock ws : List Nat) : Nat × List Nat :=
  List.rec (0, []) (fun w _ ih =>
    match ih with
    | (fl, acc) =>
      forceWP (canonV2 cut w) (fun v =>
        Bool.rec
          (Bool.rec
            (Bool.rec (fl, v :: acc) (fl, acc) (memN v acc))
            (fl, acc) (memN v stock))
          (forceWP (Nat.add fl 1) (fun fl1 => (fl1, acc)))
          (Nat.beq v 0))) ws
theorem flatStartF_eq (cut : Nat) (stock ws : List Nat) :
    flatStartF cut stock ws = (flatCount cut ws, recipeStart cut stock ws) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have hstep : flatStartF cut stock (w :: ws) =
      match flatStartF cut stock ws with
      | (fl, acc) =>
        forceWP (canonV2 cut w) (fun v =>
          Bool.rec
            (Bool.rec
              (Bool.rec (fl, v :: acc) (fl, acc) (memN v acc))
              (fl, acc) (memN v stock))
            (forceWP (Nat.add fl 1) (fun fl1 => (fl1, acc)))
            (Nat.beq v 0)) := rfl
    rw [hstep, ih]; dsimp only; rw [forceWP_eq, canonV2_eq, forceWP_eq]
    change Bool.rec
        (Bool.rec
          (Bool.rec (flatCount cut ws, canon cut w :: recipeStart cut stock ws)
            (flatCount cut ws, recipeStart cut stock ws) (memN (canon cut w) (recipeStart cut stock ws)))
          (flatCount cut ws, recipeStart cut stock ws) (memN (canon cut w) stock))
        (Nat.add (flatCount cut ws) 1, recipeStart cut stock ws) (Nat.beq (canon cut w) 0) =
      (bsel (Nat.beq (canon cut w) 0) (flatCount cut ws + 1) (flatCount cut ws),
       if availB stock (canon cut w) then recipeStart cut stock ws else addUniq (canon cut w) (recipeStart cut stock ws))
    simp only [memN_eq, availB, addUniq]
    have haux (b1 b2 b3 : Bool) :
        Bool.rec (Bool.rec (Bool.rec (flatCount cut ws, canon cut w :: recipeStart cut stock ws)
          (flatCount cut ws, recipeStart cut stock ws) b3)
          (flatCount cut ws, recipeStart cut stock ws) b2)
          (Nat.add (flatCount cut ws) 1, recipeStart cut stock ws) b1 =
        (bsel b1 (flatCount cut ws + 1) (flatCount cut ws),
         if (b1 || b2) = true then recipeStart cut stock ws
         else if b3 = true then recipeStart cut stock ws else canon cut w :: recipeStart cut stock ws) := by
      cases b1 <;> cases b2 <;> cases b3 <;> rfl
    exact haux _ _ _
def recipeCloseV2 (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun (w, a, b) _ next acc =>
      forceWP (canonV2 cut w) (fun v =>
        Bool.rec (next acc)
          (forceWP (canonV2 cut a) (fun va =>
            forceCons
              (Bool.rec (Bool.rec (Bool.rec (va :: acc) acc (memN va acc)) acc (memN va stock)) acc (Nat.beq va 0))
              (fun acc1 =>
                forceWP (canonV2 cut b) (fun vb =>
                  forceCons
                    (Bool.rec (Bool.rec (Bool.rec (vb :: acc1) acc1 (memN vb acc1)) acc1 (memN vb stock)) acc1 (Nat.beq vb 0))
                    next))))
          (memN v acc))) hist needed
theorem recipeCloseV2_eq (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) :
    recipeCloseV2 cut stock hist needed = recipeClose cut stock hist needed := by
  induction hist generalizing needed with
  | nil => rfl
  | cons rec hist ih =>
    obtain ⟨w, a, b⟩ := rec
    have hstep : recipeCloseV2 cut stock ((w, a, b) :: hist) needed =
      forceWP (canonV2 cut w) (fun v =>
        Bool.rec (recipeCloseV2 cut stock hist needed)
          (forceWP (canonV2 cut a) (fun va =>
            forceCons
              (Bool.rec (Bool.rec (Bool.rec (va :: needed) needed (memN va needed)) needed (memN va stock)) needed (Nat.beq va 0))
              (fun acc1 =>
                forceWP (canonV2 cut b) (fun vb =>
                  forceCons
                    (Bool.rec (Bool.rec (Bool.rec (vb :: acc1) acc1 (memN vb acc1)) acc1 (memN vb stock)) acc1 (Nat.beq vb 0))
                    (recipeCloseV2 cut stock hist)))))
          (memN v needed)) := rfl
    rw [hstep]
    simp only [forceWP_eq, forceCons_eq, canonV2_eq, memN_eq]
    change Bool.rec (recipeCloseV2 cut stock hist needed) _ (needed.contains (canon cut w)) =
      (if needed.contains (canon cut w) then
        let va := canon cut a; let vb := canon cut b
        let acc1 := if availB stock va then needed else addUniq va needed
        let acc2 := if availB stock vb then acc1 else addUniq vb acc1
        recipeClose cut stock hist acc2
      else recipeClose cut stock hist needed)
    cases needed.contains (canon cut w)
    · exact ih needed
    · dsimp only [ite_true]
      rw [ih]
      congr 1
      have hadd (v : Nat) (l : List Nat) :
          Bool.rec (Bool.rec (Bool.rec (v :: l) l (l.contains v)) l (stock.contains v)) l (Nat.beq v 0) =
          if availB stock v then l else addUniq v l := by
        dsimp only [availB, addUniq]
        have haux (b1 b2 b3 : Bool) :
            Bool.rec (Bool.rec (Bool.rec (v :: l) l b3) l b2) l b1 =
            if (b1 || b2) = true then l else if b3 = true then l else v :: l := by
          cases b1 <;> cases b2 <;> cases b3 <;> rfl
        exact haux _ _ _
      rw [hadd (canon cut a) needed, hadd (canon cut b)]
def boundClosesV2 (fuel : Nat) (ws : List Nat) (hist : List (Nat × Nat × Nat))
    (bound : Nat × List Nat × Nat × Nat) : Bool :=
  let (cut, bstock, lower, _) := bound
  match flatStartF cut bstock ws with
  | (fl, start0) =>
    forceWP (Nat.sub fuel fl) (fun rem =>
      Bool.rec false
        (match start0 with
         | [] => true
         | s0 :: sr =>
           forceList (s0 :: sr) (fun start =>
             Bool.rec false
               (Nat.blt (Nat.add (lenN (recipeCloseV2 cut bstock hist start)) rem) lower)
               (Nat.blt (Nat.add (lenN start) rem) lower)))
        (Nat.blt rem lower))
theorem boundClosesV2_sound {mask goal : Nat} {stock : List Nat}
    {fuel : Nat} {ws : List Nat} {hist : List (Nat × Nat × Nat)}
    {bound : Nat × List Nat × Nat × Nat}
    (hlow : LowerBin bound.1 bound.2.1 bound.2.2.2 bound.2.2.1)
    (sub : mask &&& bound.1 = bound.1)
    (hg : canon bound.1 goal = bound.2.2.2) (hnz : bound.2.2.2 ≠ 0)
    (hstk : ∀ s ∈ stock, Avail bound.2.1 (canon bound.1 s))
    (hv : HistValid mask stock hist) (hc : WsCovered stock hist ws)
    (nd : ws.Nodup) {k : Nat} (hk : k ≤ fuel)
    (hlive : LiveBin mask goal k ws.toFinset) :
    boundClosesV2 fuel ws hist bound = false := by
  obtain ⟨cut, bstock, lower, bgoal⟩ := bound
  dsimp only at hlow sub hg hnz hstk
  apply Bool.eq_false_iff.mpr
  intro hbc
  unfold boundClosesV2 at hbc; dsimp only at hbc
  rw [flatStartF_eq] at hbc; dsimp only at hbc
  simp only [forceWP_eq] at hbc
  cases h1 : Nat.blt (Nat.sub fuel (flatCount cut ws)) lower
  · rw [h1] at hbc; exact Bool.noConfusion hbc
  · rw [h1] at hbc; dsimp only at hbc
    have hlen_lt : (recipeClose cut bstock hist (recipeStart cut bstock ws)).length + (fuel - flatCount cut ws) < lower := by
      cases hs : recipeStart cut bstock ws with
      | nil =>
        rw [recipeClose_nil]; simp only [List.length_nil, Nat.zero_add]
        exact Nat.blt_eq.mp h1
      | cons s0 sr =>
        rw [hs] at hbc; dsimp only at hbc
        simp only [forceList_eq, recipeCloseV2_eq, lenN_eq] at hbc
        cases h2 : Nat.blt (Nat.add (s0 :: sr).length (Nat.sub fuel (flatCount cut ws))) lower
        · rw [h2] at hbc; exact Bool.noConfusion hbc
        · rw [h2] at hbc; dsimp only at hbc
          exact Nat.blt_eq.mp hbc
    set needed := recipeClose cut bstock hist (recipeStart cut bstock ws)
    set S := needed.toFinset
    set vs := buildFrom cut bstock S hist
    have hvbd : BuildsBin cut bstock vs := buildFrom_builds sub hv
    obtain ⟨hvnd, hvsub⟩ := buildFrom_nodup_sub cut bstock S hist
    have hvlen : vs.length ≤ needed.length := by
      rw [← List.toFinset_card_of_nodup hvnd]
      have hsubf : vs.toFinset ⊆ S := fun u hu => hvsub u (List.mem_toFinset.mp hu)
      exact Nat.le_trans (Finset.card_le_card hsubf) (List.toFinset_card_le needed)
    have hcov_start : ∀ u ∈ recipeStart cut bstock ws,
        Avail bstock u ∨ ∃ z x y, (z, x, y) ∈ hist ∧ canon cut z = u := by
      intro u hu
      obtain ⟨w, hww, rfl, hna⟩ := recipeStart_mem.mp hu
      rcases hc w hww with hws | ⟨a, b, hmem⟩
      · exact absurd (hstk w hws) hna
      · exact Or.inr ⟨w, a, b, hmem, rfl⟩
    have hvs_start := buildFrom_covers hstk hv (recipeStart cut bstock ws) hcov_start
      (fun u hu => List.mem_toFinset.mpr hu)
    have hsup : ∀ w ∈ ws.toFinset, Avail (vs ++ bstock) (canon cut w) := by
      intro w hw
      have hww : w ∈ ws := List.mem_toFinset.mp hw
      by_cases ha : Avail bstock (canon cut w)
      · exact avail_weaken (fun u hu => List.mem_append_right _ hu) ha
      · exact hvs_start _ (recipeStart_mem.mpr ⟨w, hww, rfl, ha⟩)
    have hgnf : canon cut goal ≠ 0 := hg.symm ▸ hnz
    obtain ⟨ys, hylen, hybd, hyhit⟩ := maskedBuildBin sub hgnf hlive (vs ++ bstock) hsup
    rw [← flatCount_card cut nd] at hylen
    have hboth := builds_append hvbd hybd
    have hfinal : Avail ((vs ++ ys) ++ bstock) bgoal := by
      rw [← hg]
      exact avail_weaken (fun u hu => by simp only [List.mem_append] at hu ⊢; tauto) hyhit
    have heno := hlow (vs ++ ys) hboth hfinal
    simp only [List.length_append] at heno
    omega
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
def checkHintBoundV5 (goal negGoal fuel1 : Nat) (ws1 : List Nat) (hist1 : List (Nat × Nat × Nat))
    (bounds : List (Nat × List Nat × Nat × Nat)) (cid : Nat) : Bool :=
  match nthBound bounds cid with
  | some b => boundClosesV2 fuel1 ws1 hist1 b
  | none => Bool.rec true false (dagPartF ws1 goal negGoal)
theorem checkHintBoundV5_open {mask goal fuel1 cid : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {ws1 : List Nat} {hist1 : List (Nat × Nat × Nat)}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s))
    (hv : HistValid mask stock hist1) (hc : WsCovered stock hist1 ws1)
    (nd : ws1.Nodup) {k : Nat} (hk : k ≤ fuel1)
    (hlive : LiveBin mask goal k ws1.toFinset) :
    checkHintBoundV5 goal (Nat.xor mask goal) fuel1 ws1 hist1 bounds cid = false := by
  unfold checkHintBoundV5
  cases hb : nthBound bounds cid with
  | some b =>
    dsimp only
    have hmem := nthBound_mem hb
    have hg := hgoals b hmem
    exact boundClosesV2_sound (hknown b hmem) (hsub b hmem) hg.1 hg.2 (hstk b hmem) hv hc nd hk hlive
  | none =>
    dsimp only
    have hdp : dagPartF ws1 goal (Nat.xor mask goal) = true := by
      have heq : dagPartF ws1 goal (Nat.xor mask goal) = dagPart ws1 goal (mask ^^^ goal) :=
        dagPartF_eq ws1 goal (mask ^^^ goal)
      rw [heq]; exact dagPart_live hgm hlive
    rw [hdp]
def hintCloseLeafV5 (goal negGoal ep cutBits cutMask : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (fuel1 : Nat) (ws1 : List Nat) (hist1 : List (Nat × Nat × Nat))
    (sp : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  Bool.rec (some (cur, h))
    (forceWP (Nat.land h 3) (fun tag =>
      Bool.rec
        (Bool.rec none
          (forceWP (Nat.shiftRight h 2) (fun h' => some (cur, h')))
          (checkHintBoundV5 goal negGoal fuel1 ws1 hist1 bounds tag))
        (forceWP (Nat.shiftRight h 2) (fun h1 =>
          forceWP (Nat.add 3 (Nat.land h1 cutMask)) (fun cid =>
            Bool.rec none
              (forceWP (Nat.shiftRight h1 cutBits) (fun h' => some (cur, h')))
              (checkHintBoundV5 goal negGoal fuel1 ws1 hist1 bounds cid))))
        (Nat.beq tag 3)))
    (Nat.beq (Nat.land ep sp) ep)
theorem hintCloseLeafV5_open {mask goal cutBits cutMask fuel1 : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {ws1 : List Nat} {hist1 : List (Nat × Nat × Nat)} {cur : List (Nat × Nat)} {h : Nat}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s))
    (hv : HistValid mask stock hist1) (hc : WsCovered stock hist1 ws1)
    (nd : ws1.Nodup) {k : Nat} (hk : k ≤ fuel1)
    (hlive : LiveBin mask goal k ws1.toFinset) :
    hintCloseLeafV5 goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask bounds fuel1 ws1 hist1 (orSep ws1) cur h = none := by
  unfold hintCloseLeafV5
  rw [sepPack_live hgm hlive]; dsimp only
  rw [forceWP_eq]
  cases Nat.beq (Nat.land h 3) 3
  · dsimp only
    rw [checkHintBoundV5_open hgm hknown hsub hgoals hstk hv hc nd hk hlive]
  · dsimp only
    rw [forceWP_eq, forceWP_eq]
    rw [checkHintBoundV5_open hgm hknown hsub hgoals hstk hv hc nd hk hlive]
def stepLeafV5 (goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel1 z spZ baseSp : Nat) (rest : List Nat) (hist1 : List (Nat × Nat × Nat))
    (tok : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  match cur with
  | (t, dest) :: tl =>
    Bool.rec
      (hintCloseLeafV5 goal negGoal ep cutBits cutMask bounds fuel1 (z :: rest) hist1 (Nat.lor spZ baseSp) cur h)
      (Bool.rec none
        (match states dest with
         | none => none
         | some saved =>
           Bool.rec none (Bool.rec none (some (tl, h)) (eqListN saved.2.1 (insertSortedF z rest)))
             (Nat.beq saved.1 fuel1))
        (Nat.blt dest count))
      (Nat.beq tok t)
  | [] =>
    hintCloseLeafV5 goal negGoal ep cutBits cutMask bounds fuel1 (z :: rest) hist1 (Nat.lor spZ baseSp) [] h
theorem stepLeafV5_ref {mask goal cutBits cutMask count fuel1 z tok h : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {rest : List Nat} {hist1 : List (Nat × Nat × Nat)} {cur : List (Nat × Nat)}
    {res : List (Nat × Nat) × Nat}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s))
    (hv : HistValid mask stock hist1) (hc : WsCovered stock hist1 (z :: rest))
    (nd : (z :: rest).Nodup) {k : Nat} (hk : k ≤ fuel1)
    (hlive : LiveBin mask goal k (z :: rest).toFinset)
    (hok : stepLeafV5 goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask count bounds states
      fuel1 z (sepPack z) (orSep rest) rest hist1 tok cur h = some res) :
    ∃ dest < count, ∃ saved, states dest = some saved ∧ saved.1 = fuel1 ∧ saved.2.1 = insertSorted z rest := by
  have hcl := hintCloseLeafV5_open (cutBits := cutBits) (cutMask := cutMask) (cur := cur) (h := h)
    hgm hknown hsub hgoals hstk hv hc nd hk hlive
  unfold stepLeafV5 at hok
  have hor : Nat.lor (sepPack z) (orSep rest) = orSep (z :: rest) := rfl
  rw [hor] at hok
  cases cur with
  | nil => dsimp only at hok; rw [hcl] at hok; cases hok
  | cons hd tl =>
    obtain ⟨t, dest⟩ := hd
    dsimp only at hok
    cases ht : Nat.beq tok t
    · rw [ht] at hok; dsimp only at hok; rw [hcl] at hok; cases hok
    · rw [ht] at hok; dsimp only at hok
      cases hlt : Nat.blt dest count
      · rw [hlt] at hok; dsimp only at hok; cases hok
      · rw [hlt] at hok; dsimp only at hok
        cases hst : states dest with
        | none => rw [hst] at hok; dsimp only at hok; cases hok
        | some saved =>
          rw [hst] at hok; dsimp only at hok
          cases hf : Nat.beq saved.1 fuel1
          · rw [hf] at hok; dsimp only at hok; cases hok
          · rw [hf] at hok; dsimp only at hok
            cases heq : eqListN saved.2.1 (insertSortedF z rest)
            · rw [heq] at hok; dsimp only at hok; cases hok
            · rw [eqListN_eq, insertSortedF_eq, beq_iff_eq] at heq
              exact ⟨dest, Nat.blt_eq.mp hlt, saved, hst, Nat.beq_eq.mp hf, heq⟩
def checkKeepsV5 (goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n z spZ spAll spNoA spNoB spNoAB : Nat)
    (ws0 wsNoA wsNoB wsNoAB : List Nat) (hist1 : List (Nat × Nat × Nat))
    (tokBase : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  match (Bool.rec
    (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoAB wsNoAB hist1 tokBase cur h)
    (some (cur, h)) (Nat.blt fuel (Nat.sub n 1)) : Option (List (Nat × Nat) × Nat)) with
  | none => none
  | some (c1, h1) =>
    match (Bool.rec
      (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoB wsNoB hist1 (Nat.add tokBase 1) c1 h1)
      (some (c1, h1)) (Nat.blt fuel n) : Option (List (Nat × Nat) × Nat)) with
    | none => none
    | some (c2, h2) =>
      match (Bool.rec
        (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoA wsNoA hist1 (Nat.add tokBase 2) c2 h2)
        (some (c2, h2)) (Nat.blt fuel n) : Option (List (Nat × Nat) × Nat)) with
      | none => none
      | some (c3, h3) =>
        Bool.rec
          (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spAll ws0 hist1 (Nat.add tokBase 3) c3 h3)
          (some (c3, h3)) (Nat.blt fuel (Nat.add n 1))
theorem checkKeepsV5_at {goal negGoal ep cutBits cutMask count fuel fuel1 n z spZ spAll spNoA spNoB spNoAB tokBase h : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 wsNoA wsNoB wsNoAB : List Nat} {hist1 : List (Nat × Nat × Nat)}
    {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (hok : checkKeepsV5 goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n z spZ spAll spNoA spNoB spNoAB
      ws0 wsNoA wsNoB wsNoAB hist1 tokBase cur h = some res)
    (keepA keepB : Bool) :
    match keepA, keepB with
    | false, false => Nat.blt fuel (n - 1) = true ∨ ∃ c hh r, stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoAB wsNoAB hist1 tokBase c hh = some r
    | true, false => Nat.blt fuel n = true ∨ ∃ c hh r, stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoB wsNoB hist1 (tokBase + 1) c hh = some r
    | false, true => Nat.blt fuel n = true ∨ ∃ c hh r, stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoA wsNoA hist1 (tokBase + 2) c hh = some r
    | true, true => Nat.blt fuel (n + 1) = true ∨ ∃ c hh r, stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spAll ws0 hist1 (tokBase + 3) c hh = some r := by
  unfold checkKeepsV5 at hok
  cases hp0 : (Bool.rec (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoAB wsNoAB hist1 tokBase cur h)
    (some (cur, h)) (Nat.blt fuel (Nat.sub n 1)) : Option (List (Nat × Nat) × Nat)) with
  | none => rw [hp0] at hok; dsimp only at hok; cases hok
  | some p1 =>
    obtain ⟨c1, h1⟩ := p1
    rw [hp0] at hok; dsimp only at hok
    cases hp1 : (Bool.rec (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoB wsNoB hist1 (Nat.add tokBase 1) c1 h1)
      (some (c1, h1)) (Nat.blt fuel n) : Option (List (Nat × Nat) × Nat)) with
    | none => rw [hp1] at hok; dsimp only at hok; cases hok
    | some p2 =>
      obtain ⟨c2, h2⟩ := p2
      rw [hp1] at hok; dsimp only at hok
      cases hp2 : (Bool.rec (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoA wsNoA hist1 (Nat.add tokBase 2) c2 h2)
        (some (c2, h2)) (Nat.blt fuel n) : Option (List (Nat × Nat) × Nat)) with
      | none => rw [hp2] at hok; dsimp only at hok; cases hok
      | some p3 =>
        obtain ⟨c3, h3⟩ := p3
        rw [hp2] at hok; dsimp only at hok
        cases keepA <;> cases keepB
        · cases hw : Nat.blt fuel (n - 1)
          · have hw' : Nat.blt fuel (Nat.sub n 1) = false := hw
            rw [hw'] at hp0; exact Or.inr ⟨cur, h, (c1, h1), hp0⟩
          · exact Or.inl rfl
        · cases hw : Nat.blt fuel n
          · rw [hw] at hp2; exact Or.inr ⟨c2, h2, (c3, h3), hp2⟩
          · exact Or.inl rfl
        · cases hw : Nat.blt fuel n
          · rw [hw] at hp1; exact Or.inr ⟨c1, h1, (c2, h2), hp1⟩
          · exact Or.inl rfl
        · cases hw : Nat.blt fuel (n + 1)
          · have hw' : Nat.blt fuel (Nat.add n 1) = false := hw
            rw [hw'] at hok; exact Or.inr ⟨c3, h3, res, hok⟩
          · exact Or.inl rfl
def checkOpV5 (mask goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n x y rawZ op : Nat) (spAll spNoA spNoB spNoAB : Nat)
    (ws0 wsNoA wsNoB wsNoAB : List Nat) (hist : List (Nat × Nat × Nat))
    (tokAB : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  forceWP (canonV2 mask rawZ) (fun z =>
    Bool.rec
      (Bool.rec
        (forceWP (sepPack z) (fun spZ =>
          checkKeepsV5 goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n z spZ spAll spNoA spNoB spNoAB
            ws0 wsNoA wsNoB wsNoAB ((z, x, y) :: hist) (Nat.shiftLeft (Nat.add tokAB op) 2) cur h))
        (some (cur, h)) (memN z ws0))
      (some (cur, h)) (Nat.beq z 0))
def check4OpsV5 (mask goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n x nx y : Nat) (spAll spNoA spNoB spNoAB : Nat)
    (ws0 wsNoA wsNoB wsNoAB : List Nat) (hist : List (Nat × Nat × Nat))
    (tokAB : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  match checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land x y) 0 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur h with
  | none => none
  | some (c1, h1) =>
    match checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.lor x y) 1 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c1 h1 with
    | none => none
    | some (c2, h2) =>
      match checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land x (Nat.xor mask y)) 2 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c2 h2 with
      | none => none
      | some (c3, h3) =>
        checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land nx y) 3 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c3 h3
theorem check4OpsV5_at {mask goal negGoal ep cutBits cutMask count fuel fuel1 n x y spAll spNoA spNoB spNoAB tokAB op h : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 wsNoA wsNoB wsNoAB : List Nat} {hist : List (Nat × Nat × Nat)}
    {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (hop : op < 4)
    (hok : check4OpsV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x (Nat.xor mask x) y
      spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur h = some res) :
    let z := binOp mask op x y
    z = 0 ∨ ws0.contains z = true ∨
      ∃ c hh r, checkKeepsV5 goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n z (sepPack z)
        spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB ((z, x, y) :: hist) (Nat.shiftLeft (Nat.add tokAB op) 2) c hh = some r := by
  unfold check4OpsV5 at hok
  have extract (rawZ op' : Nat) (c0 : List (Nat × Nat)) (h0 : Nat) (r0 : List (Nat × Nat) × Nat)
      (hz : canon mask rawZ = binOp mask op' x y)
      (hrun : checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y rawZ op'
        spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c0 h0 = some r0) :
      binOp mask op' x y = 0 ∨ ws0.contains (binOp mask op' x y) = true ∨
        ∃ c hh r, checkKeepsV5 goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n (binOp mask op' x y)
          (sepPack (binOp mask op' x y)) spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB
          ((binOp mask op' x y, x, y) :: hist) (Nat.shiftLeft (Nat.add tokAB op') 2) c hh = some r := by
    unfold checkOpV5 at hrun
    rw [forceWP_eq, canonV2_eq, hz] at hrun
    cases hz0 : Nat.beq (binOp mask op' x y) 0
    · rw [hz0] at hrun; dsimp only at hrun
      cases hm : memN (binOp mask op' x y) ws0
      · rw [hm] at hrun; dsimp only at hrun
        rw [forceWP_eq] at hrun
        exact Or.inr (Or.inr ⟨c0, h0, r0, hrun⟩)
      · rw [memN_eq] at hm; exact Or.inr (Or.inl hm)
    · exact Or.inl (Nat.beq_eq.mp hz0)
  cases hp0 : checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land x y) 0 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur h with
  | none => rw [hp0] at hok; dsimp only at hok; cases hok
  | some p1 =>
    obtain ⟨c1, h1⟩ := p1; rw [hp0] at hok; dsimp only at hok
    cases hp1 : checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.lor x y) 1 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c1 h1 with
    | none => rw [hp1] at hok; dsimp only at hok; cases hok
    | some p2 =>
      obtain ⟨c2, h2⟩ := p2; rw [hp1] at hok; dsimp only at hok
      cases hp2 : checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land x (Nat.xor mask y)) 2 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c2 h2 with
      | none => rw [hp2] at hok; dsimp only at hok; cases hok
      | some p3 =>
        obtain ⟨c3, h3⟩ := p3; rw [hp2] at hok; dsimp only at hok
        rcases (by omega : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3) with rfl | rfl | rfl | rfl
        · exact extract _ 0 cur h (c1, h1) rfl hp0
        · exact extract _ 1 c1 h1 (c2, h2) rfl hp1
        · exact extract _ 2 c2 h2 (c3, h3) rfl hp2
        · exact extract _ 3 c3 h3 res rfl hok
def loopB_V5 (mask goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n a x nx spAll spNoA : Nat) (ws0 wsNoA : List Nat) (ps : List (Nat × Nat)) (hist : List (Nat × Nat × Nat)) :
    Nat → Nat → List (Nat × Nat) → Nat → Option (List (Nat × Nat) × Nat)
  | 0, _, c, h => some (c, h)
  | rem + 1, b, cur, h =>
    forceWP (getDN ws0 b) (fun y =>
      forceList (dropValF true y ws0) (fun wsNoB =>
        forceList (dropValF true y wsNoA) (fun wsNoAB =>
          forceWP (orSepSkip y ps) (fun spNoB =>
            forceWP (orSepSkip2 x y ps) (fun spNoAB =>
              forceWP (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2) (fun tokAB =>
                match check4OpsV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x nx y spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur h with
                | none => none
                | some (cur1, h1) =>
                  loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a x nx spAll spNoA ws0 wsNoA ps hist rem (Nat.add b 1) cur1 h1))))))
theorem loopB_V5_at {mask goal negGoal ep cutBits cutMask count fuel fuel1 n a x nx spAll spNoA : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 wsNoA : List Nat} {ps : List (Nat × Nat)} {hist : List (Nat × Nat × Nat)}
    {rem b0 b h : Nat} {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (hb1 : b0 ≤ b) (hb2 : b < b0 + rem)
    (hok : loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a x nx spAll spNoA ws0 wsNoA ps hist rem b0 cur h = some res) :
    let y := getDN ws0 b
    ∃ c hh r, check4OpsV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x nx y spAll spNoA
      (orSepSkip y ps) (orSepSkip2 x y ps) ws0 wsNoA (dropValF true y ws0) (dropValF true y wsNoA)
      hist (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2) c hh = some r := by
  induction rem generalizing b0 cur h with
  | zero => omega
  | succ r ih =>
    unfold loopB_V5 at hok
    rw [forceWP_eq, forceList_eq, forceList_eq, forceWP_eq, forceWP_eq, forceWP_eq] at hok
    cases hp : check4OpsV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x nx (getDN ws0 b0) spAll spNoA
      (orSepSkip (getDN ws0 b0) ps) (orSepSkip2 x (getDN ws0 b0) ps) ws0 wsNoA
      (dropValF true (getDN ws0 b0) ws0) (dropValF true (getDN ws0 b0) wsNoA)
      hist (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b0) 2) cur h with
    | none => rw [hp] at hok; dsimp only at hok; cases hok
    | some p1 =>
      obtain ⟨cur1, h1⟩ := p1; rw [hp] at hok; dsimp only at hok
      by_cases heq : b = b0
      · subst heq; exact ⟨cur, h, (cur1, h1), hp⟩
      · exact ih (by change b0 + 1 ≤ b; omega) (by change b < (b0 + 1) + r; omega) hok
def loopA_V5 (mask goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n spAll : Nat) (ws0 : List Nat) (ps : List (Nat × Nat)) (hist : List (Nat × Nat × Nat)) :
    Nat → Nat → List (Nat × Nat) → Nat → Option (List (Nat × Nat) × Nat)
  | 0, _, c, h => some (c, h)
  | rem + 1, a, cur, h =>
    forceWP (getDN ws0 a) (fun x =>
      forceList (dropValF true x ws0) (fun wsNoA =>
        forceWP (Nat.xor mask x) (fun nx =>
          forceWP (orSepSkip x ps) (fun spNoA =>
            match loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a x nx spAll spNoA ws0 wsNoA ps hist (Nat.sub n (Nat.add a 1)) (Nat.add a 1) cur h with
            | none => none
            | some (cur1, h1) =>
              loopA_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n spAll ws0 ps hist rem (Nat.add a 1) cur1 h1))))
theorem loopA_V5_at {mask goal negGoal ep cutBits cutMask count fuel fuel1 n spAll : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 : List Nat} {ps : List (Nat × Nat)} {hist : List (Nat × Nat × Nat)}
    {rem a0 a h : Nat} {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (ha1 : a0 ≤ a) (ha2 : a < a0 + rem)
    (hok : loopA_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n spAll ws0 ps hist rem a0 cur h = some res) :
    let x := getDN ws0 a
    ∃ c hh r, loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a x (Nat.xor mask x) spAll
      (orSepSkip x ps) ws0 (dropValF true x ws0) ps hist (Nat.sub n (Nat.add a 1)) (Nat.add a 1) c hh = some r := by
  induction rem generalizing a0 cur h with
  | zero => omega
  | succ r ih =>
    unfold loopA_V5 at hok
    rw [forceWP_eq, forceList_eq, forceWP_eq, forceWP_eq] at hok
    cases hp : loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a0 (getDN ws0 a0) (Nat.xor mask (getDN ws0 a0)) spAll
      (orSepSkip (getDN ws0 a0) ps) ws0 (dropValF true (getDN ws0 a0) ws0) ps hist (Nat.sub n (Nat.add a0 1)) (Nat.add a0 1) cur h with
    | none => rw [hp] at hok; dsimp only at hok; cases hok
    | some p1 =>
      obtain ⟨cur1, h1⟩ := p1; rw [hp] at hok; dsimp only at hok
      by_cases heq : a = a0
      · subst heq; exact ⟨cur, h, (cur1, h1), hp⟩
      · exact ih (by change a0 + 1 ≤ a; omega) (by change a < (a0 + 1) + r; omega) hok
def dagCheckNodeV5 (mask goal ep cutBits cutMask : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (cursors : Nat → List (Nat × Nat)) (nodeHints : Nat → Nat) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some (fuel, ws, hist) =>
    forceWs ws (fun ws0 =>
      forceWP (lenN ws0) (fun n =>
        Bool.rec
          (Bool.rec
            (Bool.rec false
              (forceW (Nat.xor mask goal) (fun negGoal =>
                forceW (Nat.sub fuel 1) (fun fuel1 =>
                  forceSepPairs ws0 (fun ps =>
                    forceW (orSepAll ps) (fun spAll =>
                      forceW (nodeHints (Nat.add i 1)) (fun h0 =>
                        match loopA_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n spAll ws0 ps hist n 0 (cursors (Nat.add i 1)) h0 with
                        | none => false
                        | some _ => true))))))
              (Nat.blt n 17))
            true (Nat.beq fuel 0))
          false (memN goal ws0)))
def stepRootV5 (goal negGoal ep cutBits cutMask count fuel : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (ws : List Nat) (tok : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  Bool.rec
    (match cur with
     | (t, dest) :: tl =>
       Bool.rec
         (hintCloseLeafV5 goal negGoal ep cutBits cutMask bounds fuel ws [] (orSep ws) cur h)
         (Bool.rec none
           (match states dest with
            | none => none
            | some saved =>
              Bool.rec none (Bool.rec none (some (tl, h)) (eqListN saved.2.1 ws)) (Nat.beq saved.1 fuel))
           (Nat.blt dest count))
         (Nat.beq tok t)
     | [] =>
       hintCloseLeafV5 goal negGoal ep cutBits cutMask bounds fuel ws [] (orSep ws) [] h)
    (some (cur, h)) (Nat.blt (Nat.add fuel 1) (lenN ws))
def loopRootsV5 (goal negGoal ep cutBits cutMask count fuel : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (stock : List Nat) : Nat → Nat → List (Nat × Nat) → Nat → Option (List (Nat × Nat) × Nat)
  | 0, _, c, h => some (c, h)
  | rem + 1, tok, cur, h =>
    forceList (subsetWordsF stock tok) (fun ws =>
      match stepRootV5 goal negGoal ep cutBits cutMask count fuel bounds states ws tok cur h with
      | none => none
      | some (cur1, h1) =>
        loopRootsV5 goal negGoal ep cutBits cutMask count fuel bounds states stock rem (Nat.add tok 1) cur1 h1)
def dagCheckRootsV5 (mask goal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (rootCur : List (Nat × Nat)) (rootHint : Nat) (stock : List Nat) (fuel : Nat) : Bool :=
  match loopRootsV5 goal (Nat.xor mask goal) ep cutBits cutMask count fuel bounds states stock (Nat.shiftLeft 1 (lenN stock)) 0 rootCur rootHint with
  | none => false
  | some _ => true
theorem loopRootsV5_at {goal negGoal ep cutBits cutMask count fuel : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {stock : List Nat} {rem t0 tok h : Nat} {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (ht1 : t0 ≤ tok) (ht2 : tok < t0 + rem)
    (hok : loopRootsV5 goal negGoal ep cutBits cutMask count fuel bounds states stock rem t0 cur h = some res) :
    ∃ c hh r, stepRootV5 goal negGoal ep cutBits cutMask count fuel bounds states (subsetWordsF stock tok) tok c hh = some r := by
  induction rem generalizing t0 cur h with
  | zero => omega
  | succ r ih =>
    unfold loopRootsV5 at hok
    rw [forceList_eq] at hok
    cases hp : stepRootV5 goal negGoal ep cutBits cutMask count fuel bounds states (subsetWordsF stock t0) t0 cur h with
    | none => rw [hp] at hok; dsimp only at hok; cases hok
    | some p1 =>
      obtain ⟨cur1, h1⟩ := p1; rw [hp] at hok; dsimp only at hok
      by_cases heq : tok = t0
      · subst heq; exact ⟨cur, h, (cur1, h1), hp⟩
      · exact ih (by change t0 + 1 ≤ tok; omega) (by change tok < (t0 + 1) + r; omega) hok
theorem dagAllNodesV5 {mask goal cutBits cutMask fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {cursors : Nat → List (Nat × Nat)} {nodeHints : Nat → Nat}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s))
    (snd : stock.Nodup)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeV5 mask goal (edgePack mask goal) cutBits cutMask bounds count
      (dagTrace mask stock fuel forest) cursors nodeHints i = true) :
    ∀ cap i st, i < count → dagTrace mask stock fuel forest i = some st →
      st.1 = cap → ∀ k, k ≤ cap → ¬LiveBin mask goal k st.2.1.toFinset := by
  intro cap
  induction cap using Nat.strong_induction_on with
  | ind cap ih =>
    intro i st hi htr hcap k hk hlive
    obtain ⟨rem, ws, hist⟩ := st
    dsimp only at hcap hlive
    have nd : ws.Nodup := dagTrace_nodup snd htr
    obtain ⟨hv, hcov⟩ := dagTrace_valid htr
    dsimp only at hv hcov
    have hchk := hnodes i (Nat.zero_le i) hi
    unfold dagCheckNodeV5 at hchk
    rw [htr] at hchk; dsimp only at hchk
    rw [forceWs_eq, forceWP_eq, lenN_eq, memN_eq] at hchk
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
          rw [forceW_eq, forceW_eq, forceSepPairs_eq, forceW_eq, forceW_eq] at hchk
          cases hloop : loopA_V5 mask goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask count bounds
              (dagTrace mask stock fuel forest) rem (Nat.sub rem 1) ws.length (orSepAll (mapSep ws)) ws (mapSep ws) hist
              ws.length 0 (cursors (Nat.add i 1)) (nodeHints (Nat.add i 1)) with
          | none => rw [hloop] at hchk; exact Bool.noConfusion hchk
          | some resA =>
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
            obtain ⟨cA, hA, rA, hB⟩ := loopA_V5_at (a := a) (Nat.zero_le a) (by omega) hloop
            obtain ⟨cB, hB', rB, hO⟩ := loopB_V5_at (b := b) (by change a + 1 ≤ b; omega) (by change b < (a + 1) + (ws.length - (a + 1)); omega) hB
            simp only [getDN_eq, dropValF_eq, orSepAll_mapSep, orSepSkip_mapSep, orSepSkip2_mapSep] at hO
            set x := ws.getD a 0
            set y := ws.getD b 0
            set z := binOp mask op x y
            have hznz : z ≠ 0 := hzeq.symm ▸ hz0
            have hznm : ws.contains z = false := by
              cases h : ws.contains z
              · rfl
              · exact absurd (List.mem_toFinset.mpr (List.contains_iff_mem.mp h)) (hzeq.symm ▸ hf0)
            rcases check4OpsV5_at hop_lt hO with hz' | hcm | ⟨cK, hK', rK, hK⟩
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
              have hv' : HistValid mask stock ((z, x, y) :: hist) :=
                ⟨⟨op, hop_lt, rfl⟩, hcov x hxM, hcov y hyM, hv⟩
              have hcov' : WsCovered stock ((z, x, y) :: hist) (z :: rest) := by
                intro w hw
                rcases List.mem_cons.mp hw with rfl | hw'
                · exact Or.inr ⟨x, y, List.mem_cons_self⟩
                · have hwm : w ∈ ws := (dropVal_mem.mp (dropVal_mem.mp hw').1).1
                  rcases hcov w hwm with hst | ⟨u, v, hm⟩
                  · exact Or.inl hst
                  · exact Or.inr ⟨u, v, List.mem_cons_of_mem _ hm⟩
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
              have hka := checkKeepsV5_at hK keepA keepB
              have finish {tok' hh' : Nat} {c' : List (Nat × Nat)} {rr : List (Nat × Nat) × Nat}
                  (hstep : stepLeafV5 goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask count bounds
                    (dagTrace mask stock fuel forest) (Nat.sub rem 1) z (sepPack z) (orSep rest) rest ((z, x, y) :: hist) tok' c' hh' = some rr) : False := by
                obtain ⟨dest, hdest, saved, htr2, hfEq, hwEq⟩ :=
                  stepLeafV5_ref hgm hknown hsub hgoals hstk hv' hcov' hnd_u (k := k') (by change k' ≤ rem - 1; omega) hlive_u hstep
                exact ih (rem - 1) (by omega) dest saved hdest htr2 hfEq k' (by omega) (hwEq ▸ hlive_s)
              cases keepA <;> cases keepB
              · rcases hka with hwide | ⟨c', hh', rr, hst⟩
                · have := Nat.blt_eq.mp hwide; simp only [Bool.false_eq_true, ite_false] at hlen'; omega
                · rw [hdropComm] at hst; exact finish hst
              · rcases hka with hwide | ⟨c', hh', rr, hst⟩
                · have := Nat.blt_eq.mp hwide; simp only [Bool.false_eq_true, ite_false, ite_true] at hlen'; omega
                · exact finish hst
              · rcases hka with hwide | ⟨c', hh', rr, hst⟩
                · have := Nat.blt_eq.mp hwide; simp only [Bool.false_eq_true, ite_false, ite_true] at hlen'; omega
                · exact finish hst
              · rcases hka with hwide | ⟨c', hh', rr, hst⟩
                · have := Nat.blt_eq.mp hwide; simp only [ite_true] at hlen'; omega
                · exact finish hst
      · rw [hcg] at hchk; exact Bool.noConfusion hchk
def nodupB : List Nat → Bool
  | [] => true
  | w :: ws => !memN w ws && nodupB ws
theorem nodupB_spec {l : List Nat} (h : nodupB l = true) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons w ws ih =>
    unfold nodupB at h
    simp only [Bool.and_eq_true, Bool.not_eq_true', memN_eq] at h
    exact List.nodup_cons.mpr ⟨fun hm => by rw [List.contains_iff_mem.mpr hm] at h; exact Bool.noConfusion h.1, ih h.2⟩
theorem kn_nil : KnownBin [] := fun _ h => nomatch h
theorem kn_cons {m : Nat} {s : List Nat} {l g : Nat} {bs : List (Nat × List Nat × Nat × Nat)}
    (h : LowerBin m s g l) (hs : KnownBin bs) : KnownBin ((m, s, l, g) :: bs) := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact h
  · exact hs b hb
def checkSliceMetaV5 (mask goal ep : Nat) (stock : List Nat)
    (bounds : List (Nat × List Nat × Nat × Nat)) : Bool :=
  Nat.beq (Nat.land goal mask) goal &&
  !Nat.beq goal 0 &&
  stock.all (fun w => Nat.beq (canon mask w) w) &&
  nodupB stock &&
  Nat.beq ep (edgePack mask goal) &&
  bounds.all (fun b =>
    Nat.beq (Nat.land mask b.1) b.1 &&
    Nat.beq (canon b.1 goal) b.2.2.2 &&
    !Nat.beq b.2.2.2 0 &&
    stock.all (fun s => availB b.2.1 (canon b.1 s)))
theorem lowerDagV5 {mask goal ep cutBits cutMask fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {cursors : Nat → List (Nat × Nat)} {nodeHints : Nat → Nat}
    (hknown : KnownBin bounds)
    (hroots : dagCheckRootsV5 mask goal ep cutBits cutMask count bounds
      (dagTraceF mask stock fuel forest) (cursors 0) (nodeHints 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeV5 mask goal ep cutBits cutMask bounds count
      (dagTraceF mask stock fuel forest) cursors nodeHints i = true)
    (hmeta : checkSliceMetaV5 mask goal ep stock bounds = true) :
    LowerBin mask stock goal (fuel + 1) := by
  unfold checkSliceMetaV5 at hmeta
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hmeta
  obtain ⟨⟨⟨⟨⟨hgmB, hgnzB⟩, hcs⟩, hndB⟩, hepB⟩, hbdB⟩ := hmeta
  have hgm : Masked mask goal := Nat.beq_eq.mp hgmB
  have hgnz : goal ≠ 0 := fun h => by rw [h] at hgnzB; exact Bool.noConfusion hgnzB
  have snd : stock.Nodup := nodupB_spec hndB
  have hep : ep = edgePack mask goal := Nat.beq_eq.mp hepB
  have hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1 := fun b hb => by
    have h := List.all_eq_true.mp hbdB b hb
    simp only [Bool.and_eq_true] at h
    exact Nat.beq_eq.mp h.1.1.1
  have hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := fun b hb => by
    have h := List.all_eq_true.mp hbdB b hb
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨Nat.beq_eq.mp h.1.1.2, fun h0 => by rw [h0] at h; exact Bool.noConfusion h.1.2⟩
  have hstkB : ∀ b ∈ bounds, stock.all (fun s => availB b.2.1 (canon b.1 s)) = true := fun b hb => by
    have h := List.all_eq_true.mp hbdB b hb
    simp only [Bool.and_eq_true] at h
    exact h.2
  subst hep
  have hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s) := fun b hb s hs =>
    availB_spec.mp (List.all_eq_true.mp (hstkB b hb) s hs)
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
  unfold dagCheckRootsV5 at hroots
  have hpow : Nat.shiftLeft 1 (lenN stock) = 2 ^ stock.length := by
    rw [lenN_eq]; change 1 <<< stock.length = _; rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [hpow] at hroots
  cases hrl : loopRootsV5 goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask count fuel bounds
      (dagTrace mask stock fuel forest) stock (2 ^ stock.length) 0 (cursors 0) (nodeHints 0) with
  | none => rw [hrl] at hroots; exact Bool.noConfusion hroots
  | some resR =>
    obtain ⟨c, hh, rr, hsr⟩ := loopRootsV5_at (tok := tok) (Nat.zero_le tok) (by omega) hrl
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
    have hcov0 : WsCovered stock [] (subsetWords stock tok) :=
      fun w hw => Or.inl (subsetWords_subset stock tok w hw)
    have hcl := hintCloseLeafV5_open (cutBits := cutBits) (cutMask := cutMask) (fuel1 := fuel) (hist1 := []) (cur := c) (h := hh)
      hgm hknown hsub hgoals hstk trivial hcov0 hnd (k := k) (by omega) hlive'
    unfold stepRootV5 at hsr
    rw [hnw] at hsr; dsimp only at hsr
    cases c with
    | nil => dsimp only at hsr; rw [hcl] at hsr; cases hsr
    | cons hd tl =>
      obtain ⟨t, dest⟩ := hd
      dsimp only at hsr
      cases ht : Nat.beq tok t
      · rw [ht] at hsr; dsimp only at hsr; rw [hcl] at hsr; cases hsr
      · rw [ht] at hsr; dsimp only at hsr
        cases hltc : Nat.blt dest count
        · rw [hltc] at hsr; dsimp only at hsr; cases hsr
        · rw [hltc] at hsr; dsimp only at hsr
          cases htr2 : dagTrace mask stock fuel forest dest with
          | none => rw [htr2] at hsr; dsimp only at hsr; cases hsr
          | some saved =>
            rw [htr2] at hsr; dsimp only at hsr
            cases hf : Nat.beq saved.1 fuel
            · rw [hf] at hsr; dsimp only at hsr; cases hsr
            · rw [hf] at hsr; dsimp only at hsr
              cases heq : eqListN saved.2.1 (subsetWords stock tok)
              · rw [heq] at hsr; dsimp only at hsr; cases hsr
              · rw [eqListN_eq, beq_iff_eq] at heq
                exact dagAllNodesV5 hgm hknown hsub hgoals hstk snd hnodes fuel dest saved
                  (Nat.blt_eq.mp hltc) htr2 (Nat.beq_eq.mp hf) k (by omega) (heq ▸ hlive')
def unpackF (data width idx : Nat) : Nat :=
  Nat.land (Nat.shiftRight data (Nat.mul idx width)) (Nat.sub (Nat.shiftLeft 1 width) 1)
def unpackForestF (data pBits tBits : Nat) : Nat → Nat × Nat := fun i =>
  let w := Nat.add pBits tBits
  let code := unpackF data w i
  (Nat.shiftRight code tBits, Nat.land code (Nat.sub (Nat.shiftLeft 1 tBits) 1))
def unpackListAux (data off w wMask tokBits tokMask : Nat) : Nat → List (Nat × Nat) → List (Nat × Nat)
  | 0, acc => acc
  | k + 1, acc =>
    forceWP (Nat.land (Nat.shiftRight data (Nat.mul (Nat.add off k) w)) wMask) (fun code =>
      unpackListAux data off w wMask tokBits tokMask k ((Nat.land code tokMask, Nat.shiftRight code tokBits) :: acc))
def unpackCursorV5 (index data idxW idxMask sizeBits sizeMask tokBits tokMask w wMask : Nat) :
    Nat → List (Nat × Nat) :=
  fun parent =>
    forceWP (Nat.land (Nat.shiftRight index (Nat.mul parent idxW)) idxMask) (fun entry =>
      unpackListAux data (Nat.shiftRight entry sizeBits) w wMask tokBits tokMask (Nat.land entry sizeMask) [])
def unpackHintV5 (index data idxW idxMask lenBits lenMask : Nat) : Nat → Nat :=
  fun parent =>
    forceWP (Nat.land (Nat.shiftRight index (Nat.mul parent idxW)) idxMask) (fun entry =>
      forceWP (Nat.land entry lenMask) (fun hlen =>
        Bool.rec
          (Nat.land (Nat.shiftRight data (Nat.shiftRight entry lenBits)) (Nat.sub (Nat.shiftLeft 1 hlen) 1))
          0 (Nat.beq hlen 0)))

def m_0 : Nat := 0xc000c000c000c0
def s_0 : List Nat := [0x40004000400040, 0xc0000000c0, 0xc000c0]
def g_0 : Nat := 0x40004000c0
def ep_0 : Nat := 0x40008000000040000000800000000000000000000000000000000000000000000000000000004000400000
def bds_0 : List (Nat × List Nat × Nat × Nat) := []
def cur_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_0 : Nat → Nat := fun _ => 0
def f_0 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_0 : Nat → Bool := dagCheckNodeV5 m_0 g_0 ep_0 1 1 bds_0 1 (dagTraceF m_0 s_0 3 f_0) cur_0 nh_0
set_option maxHeartbeats 0 in
theorem rc_0 : dagCheckRootsV5 m_0 g_0 ep_0 1 1 1 bds_0 (dagTraceF m_0 s_0 3 f_0) (cur_0 0) (nh_0 0) s_0 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_0 : treeBlockF 0 1 ch_0 = true := by decide +kernel
theorem nc_0 : ∀ i, 0 ≤ i → i < 1 → ch_0 i = true := fun _ h1 h2 => treeBlockF_at nb_0 h1 h2
theorem lb_0 : LowerBin m_0 s_0 g_0 4 :=
  lowerDagV5 (kn_nil) rc_0 nc_0 (by decide +kernel)

def m_1 : Nat := 0xff00
def s_1 : List Nat := [0x5500, 0x3300, 0xf00]
def g_1 : Nat := 0x1700
def ep_1 : Nat := 0x60000000000000012000000000000001400
def bds_1 : List (Nat × List Nat × Nat × Nat) := []
def cur_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_1 : Nat → Nat := fun _ => 0
def f_1 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_1 : Nat → Bool := dagCheckNodeV5 m_1 g_1 ep_1 1 1 bds_1 1 (dagTraceF m_1 s_1 3 f_1) cur_1 nh_1
set_option maxHeartbeats 0 in
theorem rc_1 : dagCheckRootsV5 m_1 g_1 ep_1 1 1 1 bds_1 (dagTraceF m_1 s_1 3 f_1) (cur_1 0) (nh_1 0) s_1 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_1 : treeBlockF 0 1 ch_1 = true := by decide +kernel
theorem nc_1 : ∀ i, 0 ≤ i → i < 1 → ch_1 i = true := fun _ h1 h2 => treeBlockF_at nb_1 h1 h2
theorem lb_1 : LowerBin m_1 s_1 g_1 4 :=
  lowerDagV5 (kn_nil) rc_1 nc_1 (by decide +kernel)

def m_2 : Nat := 0xf0f0000
def s_2 : List Nat := [0x5050000, 0x3030000, 0xf0000]
def g_2 : Nat := 0x1070000
def ep_2 : Nat := 0x60000000000000000000000000000010200000000000001040000
def bds_2 : List (Nat × List Nat × Nat × Nat) := []
def cur_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_2 : Nat → Nat := fun _ => 0
def f_2 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_2 : Nat → Bool := dagCheckNodeV5 m_2 g_2 ep_2 1 1 bds_2 1 (dagTraceF m_2 s_2 3 f_2) cur_2 nh_2
set_option maxHeartbeats 0 in
theorem rc_2 : dagCheckRootsV5 m_2 g_2 ep_2 1 1 1 bds_2 (dagTraceF m_2 s_2 3 f_2) (cur_2 0) (nh_2 0) s_2 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_2 : treeBlockF 0 1 ch_2 = true := by decide +kernel
theorem nc_2 : ∀ i, 0 ≤ i → i < 1 → ch_2 i = true := fun _ h1 h2 => treeBlockF_at nb_2 h1 h2
theorem lb_2 : LowerBin m_2 s_2 g_2 4 :=
  lowerDagV5 (kn_nil) rc_2 nc_2 (by decide +kernel)

def m_3 : Nat := 0xf0f000000000000
def s_3 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_3 : Nat := 0x107000000000000
def ep_3 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
def bds_3 : List (Nat × List Nat × Nat × Nat) := []
def cur_3 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_3 : Nat → Nat := fun _ => 0
def f_3 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_3 : Nat → Bool := dagCheckNodeV5 m_3 g_3 ep_3 1 1 bds_3 1 (dagTraceF m_3 s_3 3 f_3) cur_3 nh_3
set_option maxHeartbeats 0 in
theorem rc_3 : dagCheckRootsV5 m_3 g_3 ep_3 1 1 1 bds_3 (dagTraceF m_3 s_3 3 f_3) (cur_3 0) (nh_3 0) s_3 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_3 : treeBlockF 0 1 ch_3 = true := by decide +kernel
theorem nc_3 : ∀ i, 0 ≤ i → i < 1 → ch_3 i = true := fun _ h1 h2 => treeBlockF_at nb_3 h1 h2
theorem lb_3 : LowerBin m_3 s_3 g_3 4 :=
  lowerDagV5 (kn_nil) rc_3 nc_3 (by decide +kernel)

def m_4 : Nat := 0x5050505000000000
def s_4 : List Nat := [0x1010101000000000, 0x50005000000000, 0x505000000000]
def g_4 : Nat := 0x10105000000000
def ep_4 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000000000000000000
def bds_4 : List (Nat × List Nat × Nat × Nat) := []
def cur_4 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_4 : Nat → Nat := fun _ => 0
def f_4 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_4 : Nat → Bool := dagCheckNodeV5 m_4 g_4 ep_4 1 1 bds_4 1 (dagTraceF m_4 s_4 3 f_4) cur_4 nh_4
set_option maxHeartbeats 0 in
theorem rc_4 : dagCheckRootsV5 m_4 g_4 ep_4 1 1 1 bds_4 (dagTraceF m_4 s_4 3 f_4) (cur_4 0) (nh_4 0) s_4 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_4 : treeBlockF 0 1 ch_4 = true := by decide +kernel
theorem nc_4 : ∀ i, 0 ≤ i → i < 1 → ch_4 i = true := fun _ h1 h2 => treeBlockF_at nb_4 h1 h2
theorem lb_4 : LowerBin m_4 s_4 g_4 4 :=
  lowerDagV5 (kn_nil) rc_4 nc_4 (by decide +kernel)

def m_5 : Nat := 0x5500550000000000
def s_5 : List Nat := [0x1100110000000000, 0x500050000000000, 0x550000000000]
def g_5 : Nat := 0x100150000000000
def ep_5 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000000000000000000
def bds_5 : List (Nat × List Nat × Nat × Nat) := []
def cur_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_5 : Nat → Nat := fun _ => 0
def f_5 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_5 : Nat → Bool := dagCheckNodeV5 m_5 g_5 ep_5 1 1 bds_5 1 (dagTraceF m_5 s_5 3 f_5) cur_5 nh_5
set_option maxHeartbeats 0 in
theorem rc_5 : dagCheckRootsV5 m_5 g_5 ep_5 1 1 1 bds_5 (dagTraceF m_5 s_5 3 f_5) (cur_5 0) (nh_5 0) s_5 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_5 : treeBlockF 0 1 ch_5 = true := by decide +kernel
theorem nc_5 : ∀ i, 0 ≤ i → i < 1 → ch_5 i = true := fun _ h1 h2 => treeBlockF_at nb_5 h1 h2
theorem lb_5 : LowerBin m_5 s_5 g_5 4 :=
  lowerDagV5 (kn_nil) rc_5 nc_5 (by decide +kernel)

def m_6 : Nat := 0x3300330000000000
def s_6 : List Nat := [0x1100110000000000, 0x300030000000000, 0x330000000000]
def g_6 : Nat := 0x100130000000000
def ep_6 : Nat := 0x1200000000000000000000000000010002000000000000000000000000000100100000000000
def bds_6 : List (Nat × List Nat × Nat × Nat) := []
def cur_6 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_6 : Nat → Nat := fun _ => 0
def f_6 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_6 : Nat → Bool := dagCheckNodeV5 m_6 g_6 ep_6 1 1 bds_6 1 (dagTraceF m_6 s_6 3 f_6) cur_6 nh_6
set_option maxHeartbeats 0 in
theorem rc_6 : dagCheckRootsV5 m_6 g_6 ep_6 1 1 1 bds_6 (dagTraceF m_6 s_6 3 f_6) (cur_6 0) (nh_6 0) s_6 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_6 : treeBlockF 0 1 ch_6 = true := by decide +kernel
theorem nc_6 : ∀ i, 0 ≤ i → i < 1 → ch_6 i = true := fun _ h1 h2 => treeBlockF_at nb_6 h1 h2
theorem lb_6 : LowerBin m_6 s_6 g_6 4 :=
  lowerDagV5 (kn_nil) rc_6 nc_6 (by decide +kernel)

def m_7 : Nat := 0xf000f0000000000
def s_7 : List Nat := [0x500050000000000, 0x300030000000000, 0xf0000000000]
def g_7 : Nat := 0x100070000000000
def ep_7 : Nat := 0x600000000000000000000000000000000000000000001000200000000000100040000000000
def bds_7 : List (Nat × List Nat × Nat × Nat) := []
def cur_7 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_7 : Nat → Nat := fun _ => 0
def f_7 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_7 : Nat → Bool := dagCheckNodeV5 m_7 g_7 ep_7 1 1 bds_7 1 (dagTraceF m_7 s_7 3 f_7) cur_7 nh_7
set_option maxHeartbeats 0 in
theorem rc_7 : dagCheckRootsV5 m_7 g_7 ep_7 1 1 1 bds_7 (dagTraceF m_7 s_7 3 f_7) (cur_7 0) (nh_7 0) s_7 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_7 : treeBlockF 0 1 ch_7 = true := by decide +kernel
theorem nc_7 : ∀ i, 0 ≤ i → i < 1 → ch_7 i = true := fun _ h1 h2 => treeBlockF_at nb_7 h1 h2
theorem lb_7 : LowerBin m_7 s_7 g_7 4 :=
  lowerDagV5 (kn_nil) rc_7 nc_7 (by decide +kernel)

def m_8 : Nat := 0xff000000000000
def s_8 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_8 : Nat := 0x17000000000000
def ep_8 : Nat := 0x600000000000000120000000000000014000000000000
def bds_8 : List (Nat × List Nat × Nat × Nat) := []
def cur_8 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_8 : Nat → Nat := fun _ => 0
def f_8 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_8 : Nat → Bool := dagCheckNodeV5 m_8 g_8 ep_8 1 1 bds_8 1 (dagTraceF m_8 s_8 3 f_8) cur_8 nh_8
set_option maxHeartbeats 0 in
theorem rc_8 : dagCheckRootsV5 m_8 g_8 ep_8 1 1 1 bds_8 (dagTraceF m_8 s_8 3 f_8) (cur_8 0) (nh_8 0) s_8 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_8 : treeBlockF 0 1 ch_8 = true := by decide +kernel
theorem nc_8 : ∀ i, 0 ≤ i → i < 1 → ch_8 i = true := fun _ h1 h2 => treeBlockF_at nb_8 h1 h2
theorem lb_8 : LowerBin m_8 s_8 g_8 4 :=
  lowerDagV5 (kn_nil) rc_8 nc_8 (by decide +kernel)

def m_9 : Nat := 0x4444444400000000
def s_9 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_9 : Nat := 0x4044400000000
def ep_9 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
def bds_9 : List (Nat × List Nat × Nat × Nat) := []
def cur_9 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_9 : Nat → Nat := fun _ => 0
def f_9 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_9 : Nat → Bool := dagCheckNodeV5 m_9 g_9 ep_9 1 1 bds_9 1 (dagTraceF m_9 s_9 3 f_9) cur_9 nh_9
set_option maxHeartbeats 0 in
theorem rc_9 : dagCheckRootsV5 m_9 g_9 ep_9 1 1 1 bds_9 (dagTraceF m_9 s_9 3 f_9) (cur_9 0) (nh_9 0) s_9 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_9 : treeBlockF 0 1 ch_9 = true := by decide +kernel
theorem nc_9 : ∀ i, 0 ≤ i → i < 1 → ch_9 i = true := fun _ h1 h2 => treeBlockF_at nb_9 h1 h2
theorem lb_9 : LowerBin m_9 s_9 g_9 4 :=
  lowerDagV5 (kn_nil) rc_9 nc_9 (by decide +kernel)

def m_10 : Nat := 0x22222222
def s_10 : List Nat := [0x2020202, 0x220022, 0x2222]
def g_10 : Nat := 0x20222
def ep_10 : Nat := 0x2200000000000020020000000000002020000000000000000000000000000000000
def bds_10 : List (Nat × List Nat × Nat × Nat) := []
def cur_10 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_10 : Nat → Nat := fun _ => 0
def f_10 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_10 : Nat → Bool := dagCheckNodeV5 m_10 g_10 ep_10 1 1 bds_10 1 (dagTraceF m_10 s_10 3 f_10) cur_10 nh_10
set_option maxHeartbeats 0 in
theorem rc_10 : dagCheckRootsV5 m_10 g_10 ep_10 1 1 1 bds_10 (dagTraceF m_10 s_10 3 f_10) (cur_10 0) (nh_10 0) s_10 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_10 : treeBlockF 0 1 ch_10 = true := by decide +kernel
theorem nc_10 : ∀ i, 0 ≤ i → i < 1 → ch_10 i = true := fun _ h1 h2 => treeBlockF_at nb_10 h1 h2
theorem lb_10 : LowerBin m_10 s_10 g_10 4 :=
  lowerDagV5 (kn_nil) rc_10 nc_10 (by decide +kernel)

def m_11 : Nat := 0xff0000000000
def s_11 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_11 : Nat := 0x170000000000
def ep_11 : Nat := 0x6000000000000001200000000000000140000000000
def bds_11 : List (Nat × List Nat × Nat × Nat) := []
def cur_11 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_11 : Nat → Nat := fun _ => 0
def f_11 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_11 : Nat → Bool := dagCheckNodeV5 m_11 g_11 ep_11 1 1 bds_11 1 (dagTraceF m_11 s_11 3 f_11) cur_11 nh_11
set_option maxHeartbeats 0 in
theorem rc_11 : dagCheckRootsV5 m_11 g_11 ep_11 1 1 1 bds_11 (dagTraceF m_11 s_11 3 f_11) (cur_11 0) (nh_11 0) s_11 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_11 : treeBlockF 0 1 ch_11 = true := by decide +kernel
theorem nc_11 : ∀ i, 0 ≤ i → i < 1 → ch_11 i = true := fun _ h1 h2 => treeBlockF_at nb_11 h1 h2
theorem lb_11 : LowerBin m_11 s_11 g_11 4 :=
  lowerDagV5 (kn_nil) rc_11 nc_11 (by decide +kernel)

def m_12 : Nat := 0x5050000050500000
def s_12 : List Nat := [0x1010000010100000, 0x50000000500000, 0x50500000]
def g_12 : Nat := 0x10000010500000
def ep_12 : Nat := 0x1040000000000000000000000010000000400000000000000000000000100000100000000000000000000000
def bds_12 : List (Nat × List Nat × Nat × Nat) := []
def cur_12 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_12 : Nat → Nat := fun _ => 0
def f_12 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_12 : Nat → Bool := dagCheckNodeV5 m_12 g_12 ep_12 1 1 bds_12 1 (dagTraceF m_12 s_12 3 f_12) cur_12 nh_12
set_option maxHeartbeats 0 in
theorem rc_12 : dagCheckRootsV5 m_12 g_12 ep_12 1 1 1 bds_12 (dagTraceF m_12 s_12 3 f_12) (cur_12 0) (nh_12 0) s_12 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_12 : treeBlockF 0 1 ch_12 = true := by decide +kernel
theorem nc_12 : ∀ i, 0 ≤ i → i < 1 → ch_12 i = true := fun _ h1 h2 => treeBlockF_at nb_12 h1 h2
theorem lb_12 : LowerBin m_12 s_12 g_12 4 :=
  lowerDagV5 (kn_nil) rc_12 nc_12 (by decide +kernel)

def m_13 : Nat := 0x5555000000000000
def s_13 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_13 : Nat := 0x115000000000000
def ep_13 : Nat := 0x14000000000000010400000000000001100000000000000000000000000000
def bds_13 : List (Nat × List Nat × Nat × Nat) := []
def cur_13 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_13 : Nat → Nat := fun _ => 0
def f_13 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_13 : Nat → Bool := dagCheckNodeV5 m_13 g_13 ep_13 1 1 bds_13 1 (dagTraceF m_13 s_13 3 f_13) cur_13 nh_13
set_option maxHeartbeats 0 in
theorem rc_13 : dagCheckRootsV5 m_13 g_13 ep_13 1 1 1 bds_13 (dagTraceF m_13 s_13 3 f_13) (cur_13 0) (nh_13 0) s_13 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_13 : treeBlockF 0 1 ch_13 = true := by decide +kernel
theorem nc_13 : ∀ i, 0 ≤ i → i < 1 → ch_13 i = true := fun _ h1 h2 => treeBlockF_at nb_13 h1 h2
theorem lb_13 : LowerBin m_13 s_13 g_13 4 :=
  lowerDagV5 (kn_nil) rc_13 nc_13 (by decide +kernel)

def m_14 : Nat := 0x3333000000000000
def s_14 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_14 : Nat := 0x113000000000000
def ep_14 : Nat := 0x12000000000000010200000000000000000000000000000110000000000000
def bds_14 : List (Nat × List Nat × Nat × Nat) := []
def cur_14 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_14 : Nat → Nat := fun _ => 0
def f_14 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_14 : Nat → Bool := dagCheckNodeV5 m_14 g_14 ep_14 1 1 bds_14 1 (dagTraceF m_14 s_14 3 f_14) cur_14 nh_14
set_option maxHeartbeats 0 in
theorem rc_14 : dagCheckRootsV5 m_14 g_14 ep_14 1 1 1 bds_14 (dagTraceF m_14 s_14 3 f_14) (cur_14 0) (nh_14 0) s_14 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_14 : treeBlockF 0 1 ch_14 = true := by decide +kernel
theorem nc_14 : ∀ i, 0 ≤ i → i < 1 → ch_14 i = true := fun _ h1 h2 => treeBlockF_at nb_14 h1 h2
theorem lb_14 : LowerBin m_14 s_14 g_14 4 :=
  lowerDagV5 (kn_nil) rc_14 nc_14 (by decide +kernel)

def m_15 : Nat := 0xf000f00
def s_15 : List Nat := [0x5000500, 0x3000300, 0xf00]
def g_15 : Nat := 0x1000700
def ep_15 : Nat := 0x6000000000000000000000000000000000000000000010002000000000001000400
def bds_15 : List (Nat × List Nat × Nat × Nat) := []
def cur_15 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_15 : Nat → Nat := fun _ => 0
def f_15 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_15 : Nat → Bool := dagCheckNodeV5 m_15 g_15 ep_15 1 1 bds_15 1 (dagTraceF m_15 s_15 3 f_15) cur_15 nh_15
set_option maxHeartbeats 0 in
theorem rc_15 : dagCheckRootsV5 m_15 g_15 ep_15 1 1 1 bds_15 (dagTraceF m_15 s_15 3 f_15) (cur_15 0) (nh_15 0) s_15 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_15 : treeBlockF 0 1 ch_15 = true := by decide +kernel
theorem nc_15 : ∀ i, 0 ≤ i → i < 1 → ch_15 i = true := fun _ h1 h2 => treeBlockF_at nb_15 h1 h2
theorem lb_15 : LowerBin m_15 s_15 g_15 4 :=
  lowerDagV5 (kn_nil) rc_15 nc_15 (by decide +kernel)

def m_16 : Nat := 0xc0c0c0c
def s_16 : List Nat := [0x4040404, 0xc000c, 0xc0c]
def g_16 : Nat := 0x4040c
def ep_16 : Nat := 0x4080000000000040008000000000000000000000000000000000000000000040400
def bds_16 : List (Nat × List Nat × Nat × Nat) := []
def cur_16 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_16 : Nat → Nat := fun _ => 0
def f_16 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_16 : Nat → Bool := dagCheckNodeV5 m_16 g_16 ep_16 1 1 bds_16 1 (dagTraceF m_16 s_16 3 f_16) cur_16 nh_16
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsV5 m_16 g_16 ep_16 1 1 1 bds_16 (dagTraceF m_16 s_16 3 f_16) (cur_16 0) (nh_16 0) s_16 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16 : treeBlockF 0 1 ch_16 = true := by decide +kernel
theorem nc_16 : ∀ i, 0 ≤ i → i < 1 → ch_16 i = true := fun _ h1 h2 => treeBlockF_at nb_16 h1 h2
theorem lb_16 : LowerBin m_16 s_16 g_16 4 :=
  lowerDagV5 (kn_nil) rc_16 nc_16 (by decide +kernel)

def m_17 : Nat := 0xa0a0a0a
def s_17 : List Nat := [0x2020202, 0xa000a, 0xa0a]
def g_17 : Nat := 0x2020a
def ep_17 : Nat := 0x2080000000000020008000000000000000000000000000202000000000000000000
def bds_17 : List (Nat × List Nat × Nat × Nat) := []
def cur_17 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_17 : Nat → Nat := fun _ => 0
def f_17 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_17 : Nat → Bool := dagCheckNodeV5 m_17 g_17 ep_17 1 1 bds_17 1 (dagTraceF m_17 s_17 3 f_17) cur_17 nh_17
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsV5 m_17 g_17 ep_17 1 1 1 bds_17 (dagTraceF m_17 s_17 3 f_17) (cur_17 0) (nh_17 0) s_17 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17 : treeBlockF 0 1 ch_17 = true := by decide +kernel
theorem nc_17 : ∀ i, 0 ≤ i → i < 1 → ch_17 i = true := fun _ h1 h2 => treeBlockF_at nb_17 h1 h2
theorem lb_17 : LowerBin m_17 s_17 g_17 4 :=
  lowerDagV5 (kn_nil) rc_17 nc_17 (by decide +kernel)

def m_18 : Nat := 0xf0f000000000f0f0
def s_18 : List Nat := [0x5050000000005050, 0x3030000000003030, 0xf00000000000f0, 0xf0f0]
def g_18 : Nat := 0x100000000010f0
def ep_18 : Nat := 0x100000000000e0000000000000000000100000000010000010000000001000
def bds_18 : List (Nat × List Nat × Nat × Nat) := []
def cur_18 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb1e58f347d23971928c4c6000f 7 127 3 7 10 1023 13 8191
def nh_18 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_18 : Nat → Nat × Nat := unpackForestF 0x18fac7863931918c4c6000f 3 10
def ch_18 : Nat → Bool := dagCheckNodeV5 m_18 g_18 ep_18 1 1 bds_18 7 (dagTraceF m_18 s_18 4 f_18) cur_18 nh_18
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsV5 m_18 g_18 ep_18 1 1 7 bds_18 (dagTraceF m_18 s_18 4 f_18) (cur_18 0) (nh_18 0) s_18 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_18 : treeBlockF 0 7 ch_18 = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 7 → ch_18 i = true := fun _ h1 h2 => treeBlockF_at nb_18 h1 h2
theorem lb_18 : LowerBin m_18 s_18 g_18 5 :=
  lowerDagV5 (kn_nil) rc_18 nc_18 (by decide +kernel)

def m_19 : Nat := 0xff0000ff00
def s_19 : List Nat := [0x5500005500, 0x3300003300, 0xf00000f00, 0xff00]
def g_19 : Nat := 0x5700001700
def ep_19 : Nat := 0x20000060000000002000012000000005400001400
def bds_19 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_19 : Nat → List (Nat × Nat) := fun _ => []
def nh_19 : Nat → Nat := unpackHintV5 0x4 0x1 6 63 3 7
def f_19 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsV5 m_19 g_19 ep_19 1 1 0 bds_19 (dagTraceF m_19 s_19 4 f_19) (cur_19 0) (nh_19 0) s_19 4 = true := by decide +kernel
theorem nc_19 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_19 g_19 ep_19 1 1 bds_19 0 (dagTraceF m_19 s_19 4 f_19) cur_19 nh_19 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_19 : LowerBin m_19 s_19 g_19 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_19 nc_19 (by decide +kernel)

def m_20 : Nat := 0xff00ff0000000000
def s_20 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_20 : Nat := 0x100170000000000
def ep_20 : Nat := 0x1600000000000000000000000000010006000000000001001200000000000100140000000000
def bds_20 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7), (m_11, s_11, 4, g_11), (m_5, s_5, 4, g_5), (m_6, s_6, 4, g_6)]
def cc_20_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_20_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_20 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_20_1 (Nat.sub p 32)) (cc_20_0 p) (Nat.blt p 32)
def hc_20_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_20_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_20 : Nat → Nat := fun p => Bool.rec (hc_20_1 (Nat.sub p 32)) (hc_20_0 p) (Nat.blt p 32)
def f_20 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_20 : Nat → Bool := dagCheckNodeV5 m_20 g_20 ep_20 1 1 bds_20 43 (dagTraceF m_20 s_20 6 f_20) cur_20 nh_20
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV5 m_20 g_20 ep_20 1 1 43 bds_20 (dagTraceF m_20 s_20 6 f_20) (cur_20 0) (nh_20 0) s_20 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_20_0 : treeBlockF 0 32 ch_20 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_20_1 : treeBlockF 32 43 ch_20 = true := by decide +kernel
theorem nj_20_1 : ∀ i, 0 ≤ i → i < 43 → ch_20 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_20_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_20_1 h1 h2)
theorem nc_20 : ∀ i, 0 ≤ i → i < 43 → ch_20 i = true := nj_20_1
theorem lb_20 : LowerBin m_20 s_20 g_20 7 :=
  lowerDagV5 (kn_cons lb_7 (kn_cons lb_11 (kn_cons lb_5 (kn_cons lb_6 (kn_nil))))) rc_20 nc_20 (by decide +kernel)

def m_21 : Nat := 0xffff000000000000
def s_21 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_21 : Nat := 0x117000000000000
def ep_21 : Nat := 0x16000000000000010600000000000001120000000000000114000000000000
def bds_21 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3), (m_8, s_8, 4, g_8), (m_13, s_13, 4, g_13), (m_14, s_14, 4, g_14)]
def cc_21_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_21_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_21 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_21_1 (Nat.sub p 32)) (cc_21_0 p) (Nat.blt p 32)
def hc_21_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_21_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_21 : Nat → Nat := fun p => Bool.rec (hc_21_1 (Nat.sub p 32)) (hc_21_0 p) (Nat.blt p 32)
def f_21 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_21 : Nat → Bool := dagCheckNodeV5 m_21 g_21 ep_21 1 1 bds_21 43 (dagTraceF m_21 s_21 6 f_21) cur_21 nh_21
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV5 m_21 g_21 ep_21 1 1 43 bds_21 (dagTraceF m_21 s_21 6 f_21) (cur_21 0) (nh_21 0) s_21 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21_0 : treeBlockF 0 32 ch_21 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21_1 : treeBlockF 32 43 ch_21 = true := by decide +kernel
theorem nj_21_1 : ∀ i, 0 ≤ i → i < 43 → ch_21 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_21_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_21_1 h1 h2)
theorem nc_21 : ∀ i, 0 ≤ i → i < 43 → ch_21 i = true := nj_21_1
theorem lb_21 : LowerBin m_21 s_21 g_21 7 :=
  lowerDagV5 (kn_cons lb_3 (kn_cons lb_8 (kn_cons lb_13 (kn_cons lb_14 (kn_nil))))) rc_21 nc_21 (by decide +kernel)

def m_22 : Nat := 0xffff00000000
def s_22 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_22 : Nat := 0x175700000000
def ep_22 : Nat := 0x4000000000000006020000000000001202000000000000145400000000
def bds_22 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_22 : Nat → List (Nat × Nat) := fun _ => []
def nh_22 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_22 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV5 m_22 g_22 ep_22 1 1 0 bds_22 (dagTraceF m_22 s_22 4 f_22) (cur_22 0) (nh_22 0) s_22 4 = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_22 g_22 ep_22 1 1 bds_22 0 (dagTraceF m_22 s_22 4 f_22) cur_22 nh_22 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_22 : LowerBin m_22 s_22 g_22 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_22 nc_22 (by decide +kernel)

def m_23 : Nat := 0xff00ff00000000
def s_23 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_23 : Nat := 0x17005700000000
def ep_23 : Nat := 0x40000000000000000000000000000600020000000000120002000000000014005400000000
def bds_23 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_23 : Nat → List (Nat × Nat) := fun _ => []
def nh_23 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_23 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV5 m_23 g_23 ep_23 1 1 0 bds_23 (dagTraceF m_23 s_23 4 f_23) (cur_23 0) (nh_23 0) s_23 4 = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_23 g_23 ep_23 1 1 bds_23 0 (dagTraceF m_23 s_23 4 f_23) cur_23 nh_23 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_23 : LowerBin m_23 s_23 g_23 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_23 nc_23 (by decide +kernel)

def m_24 : Nat := 0xf0f0f0f000000000
def s_24 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_24 : Nat := 0x10105000000000
def ep_24 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000010105000000000
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cur_24 : Nat → List (Nat × Nat) := fun _ => []
def nh_24 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_24 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV5 m_24 g_24 ep_24 1 1 0 bds_24 (dagTraceF m_24 s_24 4 f_24) (cur_24 0) (nh_24 0) s_24 4 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_24 g_24 ep_24 1 1 bds_24 0 (dagTraceF m_24 s_24 4 f_24) cur_24 nh_24 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_24 nc_24 (by decide +kernel)

def m_25 : Nat := 0xcccccccc00000000
def s_25 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_25 : Nat := 0x4044400000000
def ep_25 : Nat := 0x440000000000004004000000000000404000000000000000000000000000004044400000000
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_25 : Nat → List (Nat × Nat) := fun _ => []
def nh_25 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_25 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV5 m_25 g_25 ep_25 1 1 0 bds_25 (dagTraceF m_25 s_25 4 f_25) (cur_25 0) (nh_25 0) s_25 4 = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_25 g_25 ep_25 1 1 bds_25 0 (dagTraceF m_25 s_25 4 f_25) cur_25 nh_25 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_25 : LowerBin m_25 s_25 g_25 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_25 nc_25 (by decide +kernel)

def m_26 : Nat := 0x3333333300000000
def s_26 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_26 : Nat := 0x113131300000000
def ep_26 : Nat := 0x1200000000000012000000000000010202020000000000000000000000000110101000000000
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cur_26 : Nat → List (Nat × Nat) := fun _ => []
def nh_26 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_26 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV5 m_26 g_26 ep_26 1 1 0 bds_26 (dagTraceF m_26 s_26 4 f_26) (cur_26 0) (nh_26 0) s_26 4 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_26 g_26 ep_26 1 1 bds_26 0 (dagTraceF m_26 s_26 4 f_26) cur_26 nh_26 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_26 : LowerBin m_26 s_26 g_26 5 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_26 nc_26 (by decide +kernel)

def m_27 : Nat := 0x5050505050505050
def s_27 : List Nat := [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050]
def g_27 : Nat := 0x10105010501050
def ep_27 : Nat := 0x1040000000001040000000000010004000400040000000000000000000101000100010000000000000000000
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cur_27 : Nat → List (Nat × Nat) := fun _ => []
def nh_27 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_27 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV5 m_27 g_27 ep_27 1 1 0 bds_27 (dagTraceF m_27 s_27 4 f_27) (cur_27 0) (nh_27 0) s_27 4 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_27 g_27 ep_27 1 1 bds_27 0 (dagTraceF m_27 s_27 4 f_27) cur_27 nh_27 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_27 nc_27 (by decide +kernel)

def m_28 : Nat := 0x5555555500000000
def s_28 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_28 : Nat := 0x115155500000000
def ep_28 : Nat := 0x1440000000000014004000000000010404000000000001101000000000000000000000000000
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5), (m_13, s_13, 4, g_13), (m_4, s_4, 4, g_4), (m_9, s_9, 4, g_9)]
def cc_28_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_28_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_28 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_28_1 (Nat.sub p 32)) (cc_28_0 p) (Nat.blt p 32)
def hc_28_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e02200586415a60dad5545a0ad39b942665566b5910608437408a0203a61035944 15 32767 6 63
def hc_28_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e7540e571014d8c00562302 13 8191 6 63
def nh_28 : Nat → Nat := fun p => Bool.rec (hc_28_1 (Nat.sub p 32)) (hc_28_0 p) (Nat.blt p 32)
def f_28 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_28 : Nat → Bool := dagCheckNodeV5 m_28 g_28 ep_28 1 1 bds_28 43 (dagTraceF m_28 s_28 6 f_28) cur_28 nh_28
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV5 m_28 g_28 ep_28 1 1 43 bds_28 (dagTraceF m_28 s_28 6 f_28) (cur_28 0) (nh_28 0) s_28 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28_0 : treeBlockF 0 32 ch_28 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28_1 : treeBlockF 32 43 ch_28 = true := by decide +kernel
theorem nj_28_1 : ∀ i, 0 ≤ i → i < 43 → ch_28 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_28_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_28_1 h1 h2)
theorem nc_28 : ∀ i, 0 ≤ i → i < 43 → ch_28 i = true := nj_28_1
theorem lb_28 : LowerBin m_28 s_28 g_28 7 :=
  lowerDagV5 (kn_cons lb_5 (kn_cons lb_13 (kn_cons lb_4 (kn_cons lb_9 (kn_nil))))) rc_28 nc_28 (by decide +kernel)

def m_29 : Nat := 0x66006600660066
def s_29 : List Nat := [0x22002200220022, 0x6000600060006, 0x6600000066, 0x660066]
def g_29 : Nat := 0x6004600460066
def ep_29 : Nat := 0x40002000000040000000200000000000000000000600020002000000000000000000000000000000000000
def bds_29 : List (Nat × List Nat × Nat × Nat) := []
def cur_29 : Nat → List (Nat × Nat) := unpackCursorV5 0x16ac58b12a44890e8701 0x1924309193c2050d3c205263d88d5d2a549902a109800f 7 127 3 7 10 1023 14 16383
def nh_29 : Nat → Nat := unpackHintV5 0x340d0340d0302c0300c02c215002 0x0 10 1023 5 31
def f_29 : Nat → Nat × Nat := unpackForestF 0xc7a63529564f0a4c42a49e205084c00f 3 10
def ch_29 : Nat → Bool := dagCheckNodeV5 m_29 g_29 ep_29 1 1 bds_29 10 (dagTraceF m_29 s_29 4 f_29) cur_29 nh_29
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV5 m_29 g_29 ep_29 1 1 10 bds_29 (dagTraceF m_29 s_29 4 f_29) (cur_29 0) (nh_29 0) s_29 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29 : treeBlockF 0 10 ch_29 = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 10 → ch_29 i = true := fun _ h1 h2 => treeBlockF_at nb_29 h1 h2
theorem lb_29 : LowerBin m_29 s_29 g_29 5 :=
  lowerDagV5 (kn_nil) rc_29 nc_29 (by decide +kernel)

def m_30 : Nat := 0x3030303030303030
def s_30 : List Nat := [0x1010101010101010, 0x30003000300030, 0x303000003030, 0x30303030]
def g_30 : Nat := 0x10101010101030
def ep_30 : Nat := 0x1000002000001000000000200010000000000020000000000000000000000000000000000010101010101000
def bds_30 : List (Nat × List Nat × Nat × Nat) := []
def cc_30_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_30_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_30 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_30_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_30_0 p) (Nat.blt p 32)
def hc_30_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_30_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_30_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_30 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_30_2 (Nat.sub p 64)) (hc_30_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_30_0 p) (Nat.blt p 32)
def f_30 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_30 : Nat → Bool := dagCheckNodeV5 m_30 g_30 ep_30 1 1 bds_30 64 (dagTraceF m_30 s_30 5 f_30) cur_30 nh_30
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV5 m_30 g_30 ep_30 1 1 64 bds_30 (dagTraceF m_30 s_30 5 f_30) (cur_30 0) (nh_30 0) s_30 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_0 : treeBlockF 0 32 ch_30 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_1 : treeBlockF 32 64 ch_30 = true := by decide +kernel
theorem nj_30_1 : ∀ i, 0 ≤ i → i < 64 → ch_30 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_30_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_30_1 h1 h2)
theorem nc_30 : ∀ i, 0 ≤ i → i < 64 → ch_30 i = true := nj_30_1
theorem lb_30 : LowerBin m_30 s_30 g_30 6 :=
  lowerDagV5 (kn_nil) rc_30 nc_30 (by decide +kernel)

def m_31 : Nat := 0xc0c0c0c0c0c0c0c0
def s_31 : List Nat := [0x4040404040404040, 0xc000c000c000c0, 0xc0c00000c0c0, 0xc0c0c0c0]
def g_31 : Nat := 0x40004000c0
def ep_31 : Nat := 0x400080000000400000008000000040004000c0000000000000000000000000000000000000004000400000
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_31 : Nat → List (Nat × Nat) := fun _ => []
def nh_31 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_31 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV5 m_31 g_31 ep_31 1 1 0 bds_31 (dagTraceF m_31 s_31 4 f_31) (cur_31 0) (nh_31 0) s_31 4 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_31 g_31 ep_31 1 1 bds_31 0 (dagTraceF m_31 s_31 4 f_31) cur_31 nh_31 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_31 nc_31 (by decide +kernel)

def m_32 : Nat := 0xcccc0000cccc
def s_32 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_32 : Nat := 0x444000004cc
def ep_32 : Nat := 0x88000000000000000000000040000000c8000004000000040000000000000000000000044400000400
def bds_32 : List (Nat × List Nat × Nat × Nat) := []
def cur_32 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_32 : Nat → Nat := fun _ => 0
def f_32 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_32 : Nat → Bool := dagCheckNodeV5 m_32 g_32 ep_32 1 1 bds_32 1 (dagTraceF m_32 s_32 3 f_32) cur_32 nh_32
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV5 m_32 g_32 ep_32 1 1 1 bds_32 (dagTraceF m_32 s_32 3 f_32) (cur_32 0) (nh_32 0) s_32 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32 : treeBlockF 0 1 ch_32 = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 1 → ch_32 i = true := fun _ h1 h2 => treeBlockF_at nb_32 h1 h2
theorem lb_32 : LowerBin m_32 s_32 g_32 4 :=
  lowerDagV5 (kn_nil) rc_32 nc_32 (by decide +kernel)

def m_33 : Nat := 0x3333000033330000
def s_33 : List Nat := [0x1111000011110000, 0x303000003030000, 0x33000000330000, 0x33330000]
def g_33 : Nat := 0x113000011130000
def ep_33 : Nat := 0x1000000000000000000000000012000000020000010200000002000000000000000000000110000011100000
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
def cur_33 : Nat → List (Nat × Nat) := fun _ => []
def nh_33 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV5 m_33 g_33 ep_33 1 1 0 bds_33 (dagTraceF m_33 s_33 4 f_33) (cur_33 0) (nh_33 0) s_33 4 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_33 g_33 ep_33 1 1 bds_33 0 (dagTraceF m_33 s_33 4 f_33) cur_33 nh_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagV5 (kn_cons lb_14 (kn_nil)) rc_33 nc_33 (by decide +kernel)

def m_34 : Nat := 0x5500550055005500
def s_34 : List Nat := [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500]
def g_34 : Nat := 0x100150011001500
def ep_34 : Nat := 0x1000000000001400000004000000000000000000010004000000040001001000110010000000000000000000
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
def cur_34 : Nat → List (Nat × Nat) := fun _ => []
def nh_34 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV5 m_34 g_34 ep_34 1 1 0 bds_34 (dagTraceF m_34 s_34 4 f_34) (cur_34 0) (nh_34 0) s_34 4 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_34 g_34 ep_34 1 1 bds_34 0 (dagTraceF m_34 s_34 4 f_34) cur_34 nh_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagV5 (kn_cons lb_5 (kn_nil)) rc_34 nc_34 (by decide +kernel)

def m_35 : Nat := 0xf0f00000f0f0
def s_35 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_35 : Nat := 0x1050000010f0
def ep_35 : Nat := 0xa0000000000000000000000040000000e0000000000000000000001000000010000000105000001000
def bds_35 : List (Nat × List Nat × Nat × Nat) := []
def cur_35 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_35 : Nat → Nat := fun _ => 0
def f_35 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_35 : Nat → Bool := dagCheckNodeV5 m_35 g_35 ep_35 1 1 bds_35 1 (dagTraceF m_35 s_35 3 f_35) cur_35 nh_35
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV5 m_35 g_35 ep_35 1 1 1 bds_35 (dagTraceF m_35 s_35 3 f_35) (cur_35 0) (nh_35 0) s_35 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35 : treeBlockF 0 1 ch_35 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 1 → ch_35 i = true := fun _ h1 h2 => treeBlockF_at nb_35 h1 h2
theorem lb_35 : LowerBin m_35 s_35 g_35 4 :=
  lowerDagV5 (kn_nil) rc_35 nc_35 (by decide +kernel)

def m_36 : Nat := 0x3300330033003300
def s_36 : List Nat := [0x1100110011001100, 0x300030003000300, 0x330000003300, 0x33003300]
def g_36 : Nat := 0x100130011001300
def ep_36 : Nat := 0x1000000000001200000002000000000000000000010002000000020000000000000000000100100011001000
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cur_36 : Nat → List (Nat × Nat) := fun _ => []
def nh_36 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV5 m_36 g_36 ep_36 1 1 0 bds_36 (dagTraceF m_36 s_36 4 f_36) (cur_36 0) (nh_36 0) s_36 4 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_36 g_36 ep_36 1 1 bds_36 0 (dagTraceF m_36 s_36 4 f_36) cur_36 nh_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_36 nc_36 (by decide +kernel)

def m_37 : Nat := 0x33333333
def s_37 : List Nat := [0x11111111, 0x3030303, 0x330033, 0x3333]
def g_37 : Nat := 0x11131333
def ep_37 : Nat := 0x2200000000000020020000000000002020000000000000000000000000011101000
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_37 : Nat → List (Nat × Nat) := fun _ => []
def nh_37 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV5 m_37 g_37 ep_37 1 1 0 bds_37 (dagTraceF m_37 s_37 4 f_37) (cur_37 0) (nh_37 0) s_37 4 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_37 g_37 ep_37 1 1 bds_37 0 (dagTraceF m_37 s_37 4 f_37) cur_37 nh_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_37 nc_37 (by decide +kernel)

def m_38 : Nat := 0xcc00cc00cc00cc
def s_38 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_38 : Nat := 0x40044004400cc
def ep_38 : Nat := 0x40008800000040000000880000000000000000000400000000000000000000000000000004004400440000
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def nh_38 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV5 m_38 g_38 ep_38 1 1 0 bds_38 (dagTraceF m_38 s_38 4 f_38) (cur_38 0) (nh_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_38 g_38 ep_38 1 1 bds_38 0 (dagTraceF m_38 s_38 4 f_38) cur_38 nh_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_38 nc_38 (by decide +kernel)

def m_39 : Nat := 0xffff0000
def s_39 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_39 : Nat := 0x11570000
def ep_39 : Nat := 0x460000000000000002000000000000110200000000000011540000
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cur_39 : Nat → List (Nat × Nat) := fun _ => []
def nh_39 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_39 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV5 m_39 g_39 ep_39 1 1 0 bds_39 (dagTraceF m_39 s_39 4 f_39) (cur_39 0) (nh_39 0) s_39 4 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_39 g_39 ep_39 1 1 bds_39 0 (dagTraceF m_39 s_39 4 f_39) cur_39 nh_39 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_39 : LowerBin m_39 s_39 g_39 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_39 nc_39 (by decide +kernel)

def m_40 : Nat := 0xffff
def s_40 : List Nat := [0x5555, 0x3333, 0xf0f, 0xff]
def g_40 : Nat := 0x17ff
def ep_40 : Nat := 0xe8000000000000060000000000000012000000000000001400
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_40 : Nat → List (Nat × Nat) := fun _ => []
def nh_40 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_40 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV5 m_40 g_40 ep_40 1 1 0 bds_40 (dagTraceF m_40 s_40 4 f_40) (cur_40 0) (nh_40 0) s_40 4 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_40 g_40 ep_40 1 1 bds_40 0 (dagTraceF m_40 s_40 4 f_40) cur_40 nh_40 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_40 : LowerBin m_40 s_40 g_40 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_40 nc_40 (by decide +kernel)

def m_41 : Nat := 0xff00ff00
def s_41 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_41 : Nat := 0x11001700
def ep_41 : Nat := 0x6000000000000000000000000000000060000000000110012000000000011001400
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def nh_41 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV5 m_41 g_41 ep_41 1 1 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) (nh_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_41 g_41 ep_41 1 1 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 nh_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_41 nc_41 (by decide +kernel)

def m_42 : Nat := 0xf0f0f0f0
def s_42 : List Nat := [0x50505050, 0x30303030, 0xf000f0, 0xf0f0]
def g_42 : Nat := 0x105010f0
def ep_42 : Nat := 0xa000000000004000e0000000000000000000000000100010000000000010501000
def bds_42 : List (Nat × List Nat × Nat × Nat) := []
def cur_42 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_42 : Nat → Nat := fun _ => 0
def f_42 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_42 : Nat → Bool := dagCheckNodeV5 m_42 g_42 ep_42 1 1 bds_42 1 (dagTraceF m_42 s_42 3 f_42) cur_42 nh_42
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV5 m_42 g_42 ep_42 1 1 1 bds_42 (dagTraceF m_42 s_42 3 f_42) (cur_42 0) (nh_42 0) s_42 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42 : treeBlockF 0 1 ch_42 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 1 → ch_42 i = true := fun _ h1 h2 => treeBlockF_at nb_42 h1 h2
theorem lb_42 : LowerBin m_42 s_42 g_42 4 :=
  lowerDagV5 (kn_nil) rc_42 nc_42 (by decide +kernel)

def m_43 : Nat := 0xf0f0f0f
def s_43 : List Nat := [0x5050505, 0x3030303, 0xf000f, 0xf0f]
def g_43 : Nat := 0x107070f
def ep_43 : Nat := 0x6080000000000060008000000000000000000000000010202000000000001040400
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2), (m_15, s_15, 4, g_15), (m_16, s_16, 4, g_16), (m_17, s_17, 4, g_17)]
def cc_43_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_43_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_43 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_43_1 (Nat.sub p 32)) (cc_43_0 p) (Nat.blt p 32)
def hc_43_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e56655092040a6ad8c0011820539b81622002630805682cb74a008803a6b2b0810 15 32767 6 63
def hc_43_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e754ae0732b4dad55068b56 13 8191 6 63
def nh_43 : Nat → Nat := fun p => Bool.rec (hc_43_1 (Nat.sub p 32)) (hc_43_0 p) (Nat.blt p 32)
def f_43 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_43 : Nat → Bool := dagCheckNodeV5 m_43 g_43 ep_43 1 1 bds_43 43 (dagTraceF m_43 s_43 6 f_43) cur_43 nh_43
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV5 m_43 g_43 ep_43 1 1 43 bds_43 (dagTraceF m_43 s_43 6 f_43) (cur_43 0) (nh_43 0) s_43 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_0 : treeBlockF 0 32 ch_43 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_1 : treeBlockF 32 43 ch_43 = true := by decide +kernel
theorem nj_43_1 : ∀ i, 0 ≤ i → i < 43 → ch_43 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_43_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_43_1 h1 h2)
theorem nc_43 : ∀ i, 0 ≤ i → i < 43 → ch_43 i = true := nj_43_1
theorem lb_43 : LowerBin m_43 s_43 g_43 7 :=
  lowerDagV5 (kn_cons lb_2 (kn_cons lb_15 (kn_cons lb_16 (kn_cons lb_17 (kn_nil))))) rc_43 nc_43 (by decide +kernel)

def m_44 : Nat := 0xcccccccc
def s_44 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_44 : Nat := 0x4404cc
def ep_44 : Nat := 0x48800000000004400c8000000000000040000000000000000000000000000440400
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16)]
def cur_44 : Nat → List (Nat × Nat) := fun _ => []
def nh_44 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_44 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV5 m_44 g_44 ep_44 1 1 0 bds_44 (dagTraceF m_44 s_44 4 f_44) (cur_44 0) (nh_44 0) s_44 4 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_44 g_44 ep_44 1 1 bds_44 0 (dagTraceF m_44 s_44 4 f_44) cur_44 nh_44 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_44 : LowerBin m_44 s_44 g_44 5 :=
  lowerDagV5 (kn_cons lb_16 (kn_nil)) rc_44 nc_44 (by decide +kernel)

def m_45 : Nat := 0xaaaaaaaa
def s_45 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_45 : Nat := 0x202aa
def ep_45 : Nat := 0x2a800000000000200a8000000000002020000000000000202000000000000000000
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_45 : Nat → List (Nat × Nat) := fun _ => []
def nh_45 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV5 m_45 g_45 ep_45 1 1 0 bds_45 (dagTraceF m_45 s_45 4 f_45) (cur_45 0) (nh_45 0) s_45 4 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_45 g_45 ep_45 1 1 bds_45 0 (dagTraceF m_45 s_45 4 f_45) cur_45 nh_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin m_45 s_45 g_45 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_45 nc_45 (by decide +kernel)

def m_46 : Nat := 0xff000000ff0000
def s_46 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_46 : Nat := 0x17000000570000
def ep_46 : Nat := 0x40000000000000000000000000000000000000000600000002000000120000000200000014000000540000
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_46 : Nat → List (Nat × Nat) := fun _ => []
def nh_46 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_46 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV5 m_46 g_46 ep_46 1 1 0 bds_46 (dagTraceF m_46 s_46 4 f_46) (cur_46 0) (nh_46 0) s_46 4 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_46 g_46 ep_46 1 1 bds_46 0 (dagTraceF m_46 s_46 4 f_46) cur_46 nh_46 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_46 : LowerBin m_46 s_46 g_46 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_46 nc_46 (by decide +kernel)

def m_47 : Nat := 0xf000f000f000f0
def s_47 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_47 : Nat := 0x100050005000f0
def ep_47 : Nat := 0x4000a000000040000000a00000000000000000000000000000000000100000000000000010005000500000
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_47 : Nat → List (Nat × Nat) := fun _ => []
def nh_47 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_47 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV5 m_47 g_47 ep_47 1 1 0 bds_47 (dagTraceF m_47 s_47 4 f_47) (cur_47 0) (nh_47 0) s_47 4 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_47 g_47 ep_47 1 1 bds_47 0 (dagTraceF m_47 s_47 4 f_47) cur_47 nh_47 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_47 : LowerBin m_47 s_47 g_47 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_47 nc_47 (by decide +kernel)

def m_48 : Nat := 0xf0f00000f0f00000
def s_48 : List Nat := [0x5050000050500000, 0x3030000030300000, 0xf0000000f00000, 0xf0f00000]
def g_48 : Nat := 0x10000010500000
def ep_48 : Nat := 0x1040000000000000000000000010000000400000000000000000000000100000100000000010000010500000
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cur_48 : Nat → List (Nat × Nat) := fun _ => []
def nh_48 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_48 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV5 m_48 g_48 ep_48 1 1 0 bds_48 (dagTraceF m_48 s_48 4 f_48) (cur_48 0) (nh_48 0) s_48 4 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_48 g_48 ep_48 1 1 bds_48 0 (dagTraceF m_48 s_48 4 f_48) cur_48 nh_48 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_48 : LowerBin m_48 s_48 g_48 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_48 nc_48 (by decide +kernel)

def m_49 : Nat := 0x5500aa005500aa
def s_49 : List Nat := [0xaa000000aa, 0x11002200110022, 0x5000a0005000a, 0x5500aa]
def g_49 : Nat := 0x150002005500aa
def ep_49 : Nat := 0x4000a800000000000000000000000000000000000400020000000000100002000000000000000000000000
def bds_49 : List (Nat × List Nat × Nat × Nat) := []
def cur_49 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58b12a44874e0701 0x1a4471b4371343927d8d5ed5949d1540f 7 127 3 7 6 63 10 1023
def nh_49 : Nat → Nat := unpackHintV5 0x340c0b00c02c2b02c0b02c015002 0x0 10 1023 5 31
def f_49 : Nat → Nat × Nat := unpackForestF 0xfa7536ed0caf472174aa0f 3 6
def ch_49 : Nat → Bool := dagCheckNodeV5 m_49 g_49 ep_49 1 1 bds_49 10 (dagTraceF m_49 s_49 4 f_49) cur_49 nh_49
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV5 m_49 g_49 ep_49 1 1 10 bds_49 (dagTraceF m_49 s_49 4 f_49) (cur_49 0) (nh_49 0) s_49 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_49 : treeBlockF 0 10 ch_49 = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 10 → ch_49 i = true := fun _ h1 h2 => treeBlockF_at nb_49 h1 h2
theorem lb_49 : LowerBin m_49 s_49 g_49 5 :=
  lowerDagV5 (kn_nil) rc_49 nc_49 (by decide +kernel)

def m_50 : Nat := 0x4444444444444444
def s_50 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_50 : Nat := 0x4044400440444
def ep_50 : Nat := 0x40000000000440000004000004004000440040000404000000040000000000000000000000000000000000
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_50 : Nat → List (Nat × Nat) := fun _ => []
def nh_50 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_50 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV5 m_50 g_50 ep_50 1 1 0 bds_50 (dagTraceF m_50 s_50 4 f_50) (cur_50 0) (nh_50 0) s_50 4 = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_50 g_50 ep_50 1 1 bds_50 0 (dagTraceF m_50 s_50 4 f_50) cur_50 nh_50 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_50 : LowerBin m_50 s_50 g_50 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_50 nc_50 (by decide +kernel)

def m_51 : Nat := 0x55005500aa00aa
def s_51 : List Nat := [0xaa00aa, 0x11001100220022, 0x50005000a000a, 0x55000000aa]
def g_51 : Nat := 0x150055000200aa
def ep_51 : Nat := 0x40000000a80000000000000000000400000002000000100000000200000000000000000000
def bds_51 : List (Nat × List Nat × Nat × Nat) := []
def cur_51 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58b12a44874e0701 0xd2440c34d0c309343924cf626af2d592906842c00f 7 127 3 7 9 511 13 8191
def nh_51 : Nat → Nat := unpackHintV5 0x340c0b00c02c2b02c0b02c015002 0x0 10 1023 5 31
def f_51 : Nat → Nat × Nat := unpackForestF 0x33d33532dd3432573472421a21600f 3 9
def ch_51 : Nat → Bool := dagCheckNodeV5 m_51 g_51 ep_51 1 1 bds_51 10 (dagTraceF m_51 s_51 4 f_51) cur_51 nh_51
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV5 m_51 g_51 ep_51 1 1 10 bds_51 (dagTraceF m_51 s_51 4 f_51) (cur_51 0) (nh_51 0) s_51 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51 : treeBlockF 0 10 ch_51 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 10 → ch_51 i = true := fun _ h1 h2 => treeBlockF_at nb_51 h1 h2
theorem lb_51 : LowerBin m_51 s_51 g_51 5 :=
  lowerDagV5 (kn_nil) rc_51 nc_51 (by decide +kernel)

def m_52 : Nat := 0x2222222222222222
def s_52 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_52 : Nat := 0x2020200020222
def ep_52 : Nat := 0x2000000200000002200002000000020020000202020002020000000000000000000000000000000000
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_52 : Nat → List (Nat × Nat) := fun _ => []
def nh_52 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_52 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV5 m_52 g_52 ep_52 1 1 0 bds_52 (dagTraceF m_52 s_52 4 f_52) (cur_52 0) (nh_52 0) s_52 4 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_52 g_52 ep_52 1 1 bds_52 0 (dagTraceF m_52 s_52 4 f_52) cur_52 nh_52 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_52 : LowerBin m_52 s_52 g_52 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_52 nc_52 (by decide +kernel)

def m_53 : Nat := 0xa0a0a0a0a0a0a0a
def s_53 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_53 : Nat := 0x202020002020a
def ep_53 : Nat := 0x800000200000002080002000000020008000000000000000000020202000202000000000000000000
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 4, g_17)]
def cur_53 : Nat → List (Nat × Nat) := fun _ => []
def nh_53 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_53 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV5 m_53 g_53 ep_53 1 1 0 bds_53 (dagTraceF m_53 s_53 4 f_53) (cur_53 0) (nh_53 0) s_53 4 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_53 g_53 ep_53 1 1 bds_53 0 (dagTraceF m_53 s_53 4 f_53) cur_53 nh_53 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_53 : LowerBin m_53 s_53 g_53 5 :=
  lowerDagV5 (kn_cons lb_17 (kn_nil)) rc_53 nc_53 (by decide +kernel)

def m_54 : Nat := 0x5a005a005a005a
def s_54 : List Nat := [0xa000a000a000a, 0x12001200120012, 0x5a0000005a, 0x5a005a]
def g_54 : Nat := 0x1200520052005a
def ep_54 : Nat := 0x40000800000040000000080000000000000000000000000000000000120002000200000000000000000000
def bds_54 : List (Nat × List Nat × Nat × Nat) := []
def cur_54 : Nat → List (Nat × Nat) := unpackCursorV5 0x16ac58b12a44890e8701 0x193430d19282090d28209263a88d9d3a54d903a10d800f 7 127 3 7 10 1023 14 16383
def nh_54 : Nat → Nat := unpackHintV5 0x340d0340d0302c0300c02c215002 0x0 10 1023 5 31
def f_54 : Nat → Nat × Nat := unpackForestF 0xc7463629d64a0a6c43a494209086c00f 3 10
def ch_54 : Nat → Bool := dagCheckNodeV5 m_54 g_54 ep_54 1 1 bds_54 10 (dagTraceF m_54 s_54 4 f_54) cur_54 nh_54
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV5 m_54 g_54 ep_54 1 1 10 bds_54 (dagTraceF m_54 s_54 4 f_54) (cur_54 0) (nh_54 0) s_54 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54 : treeBlockF 0 10 ch_54 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 10 → ch_54 i = true := fun _ h1 h2 => treeBlockF_at nb_54 h1 h2
theorem lb_54 : LowerBin m_54 s_54 g_54 5 :=
  lowerDagV5 (kn_nil) rc_54 nc_54 (by decide +kernel)

def m_55 : Nat := 0xc0c0c0c0c0c0c0c
def s_55 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_55 : Nat := 0x404040004040c
def ep_55 : Nat := 0x800000400000004080004000000040008000000000000000000000000000000000004040400040400
def bds_55 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16)]
def cur_55 : Nat → List (Nat × Nat) := fun _ => []
def nh_55 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_55 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV5 m_55 g_55 ep_55 1 1 0 bds_55 (dagTraceF m_55 s_55 4 f_55) (cur_55 0) (nh_55 0) s_55 4 = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_55 g_55 ep_55 1 1 bds_55 0 (dagTraceF m_55 s_55 4 f_55) cur_55 nh_55 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_55 : LowerBin m_55 s_55 g_55 5 :=
  lowerDagV5 (kn_cons lb_16 (kn_nil)) rc_55 nc_55 (by decide +kernel)

def m_56 : Nat := 0x55aa55aa
def s_56 : List Nat := [0xaa00aa, 0x11221122, 0x50a050a, 0x55aa]
def g_56 : Nat := 0x110215aa
def ep_56 : Nat := 0x4a80000000000000000000000000002040000000000110210000000000000000000
def bds_56 : List (Nat × List Nat × Nat × Nat) := []
def cur_56 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0x14a99300f 4 15 2 3 9 511 11 2047
def nh_56 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_56 : Nat → Nat × Nat := unpackForestF 0x32ac980f 1 9
def ch_56 : Nat → Bool := dagCheckNodeV5 m_56 g_56 ep_56 1 1 bds_56 3 (dagTraceF m_56 s_56 4 f_56) cur_56 nh_56
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV5 m_56 g_56 ep_56 1 1 3 bds_56 (dagTraceF m_56 s_56 4 f_56) (cur_56 0) (nh_56 0) s_56 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56 : treeBlockF 0 3 ch_56 = true := by decide +kernel
theorem nc_56 : ∀ i, 0 ≤ i → i < 3 → ch_56 i = true := fun _ h1 h2 => treeBlockF_at nb_56 h1 h2
theorem lb_56 : LowerBin m_56 s_56 g_56 5 :=
  lowerDagV5 (kn_nil) rc_56 nc_56 (by decide +kernel)

def m_57 : Nat := 0x1122112211221122
def s_57 : List Nat := [0x22002200220022, 0x102010201020102, 0x112200001122, 0x11221122]
def g_57 : Nat := 0x102110211021122
def ep_57 : Nat := 0x1000002000001000000000200000000000000000010200020002000000000000000000000000000000000000
def bds_57 : List (Nat × List Nat × Nat × Nat) := []
def cur_57 : Nat → List (Nat × Nat) := unpackCursorV5 0x16ac58b12a44890e8701 0x193430d19282090d28209263a88d9d3a54d903a10d800f 7 127 3 7 10 1023 14 16383
def nh_57 : Nat → Nat := unpackHintV5 0x340d0340d0302c0300c02c215002 0x0 10 1023 5 31
def f_57 : Nat → Nat × Nat := unpackForestF 0xc7463629d64a0a6c43a494209086c00f 3 10
def ch_57 : Nat → Bool := dagCheckNodeV5 m_57 g_57 ep_57 1 1 bds_57 10 (dagTraceF m_57 s_57 4 f_57) cur_57 nh_57
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV5 m_57 g_57 ep_57 1 1 10 bds_57 (dagTraceF m_57 s_57 4 f_57) (cur_57 0) (nh_57 0) s_57 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57 : treeBlockF 0 10 ch_57 = true := by decide +kernel
theorem nc_57 : ∀ i, 0 ≤ i → i < 10 → ch_57 i = true := fun _ h1 h2 => treeBlockF_at nb_57 h1 h2
theorem lb_57 : LowerBin m_57 s_57 g_57 5 :=
  lowerDagV5 (kn_nil) rc_57 nc_57 (by decide +kernel)

def m_58 : Nat := 0x50a050a050a050a0
def s_58 : List Nat := [0xa000a000a000a0, 0x1020102010201020, 0x50a0000050a0, 0x50a050a0]
def g_58 : Nat := 0x1000100010a0
def ep_58 : Nat := 0x100000a000001000000000a00000000000000000000000000000000000001000100010000000000000000000
def bds_58 : List (Nat × List Nat × Nat × Nat) := []
def cc_58_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xd41a8312620c4188310620b49606c0561ac140e80500a0140251ca094128240c618c0f15e03c0704d841d001 0x824c3f201e530ea806a4c3322184a0ba48502c291e15d30985848241fa60e1306888102006100992044801e380d180204022600d2804924d8fe647b2a3b8b1bbc8d5d466e53f709db34dd9266b52f5095a749d1a46883f421d9c0dcd866582f22159009c60462c1f140d8505c0826000f 11 2047 5 31 10 1023 17 131071
def cc_58_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xc8ba8e888180808080808064606060606044393831301b181818180300000000 0xfe3c7c98448f9dc7b0d3e8299400f9e864ee4c6f2636901a898d0406326309117850b824560c2b8f16698a818520a26d312a989144 8 255 3 7 10 1023 17 131071
def cc_58_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x916660595851504925121010020000 0x44912246d2e355894a6484a8523c219722428f1fc79123c92a6485023899184084983f0c21478f830 8 255 3 7 10 1023 17 131071
def cur_58 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_58_2 (Nat.sub p 64)) (cc_58_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_58_0 p) (Nat.blt p 32)
def hc_58_0 : Nat → Nat := unpackHintV5 0x89121868129e127611d047021b846929a0268019c263217c85a29642571154451211963b58e443330bc82d1095021207c419303d40170002 0x0 14 16383 5 31
def hc_58_1 : Nat → Nat := unpackHintV5 0xda06d032258c2c03574a81d3c29a24b1240d0ca7493811b08c886022b29504a80521252109070a3611910b884c81490338104004 0x0 13 8191 5 31
def hc_58_2 : Nat → Nat := unpackHintV5 0x2c68aa02699645090438886110220802000800 0x0 10 1023 4 15
def nh_58 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_58_2 (Nat.sub p 64)) (hc_58_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_58_0 p) (Nat.blt p 32)
def f_58 : Nat → Nat × Nat := unpackForestF 0xc7e063d9722018ee329919408c26461000c6ef63e7a9f428f1ea64f43e7d1e3e4c1e86406357726018cc0a7e053b692634901a098d040029b814cd7498ba445c142e0900a5ea74c571e290614828052b0293a4d31229891440291810fc0876764c3b201d530ea800437021997930bc885d282e92010bc9698523c241612090085604271ba60d13068880423020f8106c34901a400d1c068c0082e0d300694024900826000f 7 10
def ch_58 : Nat → Bool := dagCheckNodeV5 m_58 g_58 ep_58 1 1 bds_58 78 (dagTraceF m_58 s_58 5 f_58) cur_58 nh_58
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV5 m_58 g_58 ep_58 1 1 78 bds_58 (dagTraceF m_58 s_58 5 f_58) (cur_58 0) (nh_58 0) s_58 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_0 : treeBlockF 0 32 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_1 : treeBlockF 32 64 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_2 : treeBlockF 64 78 ch_58 = true := by decide +kernel
theorem nj_58_1 : ∀ i, 0 ≤ i → i < 64 → ch_58 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_58_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_58_1 h1 h2)
theorem nj_58_2 : ∀ i, 0 ≤ i → i < 78 → ch_58 i = true := block_join nj_58_1 (fun _ h1 h2 => treeBlockF_at nb_58_2 h1 h2)
theorem nc_58 : ∀ i, 0 ≤ i → i < 78 → ch_58 i = true := nj_58_2
theorem lb_58 : LowerBin m_58 s_58 g_58 6 :=
  lowerDagV5 (kn_nil) rc_58 nc_58 (by decide +kernel)

def m_59 : Nat := 0x5555555555555555
def s_59 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_59 : Nat := 0x115155511551555
def ep_59 : Nat := 0x1040000000001440000004000014004000440040010404000000040001101000110010000000000000000000
def bds_59 : List (Nat × List Nat × Nat × Nat) := [(m_28, s_28, 7, g_28)]
def cur_59 : Nat → List (Nat × Nat) := fun _ => []
def nh_59 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_59 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_59 : dagCheckRootsV5 m_59 g_59 ep_59 1 1 0 bds_59 (dagTraceF m_59 s_59 7 f_59) (cur_59 0) (nh_59 0) s_59 7 = true := by decide +kernel
theorem nc_59 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_59 g_59 ep_59 1 1 bds_59 0 (dagTraceF m_59 s_59 7 f_59) cur_59 nh_59 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_59 : LowerBin m_59 s_59 g_59 8 :=
  lowerDagV5 (kn_cons lb_28 (kn_nil)) rc_59 nc_59 (by decide +kernel)

def m_60 : Nat := 0xff00ff00ff00ff00
def s_60 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_60 : Nat := 0x100170011001700
def ep_60 : Nat := 0x1000000000001600000006000000000000000000010006000000060001001200110012000100140011001400
def bds_60 : List (Nat × List Nat × Nat × Nat) := [(m_20, s_20, 7, g_20)]
def cur_60 : Nat → List (Nat × Nat) := fun _ => []
def nh_60 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_60 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsV5 m_60 g_60 ep_60 1 1 0 bds_60 (dagTraceF m_60 s_60 7 f_60) (cur_60 0) (nh_60 0) s_60 7 = true := by decide +kernel
theorem nc_60 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_60 g_60 ep_60 1 1 bds_60 0 (dagTraceF m_60 s_60 7 f_60) cur_60 nh_60 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_60 : LowerBin m_60 s_60 g_60 8 :=
  lowerDagV5 (kn_cons lb_20 (kn_nil)) rc_60 nc_60 (by decide +kernel)

def m_61 : Nat := 0xf0f0f0f0f0f0f0f0
def s_61 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_61 : Nat := 0x101050105010f0
def ep_61 : Nat := 0x104000a000001040000000a000100040004000e0000000000000000000101000100010000010105010501000
def bds_61 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4), (m_48, s_48, 5, g_48), (m_47, s_47, 5, g_47), (m_31, s_31, 5, g_31), (m_30, s_30, 6, g_30), (m_12, s_12, 4, g_12), (m_35, s_35, 4, g_35), (m_0, s_0, 4, g_0), (m_42, s_42, 4, g_42), (m_58, s_58, 6, g_58), (m_18, s_18, 5, g_18)]
def cc_61_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb205806c01600a62d3029814c0a01bc51d82e427203901c80d446a03405a00cc16603205900c025432a01500a024e0a3100c4001 0xf4501045e0fc520e9520e03e0d8320c93e0c1320b82e2c45e2b453284522735f253532434f2334322a5e21a531ea521e2431ca3e1ba3b1aa33142321193e109320d03e0b0320301007014069240a0440923408934059240803407034061280283c0414c0203c06a3f05a33051330492b039230182e02829020210181409b4f07b43031240103eb4b4eb3b4bb2343afb42ada4fac24ba9247a6243a323fa02339e94f9a94b91147871438513f841337a92f7892b75927739237084f6c84b63047540435003f4f0334202f4002b3a827360233181f2c81b0a817008130001f 13 8191 6 63 11 2047 20 1048575
def cc_61_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x9821580600801d3741b268582601715c152541505054050140501312e0b0284a0244451001304001 0x85145fc507cd45223e3a0f8502077179d452708f9c13c1208040106c5703820685117b50645117c50551419c5e63149835e5cd496b4e58d09594d5251529504b1413c5e4d1492152380f8c832444b8d83e300c8f150 10 1023 4 15 11 2047 18 262143
def cc_61_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xc0700bc6f0b8695952508ca308c2218460156d504c91244101310c024c8114c50140411004010004 0x2f834ba099c232c0d3ef343b84fad83eb4099da3e668c9393e400fa1260ae922a2408254201509ad4622517e942aa4aa6919d23e628ca91464c4fa88463e0fa7a58608c17a40988e264509b581f2605c9025a38929216a301a0406020589023a38160422560829192a3e80118f03e 10 1023 4 15 11 2047 18 262143
def cc_61_3 : Nat → List (Nat × Nat) := unpackCursorV5 0x94ca2512889c4221107db3990ba5c27130984c228bc582c1289041200e47015080400400 0xf8547e460ee933d94cf317bc25eee54bfc5efcd4be95ff454fb13dde0f7a13432490c134e4493703470091c232dc4cb9a3fe28ccb126e0133783eda09b5a44d45134134cc49b4b4fced0f2a3ec84fad015c45130844 9 511 3 7 11 2047 18 262143
def cc_61_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xa8338e41c8090120240480885085f13e07c0f81f03e07c0f81a2b40680d01a0340604a8c4888010020011801 0x13e098ec96c89252002c744b640928f8168e4692e4d0700a46a341b0492317a422947b528e2a51a48a2014c38218a04d1205a180a4ec5e9c8a536d4e692fcca5e982bf2c54e549fca1333925b264ae4893c61258b0bd0a149700d0d016830590409a04123c93d 11 2047 5 31 11 2047 19 524287
def cc_61_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x94a50942328c2308c20380200801e2781c2701b16c1b0685a0609262288020080188601804201000 0x180512fc225e934bc06975182e4a65c04cb547f688cec9194483eb0069100f2aca64383caf47f5c8ceb499d612baa2470c0bb0da7e0b43be49f768fedd1bc293eb607d660b2c41354824a24894a5128e2951152a76bd4c57e90a9d0935 10 1023 4 15 11 2047 19 524287
def cc_61_6 : Nat → List (Nat × Nat) := unpackCursorV5 0x9826090a409020480200789e0781c2701c06118060144501404892048102220711c0340c00300000 0xde4d37434dfd3f7343db133683ed1d3b3f42d58ff5233d2db34660cc5b32560cfd833a6ccb5b32160cc4bf2d23c98ff2233d8d435e5cd69474e50d08ff3633ca5731d50b00531544c4112d42caf0930834b40b2b824 10 1023 4 15 10 1023 18 262143
def cc_61_7 : Nat → List (Nat × Nat) := unpackCursorV5 0xe41b8b41e80d01a0340680bcaf45e03c0780d8da0b21640c8161a06400800e11062004008010020009c10001 0x7f8297f02180926800157e8147cc5e7c4527ba525e8523a03283c5e8345282b538225f81a5e8115e7e1527185f5d8534a83f398331c82d7d82b7d0277b0253281d118157a01879815790147703d5d0517745e76b5e5c8527845e77b527493d7105f5b8537603d1c132390327514c7493e4a03f3883310825740157323f72a332294d7213f7192f711274582e70044 11 2047 5 31 11 2047 20 1048575
def cc_61_8 : Nat → List (Nat × Nat) := unpackCursorV5 0xa025394250942328c21284201802007c5f074976368d0340b21d0701843300c00000000000000000 0x8f2691a062280a46e3f8d467008fa3099459347fc78fe8f222264563f8a466fd4ba2619c482b880471fd3e3ba1bf23e8e27ca413d2c1f9e8378c831170561e0a43352600a50dd79c82faf8538586b090547616be4251382a3a0b5f01289815 10 1023 4 15 10 1023 19 524287
def cc_61_9 : Nat → List (Nat × Nat) := unpackCursorV5 0xac247902318c23084a10841d4741d06c9b06c192641905515054114441103c8f03c0d21604110004 0x13f8fe7d19c092e2289aa60fd30179f4279e2893a8d2729a4ef4f9c687375326c9f4b74e95e85318fe6119cbb6c96cc1281b24a304af60954d9271b248304a12f93a47258fe4919cd35099cb9329465f284b23f94c672617246284581490c8920512360c45414 10 1023 4 15 10 1023 19 524287
def cc_61_10 : Nat → List (Nat × Nat) := unpackCursorV5 0xf83e0f83a4e83a0e0b80e0380e0380cd730cc321c8320aa2a0a82739c24357d5054123480f303c00 0xaf35eae945ae04527017ad450aca4cabb50ab15caa950aa05ca985026817a8c5ea8452a7c508293fa71254d83fa682525017a5352909523581da4352628523101aa5b5e9f95f9d95b961578f953a49357305f6f85b6805761853a38353481f3001b2401709813a22529d15a09011a12526f05a08812a2a5e9f15f9c15b949578e953a19257285f6e05b6685760853a08253381f2f01b2301707813 10 1023 4 15 11 2047 20 1048575
def cc_61_11 : Nat → List (Nat × Nat) := unpackCursorV5 0x4a2411188441c6e059ac10608 0x2d1a757a4fa8c87074bde093a742f3f84e5805ed1a659935b286a5605ec62694c452902b61534a6a294416ad4935090e9f20d89378325f600dd381794017 9 511 4 15 10 1023 19 524287
def cur_61 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_61_11 (Nat.sub p 352)) (cc_61_10 (Nat.sub p 320)) (Nat.blt p 352)) (cc_61_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (Bool.rec (cc_61_8 (Nat.sub p 256)) (cc_61_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_61_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (cc_61_5 (Nat.sub p 160)) (cc_61_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_61_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_61_2 (Nat.sub p 64)) (cc_61_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_61_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def hc_61_0 : Nat → Nat := unpackHintV5 0x80804fd041f4063de0a714a8e0029be023740866880953812a0023c1846c0c8c019180021c14438008383907001fc123e01877050eb031bc1a288f051000a2001281c1b0a00c2a0001800000 0x18e342348d00170c3978e5e5905d57423088c0000c3a00005c1001c0071cf003c31c71c70cf8f8b004f474f4f4002c2c5c1c5c5c554048c31e03cf8d0308c8e33e31e38e31f8cf1e37c000001c70003c71cf3c00000001f2300007df0000c71c300555000004000001c700055550000000001000000c01c00201001c71c71c71c7 19 524287 8 255
def hc_61_1 : Nat → Nat := unpackHintV5 0xbe07a6e8a9704a5c00950220e4680831e61c79801be286f801b8066b0319e0e678019806610517e065c8316c065b00166063f9a0f40a3a828e802360407c5c1d020146002828000a 0xb8e388c002c08cb0f0c71c36e9b000002310000b1031c76c6c0f0c71c33cf3cf5c31cf8f45c4f3cf1e15d071e31b0e33e3171e31c70cf3db06c30c71c70cf3d0575d12308c08e31053c30e3e38f820b2cf03c58c2cb2cb2cb0c3a053d4b2d5108d635 18 262143 8 255
def hc_61_2 : Nat → Nat := unpackHintV5 0x9383d2680a361740468758b0bbaf9463128a02480948e0211c0022e0a4481486828e5281be0c3245860048c000180002946c510188b17116001e04c2299841040622008440100081f010003e 0x234f8c3000001403085c001c7000c71c3003cf3d3d00000000c71c33e80f40171100000001c70003d1d3d3d0000000048c0000000c01c00200001c0071c71e8071cb00071100078c0c71c30cf0d3c5c070780c4341c0000c3a02cb000440031e38fa4f2c5c26cb08c8f3db2d3c17038c31e3e93c5e31c3833c30f01c31c39b8f003cb02c5c40010f0002d0631e31e304b2c71db6c01000b 19 524287 8 255
def hc_61_3 : Nat → Nat := unpackHintV5 0xc04cd77892e50a5c802b543d6a802d40159c0ca64d51bb1231064342e85c0d02099ca3a3365e6600cba1210c6821800430007e080f9031d41e3a404641088444026e204c0009800031000006 0x134e0831c70c003d3d0808c022e3e33d8e3a38c23598c5c8d74c0f0c71c3413cf4eaa8f17173c704d3a00aa1ea0e0aa8004c71d3a6a6a8013072a8088d717231e38c4c73c44f8e4c784c750000008383000c30c34e93000000000000c71c303d3d04c08e205e30000c71c33d40f00000000008793004c71d3a00013000022300000000c0070700100008d0c79638e30d45e34b2c14b43592cb04f2cb2cb1c72c0b0c71c355442cb5d73c5c51cb02cb2c0b1c7401555552c0150d51d5565002c02d7071717048d4163230c7823 19 524287 8 255
def hc_61_4 : Nat → Nat := unpackHintV5 0xcbdbd83942d53257e2cac439439526c1b4d60296845230a22f174401e8443d088021100420028340d03831d6313624a6b80cd3041a60034c0067028c40a111771ca582bcd83d9a01e5d0003c 0xc30c3000c30c34d34d30000032313000000000304c080400001c0071c71c1401c238801c4d34c0034d30c140302388138db0008c5c5c1788c5c070c70c6c00f4f40000f2cb3e34f5c8c235758c1740f8d3e3178d4c73c18c5d74f8d724f5ca35c5e31cf00c71c3443c71cf3cf885cf0003808d7023800171638cb50002d000500c2001c13821e4c0176d30c71c71d30c004c71d3a5d5d004d30713223a0a97170000002a80155540000000000031c70da400f1c74ea820000000002a800f1c74ea8000080000000002a80131c74ea8000088c000000000c01c08100000070087870662023 19 524287 8 255
def hc_61_5 : Nat → Nat := unpackHintV5 0xc6820c5c06c5802c0c26be414bcc0cbc802b8c1eae454ad806acc06a1c589f4148d0928d0008c0088b4068a80688c0e88c0086c1078474604c052c6c4d42c4d0024902048c02480063688c0c15400060 0x8e30304f3c8e30b3c13e38e8e33c238c213c0071c0031c70c0f4f400238c0000071c01555400000000f0c7000031c70cfa003c71cb3cb3cb00100042c008c8e38c2cf1d00000071c00f1c73cf000000002c000000071c0071cb2cb00023000002c00003007000804000000c00c300024e4c31cf4f4000130f0cb0e34f8c8d0d6317173c070d123e4c31cf0c30c34cf1c1c4d35cf0c700c30c0030c04c130c30c31c30e0d30e0c300c30c30c30d0c3534d34c000c8c30c030c74d313135c5c0000d433e9300c33d304c000 20 1048575 9 511
def hc_61_6 : Nat → Nat := unpackHintV5 0xcf80d9e80b2b125d284ae4c125b7209423ae6465d00ca0198d072968451814a181933102561049814880b10d0321406338f065818c40712860089c81100022000242003c0c02058010300002 0x3238c0c70c00000030c30c0030c30cb2cb2c00000000000031c70c0b2cb4b400002c0000071c00b1c72cb2cb2c08c00000000b0003001c1c0020100b0000000030c30c0030c30cb2cb2c0000000000002a802a8b1c72c0000000000071c0031c70c0b2cb2cb4b4000002e38c5c0000071c00b1c72cb2cb2c000000000b0238c70c2a38e305c231c3a300e3178e3000001cb1cb002cb2cb1c7000000008e317000001c7005555000000000400071c0003000080000071c0b000400b1c72cb2cb2c0000230000002c8e3031e08e38c303c 19 524287 8 255
def hc_61_7 : Nat → Nat := unpackHintV5 0xa98005400629306945c1ea100f5080028400141c029ac3144d44a108b0f6c8c7264831e3a97d090adc8656e002b6009408d484cdc382521881c8ac0c034110174160ac0704d048204320e210010308078040001e 0x2cb0502cb052d0d64158cf0f5d88d8f3cf1700c71c341885c71d73cf3cf1cb1d38ba1e4cb0b0f6d30c71c71cf0d52d2d3d34753663a5a8b2d31c74e8f0f13cf4000002a801555400000000b2e4b02c31c70ca104b2cb2d31c74ea955472cb1cb2eaaa95555954b2cb2d31c74ea95472cb1cb2eaa2ea9555598d552d1150d51d5954b2cb2d31c74ea95554542c780b878758b998c82cb2d34ea831c70c50b2e6632c2c2d71704c170c71c3443c3ca5d34ea8f3c72c74d3a88aa1ea0eaaa952d2d3d1daa56632cb4c71d3a2a2a93cf432c30c30e2e2e0e0d555554b2cb2c30c30d3a4d54b2cb02c31c70d4b4f563993c5c4f2cb2c0b0c71c33c104b2d7551cb2c72cb8b2e2cb87934b555355556634b44543551d1d5552cb2cb4c71d3a5555141c35c28e3178d700e35c038e3175c0f3d8e3172e05e38d700000070003002001b1c700000471cb2cb023000000000b00238c31e0 21 2097151 9 511
def hc_61_8 : Nat → Nat := unpackHintV5 0x9520349e05a340d9194068c40343616216028fb47e7da003e9021f300cf8c067bc053de001eb020e3890654642e02516f804a648c3b6be19f1e0892343706c134420820c0390400f06c012330060180001800000 0x8e38c352cb2cb1c72c0b0c71c355445c5c8e3000001c7005555000000000c75d0040031c70d7a00000170717171010123638e345c711cb02cb2c0b1c740155554b02d71c75d70151cb02cb2c0b1c750063555552d4354755594000070104144500c31c30c30c704593930c72cb1c1c54cb5c5c070d70410c793931c1c4d35c30c30d34cf3c31c30c30c30c0c0c35532cb4c30c30c70c3834c3830cb4b50d8c30d430c73d34f532cb0c30c30c30c0c3134d34d3cf470d34b02c300d3a4d04b2c30d34d5431c30c30cb2cb2c30c30d55550d8d4d552d1150d5356554b2cb2c30c30d34d34d555142c72c0b1c71c752cb1c798e680b1c72d34d32c0b0d34c352cb0c398e680b4e36c442e34f2cf13e632cf2cb1c31c32db112cb8855c5c52cb0c38b2e8cf02e38214f2c238c0 21 2097151 9 511
def hc_61_9 : Nat → Nat := unpackHintV5 0xdd824bad16ba802b6c1eb6006b5c02b1424a4c649b44c84cb4764746ac5c5c4745b80659c0e4bc704a80a49c0645c2043c104280a3d02c3c4063b8062e8682dc062c00e1e070040d0040000400000020 0x8cf0cb0e35472c0b2c71cb0c71cb0cb02cb8b2cb8b6c71c18c1402d1d2d2d2c00b02cb0070102c08e30c7803238d0c70c00000030c30c01555400000000000031c70c0155400000000071c18c015554003001c1c00201000000000000000000030c30c003434b4b40000000000002a80264b4740000000000071c0031c70c00b4b4b4b40000238d3c0000071c000b474b4b4000000000238c70c2a38e313c231c3a300e34f8e3000000000001c700002d1d2d2d8e34f000001c70002d1d2d2d00000000000071c0003000080000071c0b000632d1d2d2d000000000000008e3431e5 20 1048575 9 511
def hc_61_10 : Nat → Nat := unpackHintV5 0xf1c2b74a2238b0d1aa0dccdc3a6341d2e29bd64468abe32533162808c9334688d0654321b1f8904e34c86864a30b1c13d2448d88846c00207179038007605e2da6b12f1f0928283b0721c40a0a91c80c24400030 0x81e1c7823201e92d8b0002c0b2cb1c31c38114b2e8f2e6395c3c2cf0001c31c30000f4f42130238179b8704d3a8387a0a30a02a8b02ea694c71cbaa8b00a0813072080b093831304c0cb2c32e8b0000000000000008383000c30c32e8b00000000000130a3008793000c0070701b000b1c72cba2c042c000000000000000000aa80030c30ea8000000000072c72c002a802a800000000000002a80155540000000000000000002a80000b1c72ea8000002a800b1c72ea800000000001c70000c0002000a3aa02c001002c71cbaa0000000000000074e0231c72831c702cb2d2d000078008d34ca1c70c0b02cb2cb4b4000024d3930e1c74c70c00cb4c34e2e2cb6cb6cb0c4c4c206c6c2c0b2e0831c70c542c2cb1c73d2d8cf2d70f0b3c00031c70c0003d3d0075c08d705c713134e8028e1e4ea4c31c71c74c300b02d31c72e2e2cb6db2d6cb4013070206db06c0b0a1c30c30c700c0c3a88a3d3d0c75c5c0c71c33c0350e64f0c3aa5c3c3c70d700c03883d3d5c30ea970c70c30c3a22a0eaa83a3aaa830c30c70ea69aa0c30c31c3a8a2a830c70c30c31c22934c1c1e8f4f5717230c5c70e8f0961d473c30cf4c30d70f0f4f8c31c3a5c208701cf4f570c34d30c35c31c30c30e4e4e830e0e8c30c0c0c3a831c30c30c34e930c30d0c3430c30d3a4c30c3030c1c33e2e8e34f 21 2097151 9 511
def hc_61_11 : Nat → Nat := unpackHintV5 0xb1482a008a840e0700a0618742fd8e2fc001e48c1e40011c640008e 0x1c701c71c72c0b1c71c72cb001c1c02c00300130c30c3000c30c32cb2cb0000000000e300000c00130c30c301320000c30c3010b02cb2cb0000000000001c31c071503031e3e4cb2c343630c32cf5c3c2cf000000031e4e4cf4f4030230c13170c70c7000e30c70c04c4c4d30c30c70c70c30e0d30e0c32c0b0c30c70c70c30c30d0c3532d32c0030c031c030c0304c4c2c0701c70d4b4e4e4c34cb2c30c343632d302c000c04e4e4c34d4030302313071c74c034d30cb02c32c32d32c0030130b0 20 1048575 9 511
def nh_61 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_61_11 (Nat.sub p 352)) (hc_61_10 (Nat.sub p 320)) (Nat.blt p 352)) (hc_61_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (Bool.rec (hc_61_8 (Nat.sub p 256)) (hc_61_7 (Nat.sub p 224)) (Nat.blt p 256)) (hc_61_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (hc_61_5 (Nat.sub p 160)) (hc_61_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_61_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_61_2 (Nat.sub p 64)) (hc_61_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_61_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def f_61 : Nat → Nat × Nat := unpackForestF 0xb4eb434c00b4bb2935b283500b43b184db0137b094db003700b42ae35eae145ae04500a4facc50aca4c00a4ba9b50a995ca9950a985ca985000a47a6c5ea6c52a6c50a6925a682500a43a3b5ea5352a3935a4352a383500a3fa0a5ea2252a0925a1252a082500a339f23f9f2330094f9e1449b34f9ca349c9349b3439b14c9b13e0094b91b5091a5c91a519823f9823391a5096b6c96a6091a3f953609526c91a339392f939239185c9223f922339185000947902449014487b4f8f13487b438793e8d23f8d233878188c132878158b1348823f88233880338802b8884c88023878140094385b5e86352858350093f84815009337b45e7b4527b3537b25f7b25e7b15e7e9267e8157f0297f0217e8147b1527b02b7b0277bc5e7bc527ba527b0250092f7901879015790140092b7645e7635276c5e76b5e7603d009277414c7413e74015009237123f712337113f7112f711270084f700446d34f6e9346e8346d3436d04c6d03e0084b63b5063a5c63a516a23f6a23363a5068b6c68a6063a3f673606726c63a336592f659236395c6423f642336395000847621446204454b4f6103454b435f9445f84454a4f5e1345e03454a3f5c4605c14c5c04c54a375483e5a23f5a2335482c5923254826580345523f55233551335512b5594c55123548240084350b5e5095f52944509535145251152509350083f4f8260083342c5e42c5242b5342a5f42a5e4295f4b934429534293f429334292b4292746c5e46c5246b524695246922429254285e4302643016438294382143014428520082f4082c40826408240082b3b45e3b3523b15f3dc603d94c3b1533bc5e3ba5e3b9523b13d008273a13436a3f3912436a333684c3683e37132368260082335244351443234f3413432343331263223e3213e0081f30944308442d34f2f8342d3432e8262d13e2d03e2d0260081b0b45e2ba480b45328a4a2a24028a4628946288460b45227a580b35f25d602645025a380b35324a480b34f23a380b3430b25e225600b2531f45120246200461f4501f3510b2520b2431d45e1d4520b23e1c13c0b23b1b15c0b2331a14414c5e1914414c5214b5e17c5014b5214b4e14b421494d15450149450b2321245e1245212c50121520b13e1112e0b1320dc5e0dc520f4500d9520d83e0d8320b03e0b93e0b9320b82e0b032008170a0440134f082340813408034013430703403a3f0612803a33039330392b0414c03923011240202902021018140103e008130001f 9 11
def ch_61 : Nat → Bool := dagCheckNodeV5 m_61 g_61 ep_61 4 15 bds_61 362 (dagTraceF m_61 s_61 8 f_61) cur_61 nh_61
set_option maxHeartbeats 0 in
theorem rc_61 : dagCheckRootsV5 m_61 g_61 ep_61 4 15 362 bds_61 (dagTraceF m_61 s_61 8 f_61) (cur_61 0) (nh_61 0) s_61 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61_0 : treeBlockF 0 32 ch_61 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61_1 : treeBlockF 32 64 ch_61 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61_2 : treeBlockF 64 96 ch_61 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61_3 : treeBlockF 96 128 ch_61 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61_4 : treeBlockF 128 160 ch_61 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61_5 : treeBlockF 160 192 ch_61 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61_6 : treeBlockF 192 224 ch_61 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61_7 : treeBlockF 224 256 ch_61 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61_8 : treeBlockF 256 288 ch_61 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61_9 : treeBlockF 288 320 ch_61 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61_10 : treeBlockF 320 352 ch_61 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61_11 : treeBlockF 352 362 ch_61 = true := by decide +kernel
theorem nj_61_1 : ∀ i, 0 ≤ i → i < 64 → ch_61 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_61_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_61_1 h1 h2)
theorem nj_61_2 : ∀ i, 0 ≤ i → i < 96 → ch_61 i = true := block_join nj_61_1 (fun _ h1 h2 => treeBlockF_at nb_61_2 h1 h2)
theorem nj_61_3 : ∀ i, 0 ≤ i → i < 128 → ch_61 i = true := block_join nj_61_2 (fun _ h1 h2 => treeBlockF_at nb_61_3 h1 h2)
theorem nj_61_4 : ∀ i, 0 ≤ i → i < 160 → ch_61 i = true := block_join nj_61_3 (fun _ h1 h2 => treeBlockF_at nb_61_4 h1 h2)
theorem nj_61_5 : ∀ i, 0 ≤ i → i < 192 → ch_61 i = true := block_join nj_61_4 (fun _ h1 h2 => treeBlockF_at nb_61_5 h1 h2)
theorem nj_61_6 : ∀ i, 0 ≤ i → i < 224 → ch_61 i = true := block_join nj_61_5 (fun _ h1 h2 => treeBlockF_at nb_61_6 h1 h2)
theorem nj_61_7 : ∀ i, 0 ≤ i → i < 256 → ch_61 i = true := block_join nj_61_6 (fun _ h1 h2 => treeBlockF_at nb_61_7 h1 h2)
theorem nj_61_8 : ∀ i, 0 ≤ i → i < 288 → ch_61 i = true := block_join nj_61_7 (fun _ h1 h2 => treeBlockF_at nb_61_8 h1 h2)
theorem nj_61_9 : ∀ i, 0 ≤ i → i < 320 → ch_61 i = true := block_join nj_61_8 (fun _ h1 h2 => treeBlockF_at nb_61_9 h1 h2)
theorem nj_61_10 : ∀ i, 0 ≤ i → i < 352 → ch_61 i = true := block_join nj_61_9 (fun _ h1 h2 => treeBlockF_at nb_61_10 h1 h2)
theorem nj_61_11 : ∀ i, 0 ≤ i → i < 362 → ch_61 i = true := block_join nj_61_10 (fun _ h1 h2 => treeBlockF_at nb_61_11 h1 h2)
theorem nc_61 : ∀ i, 0 ≤ i → i < 362 → ch_61 i = true := nj_61_11
theorem lb_61 : LowerBin m_61 s_61 g_61 9 :=
  lowerDagV5 (kn_cons lb_4 (kn_cons lb_48 (kn_cons lb_47 (kn_cons lb_31 (kn_cons lb_30 (kn_cons lb_12 (kn_cons lb_35 (kn_cons lb_0 (kn_cons lb_42 (kn_cons lb_58 (kn_cons lb_18 (kn_nil)))))))))))) rc_61 nc_61 (by decide +kernel)

def m_62 : Nat := 0x3333333333333333
def s_62 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_62 : Nat := 0x113131311131333
def ep_62 : Nat := 0x1000002000001200000002200012000000020020010202020002020000000000000000000110101011101000
def bds_62 : List (Nat × List Nat × Nat × Nat) := [(m_30, s_30, 6, g_30), (m_33, s_33, 5, g_33), (m_26, s_26, 5, g_26), (m_36, s_36, 5, g_36), (m_37, s_37, 5, g_37), (m_52, s_52, 5, g_52), (m_57, s_57, 5, g_57), (m_14, s_14, 4, g_14), (m_10, s_10, 4, g_10)]
def cur_62 : Nat → List (Nat × Nat) := unpackCursorV5 0xb2691e71c7131c1 0x215d3495a5d249935a3958956791d547149c01f 6 63 2 3 10 1023 14 16383
def nh_62 : Nat → Nat := unpackHintV5 0xdf00a378a300706670006a8b62113658006c0000 0x6300058d6318f60bd1bce78efa019d40006f1ad5abb06e73c79d02776c3d8e5bd6003054068d540f1ea90058c600b5001a9e3c00038f31d 16 65535 7 127
def f_62 : Nat → Nat × Nat := unpackForestF 0x215d191da5d151cb5a2958956149c01f 4 10
def ch_62 : Nat → Bool := dagCheckNodeV5 m_62 g_62 ep_62 3 7 bds_62 9 (dagTraceF m_62 s_62 7 f_62) cur_62 nh_62
set_option maxHeartbeats 0 in
theorem rc_62 : dagCheckRootsV5 m_62 g_62 ep_62 3 7 9 bds_62 (dagTraceF m_62 s_62 7 f_62) (cur_62 0) (nh_62 0) s_62 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62 : treeBlockF 0 9 ch_62 = true := by decide +kernel
theorem nc_62 : ∀ i, 0 ≤ i → i < 9 → ch_62 i = true := fun _ h1 h2 => treeBlockF_at nb_62 h1 h2
theorem lb_62 : LowerBin m_62 s_62 g_62 8 :=
  lowerDagV5 (kn_cons lb_30 (kn_cons lb_33 (kn_cons lb_26 (kn_cons lb_36 (kn_cons lb_37 (kn_cons lb_52 (kn_cons lb_57 (kn_cons lb_14 (kn_cons lb_10 (kn_nil)))))))))) rc_62 nc_62 (by decide +kernel)

def m_63 : Nat := 0xcccccccccccccccc
def s_63 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_63 : Nat := 0x40444004404cc
def ep_63 : Nat := 0x400088000004400000048800040040004400c8000404000000040000000000000000000004044400440400
def bds_63 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9), (m_38, s_38, 5, g_38), (m_25, s_25, 5, g_25), (m_31, s_31, 5, g_31), (m_55, s_55, 5, g_55), (m_44, s_44, 5, g_44), (m_32, s_32, 4, g_32), (m_0, s_0, 4, g_0), (m_16, s_16, 4, g_16)]
def cur_63 : Nat → List (Nat × Nat) := unpackCursorV5 0x292a42909525088e118421069da0681a05cd705855154150505405014035cd0340c1288a006401 0x992f7123b9516931d9294121ca496122282e5a40bb518a3e5232b13e4132183ea8169c5e925e895279445a505b50745e6b52625e5252495e415239452024284f1843eb4ee342d243c14fa143812f3123102e0822001f 10 1023 4 15 11 2047 16 65535
def nh_63 : Nat → Nat := unpackHintV5 0x10d999dc3f3b8006beb2d54298327af80e5e20eba81d4d282950551c0ea241515af22b00442148404505829fc0f3e01879828ea889cb0a2ccca58414b0801570a1a7081b598003680000 0x180274e00739cea00005c000006004d1a30018c639acc00006130000007340d88ce7180bde80000ce3c0e338d5e1b1e0f00037b459b00781b1e339c6a00000b362f73078ce71af78c6bb5eaab166cf3decdef7bdec38c6717b1cd18deaec07319ce71af5558b37b59ee039a0aaac16339c6000ce71aaad6b58000002a800ce71aa800000800701a09d180ce71a800c38b1162c 19 524287 8 255
def f_63 : Nat → Nat × Nat := unpackForestF 0xb4e0b42d9290a43ca49094fab51a93ea81609438c5e8a5e8952092f79443c5e3b523a5e5b503a52395e395239450923184f20241843082e0822001f 5 11
def ch_63 : Nat → Bool := dagCheckNodeV5 m_63 g_63 ep_63 3 7 bds_63 30 (dagTraceF m_63 s_63 7 f_63) cur_63 nh_63
set_option maxHeartbeats 0 in
theorem rc_63 : dagCheckRootsV5 m_63 g_63 ep_63 3 7 30 bds_63 (dagTraceF m_63 s_63 7 f_63) (cur_63 0) (nh_63 0) s_63 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63 : treeBlockF 0 30 ch_63 = true := by decide +kernel
theorem nc_63 : ∀ i, 0 ≤ i → i < 30 → ch_63 i = true := fun _ h1 h2 => treeBlockF_at nb_63 h1 h2
theorem lb_63 : LowerBin m_63 s_63 g_63 8 :=
  lowerDagV5 (kn_cons lb_9 (kn_cons lb_38 (kn_cons lb_25 (kn_cons lb_31 (kn_cons lb_55 (kn_cons lb_44 (kn_cons lb_32 (kn_cons lb_0 (kn_cons lb_16 (kn_nil)))))))))) rc_63 nc_63 (by decide +kernel)

def m_64 : Nat := 0xff00ff00ff00ff
def s_64 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_64 : Nat := 0x170057005700ff
def ep_64 : Nat := 0x4000a800000040000000a80000000000000000000600020002000000120002000200000014005400540000
def bds_64 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8), (m_0, s_0, 4, g_0), (m_51, s_51, 5, g_51), (m_49, s_49, 5, g_49), (m_54, s_54, 5, g_54), (m_29, s_29, 5, g_29)]
def cc_64_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb42b2ac2b099660946509060480200801b56c1b06c1b06499064145501405014048920480d507001 0xfa443c0910b5e40d68eb5238958d95632970bb5c20d34c34510934b24528d749a5d2457050360409872341a4d0845e1f168645216d5850560c910292410d783b5a08d481a560415a034f78d1dba4f6691d714f5451d11373449ca84f2211c48370209c001f 10 1023 4 15 11 2047 18 262143
def cc_64_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x88441dae870b81b2bc5c2e1709548225108132180c0601e8e070381c0a85028028000000 0x3f4b9f15d909afa174b06bd84ce4a642537a28a404de022ecd7352bae125d02e8609724b9835ca5a6e2d16149b7a45b5aed8976326cd926ac2e4e8d260694c5ea22d4b14a46ad1956 9 511 3 7 11 2047 17 131071
def cc_64_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xc29a21100 0x884c854c534d8745204d8245 6 63 3 7 9 511 16 65535
def cur_64 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_64_2 (Nat.sub p 64)) (cc_64_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_64_0 p) (Nat.blt p 32)
def hc_64_0 : Nat → Nat := unpackHintV5 0xed09ca437c66c8cbb797602e815d00b90546b28c05180a3010cea180430084090411e883a0c6e18a2e944028804f089a111481f8c391838e801c0000 0x3fd3d13fdff0d555005103c000141540003e20019660000880f00fff13d3df7fc905550001103c43ffd0f53fdff2555400001440f055550410041000 15 32767 6 63
def hc_64_1 : Nat → Nat := unpackHintV5 0xd000d000af42af00ae02ae00ad029530950095009500744274007302730072025a305a005a005a00384438003800360434042c10260c200c023c020002000004 0x5b6d5fb555550c484155557dd754015d5555d757d4312150550f30c000004d4d30c0f0300000fff1f43df7fc341554440f10000f 16 65535 7 127
def hc_64_2 : Nat → Nat := unpackHintV5 0xd00c82c80c02030000 0x55fb6d555500 12 4095 6 63
def nh_64 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_64_2 (Nat.sub p 64)) (hc_64_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_64_0 p) (Nat.blt p 32)
def f_64 : Nat → Nat × Nat := unpackForestF 0x2204c82516114c821140b4f7a971e95d7a1740b4776131c14572531c0450293da35c68575a05d0291d925c5ed15835c5e914094f56d755a5d561700947471791c5a4c8d13034471491b5646558093736d78db5a3c910f02436d48da5636558092732970b3452ed70b2450213c935d24974915c0211c545e151686a341a4d0545214d585056020dc135e04d682a440a49013520495810560209c001f 7 11
def ch_64 : Nat → Bool := dagCheckNodeV5 m_64 g_64 ep_64 2 3 bds_64 69 (dagTraceF m_64 s_64 7 f_64) cur_64 nh_64
set_option maxHeartbeats 0 in
theorem rc_64 : dagCheckRootsV5 m_64 g_64 ep_64 2 3 69 bds_64 (dagTraceF m_64 s_64 7 f_64) (cur_64 0) (nh_64 0) s_64 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_0 : treeBlockF 0 32 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_1 : treeBlockF 32 64 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_2 : treeBlockF 64 69 ch_64 = true := by decide +kernel
theorem nj_64_1 : ∀ i, 0 ≤ i → i < 64 → ch_64 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_64_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_64_1 h1 h2)
theorem nj_64_2 : ∀ i, 0 ≤ i → i < 69 → ch_64 i = true := block_join nj_64_1 (fun _ h1 h2 => treeBlockF_at nb_64_2 h1 h2)
theorem nc_64 : ∀ i, 0 ≤ i → i < 69 → ch_64 i = true := nj_64_2
theorem lb_64 : LowerBin m_64 s_64 g_64 8 :=
  lowerDagV5 (kn_cons lb_8 (kn_cons lb_0 (kn_cons lb_51 (kn_cons lb_49 (kn_cons lb_54 (kn_cons lb_29 (kn_nil))))))) rc_64 nc_64 (by decide +kernel)

def m_65 : Nat := 0xf0f0f0f0f0f0f0f
def s_65 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_65 : Nat := 0x10707070107070f
def ep_65 : Nat := 0x800000600000006080006000000060008000000000000000001020202010202000104040401040400
def bds_65 : List (Nat × List Nat × Nat × Nat) := [(m_43, s_43, 7, g_43)]
def cur_65 : Nat → List (Nat × Nat) := fun _ => []
def nh_65 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_65 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_65 : dagCheckRootsV5 m_65 g_65 ep_65 1 1 0 bds_65 (dagTraceF m_65 s_65 7 f_65) (cur_65 0) (nh_65 0) s_65 7 = true := by decide +kernel
theorem nc_65 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_65 g_65 ep_65 1 1 bds_65 0 (dagTraceF m_65 s_65 7 f_65) cur_65 nh_65 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_65 : LowerBin m_65 s_65 g_65 8 :=
  lowerDagV5 (kn_cons lb_43 (kn_nil)) rc_65 nc_65 (by decide +kernel)

def m_66 : Nat := 0xffffffff
def s_66 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_66 : Nat := 0x115717ff
def ep_66 : Nat := 0x6a800000000004600e8000000000002060000000000110212000000000011541400
def bds_66 : List (Nat × List Nat × Nat × Nat) := [(m_43, s_43, 7, g_43), (m_39, s_39, 5, g_39), (m_41, s_41, 5, g_41), (m_37, s_37, 5, g_37), (m_45, s_45, 5, g_45), (m_40, s_40, 5, g_40), (m_44, s_44, 5, g_44), (m_10, s_10, 4, g_10), (m_1, s_1, 4, g_1), (m_42, s_42, 4, g_42), (m_56, s_56, 5, g_56), (m_15, s_15, 4, g_15), (m_17, s_17, 4, g_17)]
def cc_66_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x7e17a27a07057007007007006c26c06826046006006006005c25c05c05825045005005005005005004e146432a038001 0x150a81815010160f3481d4882819070220183c174a01e570551c061341969a30d2459a28a341104a01e570351c061341269e22d2c39a385b43042680ed3c19a582b47036864b17c922d8fc571b8a6341704c2b050540909810110081e5134fa169730d1e2da1c514f882970a51dfca1bd13f78276ee4ddd499b984f6e096da11dac21b483f67076ca0dd7019a801f470364e05c04098001f 12 4095 5 31 11 2047 19 524287
def cc_66_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb42b299660982518ca308c230886208820280200801e2781e056550504d7340a3208801885114005 0x1d15866481fb48729a1f248628c1e94474911dc5973145a95c668d191345ed7173506ed3db34b68d1d8b436053d6947584fd5937521294a308b17e245b8115de45370969523050168c8644c150383c30190303c2e15118341e1111360429b1006c2c150283c 10 1023 4 15 11 2047 18 262143
def cc_66_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x803c9b6d868b41a0d06130180c055aa10a80402010072381c0c444200c844200c8600600 0xbe96af156c695f0056ba09ad954b0d82b96caad22a244a6512d45fb316eb457a514e89569ad82626c94d224a449f17e745b9715e44538c961ba30769a1b230868e2136082981a230 9 511 3 7 11 2047 18 262143
def cc_66_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0a9a8a88c88818080797871707069684c484841403938313029281310100200 0xfc943ec56f8d5bd957e016fc93cec55ba248e21139257e093d4126de09b6026d4d5b4026cc903206cc2152f024c45770945 8 255 3 7 11 2047 18 262143
def cc_66_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xe8382e0380be6d299e24881e4781e0781c2701a259160580ca2c4b0284a028055140501405014005 0x9f0f278307e4f6812b9d49e702b9b09d601f4d06d08172204d3019210466a5099575f53d5607d2c1b4005c7c135507d281b3f05c78135407524193d05474113ad6249300c152402c940be4c2b9109e3c23978e25938954d639348d0e230345207d201b3c05c6c1389516255687d4ded3f8614dc84b630ce114c83512093c810620014 10 1023 4 15 10 1023 18 262143
def cc_66_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x484a10000 0x147455a0fa786d142e4a13590fa706d102e4813 7 127 3 7 9 511 17 131071
def cur_66 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (cc_66_5 (Nat.sub p 160)) (cc_66_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_66_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_66_2 (Nat.sub p 64)) (cc_66_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_66_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def hc_66_0 : Nat → Nat := unpackHintV5 0x81c48fd069e81239a36674c0cd019960432c0062830c500181092ae545500ca881951002a20052024a4001480027e1245ca073980b730168062c40c54048a8001341c198d0082b0001000000 0x2b1cf0db9eb1cf0cad5b071ebac92eb1cf0c75071c71c0002aaa80155540152bad6b2b2dac92d433c33c0002aaa955541abaeb22dac92c0002aaa8015554001560f3cf3c0002aaa8015554015030c30c0002aaa80155540152baeb8dbadb8e4b8db8db8db8dbaaaa02555501540000aaaa0055550005566b4755553d543541000065500000000 19 524287 8 255
def hc_66_1 : Nat → Nat := unpackHintV5 0xee84b9e1cd80fb540cd5003480cbd152e60eb801ae000b5032d400b381ab816aa83aaa00aa802a406a781a9806879ea120c758f0dcfa34828a82a1e0c0720615078480c0d8480036 0x1bab6b0cf4aeb070cf1cb1c92ebac3acb5d72cb3c30cf00962cb99ad2ebadbaeb9b4bac2ebadb5e5e5e5e6db6db102d2cb4b4b691a00b6471c30c02d4b4b640000b1cb2cb2c72cb2c32c32cf000002d797979780152d2cb4b4b402aa566b6b6bac70d4f0caeb1cf0cf534aeb1cf0dbac35ac6eb22dad0d1cf0c 18 262143 8 255
def hc_66_2 : Nat → Nat := unpackHintV5 0x9f02129151ed653da007882ce70a1c50938a006bc58d6019a9033440e64444b39510e591f8243b83875818e5061aa203480c66030b8140b4bc16800200d02a1605400090180d050091100012 0xadad1df1cba2c0173cf0555550cf0cf00004d74cf0c33c0155550dac01551d554b4000195556b0eabacf0cf93ab3c3aeb20e3c32daebac76bac87a4bae833c33c02668b4b4b2c280002aaa8021eaa8fa83a000054b4b4b4b40019ae968bad2eb0d5daeb3d4daeb0eb2ad7436bac7ac92eb1d5d00005e5e5e5e00555d550066b554755754f543500004b55ac32c30cf12ebac72d32cf2b6ebac6ebac2c30cae76eb 19 524287 8 255
def hc_66_3 : Nat → Nat := unpackHintV5 0x8fa0623504c8a01a21fc427e94b1e54a87203a99e1506411b9758d65743113553e4be0b92f8004a60c11f850412360da9503331b8b20d628e1d07dd2e1cb160570de0f434013d4a04f0000d8320360000b01400016000000 0x1c70c30cf0cf1c700ca0c32c33cf0e0e3cf000e0e4df0c32d2d0cf0cf0c71dfaeb0c33cf0cf3c73cf3cf1ea0000000004ea0eac30e830c3004d74cf3c30d73cf2cf4f2cf4025d7830c30d34d34c0c2aa8a80934d34c30c30d75d75ea830c30c0002a93a0eaea8021ea4ea0e080002a4d34d30c30c300aaa98b90c30d30c30c70c34c30c3a80000000013934d3830cf0c3a83ab004d34d30cb0d0c30d0d70c30c300975ea0cf0cf3cf000aaaa0eacb4b535c33c33c0002aaaa0eac021eaa8f80002a4d75d33c30cf00aaa98b91c71c7014d34d31c71c74d34d35d75d711c71d2d2d2c02d2d5471c71c70c73c70c71c0001c000001c71c75c71c71e1d71e4d34d300476b1c751c72cb4b400b4b6b2dae4b4b9faeb4d2cf0cf58b2e3c30cf005df555551d34c700001d71d34d700476b55554d0005552d4f543500006555554b0cb2cb0cb3c74d31c00000000b5cb8b2cb875d75d71d74d35c0071c71c75476b2d4cb2d0002d5cb2d1e873c30cf001c74d30551dad55471c71c000071c71d34d34c01551dad5401551d4f54350000655552cb0d0d3cf005e5e3d30d0d2cb0c30cf0cf2c72cb2cb1d5000000004d75d33cf0c35cf2cb2e2d72e002d2d436b0c350c30c00b4b474d31e0c380030d54d555430c30c000134d34c30c30c0155350dad5401551d54d50d0000655550c30c34d34d3104d34d30d70c30c35d75d72d4cb2d0d12c02d2d0c30d30c30c70c30c3540000000c004d34d30d70e0c30e0d70c30c3002d4cb2d0c32c30d50dac00b4b433eb2dad7d1e4faeb50cb0cb3cf0009f9355543 22 4194303 9 511
def hc_66_4 : Nat → Nat := unpackHintV5 0xed80076901bb300dd8c06e105b6da1731da7d774bcb3e3e559232ab00d54c06aa60054606aa30014e41a9ce524a91f229958ea554624972e1189391bc97c2649c111bd488be9004e4881ce520b71803a908000ea 0xaeb6c30c3031c3c00c074d31c30c30c36db1d34c70c30c36db3e3e0e0e000c34d30c32d2d0c33c30c30c30c30c70eb0000030000030e0c30e1d34c70c30c30c0032c3430c3474d31c30c30c0031c3000c03c71c71cf0c33db9e76c71c71cf0c33db9e76c31c300002aaa80071c71cf0c33c02a871c3a0cfa3c00071c71cf0c33c71c00b4b6bac30cf2bac73c3031c70c7031c71cf0c33c000000071c71cf0c33c0031c30000071c71cf0c33c015554015431c3031c71cb0c32c00000071c71cf0c33cb2cb2c0030c71c31c3ac30c31cf1c0000001c0001c71c73c30cf1c71c7871c780071c71cf0c33c71c71d1c72c7402a1c71c71c31cf1c31c70000000087ab1c7a1c74e4e001c71c75c71c71d1cb1d4d34d300975e00cf0cf001e1caae4cb4b475c74d31c00021eaeaaa93802a3ea0e80002a1d75c75d34d700aaa98b93d30eb4e1eb575cb1ea930df3d30cf1d34c7000000001c71c71ea1eae4d34e005cb7d5cb475d75c75d34c025d7871c71c0002a2a80071c71cf3cf3c02a830c30c0002a872a80071c71c30c30c02a871c71c01d34d34ea2a80871c71d34d34d75d75ea871c71c0002a2a8015554015471c71c0002aa2a80071c71cb2cb2c02a871c71c0002aa1eaea8021e8faa0ea080002a1c71c74d34d300aaaa68b9 21 2097151 9 511
def hc_66_5 : Nat → Nat := unpackHintV5 0x5006c53a6407500000700000 0x1e871c30e0e0001c70c30c32d2d0c70c31c3ac30c30c30c30000000001c71c70c30e0c3830c30c0071c71c30c3432c3430c30c0031c3ac30c71c30c31c71c0000000074d31cf3c30d33cf3cf8f4cf80074d31cf0c33cf2cf4f2cf402b03 19 524287 9 511
def nh_66 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (hc_66_5 (Nat.sub p 160)) (hc_66_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_66_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_66_2 (Nat.sub p 64)) (hc_66_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_66_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def f_66 : Nat → Nat × Nat := unpackForestF 0xa328a02d3c05a5cd92b9e0793c0c26c93cd82b9b04f3294264ae80b478c471184e2309ac782f8f057244c23c13c802c8f047184d2301c46034016860253e24ab0094b866a70c14c04a3c014c80289004f2000c4001401286fc941ee2b3db567b2ae024fde49e0093b0126eec5580499ba2480109ede95dc42237a4f6f04c0212c0423b602601086d4d58041fb402601076cc900041bb206c5d4aec257584a2ae8565e4b4bc5597413008335b2a8a317d462dabb60572d8a315d4da429a4453288a314d44ab0081f488be9116d31b02626c488ae92d21252224453010368c960a22f9445b4347082d810530144573d6907a920f4a214453398b274910e6289425a2b69e56d2cd4ae15b4732468644d0ada19594f2e6b85cd40aca39593f2b26e508c0a5181405a0102e4c1500a2f8145b2306840d8081361006c028ae38d2071220e044028a60417051a68a349174a028d14551c0a341020ac16d3c2da587a500f2b816d1c311c061340b686041500826010440369e06d2c0da38213403686040f004098001f 8 11
def ch_66 : Nat → Bool := dagCheckNodeV5 m_66 g_66 ep_66 4 15 bds_66 164 (dagTraceF m_66 s_66 8 f_66) cur_66 nh_66
set_option maxHeartbeats 0 in
theorem rc_66 : dagCheckRootsV5 m_66 g_66 ep_66 4 15 164 bds_66 (dagTraceF m_66 s_66 8 f_66) (cur_66 0) (nh_66 0) s_66 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_0 : treeBlockF 0 32 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_1 : treeBlockF 32 64 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_2 : treeBlockF 64 96 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_3 : treeBlockF 96 128 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_4 : treeBlockF 128 160 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_5 : treeBlockF 160 164 ch_66 = true := by decide +kernel
theorem nj_66_1 : ∀ i, 0 ≤ i → i < 64 → ch_66 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_66_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_66_1 h1 h2)
theorem nj_66_2 : ∀ i, 0 ≤ i → i < 96 → ch_66 i = true := block_join nj_66_1 (fun _ h1 h2 => treeBlockF_at nb_66_2 h1 h2)
theorem nj_66_3 : ∀ i, 0 ≤ i → i < 128 → ch_66 i = true := block_join nj_66_2 (fun _ h1 h2 => treeBlockF_at nb_66_3 h1 h2)
theorem nj_66_4 : ∀ i, 0 ≤ i → i < 160 → ch_66 i = true := block_join nj_66_3 (fun _ h1 h2 => treeBlockF_at nb_66_4 h1 h2)
theorem nj_66_5 : ∀ i, 0 ≤ i → i < 164 → ch_66 i = true := block_join nj_66_4 (fun _ h1 h2 => treeBlockF_at nb_66_5 h1 h2)
theorem nc_66 : ∀ i, 0 ≤ i → i < 164 → ch_66 i = true := nj_66_5
theorem lb_66 : LowerBin m_66 s_66 g_66 9 :=
  lowerDagV5 (kn_cons lb_43 (kn_cons lb_39 (kn_cons lb_41 (kn_cons lb_37 (kn_cons lb_45 (kn_cons lb_40 (kn_cons lb_44 (kn_cons lb_10 (kn_cons lb_1 (kn_cons lb_42 (kn_cons lb_56 (kn_cons lb_15 (kn_cons lb_17 (kn_nil)))))))))))))) rc_66 nc_66 (by decide +kernel)

def m_67 : Nat := 0xffff0000ffff0000
def s_67 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_67 : Nat := 0x117000011570000
def ep_67 : Nat := 0x1040000000000000000000000016000000460000010600000002000001120000110200000114000011540000
def bds_67 : List (Nat × List Nat × Nat × Nat) := [(m_21, s_21, 7, g_21)]
def cur_67 : Nat → List (Nat × Nat) := fun _ => []
def nh_67 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_67 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_67 : dagCheckRootsV5 m_67 g_67 ep_67 1 1 0 bds_67 (dagTraceF m_67 s_67 7 f_67) (cur_67 0) (nh_67 0) s_67 7 = true := by decide +kernel
theorem nc_67 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_67 g_67 ep_67 1 1 bds_67 0 (dagTraceF m_67 s_67 7 f_67) cur_67 nh_67 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_67 : LowerBin m_67 s_67 g_67 8 :=
  lowerDagV5 (kn_cons lb_21 (kn_nil)) rc_67 nc_67 (by decide +kernel)

def m_68 : Nat := 0xffff0000ffff
def s_68 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_68 : Nat := 0x1757000017ff
def ep_68 : Nat := 0xa8000000000000000000000040000000e8000006020000060000001202000012000000145400001400
def bds_68 : List (Nat × List Nat × Nat × Nat) := [(m_40, s_40, 5, g_40), (m_11, s_11, 4, g_11), (m_35, s_35, 4, g_35), (m_32, s_32, 4, g_32)]
def cur_68 : Nat → List (Nat × Nat) := unpackCursorV5 0x4080e5c3862c0681 0xd2e3d73e9f747927a91cc6e01f 7 127 3 7 10 1023 13 8191
def nh_68 : Nat → Nat := unpackHintV5 0x3287ca03005b21ec80a61a8820144000 0xe9ee8fcdd3a5555550400000001 14 16383 7 127
def f_68 : Nat → Nat × Nat := unpackForestF 0x3a7e970e8e64f7ae191cc6e01f 3 10
def ch_68 : Nat → Bool := dagCheckNodeV5 m_68 g_68 ep_68 1 1 bds_68 8 (dagTraceF m_68 s_68 6 f_68) cur_68 nh_68
set_option maxHeartbeats 0 in
theorem rc_68 : dagCheckRootsV5 m_68 g_68 ep_68 1 1 8 bds_68 (dagTraceF m_68 s_68 6 f_68) (cur_68 0) (nh_68 0) s_68 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68 : treeBlockF 0 8 ch_68 = true := by decide +kernel
theorem nc_68 : ∀ i, 0 ≤ i → i < 8 → ch_68 i = true := fun _ h1 h2 => treeBlockF_at nb_68 h1 h2
theorem lb_68 : LowerBin m_68 s_68 g_68 7 :=
  lowerDagV5 (kn_cons lb_40 (kn_cons lb_11 (kn_cons lb_35 (kn_cons lb_32 (kn_nil))))) rc_68 nc_68 (by decide +kernel)

def g_69 : Nat := 0x1171757115717ff
def ep_69 : Nat := 0x104000a800001640000006a800160040004600e8010606020002060001121202110212000114145411541400
def bds_69 : List (Nat × List Nat × Nat × Nat) := [(m_67, s_67, 8, g_67), (m_64, s_64, 8, g_64), (m_65, s_65, 8, g_65), (m_62, s_62, 8, g_62), (m_66, s_66, 9, g_66), (m_60, s_60, 8, g_60), (m_59, s_59, 8, g_59), (m_28, s_28, 7, g_28), (m_61, s_61, 9, g_61), (m_63, s_63, 8, g_63), (m_68, s_68, 7, g_68), (m_53, s_53, 5, g_53), (m_20, s_20, 7, g_20), (m_52, s_52, 5, g_52), (m_0, s_0, 4, g_0), (m_12, s_12, 4, g_12), (m_21, s_21, 7, g_21), (m_43, s_43, 7, g_43), (m_50, s_50, 5, g_50), (m_11, s_11, 4, g_11), (m_36, s_36, 5, g_36), (m_46, s_46, 5, g_46), (m_30, s_30, 6, g_30), (m_34, s_34, 5, g_34), (m_49, s_49, 5, g_49), (m_33, s_33, 5, g_33), (m_54, s_54, 5, g_54), (m_55, s_55, 5, g_55), (m_3, s_3, 4, g_3), (m_29, s_29, 5, g_29), (m_23, s_23, 5, g_23), (m_35, s_35, 4, g_35), (m_45, s_45, 5, g_45)]
def cc_69_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x801c002000f827a0bd01e02f007803c01e00e047003705b80d816c03601986cc0544aa01500a805402a01500a805402a000d2001 0x431f0204f80f97c075a7838d1c1b2a80c96405ebe02d5c0154f80a17c04abf0205500fce40726c034b60495bc22ad60f56706ab18311bc138ce08c5f0322b8165ba2d8bf15c5b8a22bc4d14e1e6bf0d357859a7c20d1dff4befba5b7b12bbbc94dd249ee424b6d923b5290d9b476c0a37598afaa656d3c2ae8c153414a79e452ccb28e589432489d8e44dc5925e2012b0989381448c090b60405301c2580c10c050760202b00c1180406c010260003f 13 8191 6 63 11 2047 21 2097151
def cc_69_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xe170345a0d0646e570a9542a132984c2612179bc1c2e068b41a0b2148802210008000000 0x358fffb68a5b87ad63a497dc7ce5b850dc376b1ad7fd1b46096f2af98d70bdb85b5fab6c14d69a2b0fd5bfcad7c567dab1e71bee8cf645faa2bced8a52c91954 9 511 4 15 11 2047 17 131071
def cc_69_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x94650942328c1a96819164181601805896058142501314c1304c103400e2380c2300c0300a202800 0xbf5faee72b89b3856fdd5af5d67d358f246fc119ef45fb715ed26eb0592b154a91f2997ca295281549c592657c975c2517c915fa18188c5b2101886d3e1347af5bead6ba559e7d639b1be4c678f17e2c57885ba0818 10 1023 4 15 11 2047 18 262143
def cc_69_3 : Nat → List (Nat × Nat) := unpackCursorV5 0x8c6308c21284201801f17c1e1781c23f4f0348d0304c0300a2244721c070184600cc300c03000c00 0x7f4b8fb1c9f22c3d25c788c0ec911d6b93a25c90adf1d5ae32b3c5563868c5089be0935c02677e4c6f697de52dbba57734a6d11fdc53237a546d8f8d89f19db7b347f6a4a8ce951a2bfb3573654c8c75f18ab830a7c 10 1023 4 15 11 2047 19 524287
def cc_69_4 : Nat → List (Nat × Nat) := unpackCursorV5 0x88202801f17c1e1781e06cdb06c192334c02c4b0284a02449020480200800d430084200441000400 0x254bf4f1549c269345b2611a4a17e972692a93e5121d7d6fadad75759ea2b1d336fa46d744d9e7db1ceb5f9b6b732d5e59a9c996e918d11f162363845c587d4beea94e251dc4237870750b1a20d2e40c70 10 1023 4 15 11 2047 19 524287
def cc_69_5 : Nat → List (Nat × Nat) := unpackCursorV5 0xe86cb43a0c8e430380c054ea150992a54091482050071381c0a450209006230108804002 0x5fa4bbe48f7a4d2ec9a5c944b8ae56e972d8ae5a36db36cb931bf1e33e2b6fc36d780d9ef1b1dd34bb568f645bac0b257154ac2f954952a4aa53964a5269465f2851a50134 9 511 4 15 11 2047 19 524287
def cc_69_6 : Nat → List (Nat × Nat) := unpackCursorV5 0x88a20882027c5f07c1d2741c16c5a1645816017158524444892006218042100310c0210802000800 0xe0ce1be9b375a7ee347dbae1b39c361366b26cd36f1a0d934e3e67b60d06d99f1d351b7e936bd16cf9cd8f363077d62ed6dfc8d9f8937ef26bda4cfae98f551de6237b42f99459320be5996cc62c9884d3093e6097c 10 1023 4 15 11 2047 19 524287
def cc_69_7 : Nat → List (Nat × Nat) := unpackCursorV5 0x84201801f17c1f0749d0705c06c5b04a520480e4380d1304b128491240811c434084200441000400 0x7f1347e17c7d2347c9347b9347a95c81c6f80c677fb6f7eb6b7db677c3637b34b7a3477996e702696ca6178a4b782477756875a587424475b5c73a407424c73b547624f7524b74a477324372d7071d6870a56 10 1023 4 15 11 2047 20 1048575
def cc_69_8 : Nat → List (Nat × Nat) := unpackCursorV5 0x9ca70986609824257d5054141501314c1214811144101400f13c0e1380e0308390c0210801104001 0x9025c8f95c8ea4f8db4f8d3479d56f9c5639b46f9ac5f99c5798b6f97b6396b5f95b5b93b5791b5390b4b8f3478e16e8c8188b4648a47c89464882548747c86254852548447283c588bc6e8ab6f89b6788a6f87a6b86a6785a6384a3b83237821648117c80164 10 1023 4 15 11 2047 20 1048575
def cc_69_9 : Nat → List (Nat × Nat) := unpackCursorV5 0xf070a552088c42030078b85c0c2602c560a1502090071381c0e043201004411080040000 0x9fb4f9f347a934fa8347a724fa624ba4247a3243a223ba02378e16d9e8609da649ca549ba648d8189a16c8d01899264982348e97e97154961349567094a6c9416c9324b92a479213491134 9 511 4 15 11 2047 20 1048575
def cc_69_10 : Nat → List (Nat × Nat) := unpackCursorV5 0xe870781a2d06830580b8dc2c2e868b4164b049241028040188a250209006230180480200 0xaf156aee70ae16cad234ac934ab934aa95cb2c5fb1c57b0b5fafb5badb57ac353ab34baa3479f870a8d709f070a7c7c8e97da6a7ca5b4fa504ea4d70a3a7ca2a7ca1b5ba1353a0c70 9 511 4 15 11 2047 20 1048575
def cc_69_11 : Nat → List (Nat × Nat) := unpackCursorV5 0xf03c0f03a1e83a0e0780e0380e0380e0342d0321c8301c02e1b82c1b02a11c860180411002108001 0xb924fbcd68b9c64b9367b8264b7568b6264b5264b4468c046fbfc63bf45bbec57be36fbdb57bd34fbc347bba6fbb263baa5bba257b8a4fb7a4bb6a47b5a43b4a3bb3a37b216cb1154b0134 10 1023 5 31 11 2047 20 1048575
def cc_69_12 : Nat → List (Nat × Nat) := unpackCursorV5 0xf03c0e4ebeac2b0a0e80a0244902318c203802007c5b46c1b06c1b055950541505415039c0e00000 0xcfd6fcf567cea62d3d6fd2d6bd1d67d0d63d026eb496fab16ba2167909638495f7b15b6a9575d153ce125cd468cc965c394dc6470cbc58cb155c314dca13fc9c70c917dc294dc7c50c5c70c8458c7155c214dc6569c5d618415f5c153c513bc4937c3d6fc356bc2d67c2563c1c6e901625b952cc56fcad6bc8d67c6d63c4462b396faa16ba01678f1638315f7a15b661575a953c114d 10 1023 4 15 11 2047 20 1048575
def cc_69_13 : Nat → List (Nat × Nat) := unpackCursorV5 0xc0b00b4ed0b42d0a52907ade06cdb060d806016258160545504146a18042100310c0120400100000 0xe014fdf943df570de97ddc95dddd6edd36fdcb6794962e2562e0b6fde367b696fad96ba416793963dc15d4c93b3b937db850d8a7cdaa64d7125d9a7cd826cd6125d8b6dd8365d6a70d746fd6467d5a62ad16a4c14ada46fd9467d7a6eb596fac16ba3167919634b14b39947d5125d4264cf925d3254d227ccf125d1254 10 1023 4 15 11 2047 20 1048575
def cc_69_14 : Nat → List (Nat × Nat) := unpackCursorV5 0xb3ac0b02c0a4e90a42639826098233669905c97054950541505412322880200710d0300c00300000 0xf5d6ff5563f4c6ff445ff2c57bb16f979638595f7c15b6b9575e1534f94b3f147ef925ee464ed965ea945ecc7cec17dea145eb462eab6fea367eec6eed36febb67b896fb096ba716796963e99454e93b3d937e8a64e6125e7a7ce5925e646fe5c67e5262e846fe7467e6a6eb796faf96ba6167959634d94b3c947e4925e3052ae96995161e394be2947e1d68e1165dd15d 10 1023 4 15 11 2047 20 1048575
def cc_69_15 : Nat → List (Nat × Nat) := unpackCursorV5 0xc8720c82f3bc2f0b4a4990213841e3781e06cdb06c1923e8e1344c12c4b02c083200802008020008 0xfd125fee70fe26cfc925fd45ffcc57ff45ffdc578795f7e95b6f157619535214b41147fc125f917dfb145f7870fa570f897df7070f934ff8b4761142f7b4ff7347fab4ff9b47f816d8694f7d94b6d147601435113b40137f6860f2125f1925f1125f0925f3e70f326cf0125f256ff1d63f146ff0c5ff0457981627d15a5094a 10 1023 4 15 11 2047 20 1048575
def cc_69_16 : Nat → List (Nat × Nat) := unpackCursorV5 0xc73be4b64b0392f8a48a084368e6806805c65c05823ce3c03823803423403023002c22c02822802802802802801c600e 0x2248df1146382937bd298dda49ee824b70523b6890d7c2de9b16387caaa2a53d0329676947324a18c84bc4d25619927060918c64bc4c2561912705c918c44bc4b2561892705891bb093dbd48e0a92287636439181d749ee724b6f123b6490e1b2da8994f404a59c851cc72863012f1249585c49c132462f92f1209585a49c122470c46282537bec99e198dd0426f7f935bea99de84c6bd16f594b5aa459d352c70b9451789788e4ac2c24e089237f534bce986152970a1471749781e48e12adc0712284eb140c9bdfb4d6f9a6779531af05bd632d6a81674ccb1c225745b25e2292b0a89381848e052cb07955810b2c1a516032cb05955808b2c1251607ad10096581637c0918e036df0134f805a3a6458a0e8df06463829b7c10d3e0668ebb96f4c4b1c005551129e7f94b388a398a50ca627642137 12 4095 5 31 11 2047 21 2097151
def cc_69_17 : Nat → List (Nat × Nat) := unpackCursorV5 0x928ef9d0b195a8ac90d1b61bc3404a0900c618030006 0x112b6f83d37b328dd3b2c51236f83937bd698da7476cc237600b7a7458e2e2aa5793b2409b8e04bc572561f12709091b2c8dda5476caa378b0a295a4ec8e26e3712f1549587849c222463692f1509587649c21246c923708091454db1a3476c8a378a4b69564ec8c26e3592f1489587049c1e24711b6f83537b1c8dd392c45513a14495444dbe0c4def52636851db1a8dd7f2de9c16389ca29504ec8a26e3492f13c9586c49c1a24710965894aa8d04bc3524f1016588ca28cc4be218df1046382d37bb693dc248e9b962 11 2047 4 15 11 2047 21 2097151
def cur_69 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_69_17 (Nat.sub p 544)) (cc_69_16 (Nat.sub p 512)) (Nat.blt p 544)) (cc_69_15 (Nat.sub p 480)) (Nat.blt p 512)) (Bool.rec (cc_69_14 (Nat.sub p 448)) (cc_69_13 (Nat.sub p 416)) (Nat.blt p 448)) (Nat.blt p 480)) (Bool.rec (Bool.rec (cc_69_12 (Nat.sub p 384)) (cc_69_11 (Nat.sub p 352)) (Nat.blt p 384)) (Bool.rec (cc_69_10 (Nat.sub p 320)) (cc_69_9 (Nat.sub p 288)) (Nat.blt p 320)) (Nat.blt p 352)) (Nat.blt p 416)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_69_8 (Nat.sub p 256)) (cc_69_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_69_6 (Nat.sub p 192)) (Nat.blt p 224)) (Bool.rec (cc_69_5 (Nat.sub p 160)) (cc_69_4 (Nat.sub p 128)) (Nat.blt p 160)) (Nat.blt p 192)) (Bool.rec (Bool.rec (cc_69_3 (Nat.sub p 96)) (cc_69_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (cc_69_1 (Nat.sub p 32)) (cc_69_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 128)) (Nat.blt p 288)
def hc_69_0 : Nat → Nat := unpackHintV5 0xce96efce1420cd4035c549feba7ab4b369c4aba5f1a66d4ea0dd649b396994e1968cb20c88c8fa80d1fe7e84937a411175154b6e6daa66d1e75e921059295a4e0ac842eac83802ba2d1aba2535f91e31c113a6a3098a870215dd000085000000 0x60c783060c183060c18f07ec18381830703065cb8f1e3c783060c1a0d41835060c58b45a2d068345a2c0600000000000009ec060000c06000f007800c3600301805c08016000c383060c183261c7871e0c183061c987261d4580004c0e06c2e5ef60c7972f175e7b063c7831e03060003c7800331e3cb9b065c1972f172f172e8b45a0d16a2c5a8b168b4580000000000009ec0e3c3930e0c1930e1c9930e1c9930e4c3930ea2c001831e3c18f07ec183063c78f663c797360cb832e5cdc5cb9b8b9745a2d068b5162d458b45a2c0000000000004f623007806c00601b0d8006c000b81002c0038f0e4c383064c387264c387264c3930e4c3a8b0000981c0b97000663c7b3660d99b660d99b21f500505545d168b5162d69168b660000000000000e3c3930ecc387264c387269c9930e4c393aa0ea2c022f331e3d9d46e0750fbdd555551745a2d616b48b45b300000000000009ec4600f02200200036003020200580071e1c9d44e0f41c98727541d4580004c0e00c1830745548b45a0d06cc0000000027b07803c006003020200580071e1c783060c1d507516000130380f1e3c7d443ea9168b45a2d98000000004f60f007806c036041702200580071e1c787261c9d507516000130380f00f9f3e7c78f1e3e028aa93efb9458b45a2d168b660f8003c000080581c987261c7871e1c98727541d458130078f000660d99b660d99b1e3c78fa000a2aa5a5162d168b45a2d98000000000000387264c387264c38f0e3c3930e4ea83a8b00a1f40eaa8d8f1e3c7d5550fbdd532d2d0b168b45a2d16cc400000000000009ec800220007803c036003020b811002c020f55130e3c38f0e4c393aa0ea2c00026070a366c197065eaaa9168b0004f68c1e231180fc7e01b019102c00e4c3930987019b066ea87d45eaa8bc0ef755522d168345ac2d69980000000000004f623007806c0060440044f0020b811002c003a70e9c383066ea2707aaa0ea2c0002607080060c183a077baa162d168b0004f61c987260c1d03060c1d503bdd50b168b4580027b460f0180c462301780440b003930e4c261c3e7cf9f060c18306055405122d16b28b41a0d98003e0003002016074e1d3873e1cf83060c1d50751600bd1af1ebc7af460c183060c180055500055103bda2d16b4a2c5a0d06cc0000000000001d3874e1c3a7261c3a7260c18307541d4580543ea060c183a075555540ef68b45ad2c2d068366002000000000004f623007810004400030018101002c003a70e9e0f5513060c183aa0ea2c000260700118f1e8d183566d583466d18f1e5d1c5cba38b97465d197458b458b5162d458b45a2d168b00000000000000e1c7870e4c387264c387264c3930e4c3930e4c3a8b002e5cb9745a2d168b45a2c000000004f6003c03600300b81002c003a70e9c3a70e9c3a70e5c3a8b0000981c078f1e3c78f1e3dd97765c78f1e3d3a74e9cba74e5c78f1e3dbb76edcbb76e5d3a74e9c3870fec3870e3c3870e1c387261c3870e1c3870e1c9870e1c3870e3cd8f063c18f1e3cb8f87c3c78f163d1e8f163c1e3c7b71e070e3c98f1e4c98f1e4dd97765c98f1e4d3a74e9cba74e5c98f1e4dbb76edcbb76e5d3a74e9c3870e3c3870fec3870e1c3870e1c3870e1c3930e1c3870e4c3870e4cd93064c193264cb9389c4c993164d2693164c264c9b726070e3c183060c993264c183060c993264c183060cba74e5c993264c183060cbb76e5d3a74e9c3870e1c1830fec183060c387261c3870e1c3870e1c387064c183063c183060c1832e0e0703060c58341a0c183018306dc180c383064c193264c993360c197264c993360c19b2e9d397264c993360c19b2eddb974e9d3a70e1c3870e1c183060c3fb0e1c3870e1c3870e4c3870e1c993263c98f264c3870e4cb9389c4c993164d2693164c264c9b72603060c993264eaaa8993264d3a74e9ea8993264dbb76edea93a74e9c387261c3870e1c9870e1e83fbaa0e1c3870e4c3870e1c39389d43ea37503aaa173351537883c4c993264c99326ecbbb2eaaaaaa4c99326ddbb76e5dbb72eaa1c3870e1c3870e1c3870ea1fdaa870e1c3a4d51ea9b541aa5d5955455ba21d264c993264c993765dd9745a2d168b45a2c993264dbb76edcbb76e5c5a8b0e1c3870e4c3870e1c3930e1c9870e1c387550fec387261c387164c58b163c58b166c583160c58b165c5c2e162c3870e2c162c5b7162a4c993264c99326ecbbb2e4c993269d3a74e5d3a72e4c261f0f85c3e1f0f81c3930e1c3870e1c3870e1c3870e1c3872601fd870e04c9931e4c793264cd93064c193264cb9389c4c993164d2693161c38700993264c993264dd97765c993264d3a74e9cba74e5c000000003870e1c3930e1c3870e1c9870e1c3870e1c0003fb09803c03600300b81002c04000385cb972e5cb972e1c3870e1c3970e1c387 24 16777215 10 1023
def hc_69_1 : Nat → Nat := unpackHintV5 0xd7bebfd001efc53eb1c01949bfa01eb7720cac86bba501e1991afa971c7f90a19f88c5f7838d4e7dd56e7d641c76c9a76f19ec6afd076305fe5c79a354d9e84e1daf4625fe3e1e0238b55a30c1fd25f2b41e6de1138eb80e69490785b90001e1 0x19b060c783f60c183060c1831e3cb8381970703060c183060cbaa3d546aa835550683541a0d5069b5654baaaaaaaaaa807c1e030600cf8030185c3e28b5013d871e1c983060c9830e0c183060c187261c9a1d5526aa130e031e831e3c78f1e3cd83065d555555418355555366cb97572b8b9750451e0f0d80c2e1f11058b01e2c038f0e3c383064c3930e4d54387264c387264c261c063c1fb060c78f060c18f363c78f1e3cd83065c7c3cb8f878f547a3d51eaa0d536aa8f5551e8f5654baaaaaaaaaa803c1e1b0183c780f3e05c3e28b5013d871e1c787060c9870e3c9870e3c787261c9a1d5526aa130e55550306835656547aa3d506a835555550220783c0603145a809eea838f0e3c183060d0eaa935509873d978bfb060c183418f07ec78f1e3c183060d555555478f555060d54b97b5c5cba8228f0780c06170f8a089ec58b0060c038f0e3c183060c3930e4d54387264c387264c261c060c783060c183060c18f07ec18381830703065cb8f1e3c783060c1aaa0d06aa83551ea8f541aa0d5952eaaaaaaaaaa0033e00c180f0780c06170f8a2d404f60c383060c183261c7871e0c183061c98726875549aa84c380c783578f1e5cd83065d5555555541835551e3cb975f2f8b9750453e0f0d80c2e1f11058b0362c038f0e4c383064c3930e4d54387264c387264c261c060c78f063c1fb060c18f1e3d78f1e5cd832e0cb9737172e6e2e5d51e8f551aa8341aa6d36aa9b555369b5654baaaaaa6d16aaaaa01f0786c061b361b0366cf9f02e1f145a809ec38f0e4c383064c387264c387264c3930e4d0eaa935509872065ef66c1fb2f17559b2fd060cdc5fdb31e3d7b55545d555555554b975e6d983660d79b5a5550453e0f0f87c8844162c28038f0e4c3930e4ea954387264c387264c261c8bc3c7afa8dc0ea1f7baaaaaa2ea8f551aab2aacca8354dab32b25d555555555403e0f2823e07c3e4428b5013d871e1c9d44e0f41c9872754875549aa84c380c183074d54a8f547aa0d506acacaaaaaa00f0780c064428b5013d871e1c783060c1d521d5526aa130e0f1e3c7d4c3ea951ea8f54daa6d5959554daaaa00f0786c366cd910a2d404f61c7871e1c9872754875549aa84c38bc19bf63c78f1f530faa55555551e3d5579b077c1af36b4aaa08a3c1e1f0f910a089ec58b0a00e3c38f0e4c393aa550e1c9930e1c9930987287d03aaa363c78f1f55543ef754aaccaacaa3d51ea8354dab2b2aaaaaaaaa811f0a01e0f0f87c88516a027b83d544c38f0e3c3930e4ea90eaa9355098728d9b065c197aaaa47a8d57ebf551a8d069b6664baa81f0f88b44f61c987261d4983360cdd50fa8bd551781deeaaa547aa8d506a9b55667aab32b32b25d555555555403e1f0d80ca08f84428b5013d874e1d387060cdd44e0f554875549aa87c380c183075553035555555e8d78f5e3d7a35060d5569554114f87c060322144458b0a00e9c3a7060c183aa550e1d3930e1d3930f872a1f52f060c183a075555540ef6a8f551aab32ab2a83541ab2b2aaaaaaaaa807c3e47c280180c88516a027b0e9c3a783d544c183060ea90eaa93550f87079b1e6c1832e3c78f1eaaaaaaa83060c19b1e3d597468cba29b0183c783cf85c3e220b0781c183261c7871e1c98726aa1c98726130e0f1e3cd832e0cb97365cd975554dabed55366c183060d1fb54183554ba3465d14d80c366c366cd9ff6170f8882c3e07060c987261c987261c9aa87261c984c388c78f468c78f2e8cba32eaaaaaaaaab368c1ab068cd972e8e47172ea08a7cf83cf87c3e170f8882c581f1601c787261c987261c98726aa1c393261c39326130e172e5cbaa3d5541aa6d5952eaaaaaa01f0f87c3e170f8a2d404f61d3874e1d3874e1d3872e875549aa87c386cd80000c783060c001830663c7977f172efe2e5c183060c19745a2d458b5060d068345a2c00000000000038f0e4c387264c387264c183060c3930e4c3a8b00066c1831e0fd83060c183060d98f1e5c1c0cb838183060c183065d168b5062d418341a0d168b00000000000013d88c01e003018000c0001800c02e0400b000e3c393060c193061c183060c1830e4c3930ea2c0002607006031e000c181b360003c78f1e6c1832eae2e5d5c5cba2d168345a8b16a2c5a2d160000000000001c7871e1c183261c393261c393261c987261d4580031e0fd83063c783060c79b1e3c78f1e6c1832e3e1e5c7c3c7a2d168345a8b16a2c5a2d1600000000000027b07803c0361b00180c01e0f0007800170200580071e1c787060c9870e3c9870e3c787261c9875160001303855550306036645a2d06830000000013d901003c01e003001802c02a838f0e3c183060c3a8b0000981c07800c0060c067cb9f2e3c78f1e0c183069f7d835162d168b41a0d168b0f8003c00060002c0e4c3930e3c38f060c1830e4c3930ea2c09803c780003060000c180d9c5cbb38b971e3c78f060c1835060d458b45a2d068345a2c000000000000387264c387264c38f0e3c183060c3930e4c3a8b00 24 16777215 10 1023
def hc_69_2 : Nat → Nat := unpackHintV5 0xd31278cd297ac609c8bc3675b33e3eab7df0a4e9a59ad6859441a58a66778585387ee1a9746a9e6e797c67d5a95d969057dd6e5071db4b7d3d46414f40797238ede334f8fd2da9d427e17220b5cb19c5bc14d13d10252b0c9ce207bd380001ef 0x66c19baa1f517aaa2f03bdd5548b45a0d16b0b5a66168c58b163c58b166c183060c58baaa162e85cfaaaaaa00f87c36032823e11027b50543a70e9c383066ea2707aaa0ea2c387164c387162c3e1c060e8183060ea81deea858b458b16bd45a3163c583060c1a3168c58b16bc5cb162c5d501f0f89ed143930e4c3930e2d7a35e3d78f5e8c183060c183060c183060eaaaaaaa9168b585041a0d98f87c50900603222103a70e9c3874e4c3874e4c183060ea83a8b0f872a1f503060c1d03aaaaaa077b45a2d696168341b30b462c58b1e2c5d0baaaaa162c183060c183060eaaa803e1f28f9f0a2006032204f6a0a874e1d3c1eaa260c18307541d45870e2c9870e2c587c382c58b463c7a3460d59b560d19b463c79747172e8e2e5d197465d162d162d458a08b45a2d167cf83cf8a07d03e1f0b87c162071e1c9870e4c9870e4c987261c987261c987516130e172e5cba2d168b45a2d162c58b163c58b166c583160c58b165c5c2e162c03e1f0f87c2e1f04f6a0a874e1d3874e1d3874e1cb875161c38b261c38b161f0e1b3600003060c001830663c7977f172efe2e5c183060d555555555400000000000038f0e4c387264c387264c183060c3930e4d540019b060c783f60c183060c183663c79707032e0e060c183060c1975555555555000000000013d8008c01e003018000c0001800c02e0402001c787260c183260c383060c183061c98726aa00004c98070e00c063c001830366c00078f1e3cd83065d5c5cbab8b9755555555550000000000000e3c38f0e0c1930e1c9930e1c9930e4c3935500063c1fb060c78f060c18f363c78f1e3cd83065c7c3cb8f878f5555555555000000000013d8003c01e01b001803c1e000f0002e0402001c7871e1c183261c38f261c38f1e1c98726aa00004c98070e155540c180d5555540000004f60040400f007800c0060201541c7871e0c18306aa00004c98070e03c780003060000c180d9c5cbb38b971e3c78f060c183555555555500000000001000e1c9930e1c9930e3c38f060c1830e4c3935500060c783060c183060c18f07ec18381830703065cb8f1e3c783060c1aaaaa0d16aaaaaa000000000027b000180003018003c01e003001805c080400187060c183064c38f0e3c183060c3930e4d54000099300e1c018f060300780bc78f2e6c1832e7cb9f2eaaaaaaaaa23000d8007c0081038f0e4c383064c3930e4c3930e4d54000387018f0603060003c78002f1e3cb9b060cbaf8b975f172eaaaaaaaaaa00000000000001c787261c183261c393261c393261c98726aa000c18f1e0c783f60c1831e3c7af1e3cb9b065c1972e6e2e5cdc5cbaaaaaaaaaa800000006c00013d8008c01e01b001806c36001b0002e0402001c787261c183261c393261c393261c98726aa00004c98070e05cb800331e3d7b306bcdb306bcd950050552aaaaaaaaa800000000000071e1c9870e4c9870e4c987261c9d52a8045e663c7afa8dc0ea1f7baaaaaa2eaaaaaaaaaa000000000027b0011803c088008000d800c0808040038f0e4ea2707a0e4c393aa550000264c03870060c183a2aa55555500000013d8003c01e00300181010080071e1c783060c1d52a8000132601c380f1e3c7d443ea95555540000d80027b0007803c03601b020201000e3c38f0e4c393aa550000264c038701e3c0019835e6d9835e6c78f1e3e80028aa955555555540000000000400387264c387264c38f0e3c3930e4ea9540287d03aaa363c78f1f55543ef754aaaac8b555555000000000013d80100044000f007806c0060404020107aa89871e1c787261c9d52a8000132601c3851b360cb832f5554aa009ec1183c462301f8fc03603221003930e4c09930387019b066ea87d45eaa8bc0ef75552aaaaaaaaa800000000009ec004600f00d800c0880089e0040402001d3874e1c1833751383d552a80001300e1c17a35e3d78f5e8c183060c183000aaa000a2555555555500000000001000e9c3a70e1d3930e1d393060c183aa5500a87d4bc183060e81d5555503bdaaaaaaaaaa800000000009ec004600f02000880006003020201000e9c3a783d544c183060ea954000098070e00231e3d1a306acdab068cda31e3cba38b9747172e8cba32eaaaaaaaaaaa00000000000001c787261c393261c393261c987261c98726aa000c9832713a87d45eaa89c0ef75552aaaaaaaaa80000000000013264c993060c9d44e27513aa5500a87d44c183060e81d5555503bdaaaaaaaaaa80000000000013264c9c4eaa260c1830754aa004c993264c993265cbaaaaaa8000000013264c993264c993264c9aa80172e5cbaaaaaa80000009ec00007806c0060170201000e9c3a70e9c3a70e9c3975500002601c3820c183060df8f1e5c183060d555555554d9b5060d54b977f3f8b9750453e0f0180c2e1f11058b0060c038f0e4c183060c3930e4d54387264c387264c261c 24 16777215 10 1023
def hc_69_3 : Nat → Nat := unpackHintV5 0xeebaaaea012ee3a996dc25e1d52dbecb1686c481a5bc99faba8884b50960ae11bea402849f093e95f64587ab937e964570678c6961c1603e49515fb848564239afaa37a8813744193570752e51c824aa6a1da5c11645d80f15cc051680000145 0x463c7a3a87d48ea0751baaaa01458b47bed168b65a5a162d995166c583160c58ba17555542c5d0b2f55542c58b3e0f0f87ca2f4047b1620b160b0162cf9f00e3c3930e4c39383d544ea83a8b0e1c5930e1c58b098711a3d16d34d1b366c183560cdaaa346ab8eac1037daaaa9f3e87c2e171261d0eac993561c393066c19baaaa668d98f663d9a3aaa162d41155555555554f87c3603210b97050440e9c3a70e0c19baa0e1d3930e1d393550f87019b066d46a8f545b50faaa0751b55596956aaa9599405541bed5555555553e1f0d80c504f8517a023da2074e1d387060cdaa4d0eb07aa89d52a87c380c183075554bd1af1ebc7af474b3541148b45b20d9969458b3e1f0180c882e5c01830162074e1d383060c1d5070e9c9870e9c9875161f0e03060c1d43ea57503a81d555008b45a0df6a0c1ad2c2d981a3060c18f060d5a07555540c1d032f55540c5833e1f0180ca2f4047b162030600cf8074e1d383060c1c1eaa27541d4583060c9830e0c187c380c183075554cd1b31ecc7b34740c1d52822aaaaaaaaaa9f0f80c0650247b2e5c141103a70e9c183060ea83874e4c3874e4d543e1c547aa8c183060d41d43ea56b4aaaab540ea0754caad5402aaaaa837daaaaaa9f0f89f050060328bd011ed103a70e9d438755526dc183060e0f5513aa550f872a1748306d520c1bed06833e1f03930e4ea8d83066e09060df68b45a3163c5ad523168c58b16ac58b162c1833e7cb85c161f03a7264d5870e4c3930e2c19b066eaaa99a3663d98f668e6a968229168b41b332d283067c3e1b019105cb80b1602c40e9c3a70e0c19baa0e1d3930e1d3930ea2c3e1c066c19ba87d5503a8dd555008b45a8306837dad2c2d985a3162c58f162d5a17555542c5d55503060cf87c360328bd011ec5882c582c058b3e7c03a70e9c383066e0f5513aa0ea2c387164c387162c3e1ca87d5503a8dd555013530baa3e1f0f87ca2f4047b3e1f03b70edc3b70ede0f5513aa0edc3b70f870d9b162c58b162c183060c183060c183060df8f1e5dfc5cbbf8b97060c18345a2d414188341a2d167c1e034140180c2e1f01881c787261c393261c393260c183061c987261d4584c380cd83063c1fb060c183060c18f1e5c1c0cb838183060c183065d168b5062d418341a0d168b168c58b163c58b060c183060c58b060c583060c183060c183060c18b2e2e170b1601f0780c18033e00c06170f827b505438f0e4c183064c187060c183060c3930e4c3a8b0e1c5930e1c58b0987018b063c58b160c183162cd9b060c183162c78f1e3cd83065d5c5cbab8b9745a2d068b5051622d163c1e1b0183d0502e1f05881c7871e1c183261c393261c393261c987261d4584c380c783f60c18f1e0c1831e6c78f1e3c79b060cb8f87971f0f1e8b45a0d16a2c5a8b168b458b1e2c58b1e2c58b360c183062c58b1e2c78b162c58b1e2c58b162c597170b858b00783c3603078f01e7c0b87c13da82a1c7871e1c183261c38f261c38f1e1c987261d45870e2c9870e2c584c3955540c18306cc8b45a0d0755542c78b162c78b160c183060c183060440f0780c0609ed415aa0e3c38f060c1830ea2c387164c387162c261c1e3c58b162c58b060c183060c183060c1838f172f1e2e5c78f1e3c183060d418a08b45a0d068b45a80340783c06030b87c0608070e4c9870e4c9871e1c783060c187261c987516130e03063c183060c183060c783f60c1c0c18381832e5c78f1e3c183060d41835062d168b41a0d168b060c583060c183060c183062c58b1e2c58b1e2c583060c183060c18b2e2e170b16003067cf803060301e0f0180c2e1f04f6a0a830e0c183060c9871e1c783060c187261c9875161c38b261c38b16130e031e0c583062c58b162c18f1e0c183062c58f1e5cd83065e5c5cbcb8b9745a2d068b5051622d167c1e1b0186d0502e1f058a81c787261c183261c393261c393261c987261d4584c380c18f1e0c783f60c1831e3c78f1e5cd832e0cb9737172e6e2e5d168b41a2d458b162d36a2c5a2d162d18b162c78b162cd83060c18b162cd8b362c58b162cd8b162c58b165c5c2e162c03e0f0d80c366c0d9f02e1f04f6a0a871e1c987060c9870e4c9870e4c987261c9875161c38b261c38b16130e40cbdecd83f65e2e8c7c2d9c0c5bf07ee66cef63cd838b83bd972f0b616ce362c5fb2e5c58b162c58b663c7b3660d99b660d99baaaaaaaa45a2d4161168b663e0f24140f87c88840e3c3930e1c9930e1c9930e4c393aa0ea2c261c8bc3c7d46e0750fbdd555551745a2d616b48b45b30b462c58b1e2c5d550b1742ea859b160c583162eaaa803e0f2823e07c3e4409ed4150e3c393a89c1e83930e4ea83a8b0e1c5930e1c58b09870183060eaaa9168b41a0d9858f162c58f162c183060c183060eaaa801e0f0180c8813da82a1c7871e0c18307541d45870e2c9870e2c584c383c78f1f550faa45a2d162d362d9858f162c58f162c59b162c59b162eaaa801e0f0d86c8813da82a1c7871e1c98727541d45870e2c9870e2c584c383c78b162c58b172c1cb372c1cb363c78f1f55555554b0a08b45a2d16cca1203c1e1f0f9110201c393261c393261c7871e1c98727541d4584c3943e81d551b1e3c78faaaa1f7baa5a585a2d168b45b350baaaaa162c58f162c58f162c59b160c583162eaaa80a3e7c2880783c3e1f2204f6a0ac1eaa261c7871e1c98727541d45870e2c9870e2c584c3946cd832e0cbd55522d168c58f168c5a3162c5bf16fc58b166c183175407c3e27b450e4c3930e4c38b 24 16777215 10 1023
def hc_69_4 : Nat → Nat := unpackHintV5 0xe3c56edc99cbd65d8fcd7e38c7b572bff1f1baa553b4798bab8a3ca814dda3612d9ca9ae98651190e1e185f2bc7e35ef739ea66b920360b2b8592de14d9ae548c53544a5083d21e13535fb2edd962709f51f69e8159a740ee1ae06f9fa0001be 0x3360cdc7471c7c71f1d18b160015554ab4aaa2a00a0aa0000000000001d3874e1c183361c3a7261c3a72754aa000cd8336a3547aa2daaaa56655541bed555550000000023d8000000f00d86c0060301100100081010003a70e9c383066d526875aa550000981c0183060eaaa9168b5141b32f46bc7af1ebd1802855550b1600000000000000001d3874e0c18307541d45870e9c9870e9c98003060c1d55522d16837da8306cc0d183060c78306ad55503160c00008f6000000002b007800c0060402c040060300018000074e1d383060c1d5075160c183260c38306000130384b472c7cb1f2d183060c18306001554aab54aaa000a2aa00000000400001d3874e1c3a7261c3a7260c1830754aa00a8f55183060c1a83aa5a5558bd52aaaaa837daa8000000011ec00005600f010004400061b00180c081010003a70e9d438755526dc183060ea95400026070066c19baaaa45a2d068cc7cf9f3e815540c0001e06c008058007c0e9c3a70e0c19baa0ea2c39f0e7c09800cd833755548b45a83519b1a3c63f18fc68d4002aaa81830000000000000000e9c3a70e0c19baa0ea2c3874e4c3874e4c0019b066eaaa9168b5060d06fb66168c58b163c58b56aaa818306000047b00000000580003c036003020160200b058002c00003a70e9c383066ea83a8b0e1c5930e1c58b0000981c0019b066d1a3d46a3555acd516d5534aa837daa8000007261c9a4c3a00cd83375548b45a0c1bed18b1e2d18b462c58b562d98b162d6a8183000000e4c3930e4c38b0118f1e8d183566d583466eaaaaaaaa918f1e8d1acc5b3518b56aea8000000000000038f0e4c387264c387264c3930e4ea83930e4c02aaaaa800008f60000003c036003020160200076e1db876e1dbd5076e1db80004c0e103060eaaaaaa8d9ba060eaa822918f1e8c183060ea91a8c5a3518b3e0f0180c882e5c018303e1f038f0e4c183060ea8387264c387264c3930e4c261c066c1831e0fd83060c183060ea1f523aa81d550381d40e075038dd55555555008c78f460d062c1a0c183060c1cd4c2ea8f83c060c019f0060328bd011ecf87c0e3c393060c193061c183060c18383d544ea83930e4c261c063e063c7d55550307555546cdd0450f1e3c79b060cdd52b558b56ab163c1e1b019105cb80f1e07c3e071e1c787060c9d5070e4c9870e4c987261c984c380c783f60c18f1e0c1831e6c7d43ea1f503a8dd543eaa87c3eaaaaaaa801e3c78f360c19b1e8f163d1e2e6a617543c1e1b0183c780f3e145e808f67c3e071e1c787060c9870e3c9870e3c7c1eaa27541c98726130e03060e063eaaaa878faaa060eaa808a060c78f1e3c183060ea99acc5b3598b1e0f0180c8202e5c018303e1f038f0e3c183060ea8387264c387264c3930e4c261c060c783060c183060c18f07eeaa0703aa81d50fa87d40ea075555038bd555000d060c1a0c58f1e3c783060c1cd4c2ea819f0060c0783c060328bd011ecf87c061c183060c1930e3c38f060c18383d544ea83930e4c261c063c1d55555540c1d550f1f41148c78f466c18337548d462d1a8c59f0786c0644172e05cb81f0f81c787261c18327541c393261c393261c98726130e03063c7831e0fd83060c78f1f50fa91d40e0751b8dd546eaa8dc6eaaaaaa2f17aaa0118f1e8cd83066cda6c59b4d8b9a985d51f0786c061b361b0366cf9f0a2f4047b3e1f038f0e4c383064c387264c387264e0f5513aa0e4c39309872a95a3568e2918b16ad1a8d162c5d31b060c5d52a2c59f3e5c2e0b0f81d1934e8c3bb261c9871748b641a6d9a95a3568e29162d46ad55546a33e7cf885c2e075261d193de8c3bb264c78f2755555523568d1a3568d1d055131e3c9ab4ead3d523468d3a3de8d1933e0f261f0f9105cb8132607c3e5078993264ea83870e1c993264c264c463c7a3aaaaaa959b460d583466e822918f1e8d5abaa468b518b3e7c1e7c3e1f220b9702e5c0f87c0e3c3930e4c393aa0e1c993261dd870e4c987261c984c388c78f4755555542c5a3368c1a3068cda822aaaaaaaaaa9f0787c3e42172e0a0881c787261c98727541c393261c39326aa130e22d463c7a354da0d6a1f52355596956a0751baa5665aa011efb5555555555916aa7c1e2827c0f87ca2f4047b440e3c393549a1d43930e4e0f5513aa550987078f1e3eaaaa966999b660d983666e82291f22c5a2d16ccb4a2c58f0787c3e44172e02c580b1038f0e3c3930e4ea8387264c9930ecc387264c3a8b0987078f1e3ea1f50fa81d46eaaa8047bed458b45a2d69616cca8b362c18b062c5d0baaaaa162eaaa858b163c1e1f0f945e808f62c4162c059f00e3c38f0e4c39383d544ea83a8b0e1c5930e1c58b0987078f1e3eaaaa858baa5e6d983660d79b50455547aaaaaaaa8f0787c3e50247b2e5c1411038f0e3c3930e4ea8387264c387264d54261c51683554d8f1e3c7ad2aaaad50fa87d40ea36caad555402aaa8f7daaaaaaaaa7c140783c3e1f28bd011ed11438755526dc38f0e3c3930e4e0f5513aa550987118f1e8eaaaa6a9519b460d183466e822916c8b45b32d28b167c1e1f0f9105cb80b1602c40e3c3930e4c393aa0e1c9930e1c9930ea2c261c 24 16777215 10 1023
def hc_69_5 : Nat → Nat := unpackHintV5 0xd77817cf7dffc4faa1be919ab6bdf5b4c47eb134e4ac1149a6596e9f29cc99e15294ad4d8bde3485d5827f41a575567b6e89b364f6655dd9c753fe774e39714795a93d7e8637c56e30c5c02aa98721ca381c01721485df0f3953090d8b000243 0x5e2fec18f066d58f1e5cd83065d162d1e20d168b45a8001b360c183062c5972f45cb8b160000000033d8000000001c787261c183261c987261d45870e4c9870e4c980031e0cdab1e3cb9b060cba8b168f7da0d168b45aa2cd83060c18b162cb8b85c2c58b162c0000067b0000000011803c03605c080160200b058002c000038f0e4c383064c3930e4c3a8b0e1c5930e1c58b0000981c019b066eaaa9168b41a2d197a35e3d78f5e8cd9baaa0050162c00000000000000003a70e9c383066ea83a8b0e1d3930e1d39300066c19baaaa45a2d068b67dad4bea1f51ba81d2b0b80000067b0000000011803c036101002c1602204400400001d3874e1c18337541d45d44e0f4000130381b374806c1833754aa00cf6001c987266cdd29b060cdd52aa8033d80230786c8846230158022007261c984c380cd83367cf9f3e83060c19baaaa8055554051118006c0f80100081d3874e1c183361cf873f54aa001c066c19b5e8d78f5e3d7a3555366eaaaa800155554001440000000000003a70e9c383066c3874e4c3874e4ea9540019b066d51eaaa0d5375554b2aaaaaaacfb0000019ec40000000011803c03608002200404020b0110003a70e9c383066d0eaa93aa550000981c28000066c19ba375117bdd5555517468d1a3aa360c19baa000000000000e4c393aa0e0c193aa0e4c39300a475551b360c78337555117bdd55523468d19b060cdd5000000000005507261c987060c9d507261c980000c79b066cd83066cd83066cda31e3cba38b9747172e6c1832e8c78f468d662d9a8c59b060cd97468cb8000000000000071e1c9870e4c9870e4c987060c987261c987261c98003360cd972e6c1832e6c183365cb800000cf60000003c03605c080160200076e1db87060cd876e1cb876e1db80004c0e06cd80000c18300060c2aaaaaaa918f1e8d1a8c5a3518b060c183aa0000000000000e3c3930e1c9930e1c993060c183aa0e4c39300066c1831e0fd83060c183060eaaaaaaaa918f1e8c1a0c5834183060c183aa0000000023d800008c01e003018000c000186c00603020160200071e1c983060c9830e0c183060c1d507261c980004c0e00c780c78f00060c0d9b000aaaaaaaa1e3c78f360c19b56ab16ad562ea800000000000038f0e3c383064c387264c387264ea83930e4c0018f07ec1831e3c183063cd8faaaaaaaa1e3c78f360c19b1e8f163d1e2ea8000000008f600000f007806c00600f078003c0020160200071e1c787060c9870e3c9870e3c7d507261c980004c0e03c780003060000c183018faaaa0703aaaa66b316cd662c78f1e3c183060ea80000000000000387264c387264c38f0e3c183060ea83930e4c001831e0c183060c183063c1fbaaaa81c5eaaa81a0c183418b1e3c78f060c183aa0000000023d800000c000180c001e00f001800c0805808000c383060c183261c7871e0c18307541c9872600013038031e0c0600f02aaaaaa918f1e8cd83066cf9f3e7ea846001b000f84002071e1c987060c987261c9d507261c98007018f0603060003c780055555555231e3d19b060cda3518b46a3175400000000000001c787261c183261c393261c39327541c98726000c18f1e0c783f60c1831e3c7d55555555231e3d19b060cd9b4d8b369b175400000001b008f6000023007806c3600301806c36001b000805808001c787261c183261c393261c39327541c98726000130380b160008c78f468c1a3368c1a33754ab4b542a00a0aaaa0000000000001c787261c393261c393261c9872754aa008b518f1e8d536835aa5665aa47bed55555550000000023d800008c01e0220020006c006040808001c78726a9343a87261c9d52a80004c0e03c78f1f555488b45a2d98014199b660d983666eaaa858b0000000000000000e3c38f0e4c393aa0ea2c387264c387264c0078f1e3eaaa91efb5162d168b665459b160c583162eaaa858b16000047b0000000007803c036003020160200b058002c000038f0e3c3930e4ea83a8b0e1c5930e1c58b0000981c058b000660d79b660d79b1e3c78fa555aaaa500051555500000000200000e1c9930e1c9930e3c38f0e4c393aa550051683554d8f1e3c7ad2aac5eaaa955547bed5554000000008f60000200088003c01e01b001810202002870eaaa4db871e1c787261c9d52a80004c0e08c78f4755548b445a2d9900f9f3e7eaa858023000006100b000f81c787261c98727541d4587261c98007118f1e8eaaa91688b45b3280023368c1a3068cdd5550b1600000000000000001c787261c98727541d45870e4c9870e4c980231e3d1d55528b168f7da2d16cca8b362c18b062c5d5550b162c00008f600000000b004600f00d800c080580802c16000b00000e3c3930e4c393aa0ea2c387164c387162c00026070 24 16777215 10 1023
def hc_69_6 : Nat → Nat := unpackHintV5 0xb7f7a1b77c1eb6bc30ae960aa3cab39ab64591a24581f7eb7afdbe709e9870640e706400702c0e6f2c406f2c006f2c006e2c4068397d5f5a3856aa2c4fb9bc47521a406db937ae3030e1b328ca06211deb1666ae0ff99b0951aa005e3d000017 0x183063c18f060c18f060c1830600f1e3c783818307032e0c183068f7da8b16a0c1a83168341a2d16a83062c183060c183060c183162c183060c183060c597170b858b162c58f0780c19b060c0067b2e1f05882c580b3e01c7871e0c383060c183260c183061c987261d45870e2c9870e2c584c385cbdefd834bc5fdfb3e03060c183062c583060c1a8228f1e3c783060c1c5cbc5cbaaa8f7daaaaaaaa8f0780c182033d9b360a05c3e22071e1c783060c1870e4c9870e4c987261c9aa84c38a2d418355555060c1831e0c1831e83554183060c180caa971e3c78f0703060e065c183060d55547bed555555553e0a03c1e03066c1830019ecb87c4450e1d5549b70e3c38f061c183060c193060c1830e4c3935509870180c183060c1a32e8cba0d06a2c5a8df60d168b062c183060c1fb06a0c18306a0c58b162c58b160c061b0f85c3e0b1058b058b167fd80c183061c987261c987261d4587161c584c380c183060d060c1835060c0180c1ab1e3cb83060c1ab8b9757172e8b41a0d06a0c1a8b168b459f0780c061b3602c58170f82c40e3c393060c1830e1c9930e1c9930e4c3930ea2c261c060c18f063c183068c183060c180ac78f2e0e060c1c0cb83060c1a8b168f7da0d41835060c58b41a0d168b54183160c183060c183060c18b160c18b360c183060c183062cb8b85c2c58b162cf83c060cd83060033d970f82c4162c1602c59f3e01c787260c383060c183260c183061c987261d45870e2c9870e2c584c380c18306bd1af1ebc7af4741155554b5348b45a0d06a0c1a8b16cc7c3e0320d9b0a088162074e1d383060c1870e9c9870e9c9d5075161f0e03060c783060d183060c181555555038bd522d16a0c1a83168341b3ed6a5750fa81d550381d540e3750381d2b0b8f87c060cd83060033dc40b12823e01d3874e0c383060c183260c18307541d45d44e0f41f0e231e3d1836068c7a0cf81d3a33617878b4369c383060c1d555231e3d1a822d5552aaaaaaaaaa9f0f80c1880e20d9b050440e9c3a7060c183aa0e1d3930e1d393550f870183063c183068c183060c0547aaad5506835541aa83541d55555552caaaaaaaaaaab3ecf87c060cd83060033da7c14221103a70e9c187060c183064c183060d0eaa93aa550f870183063c183060c183060172e0e060c1c0cb83060c18341830683160c183065cb9f0f80c19b060c0067b2e1f0f87c0edc3b7061c183060c193060c1830edc3970edc3b70f870b97000063c19ba366ea887d401415517563c7ab5eb316bd662cd83066ea800000000000038f0e4c387264c387264c383064ea83930e4c022f031e0cdd46e0750fbdd5555517563c7ab985cd1b060cdd50000000000cf6000023001e0f02200200036101002c04000e3c393a89c1e8383064ea83930e4c000260701e3c002aaa8d9b360c7831f40014554bd662d7acc58f1e3c79b060cdd50000000000000070e4c9870e4c9871e1c787060c9d507261c98050fa060eaa8d9b063c18faaaa1f7baa9a9858f1e3c79b060cdd50000000000cf60000400110003c00783c036105c088016020041eaa261c7871e1c18327541c98726000130380b160000c78336a6cdaaab1e3cbaf8b975f172e6c1832e23d5005055550000000000000e3c3930e1c9930e1c9930e0c1930e4c393550045a0c78336a9b41aab1e3cbaa5d94d83065d1efb5555555400000000067b000011803c044004000d81702010100038f0e4d5268750e0c1930e4c393550000981c018f063c78f1e3cd83065d1168345a2d1600a06cd83060c18b165cbb399c5cb8b160000000000000001c7871e1c183261c987261d45870e4c9870e4c980031e0c78f1e3c79b060cba3df6a2c5a0d168b45aa2cd83060c18b162cb8b85c2c58b162c0000067b0000000007803c03605c080160b01100582c001600001c7871e1c183261c987261d45870e2c9870e2c580004c0e02c0067c1fb4183366c18f063cf973e5c78f1e3cd83065d014555543e000f03605c000103930e4c38f0e3c383064c3930e4d540058b000555366c18f063d7c5cbaf8b971e3c78f360c19750005155550000000000000e1c9930e1c9930e3c38f0e0c1930e4c3935500516a0c1aaa9b360c7831ecaa971e3c78f360c19755551efb55551000000000067b0000100044001e00f00d817020105808800a1c3aaa936e1c7871e1c183261c98726aa00013038178bfb 24 16777215 10 1023
def hc_69_7 : Nat → Nat := unpackHintV5 0xbdb5ebb332a1ac65b3a3be2a9ce1b79525ef8a76ac83fd9e7c5de87681776f4dcd667e346075825a5d86553d484b667643b9eb38cabc389c0b389c00384c1437444237440037440036d01d2f49e2247eb31cc1ef11f6b310f041094de9000253 0x60c1831e3c78f060c183445a0d068b45802803060c183060c1972ece67172e2c5800000000000000071e1c783060c187261c9875161c393261c39326000c183063c78f1e0c183068f7da8b168341a2d16a83060c183060c18b2e2e170b162c58b00019ec00000000001e00f0018170200580802c16000b00000e3c38f060c1830e4c3930ea2c387164c387162c00026070162c000183555060c18367172ece2e5c78f1e3c183060d4001455554000000060000001c393261c393261c7871e0c183061c98726aa00a2d4183555066c183060d9552e3c78f1e0c18306aaaa3df6aaaa000000033d800000080022000f007800c0b810080800a1c3aaa936e1c7871e0c183061c98726aa0001303803060c1ab1e3cb83060c1a2d1068345a2d00183060c1832e7cf9716008c000600402c003e071e1c983060c187261c9875161c98726001c060c183563c797060c18345a20d068b45a80003060c183060c1972eae57172e2c58000000000000000071e1c983060c187261c9875161c393261c39326000c18306ac78f2e0c18306a2c5a3df68341a2d16a83060c183060c18b2e2e170b162c58b00019ec00000000016008c01e00302e0400b0100582c001600001c787260c183061c987261d45870e2c9870e2c580004c0e00c1830755548b45a0d06a2cbd1af1ebc7af47540c1d00280b1600000000000000001d3874e0c18307541d45870e9c9870e9c98003060c1d55522d168341b3ed6a5750fa81d40e9585c00033d800000000008c01e00308080160204400400001d3874e0c18307541d45d44e0f40001303803060c1cb46cc7b31f2d1a8306ab55554000aaaaa000a2000300000000000e9c3a7060c1830e1d3930e1d393aa5500060c183547aaad506a83aaaa59555555567d8000cf6000000000023007800c1000440082e044020200074e1d383060c1a1d552754aa00013038000c183060c183060c183060c1a31e3cba38b9747172e0c183068c78f468d662d9a8c583060c197468cb8000000000000071e1c9870e4c9870e4c983060c187261c987261c98003060c1972e0c183060c183065cb8000cf6000000003c00605c080160200076e1db83060c1876e1cb876e1db80004c0e00c183060c060d197465d183162c5a351a2c58b168c183060d060c183060c1aa5e858b167cf9b0f82c3e07261c987261c583068b45a0d06834183060c060d162e52e8cba32ea8d46aaa8d468d3e7cf886c3e21c3aa4c987261c983060c183060c183060c0180c1a31e3cb83060c1a38b9747172e8c78f460c183068d16a3165d1a32e7cf83cf80c061b3607cd8170f87c3e071e1c983060c1870e4c9870e4c987261c987261c984c380c183060c183060c1972f411555555554ac78f560c18306ad562d5aac5d51f0780c8366c28220f87c0e3c393060c1830e1c9930e1c993aa0e4c393098722f03060c783060d1d5503a060ea8183060ea0703a021f7baaaaaaaa0717aa81ab1e3d5cc2e681a0c183418b060c183aa3e0f2823e00c19b060c0067b883e1f038f0e4ea2707a061c183060c193060c183aa0e4c3930987216c2e068f060e85c0d3e07270b4bc1b060c183060c78f060c183a022aaaa1f5555543c78f1e0c183068b45d50f0780c20366c28220f87c0e3c38f060c1830e1c9930e1c993aa0e4c3930987287d0307555540c183063c183063e8183aaa066c183060c0aaaa1f7baaaaaa9a9858f1e3c78341830683160c18307551f0a01e0f0183360c1800cf7107c3e41eaa261c7871e0c383060c183260c18307541c98726130e03060c183060c183062c5a822ab1e3cb83060c1ab8b9757172eaaaaaaaaaaa7c1e0310d9b0502e1f11038f0e4c183060c387264c387264c3930e4d54261c45a0c1831e0c18346aaa0d418355060c183541a0d40563c79754bb283818307032e0c183068f7daaaaaaaa8345aaaa9f078a09f0060cd83060033d970f8881c78726a9343a830e0c183060c983060c187261c9aa84c380c1834183062cf8f0603060c183068cba32e8341a835168b4583060c183062c58b162c58b162c180c360f0b87c1620b160b3e03060c187261c987261c9875161c58716130e03060c18306a0d060c18300603063c78f1e0c183070e2e5e1c5cba3c1a2c5a0d06a0c1a8b168b458f0780c061b3602c58170f82c40e3c38f060c1830e1c9930e1c9930e4c3930ea2c261c 24 16777215 10 1023
def hc_69_8 : Nat → Nat := unpackHintV5 0x80a8f93f5b3e5e99c50eed57e7492b639174c9bd6ad4d4a684666afa308baa974b3eaaf8eb353f0f5a757a8528948a861b8c3f2ef79cd7b00d424a65b73a82a3cdf1298a188a0aae3ee9871af91f0b508b04d33541e2a1c0b90e103b0860103354000206 0x118f1e8d51eaa3541aa6eaaa96555555559f6000f3d8008000000002303600301000440082e044020b01100038f0e4c3930e4d0eaa93aa550000269c038700066c19b1e8f4fa7d53eb3545b178ba5e5541bed543d8f078001c98726930e803c78f1e7c19f367c19f363c78f1e7e2e5cfc5cba32e8cb8f1e3c79f4f8b3e9f16ad5c32e8d19703d83c01e000000071e1c7870e4c9870e4c987261c987261c987261c980031e0c9c4ea1f517aaa2703bdd5544c78f266c1833730b9aaa000000000000263c393260c193a89c4ea27544c993260150fa8983060c1d03aaaaaa077b263c7939a98583060c1d5000000000000131e1c9c4eaa260c18307544c99326004c78f264c78f265cb931e3c9a74e9d3974e9cb80000000131e1c993264c993264c993264c9800f1e3c7972e5c78f2e5c001e7b00000000d800c02e0400b0100038f0e4c3930e4c3930e4c3930e4c000098070e06cd9b063cd83366c18336030608c78f2e8e2e5d1c5cb9b060cba31e3d1a35f8b7ea3166c183365d1a32e7cf83cf80c181f0606c06170f87c3e071e1c9870e4c9870e4c987060c987261c987261c984c383c7972e3c7972f41500c7833755555555175eb316bd662d58f1eacd83066eaa8018303e0f2019107c3e070e4c9870e4c9871e1c987060c9d507261c984c3917818f066ea3703a368c78f1e3cd9baaa366e8dd5010fbdd5555517aaaa563c7ab985cd1b060cd9b4d8b369b17547c1e5047c0067b060c018307107c3e071e1c9d44e0f41c183261c393261c39327541c98726130e0f1e3c78f1e3c7831e0c7d54501555555543c78f1ebd7e2d7afc59b060cdd50f0780c1850400c220f87c0e3c38f0e1c9930e1c9930e0c193aa0e4c3930987287d03075546cd831e0c7d1baaaaa366c78f1e3c78f1e3c0aaaa1f7baaaaaa9a9858f1e3c79b060cd9b4d8b369b17551f0a01e0f0067b060c018307107c3e41eaa261c7871e1c183261c393261c39327541c98726130e0f1e2c58f1e6c5a82a031e0cdaf8b975f172eac78f2e6c1832eaaaaaaaaaaa00c181f07880c2e1f110387264c387264c38f0e4c383064c3930e4d54261c45a0c78336a9b41a9b463c78f1e6cdaaa9b36a6d540563c79754bb29b060cb9b8b9737172e8f7daaaaaaaaaaaa7c1e2827c0067b060c0183065c3e22071e1c9aa4d0ea1c183261c393261c393261c98726aa130e0f1e3d51e3c18f063c1830060c583c78f1efe2e5dfc5cb9b060cba2d16a2c5a8b168345a2d163c1e0b0600c180b0185c3e0b1038f0e3c387264c387264c383064c3930e4c3a8b0987018f063c78f1e3c78f1e3c01e3c78f360c19737172e6e2e5d1efb5162d068b5162d458b45a2d5166c183060c58b166c59b162c58b166c58b162c58b2e2e170b162c58b1e0f0067b060c0183065c3e0b1058b0167c038f0e3c383064c387264c387264c3930e4c3a8b0e1c5930e1c58b0987078f162c78b1e3c18f063d514078f1e3d7c5cbaf8b97360c19755555555551e0f01830504018170f8881c7871e1c393261c393261c183261c98726aa130e28b41aaa6c18f063d4daaaaa9b363c78f1e3c78f1e032aa5c78f1e3cd83065cdc5cb9b8b9755551efb5555555553e7c1440783c019ec1830060c1970f888a1c3aaa936e1c7871e1c183261c393261c393261c98726aa130e28f1e3c79b418f066c1830060c58ac78f2f0e2e5e1c5cb9b060cba2d16a2c5a8b168345a2d167c1e0b0600c180b018306170f82c40e3c3930e1c9930e1c9930e0c1930e4c3930ea2c261c063c19b368c78f1e3cd9b0158f1e5cd83065cdc5cb9b8b975162d1efb41a2d458b5162d168b5459b166c183060c583162c59b166c58b162c59b162c58b162cb8b85c2c58b162cf83c019ec1830060c1970f82c4162c059f00e3c3930e0c1930e1c9930e1c9930e4c3930ea2c387164c387162c261c5e8d78f5e3d7a3066c19ba0a8aa9a5aaa45a2d458b5162d068b663e1f2801830806440b103a70e9c3874e4c3874e4c383066ea83a8b0f87019b066cda3363cd8f366c0aaaaaaaa45a2d068b5162d458b67dad4bea1f51b8dd40e0751b8dd546eaa56171f0f8033d830600c183881625047c03a70e9c383066c387364c387364ea83a8ba89c1e83e1c366d18f1e6c2aa94d9b360c1ab066cd9b366d1a336aed9b366ea95555419ec180c19f0f81c987261c987260cd83375554bd1af1ebc7af468aa15554aaaaaaaaaa7c3e203220183050440e9c3a70e0c19baa0e1d3930e1d393550f87019b066cda3363cd8f366c0547aaa8354daaa6d554da6eaaaaaaa965555555555559f67c3e00cf60c1803060d4f9f051088440e9c3a70e0c19b0e1cd930e1cd9343aaa4ea9543e1c066c19b366c79b1e6cd805cb9b060cb9b8b9737172e6c183366d362cda6c5972e7c3e00cf60c1803060cb87c3e1f03b70edc383066c387364c387364c3b70e5c3b70edc3e1c2e5c000183060ea8183a2a00a0aa563c7ab56ab16ad562c183060ea800000000000038f0e4c387264c387264c183060ea83930e4c022f03060c1d40e0750fbdd5555503563c7ab985cd03060c1d500000000cf60000002300781100100003082e04400b0100038f0e4ea2707a060c183aa0e4c3930000981c078f000060c1d55503060c1d0005443ea99acc5b3598b1e3c78f060c183aa00000000000000e1c9930e1c9930e3c38f060c183aa0e4c39300a1f40c1d5503360c1830755543ef7553530b1e3c78f060c183aa000000019ec000000800220007803c006101002c040083d544c38f0e3c183060ea83930e4c00026070162c000183060d541835563c79757172eae2e5c183060c540141555400000000000038f0e4c387264c387264c183060c3930e4d54011683060c1aa0d06aac78f2ea9765060c18347bed5555555000000019ec0000004600f0110010000605c080404000e3c393549a1d4183060c3930e4d5400026070 25 33554431 10 1023
def hc_69_9 : Nat → Nat := unpackHintV5 0xed618fe7e55fdee241d735ebcac71cc28211b5db2aaf09b4a61e3b9d523396a9aa8dea308791967eca327725e96bced66501b35c762354b9ef49bac044096c3d8d9f3675c62d0e5a2cb0172c54172459ff198eb313259a0b0a0705b95400016e 0x543ea1e0c1830740eaaaaa81dec78f1e3e6a6160c18307543c88f85003019107c3e07078f89d544c183060ea8993264c264c1e3c78f1e3c78f2e5c78f1e3d3a74e9cba74e5c783c3e1f0b87c3e1f0383c793264c993264c993264c984c9800f063c78f063cd8f1e3c78f878f1f0f2e3c78f1e5cb8f478b1e8f163c78f1e5cb8f1e3c7803cf67c3e170f87c3e071e1c38f1e1c38f1e4c38f0e3c3930e4c3930e4c3930e4c261c1fec03dfb007ec183f600c1e3c78f3e5cf97060c1831e3c78f3e7cf9f060c1832e8d1970781f0001800001c7871e1c987260c183061c987261c987260000c783063c1fb060c183060c18f1e3c78381970703060c183060cb8f1e3c783418b0683060c183065d1a32e000f3d80000c000000007803018000c3600030d800c0601702005808001c7871e0c183260c383060c183061c987261c9872600004c98070e00fd8f07ec07ec03dfb07803c78f1e6c1832e7cb9f2e3c7fb1e3fd9b060cd9f3e7cf97468cb83c0d8007c0080040e3c38f0e0c1930e4c3930e4c3930e4c3930000e1c060c78f063c1fb060c18f1e3c78f1e3cd832e0cb9737172e6e2e5c78f1e3c7a3360c19b369b166d362cba3465c001e7b000000d8000000f0361b00180c0361b000180c002e0400b0100038f0e3c383064c387264c387264c3930e4c3930e4c000099300e1c07fb00f7ec1e3c78f3e7cf9f2f75ec22a878f1e3cf9f3e7d5ab56aea81e07c00008000e3c38f0e7c987264c3930e4ea83930e4c00038721f0f1e3c7d46e0750fbdd55555171e3c78f985cd2b56ad5d50003cf60004000000003c220020b8006c0060417022005808001c7871f51383d07261c9d507261c98000132601c38031e0cdc8ea1f517aaa2f03bdd5548c78f466c1833730b9aaa00079ec00000000004606c360030181100113c008080160200071e1c987060c9d44e0f5541c9872600004c03870aaa467c183060c183000aaa000a2463c7a346a3168d462c183060ea800000000000038f0e4c387264c387264c183060ea83930e4c02a1f523060c183a075555540ef68c78f473530b060c183aa00079ec00000000004610004400030d800c060417022005808001c7872707aa8983060c1d507261c980001300e1c05fb00f7ec1e3c78f3e7cf9f1e3c78f3e5cf97465d1971f6bec1155541e07c00000040e3c38f0e4c3930e4c3930e4c3935500045a3c78f1ea9b41a8f1e3c7aa5d95197465d1efb55555554001e7b0001000000001e0880082c003600300b810082c044000e3c38f549a1d43930e4c3930e4d54000099300e1c078ff63c7fb1e3c78f465d1977d8b7d88b45a2d16fb00f7ec3e7cf9f2e7cf9716003c000600402c003e071e1c787261c987261c9875161c987260001c383c78f1e3d18f1e3c7a32e8cba8b168f7da2d168b45aa2cd8b062c18b162cb8b85c2c58b162c001e7b00000000005800f03600300b81002c1602200b05800880001c7871e1c987261c987261d45870e2c9870e2c58000132601c38031e0cdab3eaaa2c58002b1e3cb9b060cbc78b978f172eaa20d50050550000000000000e3c3930e0c1930e1c9930e1c9930e4c3935500063c19b51aa3d516ab1e3cb9b060cbaa5d955506fb555554001e7b000000000000d86c006030110010002e04020200071e1c987060c9aa4d0ea1c98726aa00004d38070e00c18306ac78f2e0c183068b45a8a0d168b567c183060c18300502e5d5cae2e5c58b0000000000000000e3c393060c1830e4c3930ea2c387264c387264c00183060d58f1e5c183060d168b41bed418345a2c1a3060c18f060d5065c1c0e060c18b06000f3d80000000000ac01800c02e0400b05808800c06000300000e3c393060c1830e4c3930ea2c183064c187060c00009a700e1c0183060c183060d197465d4555540000467b00000000603000440b800009ec00183060c3930e4c3930e4d54000011e3cffb1e3cf9f060c1830602b1e3cb9f2e7cb83060c1aaa028aa87c0f8000c0b80002071e1c987261c983060c187261c9aa8002aaab3e0c183060c18002b1e3cbab8b9757172e0c18306aaa000a2aa0000000000001c787261d5870e4c9870e4d593260c183061c98726aa00a8f47aa8d060c183506ac78f2ecaa97060c18355555506fb5500079ec40000000000158200088000c3600301805c08041602200071e1c9a870eaaa4c983060c187261c9aa8000134e01c387b2f17f65e2e0c78336ac78f2e6c1832e8b45a8306837d88b45ab3e2c58b162c5a800172f45cb8306000003c00000000000e3c3930e0c1930e4c3930ea2c387264c387264c0018f066d58f1e5cd83065d168b5060d06fb45a2c5a3162c58f162d5165c5c2e162c18306000f3d800000000010c0d800c02e0400b0100582c001600001c787261c183261c987261d45870e2c9870e2c58000134e01c38231e3d1d55522d168b45a8b233f5548cda3068c1a33600a02c5800000000000000071e1c987261c9d5075161c393261c39326008c78f4755548b45a2d16cfb5a91d43ea37503a56170003cf6000000000023036003020200582c044088008000038f0e4c3930e4ea83a8ba89c1e800009a700e1c118f1e8d1e3c78f3e7cf9f3f555500aaaa80a21f036001f002001038f0e4c3930e4c3930e4ea954000387118f1e8d55519f466d183460d19baaaaa00055555000510000000000000e3c3930e4c3930e1c9930e1c993aa5500 24 16777215 10 1023
def hc_69_10 : Nat → Nat := unpackHintV5 0xf0403aeb7134e4a5b3dc1a23d53db7cd91ebc2e2acbc8996b4e9e8af0d77a80dc0a1e989968ad88e8dff83b6b67bf9ef70dac8678e53587fc457cc2c5570974cda26419ecf388a4528c3f221b9c21732a216c01c16082e0fb196066254000198 0x18302e5d402b93060c183060c183465d1975155550000000000006005c000100060c1830e4c3930e4c39355000051e3d54183060c1830001e3c78f97172f2e2e5c183060d55400145541e0000000000001c7871e1c393261c393260c183061c98726aa00a8f47aa3d060c1835063c78f1ecaa97060c18355555506fb55079ec0000000000001e0800220003001805c080404000e3c38f50e1d554993060c1830e4c393550000981c018f063c78f1e3cd83065d168b41a22d163c78b1e3c7a0173e7cb83001e06c0002016001f038f0e3c383064c3930e4c3a8b0e4c3930260031e0c78f1e3c79b060cba2d1683445a2c58b162c78f162d4000b977f3f8b97060c00000000000000038f0e3c383064c3930e4c3a8b0e1c9930e1c99300063c18f1e3c78f360c19745a2d418341bed168b163c58b163c58b54597170b858b060c183cf6000000000000b001e06c0060170200580802c16000b00000e3c38f0e0c1930e4c3930ea2c387164c387162c000260701e3c78faaaa45a2d168b46aa1e3e979b5e0d7835e6c014058b0000000000000000e3c38f0e4c393aa0ea2c387264c387264c0078f1e3eaaa9168b45a2d9f6b50fa87d46ea074ac2e079ec0000000000001e06c006040400b0102200200000e3c38f0e4c393aa0ea2ea2707a0000981c078f1e3d478f55966e583960e59baaaaa000555550005107800000000000071e1c787261c9870e4c9870e4c9d52a800f1e3c7aa3d51ea8354dd5552caaaaaaab3ec1e7b0000000000000781b001808002200404020200071e1c787261c9a1d552754aa000130380f1e3c78f1e3c7972e3c78f1e5cb83cf6000000000f03600300b81002c04000e3c38f0e4c3930e4c3930e4c3930000981c00060c78f060c79b063c18f87d3eaa1f0faa87d43ea2f555543e2f550f81deeaaa1e8f163d1e2c78f1e3cd83066e61735543c7a31e3c01e7b36032823e1107c3e071e1c38f1e1c38f1e4c38f0e3c383064ea2707aaa0e4c39309870183060e8228183060c183060eaaaa81deeaaa878f1e3c183060d7abc5af578baa1e4030187cf850441f0f81c7871e0c183061c393261c39327541c98726130e01550f87d543ea87d43c183060c183060c183060e81d55555555503bd8f478b1e8f163c78f1f3530b060c183aa1e3d18f1e00f3dc7c280180c883e1f038f0e1c78f0e1c78f261c7871f07aa8983060c1d507261c984c38a08a0c7831e0c18f160c18b163c78f1efe2e5dfc5cb9b060cbaaaaaaaaaaa8f10f9f05036030b87c440e3c38f0e1c9930e1c9930e0c1930e4c39355098700060c78f060c79b063c18f47aaa8f47aaa3d51ea8b47c3c78f87971e3c78f360c19754bb2aaaaa3d16aa837daaaaaa3c78f1e00f3d9b018a09f02e1f11038f0e1c78f0e1c78f269c38f0e3c383064d5268750e4c393550987018300603060c18306a0c18341831e3c78f5f172ebe2e5c183060d168b5162d458b4183418345a2c780c3e7c0183006030b87c162071e1c7870e4c9870e4c983060c187261c987516130e000c183060c183060c783360c183063e1e3c7c3cb8f1e3c783060c1a8b16a2c5a2d16837da83068b45831e0c183060c18f063c183060c18f060c18f060d5065c1c0e060c18b063c7ab1e3c01e7b06030b87c162030600cf8071e1c38f1e1c38f1e4d3871e1c783060c187261c9875160c183260c38306130e172f7bf6ec9a283060c1930e4dd97765d41bed54783cf67c4060c1835045060c183060c1831e3c78f060c1838b97af172eaaaaa0df6aaaaaa3c7820f3d830187cf828170f8881c7871e0c183061c387264c387264c9930e4c393550987005547a3d551eaa3d51e0c183060c183060c18306a0c7c3c78f87971e3c78f6554b83060c1aaaaaaaaaa837daa8f1eac78f0079ed3e0a00c06170f8881c7870e3c7870e3c7934e1c7871ea1c3aaa93260c183061c98726aa130e0b1602c162c18f063c1831e8306a3c78f1efe2e5dfc5cb9b060cba2d16a2c1a83068345a2d163c161f3e02c581b0185c3e0b1038f0e3c387264c387264c383064c3930e4c3a8b098700063c1831e3c1831e3cd9b063c18f1f0f1e3e1e5c78f1e3cd83065d1ea2c5a8b162c5a2d16a0c1a0df68b458b1e2c58b162c58f163c58b162c58f162c58f162d5165c5c2e162c183063c7c31e3c01e7b36030b87c1620b160b0162cf9f00e3c3871e3c3871e3c9a70e3c38f0e0c1930e4c3930ea2c387164c387162c261ca08a1e3c78f5e0d79b5e0d79baa5a9aaa45a2d458b5162d168b69a1e41f3e1407c3e440b1038f0e3c387264c387264c3930e4ea83a8b0987001e0c78f1e0c79b1e3c78faaaa87c5eaaa9458b5162d168b45a2d9f6b50faaa1f0faa87d43ea37503a56170f1e8c78f0079ecf87c881625047c038f0e1c78f0e1c78f269c38f0e3c3930e4ea83a8ba89c1e8261cae0cdfb375c1fb1687c78f1e3eaaa94116b9b075c19baaaa55555559f6aaaa3c7883cf87c883e7c1411038f0e3c3930e4ea8387264c387264d54261c007831e3c7831e6c78f1e3d551e8f5547aa8f547aa0d53755555554b2aaaaaaaaaaacfb1e3d18f1e00f3d9f0f89f05088440e3c3871e3c3871e3c9a70e3c38f0e4c39343aaa4ea954261c063c18f87d43ea2f5543e077baaa878f1e3cd83066e61735543c836032823e1107c3e07078f260c193a89c4eaa8993264c264c 24 16777215 10 1023
def hc_69_11 : Nat → Nat := unpackHintV5 0x9451ddc66deee1ccda903beaa7c7d58bc537adcd9542db9ecb66bbc52ff7d9969ed74ad49eb560e25a86da6931448a8a738c415af79dedb00dcd4a6603b8c2ca0df13dc9d092ab0e4042451c46f68c0088c52137c20f2060d24d5048c818150bd60002a1 0xd18f066cd833e0cf83066cd9b366c1e3c1830060c183366cda31e3cb9f3e5cb9f665cb9b060cb9b8b9737172e8c78f467cf9f667d79f3e6c183366d362cda6c597468cb83cf63c780f1e3cd9b019f078f0363c0b87c3e1f038f0e4c387264c387264c383064c387264c387264c3930e4c3930e4c261c063c01830603066cd800c183060c183068c183060c183067c19f0703060e065d18f1e5cf9f2e5cfb32e5c183060c1a0c183418b463c7a33e7cfb33eccf9f060c1832e8d197063c01830079ec78f01e3c7833e0306170f87c3e030e0c183060c9871e1c9870e4c9870e4c983060c187261c987261c984c38043e8bc5c0222a87a31e3c78f3e0d19b460cf9ba8dc0ea1f7baaa8bc5eaaaaaa8b8f1e3c79f518b469f1730b9a56ad5abaa079ec78f01e3c7d1051f3e07c3e441f0f81c7871e1c393261c3932751383d07261c9d507261c984c390f0a8a2e5c081d546d18f1e8cf9f3eccfb33e7eaaa8bd5545e2f553530b463c7a33e7cfb33eccf9f56ae1d543c2801e7b1e3c078f1e7c3e45ca0f87c83d544c38f0e4c387264c387264c3930e4e0f541c98726130e000c783360c19b360c19b3723a87d47e3f5523a7d545eaa8bd55540ef7555231e3d19f518b469f166c1833730b9aaa079ec78f01e3c79b019411f0883e1f038f0e4c387264c387264c383064ea2707aaa0e4c39309870183060e2a80183060c183060eaaaaaaa918f1e8c183060d1a8c5a3518baa81e030183c7850441f0f81c787260c183061c393261c39327541c98726130e0150fa91d548eaa8fc7c183060c183060c183060e81d55555555503bda31e3d19f518b469f173530b060c183aa079ec78f01e3c7c7c280180c883e1f038f0e4c387264c387264e0f5513060c183aa0e4c39309870045a8b4580222a8f1e3c79f068cda3067cdaa6d06a3c78f1e7e2e5d1c5cbaa5d95197465d1efb55551a2d55555555079ec78f01e3c7a8829f3e07c3e170f8881c38f0e1c7870e4c9870e4c9aa4d0ea1c987261c98726aa130e003c78f1e7c1a3368c19f363c78f1e7e2e5d1c5cba32e8cba8b168f7da8b162c5a8d458b45a2d168b5554005882c58b162cd8b062c18b162cb8b85c2c58b162c1e7b1e3c078f1e7c3e170f82c4162c1602c59f3e01c7871e1c393261c393261c987261c987261d45870e2c9870e2c584c380231e3d19f3e7d99f667cfa31e3cb9f3e5cb9f665cba32e8cba8c5a2c5a7d3ea2c58b168b45a2d162c162d415459b160c583162c597170b858b162c583cf63c780f1e3cf87c2e1f058b13e0b1602c78071e1c9870e4c9870e4c987261c987261c9875161c38b261c38b16130e22c151458b0106aa9b463c7a33e7cfaf3eccf9f6554ba31e3cb9f3e5cb9f665cba32e8cbaaaaa35554fa7d55551e0a00f3d8f1e03c78f3e1f0b87c4f8a2870eaaa4c9871e1c9870e4c9870e4c987261c987261c9aa84c38a0a80c18b160c19b160c78336ce2e5d9c5cbab1e3cb9b060cbaaaaaaaaaaa80f1e083c36030b87c440e1c9930e1c9930e3c3930e0c1930e4c3935509870b8337cd93eb362fefd800c783360c19b360c19b36a3547aa7d3eaab355516ab1e3cb9f8b978b97360c19754bb2aaaaaaa0df6aaaaa83cf63c780f1e3cd80c504f8170f8881c787261c393261c393261c18326a9343a87261c9aa84c380c1803060c068306a0c183060c1ab8b9757172eac78f2e0c18306a2c5a8b168b45a0d068b45830603c78030780c06170f82c40e1c9930e1c9930e3c393060c1830e4c3930ea2c261c00183060c183060c183060d58f1e5cfc5cbab8b97060c18345a2d458b5162d06fb5060d168b068c183063c183067c19f060c18306ac183060c1aa0cb8381c0c183160c1e7b1e3c078f1e0c06170f82c4060c019f00e3c3930e1c9930e1c993060c1830e4c3930ea2c183064c187060c261c060c1834550060c183060c183563c797060c18357172eae2e5d555555555501e00c060f1e0a05c3e22071e1c983060c1870e4c9870e4c987261c9aa84c3802a3d546aaab5553e9f060c183060c183060c183506ac78f2e7e2e5d5c5cbb2aa5c183060d55555555541bed541e7b1e3c078f1ea7cf8288030185c3e22071e1c9870e4c9870e4c9a870eaaa4c983060c187261c9aa84c382c580b162c060d418336831e0cdb38b9767172eac78f2e6c1832ea0c1a8b068b45a0d168b458b1603c780b078f1e1b0185c3e0b10387264c387264c38f0e4c383064c3930e4c3a8b098700063c19b060cd9b060cd9b563c7973f172f0e2e5cd83065d168b5162d458b5060d06fb45a2c5a3162c58f162c59f167c58b162c5b3162c58b16a8b2e2e170b160c183079ec78f01e3c79b0185c3e0b1058b0167c038f0e4c387264c387264c383064c3930e4c3a8b0e1c5930e1c58b0987282a1183466d183466d18f1e8e696aaaa9458b5162d168b45a2d9a8078f081e1f0f9102c40e1c9930e1c9930e3c3930e4c393aa0ea2c261c0118f1e8cf83466d1833e6eaaaaaaa9168b5162d458b45a2d9f6b523a87d47e3f5523aaa37503a561703cf63c780f1e3cf87c881625047c038f0e4c387264c387264c3930e4ea83a8ba89c1e8261c463c7a3aaaa4550466d183460d19baaaa555555555541e1f0f9103c782822071e1c987261c9d5070e4c9870e4c9aa84c380231e3d19f068cda3067cdaa3d546aaa35553e9f541aa6eaaaaaaa965555555555559f60f3d8f1e03c78f3e1f14f9f051088440e3c3930e1c9930e1c9930e4c39343aaa4ea954261c0078f3e0cd833e6c78f2e7e2e5e2e5cb971e3cfa2d3e2cb97079ec78f01e3c79f0f85c3e1f0f81c787261c393261c393261c987261c987261c98726130e031e0c7c3ea1f517aaa1f03bdd5543c78f1e6c1833730b9aaa079ec0000000000001e06c0060440044f0020b811002c04000e3c38f0e0c193a89c1eaa83930e4c00026070a1e3ea8183060c183000aaa000aa2077b1e3c78f5eaf16bd5e2c183060ea800000000000038f0e3c387264c387264c183060ea83930e4c02a1f50f060c183a075555540ef63c78f1f3530b060c183aa079ec0000000000001e10004400030018101002c04000e3c38f83d544c183060ea83930e4c00026070063c18f551e3d458b0001e3c78f360c1977f172efe2e5d545401415400000000000038f0e3c383064c387264c387264c3930e4d540018f063d1ea8f545a3c78f1e6c1832ea97655541bed55555079ec0000000000001e06c0060220020005c080404000e3c38f0e0c193549a1d43930e4d5400026070060c1831e3c78f060c18345a2d1068b4583060c18f1e0c18028172ebe5f172e2c5800000000000000071e1c783060c187261c9875161c393261c39326000c183063c78f1e0c183068b45a0df6a0c1a2d160c783060c78306a832e0e0703060c583079ec0000000000001e00c0060170200580800c06000300000e3c38f060c1830e4c3930ea2c183064c187060c00026070 25 33554431 10 1023
def hc_69_12 : Nat → Nat := unpackHintV5 0xcf38b8e40473302e3a977b937b510d9d86e4369ca4db40b9b39c2886c95098a48a03d15a9d586588fbe5a9a5d8834ae778996f608bb278a717c92e6b0b1b354d470a85842528c3408831863e10c11be0650c463545589952440d0900c4283fc8140003fc 0x31e0c183063c1fbaa81c5d068b067cf83060c183060cfe71e3c78f060c183141602cf80ca162e8383064c3930e4d18f1e8eaaa9168b45a2d98f9f3e8cda3068c1a33715402c5820b167cf83cf87c3e440b12828038f0e4c3930e4ea83a8b0e1c9930e1c993098717afaaaa45a2d168b663e7cf8f3e3cf9f367c19f067cdc4a80b16082c59f0f87c3e4540b1620ba83a70e9c3a70e9ea83a8b0e1cf930e1cf930f872aaa9168b45a2d9f6b5543ea37503a5617550b517514074e1d3874e1d3d50751751383d074e1d3a0c183060eaaa9554d9b5060d56aaa9555555555518f1e8c183060ea919f46233e8c550e3c393060c183aa0e1c9930e1c993550e4c3933606c180c47a8d53e9f54fb6d0683aa655559f67d183060c1a7cf8a01c987261d4983360c18f07ec183060c18306a8f551aaa0d5541a0d50683541a6eaaaaaaaa965555555555559f68c78f460c18301830183060d454aa550e3c393060c193061c183060c18343aaa4ea9543930e4c18f418f1f5554a0c1aaaaa9b375554aaaaaaaaaa3c78f1e6c1833754acfab159f562a871e1c787060c9d5070e4c9870e4c9aa87261c980c186c0da3d1e834daa7d3ea9f59d532aaacfb1e3cd9b1e3d3e7c500e4c3930ea4c18f07ec1831e3c183063cd8f547a3d51eaa0d536aa8f5551e8faaaaaaaa595555555555567d8f1e3c79b060cd8f1e3c1e3c5152a95438f0e3c383064c3871e4c3871e3d0eaa93aa550e4c393f60c667c183060d063c1fbaaaa51e3d55418355aaaa8183555555555551e3c78f060c183aa3eccd67d98aa1c7871e0c18307541c393261c39326aa1c987263c1e03018a9f59aa7d3e8f47a0d0754caaab3ec1831e3c1834f9f14143930e4c3a93264c1831e0c183060c183063c1fb5541a0d5506aa3d51ea83541d55540e2f5554b2aaaaaaaaaaacfb060c060c183c78f1e0c18306a2a552a830e0c183060c9871e1c783060c1a1d552754aa1c987260c7836aaa95541835551e3eaaa9555555555518f1e8cd83066ea919f46233e8c550e3c3930e0c193aa0e1c9930e1c993550e4c3934608cd81baa5553e8cd9ba368a8a1c987261c3830063c07a3d46834daa7d3ea9f6a9955567d9f466cd9b367d054a50e4c3930ea4c387060c78f063c1fb060c18f1e3d51e8f551aa8341aa6d36aa9b555369baaaaaa8bc5eaa96555554da2d55555567da31e3d19b060cd9b366c366c5152a95438f0e4c383064c387264c387264d0eaa93aa550e4c3931e6c7d555520c183066c78f5754aaaaaaaaa6c183363c78f1f548d5ab46aa1c183261c7871f541c98726aa1c987263c78faaaa8bd5ee366c183060d1fb54183556a955536afb55554d83066cd9b366ea91a3468d54383064c3930e4ea83930e4d543930e4d5a3a5568d5a3aa555460ad188c010786c0644230fa2007261c984c38ad1d229b060cdd52ab46ad1d500aaaaa8d1ab568d1a33e7c46230e4c3930e4c393463c7a3aaaaa5559b460d583466eaaa95555555555518f1e8d5abaa467c3e8c550e3c3930e4c393aa0e1c9930e1c993550e4c393360c783f60c183068c78f3e0c183067cf833efc183060c1830755510aa887d1830600cf9f01835a5064c3830e4c3930e1c783f60c783066c78f1e3c79b060cd8f1e3c79f3e3cfab1e3c7d5442aa20f1e6cd8f1e03cf9f16943930e3c3930e4c387063c183060c783f60cfcb060c183060c19f3e3c78f1e0c1830755038bc42aa2033e7c060c078f060d694383064c3930e4c387063c783f60c18f1e8c78f3e6c183366cd9b367cf9b3f2cd9b375178bd54426d16aa887d19b366cd9b0f9b05a50e4c3930e4c3930e1cf9f3e8c78f468c1a3368c1a33755514154aaa8a0aaaa7cf83cf8a0a07c3e4422071e1c9870e4c9870e4c987261c9d52a84c387cf8f3e3cf9f3e6cf833e0cf9baaaaa0a855555054553e7c3e1f3e1f158a84540e9c3a70e9c3a70e1cf930e1cf93aa55039f0e1c547aaa8354dd5552caaaaaaab3ed454aa550e9c3a70e9c3a743aaa4ea9543a70e9c0063c183360cd80030180c183060c783f60c183060c183460cd83060c183060c1831e8c78f1e3cfc5cba38b9707032e0e060c183060c1971e3c78f3ea3168d3e2c1a0c5834183060c1832e8d197079ec78f01e3c78306030060cf9f006030b87c3e1f038f0e3c387264c387264c183064c187060c183060c3930e4c3930e4c261c001831e3c18f07ec183366cd9b068c183366c183060c18306006c061b366cd8f1e3c78f1e3cfc5cba38b97360cb832e5cdc5cb9b8b971e3c78f3ea3168d3e2cd83066cda6c59b4d8b2e8d197079ec78f01e3c79b0186cd86c0d9b3e7c0b87c3e1f038f0e3c387264c387264c383064c387264c387264c3930e4c3930e4c261c 25 33554431 11 2047
def hc_69_13 : Nat → Nat := unpackHintV5 0xee45bfe9a927e13a1cd92206d4a91ed00d27c7f207c2f140bcd986b4e5fdaa06b8a231f596e6d390e97f8b2970811a847bbd577904ae73fd4269ea8560865957f225506de1459ab53dddef3346a62b3a032076b118e1e50d96d3058e02000163 0x60c18351e3d5681830755554c3ef7554aaaaaaaaaaaaaa3c78f1e0c183067ef97cf954aa1c7871e0c183061c393261c3932754aa1c987263c1e2a7d66a9f4fa3d1e0c18306838896555506fba1e3d3e7c50a50e4c393438754993264e87aab32ab2a8f547d03075540cd83060c1a83aaaa1f7b6556aa555555555506fb55a2a078f1e3d454060c183aa5583d544c38f0e3d4387555264c183060ea9543930e4cf9f3e0c183060c18301830463c79747172e8e2e5c183060d5551415554f9f079f14140180c2e1f11038f0e4c387268c9930e8c387264c183060c3930e4d54261c2f231e3cfd51f3f1f67540c1c0c060fbdd55540d5510faba08f9f14183a5898783930e4e1f1f975551f3e3c78f1f0307503360c06550fbdd52aa247cf9403c7a83074a1e8987261c99f3e3cf8f3e7c183060c1830060c185cb9f8b973f172e0c18306aaa0a8aaaa7cf87c54180c1830b970f85d1503a70e9c3873e4c3873e4c183060c3a70e5d543e1c060c183264c993060c183555555264c993060c1832eddb9755264c993060c183264c99355264c993547aa0c18306a0cb976554b83060c1aaaaaa837daaa8a80c183065cbaa874e1d3a870eaaa4c183060c3a70e5d543a70e9cb97162c58b162c18f066e96a687d55555551745a2d41835a41b332b1e3d5b33ecc667d986c18337542d45871e1c9870e4c9870e4c987060c9d5075161c9872717818f066ea3703a87deeaaaaa8ba2d16b0b5a5060d06fb66168c58b162c78b1e2c5d550b1742ea95aaaa060c1ab1e3d5d450e0d83066ea85a8b162c582c581c7872751383d07060c9d5075161c38b261c38b161c987263c78b162c58b175534a831e0c7d55555552d283068b45a835999f9f7e3f3efc1e3c78f360c19baa16a2c387264c387264c38f0e3c383064ea83a8b0e4c393a1f40c1d551b360c7831f55543ef754b4b0b45a2d418341bed9a85d55550b162c78b162c58f163c58b568597aaaa060c1d0e2a078f1e3cd83066ea85a8b162c582c5907aa89871e1c787060c9d5075161c38b261c38b161c98727550b85c0cd8368dd545ef75555545d1683616d20d9991a3468ea8d83066ea85a8b0e4c393aa0e0c193aa0ea2c3930e4e91d5546cd831e0daaaa8bdeea9a6168b41a0d99aa91a3468cd83066ea85a8baa0e4c3930e0c193aa0ea2c3930e4c58b160c79b066cd83066d060d518f1e5d1c5cba38b97360c197458b458b5160d418341a2d168b463c7a3467df8fcfa30d83066cba3465c5a8b0e3c3930e1c9930e1c9930e0c1930e4c3930ea2c3930e4cbd1b070fbdd545d16c7c78f47547d9c7cfd4835545cb830063c7d047cf86cdd0b162c5c4c3c1c987264c9c3c78f1e3cd81baa1602c78fa162c5c5407261c993270f8183a8d9baa1f7b645c7cfd5547c78f1e3d06a818033f0540f1e6cdd0b162c587a261c987264c9831e0cda31e3cb9b060cba2d168345a2d167cf9f366c0186cd972e8e47172e2c5820b167cf83c78f3fec36030b87c1620b160f058b162c038f0e4c383064c3930e4c3a8b0e1c9a3264c3a30e1c9930987019b066cb97360c19745a2d068b45a2cf9f3e3cf8f3ea00c36972e7e3f172e0c1820b067c3e7c366c061b2e1f3e0b1620b162c5874e1d387060cd874e1cb875161c39f261c39f261f3e1c4e0cd83365cb9b060cba2d16a0c1a0df68b458b162c58f162d5165c5c2e162c183066c183365cb8b5162c58b058b03a70e9c383066c3a70e5c3a8b0e1c5930e1c58b0e9c3a7366eaaa060c1d5030755534b5548b45a8b16a0c1a0d06cc8c78f468cfa3119f4603060c1d50b5161c787261c393261c393260c18307541d4587261c983360c18f07ec183060c183075555555548b45a8316a0c1a0d06cfb5a91d43ea0703aa81d55038dd40e074ac2e463c7a3060c180e1830183060ea85a8ba8a038f0e4c183064c187060c183060ea83a8ba89c1e83930e4c18f818f1f540c1d1b37555555534b48b45a0d16a2c5a8b16cc3c78f1e6c18336acfab159f56550b5161c7871e1c183261c393261c39327541d4587261c9831e0fd83063c783060c79b1f555555548b45a0d16a2c5a8b16cfb5a87d43ea37503a87c3eaa1f552b0b878f1e3cd83066c78f1e0f863caa16a2ea25f01c7871e1c183261c38f261c38f1f541d45d44e0f41c987263c7d5503075540c183818f56a60703aaaa5060d458b45a2d06835965e7d78bcfaf078f1e3c183060ea85a8b0e1c9930e1c9930e3c38f060c183aa0ea2c3930e4c1831e0c183060c183063c1fbaaaa81c5eaaa941835062d168b41a0d9f6b503aaa0703aa87d43ea07503a561703860c060c183c78f1e0c18307542d45d4500c383060c183261c7871e0c18307541d45d44e0f41c987260c7838183aaa1e3eaaaaaaa6969168b41a2d458b5162d65918f1e8cd83066d19f46233e8caa16a2c38f0e4c383064c387264c387264ea83a8b0e4c393060c78f063c1fb060c18f1e3eaaaaaaaa9168b41a2d458b162d36a2c5b3ed6a4750fa8dc6ea0703a8dc6eaa37552b0b918f1e8cd83066cd9b361b866caa16a2ea25f01c787261c183261c393261c39327541d45d44e0f41c987275231e3d1a306acdab068cdd552d4d5522c5a2c5a8b16a2c5a2d16cc8c78f468cfd3299f462f56ad7d50b5161c787261c393261c393261c98727541d4587261c99b063c1fb060c183aaa45a0cf8f1e8c183060cfbf067cf83060c183060c50580b061f2858ba064c3830e4c393 24 16777215 10 1023
def hc_69_14 : Nat → Nat := unpackHintV5 0xc8ba09bfea34b91db3b49d20ac9a01a5b5b9a16115993a0a9181ee8d84ff8931158169f27b7d7b73d1eb68feb56105fe5656ac4c468447e5184361213a2e4d313a3d28a62524391b23b0221e15671546340e8dae09913f01122000ac1900002b 0xf1e3c7972e5d458b47bed168b45a2d5166c583160c58b165c5c2e162c58b163c7972e2d458b162c162c0e3c3930e4c3930e4c3930ea2c387164c387162c3930e4d5063cd83366c183362c183162d18f1e5d1c5cba38b97360c19755555555555463c7a3467df8fcfa30d83066cba3465d5438f0e4c387264c387264c383064c3930e4d543930e4d4b9755a162ea818f066d5695aaaa2eaaaaaaaaaaccfb3199f662b1e3d59b060cdd52a870e4c9870e4c9871e1c987060c9d52a87261c99702e0cd83368d1e9f63aa7d3ea8b621a5541bed54faba43e51f0e1c9873e4c9a4c3a1c3c5e063c19ba8dc0e946a8f56655655516c3ef75555545d599555555506fb55555558f1eaea28360c19b5452a95438f0e4ea2707a0e0c193549a1d6a9543930e4d478f55063c18faaaa162c5d352aad52aaaaaaaaaa8f1e3c7bf3efc7e7df86c1833754aa1c7871e1c393261c393261c1832754aa1c987263c1e03360cd9f4faa7d66a8f47a2d88695506fb55a1e3d413e7ca50e4c39349874993a1f40c1d551b360c7831ecaab32aa3d51ea8b6aaa87deea9599555555506fb5555568a81e3c78f360c19b5452a9560f55130e3c38f0e0c193549a1d6a9543930e4c18f066cf9f3e6cd8030d9b463c797360c19747172e8e2e5d55555514154f9f079f0d80c50502e1f11038f0e4c383064c387264c387264c3930e4d54261c2f46c1c7c78f47547d9c7cfd42c058fbdd545ea955120f86cdaac4c3c1c987270f8183a8d9b8f9faaa8fcb1e3c78f1602ea87deea955123e7ca0366d543d130e4c393066c19b3e7cf8f3e3cf8b1600c362cb97360c1973f172e7e2e5d5555514154f87c366c061b54b87c4540e9c3a70e0c19b0e1cf930e1cf930e9c397550f87019b066d547aa2d2e5cd83065d52ecaaa837daaaaaa6c18336a8a172eaa1d3874e1c18336a9343a874e1cbaa874e1d3972e0c183060c183060c1cd2d5555555522d16a2c5ad320d9958f1ead59f562b3eac060c183aa16a2c38f0e4c387264c387264c183060ea83a8b0e4c3938bc0c1830750381d43ef75555540d168b585ad20df6a0c1b303460c1831e0c1d55030740ea95a065eaaa818b06ac78f5751438060c183aa16a2c183060306071e1c9d44e0f40c18307541d4583060c9830e0c187261c98f1e0c183060c1ab53540c183075555550faa5a5162d168b5941b32f3ebc5e7d783c78f1e0c18307542d45870e4c9870e4c9871e1c783060c1d5075161c9872743e8183aaa066c183060eaaa87deea9696168b45a0df6a0c1b3503aaaaa060c18f060c18f060d5aaaa062c1d0e2a078f1e3c183060ea85a8b060c180c1907aa89871e1c783060c1d5075160c183260c383061c987260c183060c183060d41830683068c78f2e8e2e5d1c5cb83060c1a2c5a2c5a8b16a2c5a0d068b45a31e3d1a33f4ca67d180c183065d1a32e2d45871e1c9870e4c9870e4c983060c187261c9875161c987265e818387deeaa068b63e3c7a3aa3ece3e7ea14aa1602e0f80c18b160c1c4c3c1c987270f8183a819baa1f7b645c7cfd5547ed8f1e3c78a550b0167c8060c58b060c3d130e4c393060c183060d18f1e5c183060d168b41a0d168b3e7cf830183060c0b9747238b97162c1058b3e7c1e7c06030b87c162030600c18071e1c983060c187261c9875161c393261c39326130e03060c1972e0c183068b45a0d068b459f3e7c79f1e7c180d502e5cfc7e2e5c58b04162cf87c0603060c2e1f058b10583060c3a70e9c183060c3a70e5c3a8b0e1cf930e1cf930f870183060cb97060c18345a2d06fb5060d168b060c1831e0c1aa0cb8381c0c183160c183060cb9716a2c183060306074e1d383060c1874e1cb875160c183260c383061d3874e0c1a83060c1972e8cba32eaaa8c01188c0046803c006031187cb908801c9872607098704467d187060d0154183060d4183060c02e5e2f17465d19755555462311a3468cf9f1188d1a3ee1c3930e4c987261c9870e0c183060c1aa0c183060c183068c7971e5cb83060c1a38b9747172eaaaaaaaaaaa8c78f460c183068cf87d185d1a32eaa1c787260c183061c393261c393261c98726aa1c987260c18306aaa5cbd030754d55554aaaaaaaaaaaaaac78f560c18306acfab159f56552a871e1c983060c1870e4c9870e4c9d52a87261c99702e8f51aa7d3ea9f7383060c1a0e225955541becfaba4f9f1428f870e4c39f264d0e1d5264c3878bca8f551aab2aacc0c1830750381d28387deeaaa5a5558bd540d55555555541bed5558f1eaea285150183060ea95438f0e4ea2707a50e1d554993060c183aa550e4c3938f77cfdecbe7cbc2d 24 16777215 10 1023
def hc_69_15 : Nat → Nat := unpackHintV5 0xefc95e745e70f8303ffac5aa5d1949366904770f64a576522cb6d48ad72a8829d33853e4a0a9aac8f4b2c45638841d109975829cb63eea4c9de831acf9bf5578a08a646afd05d58c7319fa31e0f5934ab4c7f23663091e01348a006f655c24426e000244 0x18f063e1f50fa8bd550f81deeaaa47bed458b41a2d616b4cca8b360c183062c5d550b1742e7d550b2f55542c58b1e3c78f360c19ba8a1c550b5162c58b058b038f0e3c383064ea2707aaa0ea2c387164c387162c3930e4c183060eaa81deea906835945b303060c183062d78baaa162c583060c1a35ebd1d50b5162c58b160c183061c98727541d4587161c587261c9d2cd03060c183060c183060c1d5555555503bdb22d69458b41a0d9878f1e3d79f5e2f3ebc060c183aa16a2c38f0e3c387264c387264c183060ea83a8b0e4c393a87c3ea1f03060c1d03aaaaaa077b47bed458b5a585a0d06ccad0baaaaa162c183060c183060eaaa858b163c78f1f438a8060c183aa16a2c58b160b16071e1c7c1eaa260c18307541d45870e2c9870e2c587261c98f87c5e8783bdd522d850d83066ea8fb38f9faaa8580b1e3e0f82c58b17130f07261c993270f87c0ea81ded916291f3f5551f5e0c18307542c058f1e7c8162c58b0f44c3930e4c9931e3c78f1e3c78f2e5d168b45a2d168b1e0f540f9b3e0cf833e6cb973f1f8b97162c1058b1e0f1e3c3e1f0b87c162c4162c58b0e3c38f0e4c3930e4c3930ea2c387264c387264c264c384c78f1e3c78f1e3cb9747bed458b45a2d168b5459b160c583162c597170b858b162c58f1e3c7972e2d458b162c162c0e3c38f0e4c3930e4c3930ea2c387164c387162c3930e4d160d4da7cfaaaa7f38f1e3c79702f2d10aa3df6aa9f3e281b3754870ea936e1c98726a2d06aa9b063c18f5a7aaaaad43ea1f5179695562f550f81deeaaa55551efb55555555515078f1e3cd83066ea28aa5550e1d5549871e1c787060c9d44e0f554aa1c987260c1830742c5d528306ab5554c0ef74aaaaaaaaaaaaaa3c78f1e0c18306bcfaf179f5e552a871e1c783060c1870e4c9870e4c9d52a87261c9a8b5a55555aa1f50f41aaa0c183060e81b2ab55555503bdaaaa8f7daaaaaaaaa8a83c78f1f2f8a8060c183aa5550e1d5549871e1c7c1eaa260c1830754aa1c987262c1603360cd9f8fd47e6750f87c5eaa8783bdd5222aa8f1e6cdd047cf94a1c98727130f0b05951f97d47e3f0f8783060c1c0eaaa81ded1155478f8f9f280183a50e4c3930f44c58b01e2c787c19f367c19f363c78f1e7e2e5cfc5cb8f1e3c7972ea0a8aaaaaaa8f078f1e1f3e1f0b970f85d150387264c387264c38f0e3c3930e4c3930e4d54261c063c18f87d43ea2f5543e077baaa9555555555478f1e3cd83066ea26f154aa1c58f1e4c1832751389d552a93264c9d43ea1e0c1830740eaaaaa81ded555555555478f1e3e5f1500c1830754aa1c58f1f13aa8983060c1d52a93264c98f1e3c78f1e3c7972eaaaaaa3c78f1eddbb76e5dbb72eaa1c58f1e4c993264c99326aa4c99326a2d06aa9b1e3c78f6554b8f1e3c7972eaaaa3df6aaaaa2a0f1e3c7972eaaa1c3aaa930e3c38f0e4c3930e4c393550e4c393063c1831e0fd83060c183060c78f1e3c1c0cb838183060c183065d458b47bed4183162d06a0c1a0d068b45aaaa0c18b160c1a83060c183062cd83060c183060c18b2e2e170b162c58b1e3c78f060c180e1830183060cba3465c5a8b162c582c581c7871e0c183260c383060c183061c987261d45870e2c9870e2c587261c983063c7831e0c783060c78f1e3c78f1e3cb9b065c1972e6e2e5cdc5cba8b168f7da0d16a2c58b169b5162d168b5459b166c183060c583162d54183060c5835162c58b165c5c2e162c58b163c78f1e3d19b060cd9b366c370cd85d1a32e2d458b162c162c0e3c38f0e0c1930e1c9930e1c9930e4c3930ea2c387164c387162c3930e4e1f0f1e3c7d46e0750fbdd55555175162d1efb5a162d969168b665556858ba5aa166c583160c58ba165eaaa858b163c78f1f5143856ad5abaa16a2c58b160b16071e1c7d44e0f41c98727541d45870e2c9870e2c587261c9831e0cdc8ea1f517aaa2f03bdd554a2c5a3df68345ac2d69995166c59b060c183160c58baaa162e85cfaaaaaa162c5a31e3d19b060cdd450e2a85a8b162c582c581c787261c1832751383d55075161c38b261c38b161c987260c183075540ef7548341a8b16a37dccc0c583060c183f60d6a9685d55ee162c583060c1a3468d1d50b5162c58b160c183061c98727541d4587161c587261c9cd5283060c183060c183060c1d555555522d969458b41a0d9918f1e8d19f46233e8c060c183aa16a2c38f0e4c387264c387264c183060ea83a8b0e4c393a87c3ea4703060c1d03aaaaaa077b5162d1efb5a585a0d06ccad0baaaaa162c183166c183060c183060e8597aaaa162c5a31e3d1d0e2a0183060ea85a8b162c582c581c7872707aa8983060c1d5075161c38b261c38b161c987263c18f07ec183060e2f03065d1683415419f7e0cf9f060c183060c197a2e2c058f1e0c1830f830060d19f162c58b064c3830e4c3930e1c18f1e0fd83063c7972f178ba2c58b36a2d013e9b060cdaa6cfdb367cf9b366cbd171602c783cf60c19b3606cf9f119f162c58b0e4c3930e4c3930e1c7d1b070fbdd545d16c82ac7d9c7cfd46c18337542c058f1f507e0567e858b162e261e0e4c3930e1d1c3e2f45c1deea916c826c18337547e7c7cfd55545cb8b0167d18307411f3e50b162c5c4c3c1c987261c3c3e4703aa077b645a0c7cfd5547d783060c1d50b0167d19f82a0183a162c58b0f44c3930e4c3871e3c78f2e5cba2d168b45a2d16a03c3e9f367c19f067cd972e7e3f172e2c5820b167cf83c3e1f3e170f9f058b1058b162c38f0e4c3930e4c3930e4c3a8b0e1c9930e1c99303930e1c 25 33554431 11 2047
def hc_69_16 : Nat → Nat := unpackHintV5 0xca2145c59124c0dd2db8a60eb2fd6aaa8e1ca2e5ea9b1df2957d68911d188c0945835a2c7bb1ea7396076e195f69dd0f5d9b1158bd374cb3034831203f72303b98f6337a082cc1ae24c5ff1f0171192d7514f90d10fcff0cf103057ddd00015f 0x117878fa8dc0ea1f7baaaaaa2e3c7cc2e6aa878fa8a2a838f0e4ea2707a0e4c393aa0e4c3930e4c393060c183aaaa1e3c78f060c183aa1e3c78f060c183aa0e3c38f060c183aa0e4c3930e4c3931e3c78faa87d50f1e3c79b366cdd50f1e3c79b366cdd5071e1c787261c9d507261c987261c98f1e03c78f0f833e6cf833e6c78f1e3e82a2aaa8fa7c59f4f8b1e3c78f870eaaa1e0f1e3c3e1f22a0f9f0f81c393261c393261c7871e1c98727541c9872613261c2743e81d551b1e3c78faaaa1f7baa9a9858f1e3c7d551503c78f1f5507aa89871e1c787261c9d507261c987261c9d40c79b066cd83065cb83065cbd555555555231e3d1a35f8b7ea3166c18337548c78f468cfbf1f9f461b060cdd5071e1c9870e4c9870e4c987060c9d507261c987261c9831e0cd9f3e7cd9b0061b37555551408c78f466c183368d462d1a8c5d51f3e0f3e1b0194141107c3e071e1c987060c9870e4c9870e4c9d507261c984c380cd83367cf9f1e7c79f2e5c0185cbd555545043866c183367d3e2cfa7c5d51f0f86cd80c3754541f0f81db876e1c183361c39f261c39f27541db876e1f0e03360cdd50fa8bd551781deeaaa360c19b985cd551b060cdd451541dd87761c1833751383d5507761dd87761dd830740c18307540ef754bd1a35ebd1a31188c005f03c06031187e2058801c98726130e0307140c1830740c1830605503bdd5552f468b45a35ebd1a3468d1a33e7c46235ebc3930e4c3930e4c183060c183a8183060c183060eaaaaa81deeaaa918f1e8c183060d1abc5af518baa463c7a3060c183467c3e8caa5ebc38f0e4c183060c387264c387264ea83930e4c3930e4cf9f3e0c183060c18301830aaa8a0aa463c7a346a3168d462c183060ea8f9f079f28280180c883e1f038f0e4c387264c387264c183060ea83930e4c261c3e7c79f1e7cf83060c1830600c1832aa82a2a97c35f0cfa7c59f4f8b060c183aa3e1f2a0603060c8a83e7c3e076e1db870e7c9870e7c983060c1d5075e1db87c3950fa8183060e81d5555503bdcd4c2c183060eaa8a8060c183aa0eec3bb83d544c183060ea83bb0eec3bb0eec5a3c07aa9fa69f3eaa0c1a0c0625e62f171efb55551e3d0f80c18306930e87261c9a2d063c1aaa8306a0c5aa831e0fd83060c1aa8336a0c1a83060c7a31e3c78f54bb28381970703060c183060cba3df6aaaaa0d16aaaaaaa3c78f1ea8a03060c060c060c1832e8d197550e3c38f549a1d4183064c187060c183060c3930e4d543930e4c5a9b0683006aa7e9a7cfaa3c07a5e62f171efb55551e3d50fa06cd9b368cfaa4c3a1c987261c3a2d060c78f063c1fb55366d41835060c1aaa8b16a0c1aa8f1e3c78f1e3d52eca6c197065cb9b8b9737172e8f7daaaaaaa9b45aaaaa8f1e3c7aa286c183366cd9b0d9b0ba3465d5438f0e3d5268750e0c1930e1c9930e1c9930e4c393550e4c393168f01eaa7e9a5cbaa9b0683360cdb4c40f7daaaa8f1e87caa49874f870e4c393264c38745b0f95569616aa3d18f1e3c7aa6d06b51b81d43ef754ab175a5aaaa2e8f7daaaaac8b55555551e3c78f5452a2856ad5abaa550e3c38f549a1d6a2707a0e4c393aa550e4c39316a6c1a7c78f46aa7e9a7cfaa5c0bb4c40f7daaaaa1f0d9baa498743930e4d16831e0cdaa6d06b23a87d2aad2d3d562f5545d5996077baaa91efb55555555555518f1e8d514360c19ba8a2a95438f0e4d5268750e0c193a89c1eaa9543930e4c183060eaa858b5060d56aa9a95555555555555518f1e8c183060d19f46233e8caa550e3c393060c1830e1c9930e1c993aa550e4c39345b50fa91aaacb4aa0c18306a8341ad03aa5665aaaa077b47bed55555555555463c7a354525f1500c1830754aa1c78726a9343ac1eaa260c1830754aa1c987262c058f067c1bf060c19f067c183063c1fb060c183060c183463e2f178bc0c19744551e3d4187c50e4c393064c3831602c18f1e0fd83360cd83067cdcb162c59f367cd9b363c7c5e2e5cbc5e2e889b45aa8f1ea6c3e287261c987261c98b0163e3f33a8fc7ea463c19b066e360e1f7baaaa8ba22a8f1eb07c50e4c39389878580b066c19b470f8fd2ea3f1fa8bd17aa077baa44553e8d60f8a1c98727130f0b0170f91d47e3f51f9783060c1c0eaaa81ded1154fa358f9f28143930e4c3d13162c0787c58f1e7c19f367c19f363c7973f172e7e2e5cb9755545055553e7c1e2a7c3e170f88a81c787261c393261c393261c987261c98726aa130e22d1e3d5368351e3cbaa5d94b9747bed55555551e3d5142e5d5438f0e4d5268750e4c3930e4c393550e4c393 24 16777215 10 1023
def hc_69_17 : Nat → Nat := unpackHintV5 0x800e6d76ae586ca68262f26d5e612454069749fe823fda89367a5832191825bf1720854e147f020e7183081d95000207 0x366c0787cd83060c183060c060c078f2e7e2e5cfc5cb83060c18f1f0cfa7c59f4f8b060c1832f0cb9f3e0f0183060c060c185c3e1f0f81c787261c393261c393260c183061c987261c98726130e03360c18f07ec183060c183063c79707032e0e060c183060c1971e3c1a0c5834183060c1832e5c78f060c180c180c183065cb871e1c983060c9830e0c183060c187261c987261c987261c9831e0c78f0783060c0d9b0061b363c78f1e6c1832e7e2e5cfc5cb8f1e3c79b060cd9f4f8b3e9f165e1971e0f1e3c366c061b1e3c7970f87c3e071e1c787060c9870e4c9870e4c987261c987261c984c380c783f60c18f1e0c1831e6c78f1e3c79b060cb8f87971f0f1e3c78f1e6c183363d1e2c7a3c5972e3c78f1e6c183363c78f078f0b970e3c38f0e0c1930e1c7930e1c78f0e4c3930e4c3930e4c393aaaa060c183aa1e3c78f060c183aa1e3c78f060c183aa0e3c38f060c1830e4c3930e4c3931e3c078f1e030600c1830183060cfc5cb9f8b971e3c78f060c1833e9f167d3e2c78f1e3c183060cbc32e0c1831e0f1e3c0603060c2e1f0f9f0f81c393261c393261c7871e0c183061c987261c9872613261c260c18f060c183060c1831e0fd830703060e060cb971e3c78f060c1830683060d062c78f1e3c183060cb97060c060c183c78f1e0c183065cb830e0c183060c9871e1c783060c187261c987261c987261c9831e0cd830603c3e0c78f0061b1e3c797360c1973f172e7e2e5c78f866c183367d3e2cfa7c597865cf9f0786cd80c366cd9b2e1f3e1f0f9f038f0e4c383064c387264c387264c3930e4c3930e4c0e4c38701831e3c18f07ec183063c78f1e3cb9b065c1972e6e2e5cdc5cb8f1e6c183366d362cda6c5972e3c79b060cd9b366c366c2e5c38f0e4c383064c387264c387264c3930e4c3930e4c3930e4c7c3c07d51f671f3f540c1c0c060fbdd55540d16c8b458f1f07c060c183898783930e4e1f031e0eaa8183a065ea818f07ec183060ea819ba060e8183070fbdd5555038bd55555038b8f463c78f1f30b9a0683160d060c183060ea87a31e3c78fa8a018306030603060c1d533661c7871f51383d03060c9830e0c183060c1d507261c987261c98f81838d8381803aa3ece3e7ea1e03c7deeaa2f548b645a2c78fa83f01b366cdd2f3f130f07261c9870f0f81831e3c18f063ea8d9ba060e8183075545cbd0307543c78f87deeaaaaaa2f17a8bc5eaa878f1e3e617346c183366d362cda6c5d50f1e3c7d4506c183366cd9b0d9b2a97af661c7871f51383d07060c9870e4c9870e4c9d507261c987261c98f01e3c19f06fc183065c197060c18f07ec183060c183060e22aa9168b45a0c78fa061f28f870e4c393264c1930e0c3871e03c18f1e0fd83360cd83067cddb2e5cb972e5cb972e3c7c4545e2f548b45a2d163c7d1b0f947c387261c993261c987261c3972e03c2e5c78f3e0cf9b3e0cf9baaa8a0aa1e3e19f4f8b3e9f170e1d51f3e0f2a3e1f22a0f87c0e3c3930e7c387264c387267c9930e4c393aa0e4c39303930e1c 24 16777215 10 1023
def nh_69 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_69_17 (Nat.sub p 544)) (hc_69_16 (Nat.sub p 512)) (Nat.blt p 544)) (hc_69_15 (Nat.sub p 480)) (Nat.blt p 512)) (Bool.rec (hc_69_14 (Nat.sub p 448)) (hc_69_13 (Nat.sub p 416)) (Nat.blt p 448)) (Nat.blt p 480)) (Bool.rec (Bool.rec (hc_69_12 (Nat.sub p 384)) (hc_69_11 (Nat.sub p 352)) (Nat.blt p 384)) (Bool.rec (hc_69_10 (Nat.sub p 320)) (hc_69_9 (Nat.sub p 288)) (Nat.blt p 320)) (Nat.blt p 352)) (Nat.blt p 416)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_69_8 (Nat.sub p 256)) (hc_69_7 (Nat.sub p 224)) (Nat.blt p 256)) (hc_69_6 (Nat.sub p 192)) (Nat.blt p 224)) (Bool.rec (hc_69_5 (Nat.sub p 160)) (hc_69_4 (Nat.sub p 128)) (Nat.blt p 160)) (Nat.blt p 192)) (Bool.rec (Bool.rec (hc_69_3 (Nat.sub p 96)) (hc_69_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (hc_69_1 (Nat.sub p 32)) (hc_69_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 128)) (Nat.blt p 288)
def f_69 : Nat → Nat × Nat := unpackForestF 0x45c554018bf161450062dc52db2292da00c5789ca280314e252ab0fc6f88ca2c3f18e208df1046387caa802d7e1b8d90dc6086cb6802d5e178dd0c46285ca2802d3e142970a147846b14255ba112ba00b4783caac011be0d28b0046382caac00dbe0928b0034f81eb4400d1e018df00c63805b7c02d3e0168f001550052fbf117dfcce0fe26c7e22bbf317df98aefc1250052dbec515ed69efa5707b5a3be2d3df168ef696d7b9a7bdcd1ded0c000a5777eb7bbf58ddf8deefc5f79b383cc9b1df8aef056f782b1bc11bde08bef045777c9280294dd38dcedc6476cb2ba6dbdd88f8ec17d74db3ba9189d46deea36774ca280293dd14c8e4c6f73d3e39319dc94dce546f72a33b94989c924a00a4b714a5b8c149c528edbd6270ab4384595b76dedf94f6fca1b7b5c1bd2fadbb676e6b7372dbdb96cedb95d6dc2800291db54c8d546f6cd3e35519db06dad83656a9373571bdad4e0d5c676ad3135449401486d4264672b7b4c9519cad6d227c672b3b449519cac6ce26e676b7b3b59d9d4c4ce1250051db331a1992cac156f65a2c32c55582ad6ca13f64a383245f582acec745863e2831c55582ac6c4d69626b0b124ed8926ec146260eb7b075ad83acec1d6360e373045340146eb3c6f59e31acf16d678aeb3b6f59dabaced3d79ad0b3b4759d37ace98d674b6b3a575ca322e4d9d6749eb826459d25add5a16748eb626459d21ad499167476b446859d1b80257d548beb216c5522bac4551546beb0134551adabc5595cce0ae16c551abab28d159268aa35355c9a2a8d2d552b8aa347004ada7ad3d51ae09eb4753e3e27a93d4d4f89ea4b529a7a9413949ae09ea4751d3e27a90d454f89ea3b509ada84d4d418e09ea374f9a7a7cd1d3d0c0009574ed322335bd394a88cd634dd322331bd198be9a16c4662ba64991196de98234465b1a5c551196be96134465ada519c1284d89416c465aba4a92d2548e92134465a9a444d1196968fa5c47cae232d1d1d49e8c96e469a7a34d1d190300095341a3722d191066de8a47c419b3a25191064de8825441935a1d1f1064ce8625441931a149510647683c7241e2c20c8dc0129e821643ce37a045f0f38ce801643cdb79fc4d0f36d67e17c3cdb39f28d0f926879b633dc9a1e6d2cf52b879b473ccb700252cf049678247332b11dd5a0cc6de7324f3adae1cc92ce648e7424c39daa1cc90ce5ae06636738eb41989bce14ac6fe7037d361989acdc69e6e34736eb819899cd8ce06c26c331319ac9b0cc4766736f34e3e19cdacce6ce6836c33e3a19cd8ccd8c066237004a3994590b28de6417c2ca3398c590b26de621342c9b59829f0c12f8593672f92597c91cbd268593632ec9a164d2cb92885b5722d92e16c570b268e59b6d2cdb29645b8012865816424eb795c55093ad65617c24eb3952950a92a849d6329cb2126dbca526849b6b28cbe126d9ca04685013424db193c550936be4e13424dad9345b0936ae4ba3425c9a126d4c9449e4a24324cb70024ec918d039d6f23e2c0e75ac8d8e039d6722e2c0e758c8747643a3721c1d0e7188858d039a6f20d2e0e69ac818e039a671fd2e0e698c7c8e43e4581cd2f8f4970734b63c4601cd2b8ec91074ae43a25c1cd298024dc714c82d56f1bd2a0b55ac6c8f83627c16ab38d49505aac632d7f19d2a0cb5cc654c82d46f186be0c35c0614f82d46717ebf0b517c5cce42e26c16a2b8b49b80125e2c164106b78ac55041ad629c7c14cbe08359c504a828154106b189c590418de2557c12ab80945f0418ce2457e1062f88c5b0418ae2096e109a7884d1c410300092b0fdb404f5bc3d6b013d6b0e63e07492c396e013d670ddac04f58c34afe1a36809e3785f5f02fae01825b0bdb804f19c2dafc13c5f0adb004f15c28ad21456109db100249c252c805d6f08caa0175ac1f8f80fa7c07cbe01759c1c69e0e34706caa01758c192c805c6f052be0295c0144f80a17c02e338255f80b8be081540373901a9b00d2d805c5702cb700248c010b6008530042580210c010760082b0041180206c010260003f 10 11
def ch_69 : Nat → Bool := dagCheckNodeV5 fullMask g_69 ep_69 5 31 bds_69 559 (dagTraceF fullMask rootStock 11 f_69) cur_69 nh_69
set_option maxHeartbeats 0 in
theorem rc_69 : dagCheckRootsV5 fullMask g_69 ep_69 5 31 559 bds_69 (dagTraceF fullMask rootStock 11 f_69) (cur_69 0) (nh_69 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_0 : treeBlockF 0 32 ch_69 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_1 : treeBlockF 32 64 ch_69 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_2 : treeBlockF 64 96 ch_69 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_3 : treeBlockF 96 128 ch_69 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_4 : treeBlockF 128 160 ch_69 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_5 : treeBlockF 160 192 ch_69 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_6 : treeBlockF 192 224 ch_69 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_7 : treeBlockF 224 256 ch_69 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_8 : treeBlockF 256 288 ch_69 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_9 : treeBlockF 288 320 ch_69 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_10 : treeBlockF 320 352 ch_69 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_11 : treeBlockF 352 384 ch_69 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_12 : treeBlockF 384 416 ch_69 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_13 : treeBlockF 416 448 ch_69 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_14 : treeBlockF 448 480 ch_69 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_15 : treeBlockF 480 512 ch_69 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_16 : treeBlockF 512 544 ch_69 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69_17 : treeBlockF 544 559 ch_69 = true := by decide +kernel
theorem nj_69_1 : ∀ i, 0 ≤ i → i < 64 → ch_69 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_69_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_69_1 h1 h2)
theorem nj_69_2 : ∀ i, 0 ≤ i → i < 96 → ch_69 i = true := block_join nj_69_1 (fun _ h1 h2 => treeBlockF_at nb_69_2 h1 h2)
theorem nj_69_3 : ∀ i, 0 ≤ i → i < 128 → ch_69 i = true := block_join nj_69_2 (fun _ h1 h2 => treeBlockF_at nb_69_3 h1 h2)
theorem nj_69_4 : ∀ i, 0 ≤ i → i < 160 → ch_69 i = true := block_join nj_69_3 (fun _ h1 h2 => treeBlockF_at nb_69_4 h1 h2)
theorem nj_69_5 : ∀ i, 0 ≤ i → i < 192 → ch_69 i = true := block_join nj_69_4 (fun _ h1 h2 => treeBlockF_at nb_69_5 h1 h2)
theorem nj_69_6 : ∀ i, 0 ≤ i → i < 224 → ch_69 i = true := block_join nj_69_5 (fun _ h1 h2 => treeBlockF_at nb_69_6 h1 h2)
theorem nj_69_7 : ∀ i, 0 ≤ i → i < 256 → ch_69 i = true := block_join nj_69_6 (fun _ h1 h2 => treeBlockF_at nb_69_7 h1 h2)
theorem nj_69_8 : ∀ i, 0 ≤ i → i < 288 → ch_69 i = true := block_join nj_69_7 (fun _ h1 h2 => treeBlockF_at nb_69_8 h1 h2)
theorem nj_69_9 : ∀ i, 0 ≤ i → i < 320 → ch_69 i = true := block_join nj_69_8 (fun _ h1 h2 => treeBlockF_at nb_69_9 h1 h2)
theorem nj_69_10 : ∀ i, 0 ≤ i → i < 352 → ch_69 i = true := block_join nj_69_9 (fun _ h1 h2 => treeBlockF_at nb_69_10 h1 h2)
theorem nj_69_11 : ∀ i, 0 ≤ i → i < 384 → ch_69 i = true := block_join nj_69_10 (fun _ h1 h2 => treeBlockF_at nb_69_11 h1 h2)
theorem nj_69_12 : ∀ i, 0 ≤ i → i < 416 → ch_69 i = true := block_join nj_69_11 (fun _ h1 h2 => treeBlockF_at nb_69_12 h1 h2)
theorem nj_69_13 : ∀ i, 0 ≤ i → i < 448 → ch_69 i = true := block_join nj_69_12 (fun _ h1 h2 => treeBlockF_at nb_69_13 h1 h2)
theorem nj_69_14 : ∀ i, 0 ≤ i → i < 480 → ch_69 i = true := block_join nj_69_13 (fun _ h1 h2 => treeBlockF_at nb_69_14 h1 h2)
theorem nj_69_15 : ∀ i, 0 ≤ i → i < 512 → ch_69 i = true := block_join nj_69_14 (fun _ h1 h2 => treeBlockF_at nb_69_15 h1 h2)
theorem nj_69_16 : ∀ i, 0 ≤ i → i < 544 → ch_69 i = true := block_join nj_69_15 (fun _ h1 h2 => treeBlockF_at nb_69_16 h1 h2)
theorem nj_69_17 : ∀ i, 0 ≤ i → i < 559 → ch_69 i = true := block_join nj_69_16 (fun _ h1 h2 => treeBlockF_at nb_69_17 h1 h2)
theorem nc_69 : ∀ i, 0 ≤ i → i < 559 → ch_69 i = true := nj_69_17
theorem lb_69 : LowerBin fullMask rootStock g_69 12 :=
  lowerDagV5 (kn_cons lb_67 (kn_cons lb_64 (kn_cons lb_65 (kn_cons lb_62 (kn_cons lb_66 (kn_cons lb_60 (kn_cons lb_59 (kn_cons lb_28 (kn_cons lb_61 (kn_cons lb_63 (kn_cons lb_68 (kn_cons lb_53 (kn_cons lb_20 (kn_cons lb_52 (kn_cons lb_0 (kn_cons lb_12 (kn_cons lb_21 (kn_cons lb_43 (kn_cons lb_50 (kn_cons lb_11 (kn_cons lb_36 (kn_cons lb_46 (kn_cons lb_30 (kn_cons lb_34 (kn_cons lb_49 (kn_cons lb_33 (kn_cons lb_54 (kn_cons lb_55 (kn_cons lb_3 (kn_cons lb_29 (kn_cons lb_23 (kn_cons lb_35 (kn_cons lb_45 (kn_nil)))))))))))))))))))))))))))))))))) rc_69 nc_69 (by decide +kernel)

def wg : List Gate := [⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [4, 9]⟩, ⟨GateOp.and, [5, 10]⟩, ⟨GateOp.and, [8, 10]⟩, ⟨GateOp.and, [8, 11]⟩, ⟨GateOp.or, [12, 14]⟩, ⟨GateOp.or, [13, 15]⟩, ⟨GateOp.and, [16, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 4004046848) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276676776 * 2 ^ 32 + 4004046848)) (13 - 1) := by
  rw [show canon fullMask (4276676776 * 2 ^ 32 + 4004046848) = g_69 by decide]
  exact lb_69

end PEqualNP.Outside.L_meta_47881

theorem PEqualNP.Outside.L_meta_47881 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676776 * 2 ^ 32 + 4004046848) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 4004046848) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_47881.table2_from_lowerBin (4276676776 * 2 ^ 32 + 4004046848) 13 PEqualNP.Outside.L_meta_47881.root_lb PEqualNP.Outside.L_meta_47881.wg 18 rfl PEqualNP.Outside.L_meta_47881.wfits PEqualNP.Outside.L_meta_47881.weval
