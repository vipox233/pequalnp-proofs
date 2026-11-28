import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_47825

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

def m_0 : Nat := 0xf0f000000000000
def s_0 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_0 : Nat := 0x107000000000000
def ep_0 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
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

def m_1 : Nat := 0x5050505000000000
def s_1 : List Nat := [0x1010101000000000, 0x50005000000000, 0x505000000000]
def g_1 : Nat := 0x10105000000000
def ep_1 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000000000000000000
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

def m_2 : Nat := 0x5500550000000000
def s_2 : List Nat := [0x1100110000000000, 0x500050000000000, 0x550000000000]
def g_2 : Nat := 0x100150000000000
def ep_2 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000000000000000000
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

def m_3 : Nat := 0x3300330000000000
def s_3 : List Nat := [0x1100110000000000, 0x300030000000000, 0x330000000000]
def g_3 : Nat := 0x100130000000000
def ep_3 : Nat := 0x1200000000000000000000000000010002000000000000000000000000000100100000000000
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

def m_4 : Nat := 0xf000f0000000000
def s_4 : List Nat := [0x500050000000000, 0x300030000000000, 0xf0000000000]
def g_4 : Nat := 0x100070000000000
def ep_4 : Nat := 0x600000000000000000000000000000000000000000001000200000000000100040000000000
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

def m_5 : Nat := 0xff000000000000
def s_5 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_5 : Nat := 0x17000000000000
def ep_5 : Nat := 0x600000000000000120000000000000014000000000000
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

def m_6 : Nat := 0x4040404040404040
def s_6 : List Nat := [0x40004000400040, 0x404000004040, 0x40404040]
def g_6 : Nat := 0x4000404040
def ep_6 : Nat := 0x40400000000040000040000000004000400000000000000000000000000000000000000000000000000000
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

def m_7 : Nat := 0x4444444400000000
def s_7 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_7 : Nat := 0x4044400000000
def ep_7 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
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

def m_8 : Nat := 0x3300000033000000
def s_8 : List Nat := [0x1100000011000000, 0x300000003000000, 0x33000000]
def g_8 : Nat := 0x100000013000000
def ep_8 : Nat := 0x1200000000000000000000000000000000000000010000000200000000000000000000000100000010000000
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

def m_9 : Nat := 0xff0000000000
def s_9 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_9 : Nat := 0x170000000000
def ep_9 : Nat := 0x6000000000000001200000000000000140000000000
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

def m_10 : Nat := 0x5050000050500000
def s_10 : List Nat := [0x1010000010100000, 0x50000000500000, 0x50500000]
def g_10 : Nat := 0x10000010500000
def ep_10 : Nat := 0x1040000000000000000000000010000000400000000000000000000000100000100000000000000000000000
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

def m_11 : Nat := 0x5555000000000000
def s_11 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_11 : Nat := 0x115000000000000
def ep_11 : Nat := 0x14000000000000010400000000000001100000000000000000000000000000
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

def m_12 : Nat := 0x3333000000000000
def s_12 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_12 : Nat := 0x113000000000000
def ep_12 : Nat := 0x12000000000000010200000000000000000000000000000110000000000000
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

def m_13 : Nat := 0x5000500050005000
def s_13 : List Nat := [0x1000100010001000, 0x500000005000, 0x50005000]
def g_13 : Nat := 0x100010005000
def ep_13 : Nat := 0x1000400000001000000040000000000000000000000000000000000000001000100000000000000000000000
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

def m_14 : Nat := 0xcc330000cc33
def s_14 : List Nat := [0x441100004411, 0x3300000033, 0xc0300000c03, 0xcc33]
def g_14 : Nat := 0x41300004433
def ep_14 : Nat := 0x402000000000000000000000000000000000000004020000000000000000000000000000041000004400
def bds_14 : List (Nat × List Nat × Nat × Nat) := []
def cur_14 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb25935b2a73294c80f 7 127 3 7 6 63 9 511
def nh_14 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_14 : Nat → Nat × Nat := unpackForestF 0x1b6c86a33194c80f 3 6
def ch_14 : Nat → Bool := dagCheckNodeV5 m_14 g_14 ep_14 1 1 bds_14 7 (dagTraceF m_14 s_14 4 f_14) cur_14 nh_14
set_option maxHeartbeats 0 in
theorem rc_14 : dagCheckRootsV5 m_14 g_14 ep_14 1 1 7 bds_14 (dagTraceF m_14 s_14 4 f_14) (cur_14 0) (nh_14 0) s_14 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_14 : treeBlockF 0 7 ch_14 = true := by decide +kernel
theorem nc_14 : ∀ i, 0 ≤ i → i < 7 → ch_14 i = true := fun _ h1 h2 => treeBlockF_at nb_14 h1 h2
theorem lb_14 : LowerBin m_14 s_14 g_14 5 :=
  lowerDagV5 (kn_nil) rc_14 nc_14 (by decide +kernel)

def m_15 : Nat := 0xc3c3c3c300000000
def s_15 : List Nat := [0x4141414100000000, 0x303030300000000, 0xc300c300000000, 0xc3c300000000]
def g_15 : Nat := 0x103034300000000
def ep_15 : Nat := 0x240000000000002004000000000000000000000000000000000000000000100004000000000
def bds_15 : List (Nat × List Nat × Nat × Nat) := []
def cc_15_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682b1560ac148a80d009c3382704e09c1382704648c1182304607c8f81f03a2740e81b1341680c841c001 0x793875346c2c68245c305d444f484b40453c4130384c3444302c2c24254c2144184c144408100924fe3ffa3be637d233c53fb93bb537ad33a92fa52b91277d23703f643b60375833542f502b3c2728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_15_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707062606052494841404040404040242020202004 0xf54cf140ec4ce840e128dd24d828d424cc38c834c018bc14b130b244a3489f40983c94308d4c894484188014 8 255 3 7 10 1023 16 65535
def cur_15 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_15_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_15_0 p) (Nat.blt p 32)
def hc_15_0 : Nat → Nat := unpackHintV5 0xfa27b13925c04dc2654aea160aa084d1a50d28090248023090c68604112080fc47833a11c08bd25a22b111246902a50d400b0002 0x0 13 8191 5 31
def hc_15_1 : Nat → Nat := unpackHintV5 0xa2351027893c09a24a1a501204900461218d0447e23649a08c845292140e145102230e187003041800a1038c1c00a20500188006 0x0 13 8191 5 31
def hc_15_2 : Nat → Nat := unpackHintV5 0x6 0x0 6 63 3 7
def nh_15 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_15_2 (Nat.sub p 64)) (hc_15_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_15_0 p) (Nat.blt p 32)
def f_15 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c838c834053fbc18bc14053b0537b2440533052f052b97489740943c94300527814c814480188014052375387534043f682c6824043b04375d440433042f042b43484340413c413004272c4c2c442c2c2c240423214c2144041f144c1444041b041709240413000f 6 10
def ch_15 : Nat → Bool := dagCheckNodeV5 m_15 g_15 ep_15 1 1 bds_15 64 (dagTraceF m_15 s_15 5 f_15) cur_15 nh_15
set_option maxHeartbeats 0 in
theorem rc_15 : dagCheckRootsV5 m_15 g_15 ep_15 1 1 64 bds_15 (dagTraceF m_15 s_15 5 f_15) (cur_15 0) (nh_15 0) s_15 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_15_0 : treeBlockF 0 32 ch_15 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_15_1 : treeBlockF 32 64 ch_15 = true := by decide +kernel
theorem nj_15_1 : ∀ i, 0 ≤ i → i < 64 → ch_15 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_15_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_15_1 h1 h2)
theorem nc_15 : ∀ i, 0 ≤ i → i < 64 → ch_15 i = true := nj_15_1
theorem lb_15 : LowerBin m_15 s_15 g_15 6 :=
  lowerDagV5 (kn_nil) rc_15 nc_15 (by decide +kernel)

def m_16 : Nat := 0xc0c0c0c030303030
def s_16 : List Nat := [0x4040404010101010, 0x30303030, 0xc000c000300030, 0xc0c000003030]
def g_16 : Nat := 0x4010101030
def ep_16 : Nat := 0x40000000200000004000000020000000000000000000000000000000000000004010101000
def bds_16 : List (Nat × List Nat × Nat × Nat) := []
def cur_16 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb2cb2cd2e92972252132000f 7 127 3 7 9 511 12 4095
def nh_16 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_16 : Nat → Nat × Nat := unpackForestF 0x32eb2c32932232132000f 3 9
def ch_16 : Nat → Bool := dagCheckNodeV5 m_16 g_16 ep_16 1 1 bds_16 7 (dagTraceF m_16 s_16 4 f_16) cur_16 nh_16
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsV5 m_16 g_16 ep_16 1 1 7 bds_16 (dagTraceF m_16 s_16 4 f_16) (cur_16 0) (nh_16 0) s_16 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16 : treeBlockF 0 7 ch_16 = true := by decide +kernel
theorem nc_16 : ∀ i, 0 ≤ i → i < 7 → ch_16 i = true := fun _ h1 h2 => treeBlockF_at nb_16 h1 h2
theorem lb_16 : LowerBin m_16 s_16 g_16 5 :=
  lowerDagV5 (kn_nil) rc_16 nc_16 (by decide +kernel)

def m_17 : Nat := 0xcc00cc00330033
def s_17 : List Nat := [0x44004400110011, 0x330033, 0xc000c00030003, 0xcc00000033]
def g_17 : Nat := 0x4004400130033
def ep_17 : Nat := 0x40000000200000000000000000000400000002000000000000000000000004004400100000
def bds_17 : List (Nat × List Nat × Nat × Nat) := []
def cur_17 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb24b24d2d92a72652532400f 7 127 3 7 9 511 12 4095
def nh_17 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_17 : Nat → Nat × Nat := unpackForestF 0x32db2432a32632532400f 3 9
def ch_17 : Nat → Bool := dagCheckNodeV5 m_17 g_17 ep_17 1 1 bds_17 7 (dagTraceF m_17 s_17 4 f_17) cur_17 nh_17
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsV5 m_17 g_17 ep_17 1 1 7 bds_17 (dagTraceF m_17 s_17 4 f_17) (cur_17 0) (nh_17 0) s_17 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17 : treeBlockF 0 7 ch_17 = true := by decide +kernel
theorem nc_17 : ∀ i, 0 ≤ i → i < 7 → ch_17 i = true := fun _ h1 h2 => treeBlockF_at nb_17 h1 h2
theorem lb_17 : LowerBin m_17 s_17 g_17 5 :=
  lowerDagV5 (kn_nil) rc_17 nc_17 (by decide +kernel)

def m_18 : Nat := 0xcc00cc0033003300
def s_18 : List Nat := [0x4400440011001100, 0x33003300, 0xc000c0003000300, 0xcc0000003300]
def g_18 : Nat := 0x40013001300
def ep_18 : Nat := 0x400000000000000000000000000000004000200020000000000000000000000040010001000
def bds_18 : List (Nat × List Nat × Nat × Nat) := []
def cur_18 : Nat → List (Nat × Nat) := unpackCursorV5 0xb146850932244890e8701 0x54a1e787302904cfa264d2e591207442a00f 7 127 3 7 9 511 13 8191
def nh_18 : Nat → Nat := unpackHintV5 0xe81b12e45c0a8912201400800f082e002 0x0 11 2047 5 31
def f_18 : Nat → Nat × Nat := unpackForestF 0x54a067c33279e0cb864421d298148042a00f 4 9
def ch_18 : Nat → Bool := dagCheckNodeV5 m_18 g_18 ep_18 1 1 bds_18 11 (dagTraceF m_18 s_18 4 f_18) cur_18 nh_18
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsV5 m_18 g_18 ep_18 1 1 11 bds_18 (dagTraceF m_18 s_18 4 f_18) (cur_18 0) (nh_18 0) s_18 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_18 : treeBlockF 0 11 ch_18 = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 11 → ch_18 i = true := fun _ h1 h2 => treeBlockF_at nb_18 h1 h2
theorem lb_18 : LowerBin m_18 s_18 g_18 5 :=
  lowerDagV5 (kn_nil) rc_18 nc_18 (by decide +kernel)

def m_19 : Nat := 0xcccc00003333
def s_19 : List Nat := [0x444400001111, 0x3333, 0xc0c00000303, 0xcc00000033]
def g_19 : Nat := 0x44400001333
def ep_19 : Nat := 0x4000000020000004000000020000000000000000000000044400001000
def bds_19 : List (Nat × List Nat × Nat × Nat) := []
def cur_19 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb24b24d2d92a72652532400f 7 127 3 7 9 511 12 4095
def nh_19 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_19 : Nat → Nat × Nat := unpackForestF 0x32db2432a32632532400f 3 9
def ch_19 : Nat → Bool := dagCheckNodeV5 m_19 g_19 ep_19 1 1 bds_19 7 (dagTraceF m_19 s_19 4 f_19) cur_19 nh_19
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsV5 m_19 g_19 ep_19 1 1 7 bds_19 (dagTraceF m_19 s_19 4 f_19) (cur_19 0) (nh_19 0) s_19 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19 : treeBlockF 0 7 ch_19 = true := by decide +kernel
theorem nc_19 : ∀ i, 0 ≤ i → i < 7 → ch_19 i = true := fun _ h1 h2 => treeBlockF_at nb_19 h1 h2
theorem lb_19 : LowerBin m_19 s_19 g_19 5 :=
  lowerDagV5 (kn_nil) rc_19 nc_19 (by decide +kernel)

def m_20 : Nat := 0xcccc000033330000
def s_20 : List Nat := [0x4444000011110000, 0x33330000, 0xc0c000003030000, 0xcc000000330000]
def g_20 : Nat := 0x4000013130000
def ep_20 : Nat := 0x4000000000000000400000202000000000000000000000004000010100000
def bds_20 : List (Nat × List Nat × Nat × Nat) := []
def cur_20 : Nat → List (Nat × Nat) := unpackCursorV5 0xb146850932244890e8701 0x54a1e787302904cfa264d2e591207442a00f 7 127 3 7 9 511 13 8191
def nh_20 : Nat → Nat := unpackHintV5 0xe81b12e45c0a8912201400800f082e002 0x0 11 2047 5 31
def f_20 : Nat → Nat × Nat := unpackForestF 0x54a067c33279e0cb864421d298148042a00f 4 9
def ch_20 : Nat → Bool := dagCheckNodeV5 m_20 g_20 ep_20 1 1 bds_20 11 (dagTraceF m_20 s_20 4 f_20) cur_20 nh_20
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV5 m_20 g_20 ep_20 1 1 11 bds_20 (dagTraceF m_20 s_20 4 f_20) (cur_20 0) (nh_20 0) s_20 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_20 : treeBlockF 0 11 ch_20 = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 11 → ch_20 i = true := fun _ h1 h2 => treeBlockF_at nb_20 h1 h2
theorem lb_20 : LowerBin m_20 s_20 g_20 5 :=
  lowerDagV5 (kn_nil) rc_20 nc_20 (by decide +kernel)

def m_21 : Nat := 0xcc003300cc0033
def s_21 : List Nat := [0x44001100440011, 0x3300000033, 0xc0003000c0003, 0xcc0033]
def g_21 : Nat := 0x4001300440033
def ep_21 : Nat := 0x40002000000000000000000000000000000000000400020000000000000000000000000004001000440000
def bds_21 : List (Nat × List Nat × Nat × Nat) := []
def cur_21 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb25935b2a73294c80f 7 127 3 7 6 63 9 511
def nh_21 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_21 : Nat → Nat × Nat := unpackForestF 0x1b6c86a33194c80f 3 6
def ch_21 : Nat → Bool := dagCheckNodeV5 m_21 g_21 ep_21 1 1 bds_21 7 (dagTraceF m_21 s_21 4 f_21) cur_21 nh_21
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV5 m_21 g_21 ep_21 1 1 7 bds_21 (dagTraceF m_21 s_21 4 f_21) (cur_21 0) (nh_21 0) s_21 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21 : treeBlockF 0 7 ch_21 = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 7 → ch_21 i = true := fun _ h1 h2 => treeBlockF_at nb_21 h1 h2
theorem lb_21 : LowerBin m_21 s_21 g_21 5 :=
  lowerDagV5 (kn_nil) rc_21 nc_21 (by decide +kernel)

def m_22 : Nat := 0x4444444411111111
def s_22 : List Nat := [0x11111111, 0x404040401010101, 0x44004400110011, 0x444400001111]
def g_22 : Nat := 0x4044411111111
def ep_22 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
def bds_22 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cur_22 : Nat → List (Nat × Nat) := fun _ => []
def nh_22 : Nat → Nat := unpackHintV5 0x4 0x1 6 63 3 7
def f_22 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV5 m_22 g_22 ep_22 1 1 0 bds_22 (dagTraceF m_22 s_22 4 f_22) (cur_22 0) (nh_22 0) s_22 4 = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_22 g_22 ep_22 1 1 bds_22 0 (dagTraceF m_22 s_22 4 f_22) cur_22 nh_22 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_22 : LowerBin m_22 s_22 g_22 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_22 nc_22 (by decide +kernel)

def m_23 : Nat := 0x303030330303030
def s_23 : List Nat := [0x101010110101010, 0x30303030, 0x3000300300030, 0x30300003030]
def g_23 : Nat := 0x103030310101030
def ep_23 : Nat := 0x200000000200002000000000020000000000000000000000000000000000100000010101000
def bds_23 : List (Nat × List Nat × Nat × Nat) := []
def cur_23 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58b12a44874e0701 0x192440a192430a123434d263a88d9d3a54d883a10d800f 7 127 3 7 10 1023 14 16383
def nh_23 : Nat → Nat := unpackHintV5 0x340c0b00c02c2b02c0b02c015002 0x0 10 1023 5 31
def f_23 : Nat → Nat × Nat := unpackForestF 0xc7463629d6490a6ce3469a10e886c00f 3 10
def ch_23 : Nat → Bool := dagCheckNodeV5 m_23 g_23 ep_23 1 1 bds_23 10 (dagTraceF m_23 s_23 4 f_23) cur_23 nh_23
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV5 m_23 g_23 ep_23 1 1 10 bds_23 (dagTraceF m_23 s_23 4 f_23) (cur_23 0) (nh_23 0) s_23 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_23 : treeBlockF 0 10 ch_23 = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 10 → ch_23 i = true := fun _ h1 h2 => treeBlockF_at nb_23 h1 h2
theorem lb_23 : LowerBin m_23 s_23 g_23 5 :=
  lowerDagV5 (kn_nil) rc_23 nc_23 (by decide +kernel)

def m_24 : Nat := 0xffff00000000
def s_24 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_24 : Nat := 0x175700000000
def ep_24 : Nat := 0x4000000000000006020000000000001202000000000000145400000000
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_24 : Nat → List (Nat × Nat) := fun _ => []
def nh_24 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_24 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV5 m_24 g_24 ep_24 1 1 0 bds_24 (dagTraceF m_24 s_24 4 f_24) (cur_24 0) (nh_24 0) s_24 4 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_24 g_24 ep_24 1 1 bds_24 0 (dagTraceF m_24 s_24 4 f_24) cur_24 nh_24 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_24 nc_24 (by decide +kernel)

def m_25 : Nat := 0x6060606060606060
def s_25 : List Nat := [0x2020202020202020, 0x60006000600060, 0x606000006060, 0x60606060]
def g_25 : Nat := 0x4000404060
def ep_25 : Nat := 0x40402000000040000040200000004000400020000000000000000000000000000000000000000000000000
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cc_25_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9409409407cc7c07c07827807807807427217206e26e06c16c06c06825e55e05c15c05a15a05a05a0562541277032001 0x589d0ad3915270284d84e988952e11a52224883e90879200e83c1c074341e06434092600e0c01a1004a3808040104801d1c035200a690134c0229003c30060400a1100692015380224003490892510e462147c3f8c876a50e9461ca7c354c80e968092a18a4c2d49436920604a0b88c160f82a1d02c3604864080b80e168181e0103b778eee31bd8d3baea6f564be9695cc92781a46f00edd41bb8c2f6b056bd09d10119e81f340364705c02098000f 12 4095 5 31 10 1023 19 524287
def cc_25_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x84c21f4ea70b6586c0592512090481ecf0783c18cc052281408432180884012080402002 0x15241538f520fa48f124a144952c112434244014dd381120e230d92430343c14d248ce30c82cc248be30b82c92388630163ca5308230152c9934112c9238112c86388230 9 511 3 7 10 1023 16 65535
def cc_25_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x8838808618608417c47c07c07c07c07447217016e16e06265855615414e34c14a14431961801421020e10c10c0082004 0x5f912d4789410481804082e6916f40b49e23082be91423cac9e550f110408430401852d228e81263ca09e4c0f0f841302e9214b3089784278200a96044b26c913230060e0507020392a489318030733c959a49cb246291b04837a3ebb1d598e6c4715236a7194f8c67461212e0c96cb0b8405b2c1e900cb104968226c100a9c46481f291152450a2254b20a70112070984049088684c24 12 4095 5 31 10 1023 17 131071
def cc_25_3 : Nat → List (Nat × Nat) := unpackCursorV5 0x9a19a09629417127007006e16c16a16816806806806426406215c35a15a05245012d22a12051651601410c40a1024001 0x55091f5340d4b1f1388752a1946854fa0d3a824da0532694b81d2d80129fc467e0f9ec32750a9d0294b0981c214b059a81556091c03832050b8246f0d0401c6f481c2306e1103c1c564f18648508e16a30030400d2479929e246778f9da32754b9d12d48494092273129c846710f9b43a6c0d9ac326a099202569078081d2c081734852d012a3c4d0f0ac204d0b9282934088c0212a080a41061d31924c63900a010050816f4851d01853c270809810 12 4095 5 31 10 1023 18 262143
def cc_25_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xe41b8b706e0dc1b82b6560ac148a90520a03402614c0904f95f03e0744e045b8a01402804082300200000000 0x27e389e8c29e3aa68e69638a38da8a31a04b9f1299d48a71219b482682e990b65c2c9609229348f8c0dc208f8e04020909216a308e4c03c20360422e380d4822934bad2ae746b88e6d631b152ac146924f6253aac4daa135984d1ed2e3548a544a9411a4c3e920f6442e6b0aa34260908a301e89075f420845104d2c7c0c1543c 11 2047 5 31 10 1023 18 262143
def cc_25_5 : Nat → List (Nat × Nat) := unpackCursorV5 0xd8705a003c2704d85a0b40604a1130a60444788e09c0380700b19602c0580819001843006008208410001000 0x30348bf8c2281cd5d2b5349d3d234346ced06fa3e8c8f72d3eca4f7253c834e55135c64cb1531c44c3043e930f7042ebe0a6b022a808660208b8e2f120b4522ed34a3511f12cb74e03520384c2d9248e0d168248b4d22e38b3482d348b24d28e44afd22b930ad0f2af48aa8c2a43ca14f27d308b8f291308b8f27930a18e0352c 11 2047 5 31 10 1023 18 262143
def cc_25_6 : Nat → List (Nat × Nat) := unpackCursorV5 0x9018e18e08e08648608418215f25c15254854804613e43c13443213202a42a02a02812611a61810e50c10a1043021001 0x2b424a90d33f48564f04d308a08142388a4d38b4ae1d1b8239df8c7793edd4f6f935894cb704adb11b6836be0d7642e6d0ab60261508b5c1e890769c30c0d33354cc85030c4ca60c30c3ec00e6bc32ab0c69430a40833f4cd25334540a30822c30cf933314cc75028830a10c33748ccd004d3ca00827c309e0c32348c7d02fe3c564f3083c9d0827030c20bafc29ae08aa8219b0822e3c0d4b30f488a4b308308b070341c 12 4095 5 31 10 1023 18 262143
def cc_25_7 : Nat → List (Nat × Nat) := unpackCursorV5 0x8e18648608418408408027657607607227207016654704604604604604602ae2a02a02a0281280280052040040021001 0x7fa603e4c1fc923c83430848f94c1f31c2cc2067e90fb921f49e3e13059040f38e07a103ce3030c90f58e1e9183c9481e02100d25fb24bad4572a7cb14c900970ed227588afc0f9b81d3dc364a864f60b8e6153c4260c044ebd39df26ba6496848aee905daa6a1d493128aec505d61cb902e580447f07874091543c74c94e8919af1f24a3d2f25ae74a5cc92a052172894e4119bc1d374396086c920c58213368253f03c39048a0121c038 12 4095 5 31 10 1023 19 524287
def cc_25_8 : Nat → List (Nat × Nat) := unpackCursorV5 0xf41e83b1722e41c83906e2dc1b83516a0d414b2905209c5382704c1981302414618c1089c28b714020402000 0x4263c8e861098f22a184623808259168e22b184823a8fc731e8e2391b46e318d25d194b62e171c0298a0451308624104401887829088d2131c0402084468b70c08210415482d260134816c181002097e952ed1a55254a64685c7b078ea4b1b4863588c690e52a1aa34313e85a7b0a4ba0e96b7c395a862760a47e10a041d83033040541208c09205a281014d1f62233c34 11 2047 5 31 10 1023 19 524287
def cc_25_9 : Nat → List (Nat × Nat) := unpackCursorV5 0xf43e8392720e41c0770e26c03786e0d254ec981111e2382684d01622444048010020028c500a014010c20002 0x230104fb489ee800f8f22e08459308aa6139d2271a04d23c9aa7914480aa1e44e3008258104b26a974d1299324522486249052b4aa4e9348d228ba350f419fc7d0a8f6829f4313da0a5d3f4a64a914852188a413c0fa761ece83c36872540d66e194d83199861098e262104b648984691c912131a42638960412dd22571a4724494691274f24c184934891a79220c2301e45830 11 2047 5 31 10 1023 19 524287
def cc_25_10 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0094e9409409409409409216f26e06e06c16a16a06a06246016005e13b23812e52452402211a41811040e1083061003 0xb069d62936b924d1645b0c83604e6b2974a522af89a73124c422d78413c03243044ac965724aadc8d4e8fa171ed694aaca8d534eaa49cd053685a634149a9e929782dac05357094d6109dc192102327492469a5134884240550f01e18422342827155d2aa9a354e3ea947b3f8d60f195454aa828d4f4da7e9ad392e83a5ae00e57018a0c1da68334c0542a08c8130a0699425323e984f84c9c881424fa809cca132922631e4c23a905134c8e241471328c2042530a24991b4c27a264e04084c7942d2210964d43084a5940d2210964d030 12 4095 5 31 10 1023 19 524287
def cc_25_11 : Nat → List (Nat × Nat) := unpackCursorV5 0xa009c29259209208e284565064064064064064048e4804613e43e03c13c03c03822e52e02e02a2205010000000000000 0xb82713148289245bd48982617e0b2fa10408385e040cf922f4965e52080890bb0c2eda2dda45b7293554e65e98d712dbfa537c4961c90c004971072ba0c5d216dec29bc04a95086eda75da39baa9b515268aa2dd141aa2532e486e626b70496808b72105c214ae421b80412d902df1a5b144a22696a0c2d51c4b120a26916c92256905ac3cb4860ff0e08c1018548b3271654c1fc2411420b769360916b51f4aa32b028b6d4faa29d5a13687264fd124f214910214383b67066c80a86011 12 4095 5 31 10 1023 19 524287
def cur_25 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec ([]) (cc_25_11 (Nat.sub p 352)) (Nat.blt p 384)) (Bool.rec (cc_25_10 (Nat.sub p 320)) (cc_25_9 (Nat.sub p 288)) (Nat.blt p 320)) (Nat.blt p 352)) (Bool.rec (Bool.rec (cc_25_8 (Nat.sub p 256)) (cc_25_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_25_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (cc_25_5 (Nat.sub p 160)) (cc_25_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_25_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_25_2 (Nat.sub p 64)) (cc_25_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_25_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def hc_25_0 : Nat → Nat := unpackHintV5 0x8420fc31e0636186c00d801ac135026028b4316412c805900b0096002c005800b0015c1290a520092490871e0c351c6a00d4019842d1826d00520002 0x5555555555555555555555555554555515555551555555515555555455514544544545 15 32767 6 63
def hc_25_1 : Nat → Nat := unpackHintV5 0xa2251028052ca8c54031d18e807213141804b0850423291047883441528a044c21e40f007043421a00b105802440660300180006 0x15115555555555555555555555555555555555555 13 8191 5 31
def hc_25_2 : Nat → Nat := unpackHintV5 0xc41ad10b402d00b402c0498626009802600921a09082020808201f846661980660180660018005a18d263400c82282878a12304801008010 0x55555555555551555555555554515455055555445555555555 14 16383 6 63
def hc_25_3 : Nat → Nat := unpackHintV5 0x8f191e02342438c6e64d619985300c5a18a83138626824c048841082210042007e18e07190c2f0c4e4039906820c0400600000000000000000000000 0x155555555554555155555145555555555555555555155555555155555555555155454555555 15 32767 6 63
def hc_25_4 : Nat → Nat := unpackHintV5 0x9401221a2c641907d18ee31acc35806b00d409a41310e5c18a45144128805004962910722004208783089a1082200430406000a860e1c1030143000a 0x55555555555555555555555555515555555155555554555555551554555555155555554545 15 32767 6 63
def hc_25_5 : Nat → Nat := unpackHintV5 0xc01a6a69a026028e2a10a7831e0076099906211880600958a4c292824220e883028b82262078814284821008208080018204081000010000 0x14154155555551155555555541511555555555555555555555 14 16383 6 63
def hc_25_6 : Nat → Nat := unpackHintV5 0xf03390ce20b802da1b290bc3ab107ac9e0276097985e017805e017805e017805e016844a40c983200c802e10790066018006000060000000 0x555555551555555555555555555455515155555555555555555555555555554 14 16383 6 63
def hc_25_7 : Nat → Nat := unpackHintV5 0xa605422a6c64d029a0134026414a0a8e191c0234146808c050e29dd037906918c2416c62c0646488a091011e10351c6418b450a32110c1828186000c 0x55555455455545514500144155455555545554115555014155555555515155455515555555145555555 15 32767 6 63
def hc_25_8 : Nat → Nat := unpackHintV5 0xf623d80f40bc82e63368cda03584d603580d01b10cb4427189c027009a0a6028a39f8c7039c006c1180c4c5128240283340c002820028000 0x1555555555555555555555555555555455555554555555455555551554555155 14 16383 6 63
def hc_25_9 : Nat → Nat := unpackHintV5 0xea03a80e613590be62f80be02e84aa42a80aa024986c99b006a0980a562948452014024628f0a3a08c882a2080a1e085880e2010a0208002 0x15555555555555555555554550555555544554151155555555555555555 14 16383 6 63
def hc_25_10 : Nat → Nat := unpackHintV5 0xa1191e9238146828a0d0a29f483b0e5d64b419545278c491890091c122063c206840b470a321304240818c030006000c001800300060006180c00006 0x155455405055551515555555555155455555554515555555545555555555555555515545554555555514 15 32767 6 63
def hc_25_11 : Nat → Nat := unpackHintV5 0x9b01340a545478c8f011c0a2453ca0760cdc41a0630105a189091200238242147830ec11d803b007408d45178c2f005c08a450ca0112016302030010 0x154555554401441450155155555515555101415555155555155155554540051051554555415515 15 32767 6 63
def hc_25_12 : Nat → Nat := unpackHintV5 0xc 0x555 8 255 4 15
def nh_25 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_25_12 (Nat.sub p 384)) (hc_25_11 (Nat.sub p 352)) (Nat.blt p 384)) (Bool.rec (hc_25_10 (Nat.sub p 320)) (hc_25_9 (Nat.sub p 288)) (Nat.blt p 320)) (Nat.blt p 352)) (Bool.rec (Bool.rec (hc_25_8 (Nat.sub p 256)) (hc_25_7 (Nat.sub p 224)) (Nat.blt p 256)) (hc_25_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (hc_25_5 (Nat.sub p 160)) (hc_25_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_25_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_25_2 (Nat.sub p 64)) (hc_25_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_25_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)
def f_25 : Nat → Nat × Nat := unpackForestF 0xbc2537d0b2fa105e125bc053794b2f2905e02500c77728e6e4a6dc941b909b72104031bdc020b7c6964d26c89f5a648b48796a8e2d21859136b2033654e2ca985901500a775e936bd20d7939af09b5e104029bd5e4aabc8d5752aaea355c29ab84a014be99a553346a647d4c8f698a553146a626d4c4ba980cd301500a5733d2a67a4ccf48a30994610267a35124c99e8342d2266975034899a533dd227ba04cc3e9987b330f271a44e34099865330c668974d129998600149e62104c2348269504d1a57a44b02095c690492a092349b4893279260c2091b48b4891279220c2091ac4a3a89473128e23a1844a3689463124ba2496c62388905d158e22b18448228904312082091a43c18878290452a08a34113e8227b044ba131c422348225b040660aa44101500a4702482029a3c7497fa60fe491e324bc43e7c490f84f1f31c3e1307886cf10b9e51c3ca3079c60f2521e2130043b75c9aeb905d6a6bad4175872010ddc9253924672252e4495c825390460085ed7d29afa335e396bc62d74f9ae9eb5c4a6b88cd70d9ae1735c266b83c010ad7da52fb495f690d1531a2a02fb4667c98bed0599a4333405f27cbe4f57c9e31f4863e80be4c97c98af93061690c20c17c172ff485fc60be0a40213af1205da6889d2913a3226395ba70b64911318acb4859a40b24d112a52254656e90ad4c15a1e2253654e90a98c1521e225354cc74998e5331c291304cc6c998c5431c2652e4f4709e8c13291265214ca40990b93216a25344b058960911225224464487c890f5121723a4847c708e4c112132241e45c708a4d1120e804233da947b518f69f211443da747b4d8f6991ec4a3d88c7b0f8fa9a1f1383d8640107cd3251a64634c7c698c8d2971a52d3489469118d21f1ba3037a406e110d21d1a4363486469098d20f0041b2449448924912418e4c31c8048918c29e122412fc88488f8911d16b482d6805a4f0911c922382ae90554f0aa1e122362446450d20a1a01413c24462488c09924132302403c499209318120190082e464808a9200a4a0148c028f8829c10124014643c9207a900f1240129402518049f0da301ba703649004990ca4819460320b004930ba48174602e0b004928713a0e2721c4e05298071360e262264d03897092380e2521c488411c082300e2421c480380f0701d01248190f0321a0084a0108c020f8041d0334806260128e0189004120060600d8e01a90030200106c0a11004190082e0105a02078089c0112001a480207402098000f 9 10
def ch_25 : Nat → Bool := dagCheckNodeV5 m_25 g_25 ep_25 1 1 bds_25 384 (dagTraceF m_25 s_25 6 f_25) cur_25 nh_25
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV5 m_25 g_25 ep_25 1 1 384 bds_25 (dagTraceF m_25 s_25 6 f_25) (cur_25 0) (nh_25 0) s_25 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_0 : treeBlockF 0 32 ch_25 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_1 : treeBlockF 32 64 ch_25 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_2 : treeBlockF 64 96 ch_25 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_3 : treeBlockF 96 128 ch_25 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_4 : treeBlockF 128 160 ch_25 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_5 : treeBlockF 160 192 ch_25 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_6 : treeBlockF 192 224 ch_25 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_7 : treeBlockF 224 256 ch_25 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_8 : treeBlockF 256 288 ch_25 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_9 : treeBlockF 288 320 ch_25 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_10 : treeBlockF 320 352 ch_25 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_11 : treeBlockF 352 384 ch_25 = true := by decide +kernel
theorem nj_25_1 : ∀ i, 0 ≤ i → i < 64 → ch_25 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_25_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_25_1 h1 h2)
theorem nj_25_2 : ∀ i, 0 ≤ i → i < 96 → ch_25 i = true := block_join nj_25_1 (fun _ h1 h2 => treeBlockF_at nb_25_2 h1 h2)
theorem nj_25_3 : ∀ i, 0 ≤ i → i < 128 → ch_25 i = true := block_join nj_25_2 (fun _ h1 h2 => treeBlockF_at nb_25_3 h1 h2)
theorem nj_25_4 : ∀ i, 0 ≤ i → i < 160 → ch_25 i = true := block_join nj_25_3 (fun _ h1 h2 => treeBlockF_at nb_25_4 h1 h2)
theorem nj_25_5 : ∀ i, 0 ≤ i → i < 192 → ch_25 i = true := block_join nj_25_4 (fun _ h1 h2 => treeBlockF_at nb_25_5 h1 h2)
theorem nj_25_6 : ∀ i, 0 ≤ i → i < 224 → ch_25 i = true := block_join nj_25_5 (fun _ h1 h2 => treeBlockF_at nb_25_6 h1 h2)
theorem nj_25_7 : ∀ i, 0 ≤ i → i < 256 → ch_25 i = true := block_join nj_25_6 (fun _ h1 h2 => treeBlockF_at nb_25_7 h1 h2)
theorem nj_25_8 : ∀ i, 0 ≤ i → i < 288 → ch_25 i = true := block_join nj_25_7 (fun _ h1 h2 => treeBlockF_at nb_25_8 h1 h2)
theorem nj_25_9 : ∀ i, 0 ≤ i → i < 320 → ch_25 i = true := block_join nj_25_8 (fun _ h1 h2 => treeBlockF_at nb_25_9 h1 h2)
theorem nj_25_10 : ∀ i, 0 ≤ i → i < 352 → ch_25 i = true := block_join nj_25_9 (fun _ h1 h2 => treeBlockF_at nb_25_10 h1 h2)
theorem nj_25_11 : ∀ i, 0 ≤ i → i < 384 → ch_25 i = true := block_join nj_25_10 (fun _ h1 h2 => treeBlockF_at nb_25_11 h1 h2)
theorem nc_25 : ∀ i, 0 ≤ i → i < 384 → ch_25 i = true := nj_25_11
theorem lb_25 : LowerBin m_25 s_25 g_25 7 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_25 nc_25 (by decide +kernel)

def m_26 : Nat := 0xffff000000000000
def s_26 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_26 : Nat := 0x117000000000000
def ep_26 : Nat := 0x16000000000000010600000000000001120000000000000114000000000000
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_5, s_5, 4, g_5), (m_11, s_11, 4, g_11), (m_12, s_12, 4, g_12)]
def cc_26_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_26_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_26 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_26_1 (Nat.sub p 32)) (cc_26_0 p) (Nat.blt p 32)
def hc_26_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_26_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_26 : Nat → Nat := fun p => Bool.rec (hc_26_1 (Nat.sub p 32)) (hc_26_0 p) (Nat.blt p 32)
def f_26 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_26 : Nat → Bool := dagCheckNodeV5 m_26 g_26 ep_26 1 1 bds_26 43 (dagTraceF m_26 s_26 6 f_26) cur_26 nh_26
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV5 m_26 g_26 ep_26 1 1 43 bds_26 (dagTraceF m_26 s_26 6 f_26) (cur_26 0) (nh_26 0) s_26 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_26_0 : treeBlockF 0 32 ch_26 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_26_1 : treeBlockF 32 43 ch_26 = true := by decide +kernel
theorem nj_26_1 : ∀ i, 0 ≤ i → i < 43 → ch_26 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_26_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_26_1 h1 h2)
theorem nc_26 : ∀ i, 0 ≤ i → i < 43 → ch_26 i = true := nj_26_1
theorem lb_26 : LowerBin m_26 s_26 g_26 7 :=
  lowerDagV5 (kn_cons lb_0 (kn_cons lb_5 (kn_cons lb_11 (kn_cons lb_12 (kn_nil))))) rc_26 nc_26 (by decide +kernel)

def m_27 : Nat := 0xff00ff0000000000
def s_27 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_27 : Nat := 0x100170000000000
def ep_27 : Nat := 0x1600000000000000000000000000010006000000000001001200000000000100140000000000
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4), (m_9, s_9, 4, g_9), (m_2, s_2, 4, g_2), (m_3, s_3, 4, g_3)]
def cc_27_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_27_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_27 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_27_1 (Nat.sub p 32)) (cc_27_0 p) (Nat.blt p 32)
def hc_27_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_27_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_27 : Nat → Nat := fun p => Bool.rec (hc_27_1 (Nat.sub p 32)) (hc_27_0 p) (Nat.blt p 32)
def f_27 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_27 : Nat → Bool := dagCheckNodeV5 m_27 g_27 ep_27 1 1 bds_27 43 (dagTraceF m_27 s_27 6 f_27) cur_27 nh_27
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV5 m_27 g_27 ep_27 1 1 43 bds_27 (dagTraceF m_27 s_27 6 f_27) (cur_27 0) (nh_27 0) s_27 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_0 : treeBlockF 0 32 ch_27 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_1 : treeBlockF 32 43 ch_27 = true := by decide +kernel
theorem nj_27_1 : ∀ i, 0 ≤ i → i < 43 → ch_27 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_27_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_27_1 h1 h2)
theorem nc_27 : ∀ i, 0 ≤ i → i < 43 → ch_27 i = true := nj_27_1
theorem lb_27 : LowerBin m_27 s_27 g_27 7 :=
  lowerDagV5 (kn_cons lb_4 (kn_cons lb_9 (kn_cons lb_2 (kn_cons lb_3 (kn_nil))))) rc_27 nc_27 (by decide +kernel)

def m_28 : Nat := 0xff00ff00000000
def s_28 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_28 : Nat := 0x17005700000000
def ep_28 : Nat := 0x40000000000000000000000000000600020000000000120002000000000014005400000000
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
def cur_28 : Nat → List (Nat × Nat) := fun _ => []
def nh_28 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_28 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV5 m_28 g_28 ep_28 1 1 0 bds_28 (dagTraceF m_28 s_28 4 f_28) (cur_28 0) (nh_28 0) s_28 4 = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_28 g_28 ep_28 1 1 bds_28 0 (dagTraceF m_28 s_28 4 f_28) cur_28 nh_28 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_28 : LowerBin m_28 s_28 g_28 5 :=
  lowerDagV5 (kn_cons lb_5 (kn_nil)) rc_28 nc_28 (by decide +kernel)

def m_29 : Nat := 0xf0f0f0f000000000
def s_29 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_29 : Nat := 0x10105000000000
def ep_29 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000010105000000000
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_29 : Nat → List (Nat × Nat) := fun _ => []
def nh_29 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_29 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV5 m_29 g_29 ep_29 1 1 0 bds_29 (dagTraceF m_29 s_29 4 f_29) (cur_29 0) (nh_29 0) s_29 4 = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_29 g_29 ep_29 1 1 bds_29 0 (dagTraceF m_29 s_29 4 f_29) cur_29 nh_29 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_29 : LowerBin m_29 s_29 g_29 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_29 nc_29 (by decide +kernel)

def m_30 : Nat := 0xcccccccc00000000
def s_30 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_30 : Nat := 0x4044400000000
def ep_30 : Nat := 0x440000000000004004000000000000404000000000000000000000000000004044400000000
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cur_30 : Nat → List (Nat × Nat) := fun _ => []
def nh_30 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_30 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV5 m_30 g_30 ep_30 1 1 0 bds_30 (dagTraceF m_30 s_30 4 f_30) (cur_30 0) (nh_30 0) s_30 4 = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_30 g_30 ep_30 1 1 bds_30 0 (dagTraceF m_30 s_30 4 f_30) cur_30 nh_30 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_30 : LowerBin m_30 s_30 g_30 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_30 nc_30 (by decide +kernel)

def m_31 : Nat := 0x6666666600000000
def s_31 : List Nat := [0x2222222200000000, 0x606060600000000, 0x66006600000000, 0x666600000000]
def g_31 : Nat := 0x6064600000000
def ep_31 : Nat := 0x640000000000006004000000000000606020000000000000000000000000000000000000000
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cur_31 : Nat → List (Nat × Nat) := fun _ => []
def nh_31 : Nat → Nat := unpackHintV5 0x4 0x1 6 63 3 7
def f_31 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV5 m_31 g_31 ep_31 1 1 0 bds_31 (dagTraceF m_31 s_31 4 f_31) (cur_31 0) (nh_31 0) s_31 4 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_31 g_31 ep_31 1 1 bds_31 0 (dagTraceF m_31 s_31 4 f_31) cur_31 nh_31 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_31 nc_31 (by decide +kernel)

def m_32 : Nat := 0x66666666
def s_32 : List Nat := [0x22222222, 0x6060606, 0x660066, 0x6666]
def g_32 : Nat := 0x2464666
def ep_32 : Nat := 0x44200000000000440020000000000202020000000000000000000000000000000000
def bds_32 : List (Nat × List Nat × Nat × Nat) := []
def cc_32_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xc0780300600c01612c0580b0148e90520a4148290520a41482524a09412062144084308210420802d941d001 0x229310a707d343a1e1c0d0d8586824312617900b478404c1e220e0b0684820100e1e0309038280c141092061302888103c041a4d8fe647d2a3b931bc48cdd464d53f609dac4dd5a66a92f5295a849d1a46783f321d950dca0664c2f24159109c60462c1f140d8905c0826000f 11 2047 5 31 10 1023 17 131071
def cc_32_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xd0d0d0c296898888816b686868684c4848483330303030303030301409080801 0x1ea78f014871f428f60a54fd267c153b099b868dd3c7326380e1b068d13c669a320618828be4c5d202d8f13a9899444a0c240510268812c 8 255 3 7 10 1023 17 131071
def cc_32_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x996e68615958515049252012101002 0x85204b8fa147ae53d5a9aa20f4b06b2e3c8726408f1ec790b4c9094474923051142480923d0920278f014 8 255 3 7 10 1023 17 131071
def cur_32 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_32_2 (Nat.sub p 64)) (cc_32_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_32_0 p) (Nat.blt p 32)
def hc_32_0 : Nat → Nat := unpackHintV5 0x942248490123848a2214a83120448009f087729c0e67497925d096c4591158651291963b58c542b30a4425208c4211074817303d00170002 0x0 14 16383 5 31
def hc_32_1 : Nat → Nat := unpackHintV5 0xb815c02e01700a69520a7113809a149223891448623f21d14e046c23509890b0a4a71c489a44822020e1058c18a0a10120080002 0x0 13 8191 5 31
def hc_32_2 : Nat → Nat := unpackHintV5 0x326a2a62819a659142410e2218620900200000 0x0 10 1023 4 15
def nh_32 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_32_2 (Nat.sub p 64)) (hc_32_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_32_0 p) (Nat.blt p 32)
def f_32 : Nat → Nat × Nat := unpackForestF 0xc7e063e971e018ec0c6f15288a92450a228480633771f3b8f5da55013c76933b0a9e278f0147613018c9b498d8386e9e360d00a7ec53c629a310618828053b5b262d9016c7805370299814bc0a56052748a6245112030901402919f930fa70812c3e9a010fcd078683434161a09008765a4c2d20168f0086e04330217810ac084e344c1a220d0b068480423020f8106c082e09240e0a021301088083c060a020d00826000f 7 10
def ch_32 : Nat → Bool := dagCheckNodeV5 m_32 g_32 ep_32 1 1 bds_32 78 (dagTraceF m_32 s_32 5 f_32) cur_32 nh_32
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV5 m_32 g_32 ep_32 1 1 78 bds_32 (dagTraceF m_32 s_32 5 f_32) (cur_32 0) (nh_32 0) s_32 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32_0 : treeBlockF 0 32 ch_32 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32_1 : treeBlockF 32 64 ch_32 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32_2 : treeBlockF 64 78 ch_32 = true := by decide +kernel
theorem nj_32_1 : ∀ i, 0 ≤ i → i < 64 → ch_32 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_32_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_32_1 h1 h2)
theorem nj_32_2 : ∀ i, 0 ≤ i → i < 78 → ch_32 i = true := block_join nj_32_1 (fun _ h1 h2 => treeBlockF_at nb_32_2 h1 h2)
theorem nc_32 : ∀ i, 0 ≤ i → i < 78 → ch_32 i = true := nj_32_2
theorem lb_32 : LowerBin m_32 s_32 g_32 6 :=
  lowerDagV5 (kn_nil) rc_32 nc_32 (by decide +kernel)

def m_33 : Nat := 0x6666000066660000
def s_33 : List Nat := [0x2222000022220000, 0x606000006060000, 0x66000000660000, 0x66660000]
def g_33 : Nat := 0x6000002460000
def ep_33 : Nat := 0x240000000000000000000000006000000440000000600000202000000000000000000000000000000000000
def bds_33 : List (Nat × List Nat × Nat × Nat) := []
def cur_33 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0xb9710f 4 15 2 3 6 63 8 255
def nh_33 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_33 : Nat → Nat × Nat := unpackForestF 0x1e788f 1 6
def ch_33 : Nat → Bool := dagCheckNodeV5 m_33 g_33 ep_33 1 1 bds_33 3 (dagTraceF m_33 s_33 4 f_33) cur_33 nh_33
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV5 m_33 g_33 ep_33 1 1 3 bds_33 (dagTraceF m_33 s_33 4 f_33) (cur_33 0) (nh_33 0) s_33 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33 : treeBlockF 0 3 ch_33 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 3 → ch_33 i = true := fun _ h1 h2 => treeBlockF_at nb_33 h1 h2
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagV5 (kn_nil) rc_33 nc_33 (by decide +kernel)

def m_34 : Nat := 0x666600006666
def s_34 : List Nat := [0x222200002222, 0x60600000606, 0x6600000066, 0x6666]
def g_34 : Nat := 0x64600004666
def ep_34 : Nat := 0x402000000000000000000000004000000020000006020000020000000000000000000000000000000000
def bds_34 : List (Nat × List Nat × Nat × Nat) := []
def cur_34 : Nat → List (Nat × Nat) := unpackCursorV5 0x16ac58b12a44890e8701 0x1924309193c2050d3c205263d88d5d2a549902a109800f 7 127 3 7 10 1023 14 16383
def nh_34 : Nat → Nat := unpackHintV5 0x340d0340d0302c0300c02c215002 0x0 10 1023 5 31
def f_34 : Nat → Nat × Nat := unpackForestF 0xc7a63529564f0a4c42a49e205084c00f 3 10
def ch_34 : Nat → Bool := dagCheckNodeV5 m_34 g_34 ep_34 1 1 bds_34 10 (dagTraceF m_34 s_34 4 f_34) cur_34 nh_34
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV5 m_34 g_34 ep_34 1 1 10 bds_34 (dagTraceF m_34 s_34 4 f_34) (cur_34 0) (nh_34 0) s_34 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34 : treeBlockF 0 10 ch_34 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 10 → ch_34 i = true := fun _ h1 h2 => treeBlockF_at nb_34 h1 h2
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagV5 (kn_nil) rc_34 nc_34 (by decide +kernel)

def m_35 : Nat := 0x6600660066006600
def s_35 : List Nat := [0x2200220022002200, 0x600060006000600, 0x660000006600, 0x66006600]
def g_35 : Nat := 0x60002004600
def ep_35 : Nat := 0x200400000000600000044000000000000000000000006000200020000000000000000000000000000000000
def bds_35 : List (Nat × List Nat × Nat × Nat) := []
def cur_35 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0xb9710f 4 15 2 3 6 63 8 255
def nh_35 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_35 : Nat → Nat × Nat := unpackForestF 0x1e788f 1 6
def ch_35 : Nat → Bool := dagCheckNodeV5 m_35 g_35 ep_35 1 1 bds_35 3 (dagTraceF m_35 s_35 4 f_35) cur_35 nh_35
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV5 m_35 g_35 ep_35 1 1 3 bds_35 (dagTraceF m_35 s_35 4 f_35) (cur_35 0) (nh_35 0) s_35 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35 : treeBlockF 0 3 ch_35 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 3 → ch_35 i = true := fun _ h1 h2 => treeBlockF_at nb_35 h1 h2
theorem lb_35 : LowerBin m_35 s_35 g_35 5 :=
  lowerDagV5 (kn_nil) rc_35 nc_35 (by decide +kernel)

def m_36 : Nat := 0xc0c0c0c0c0c0c0c0
def s_36 : List Nat := [0x4040404040404040, 0xc000c000c000c0, 0xc0c00000c0c0, 0xc0c0c0c0]
def g_36 : Nat := 0x4000404040
def ep_36 : Nat := 0x40400000000040000040000000004000400000000000000000000000000000000000000000004000404040
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cur_36 : Nat → List (Nat × Nat) := fun _ => []
def nh_36 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV5 m_36 g_36 ep_36 1 1 0 bds_36 (dagTraceF m_36 s_36 4 f_36) (cur_36 0) (nh_36 0) s_36 4 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_36 g_36 ep_36 1 1 bds_36 0 (dagTraceF m_36 s_36 4 f_36) cur_36 nh_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_36 nc_36 (by decide +kernel)

def m_37 : Nat := 0x66006600660066
def s_37 : List Nat := [0x22002200220022, 0x6000600060006, 0x6600000066, 0x660066]
def g_37 : Nat := 0x6004600460066
def ep_37 : Nat := 0x40002000000040000000200000000000000000000600020002000000000000000000000000000000000000
def bds_37 : List (Nat × List Nat × Nat × Nat) := []
def cur_37 : Nat → List (Nat × Nat) := unpackCursorV5 0x16ac58b12a44890e8701 0x1924309193c2050d3c205263d88d5d2a549902a109800f 7 127 3 7 10 1023 14 16383
def nh_37 : Nat → Nat := unpackHintV5 0x340d0340d0302c0300c02c215002 0x0 10 1023 5 31
def f_37 : Nat → Nat × Nat := unpackForestF 0xc7a63529564f0a4c42a49e205084c00f 3 10
def ch_37 : Nat → Bool := dagCheckNodeV5 m_37 g_37 ep_37 1 1 bds_37 10 (dagTraceF m_37 s_37 4 f_37) cur_37 nh_37
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV5 m_37 g_37 ep_37 1 1 10 bds_37 (dagTraceF m_37 s_37 4 f_37) (cur_37 0) (nh_37 0) s_37 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_37 : treeBlockF 0 10 ch_37 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 10 → ch_37 i = true := fun _ h1 h2 => treeBlockF_at nb_37 h1 h2
theorem lb_37 : LowerBin m_37 s_37 g_37 5 :=
  lowerDagV5 (kn_nil) rc_37 nc_37 (by decide +kernel)

def m_38 : Nat := 0xff000000ff00
def s_38 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_38 : Nat := 0x170000005700
def ep_38 : Nat := 0x400000000000000000000000000000000000000006000000020000001200000002000000140000005400
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def nh_38 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV5 m_38 g_38 ep_38 1 1 0 bds_38 (dagTraceF m_38 s_38 4 f_38) (cur_38 0) (nh_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_38 g_38 ep_38 1 1 bds_38 0 (dagTraceF m_38 s_38 4 f_38) cur_38 nh_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_38 nc_38 (by decide +kernel)

def m_39 : Nat := 0xf0f00000f0f0
def s_39 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_39 : Nat := 0x105000005070
def ep_39 : Nat := 0x402000000000000000000000004000000020000000000000000000001000000000200000105000005040
def bds_39 : List (Nat × List Nat × Nat × Nat) := []
def cc_39_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_39_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_39 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_39_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_39_0 p) (Nat.blt p 32)
def hc_39_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_39_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_39_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_39 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_39_2 (Nat.sub p 64)) (hc_39_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_39_0 p) (Nat.blt p 32)
def f_39 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_39 : Nat → Bool := dagCheckNodeV5 m_39 g_39 ep_39 1 1 bds_39 64 (dagTraceF m_39 s_39 5 f_39) cur_39 nh_39
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV5 m_39 g_39 ep_39 1 1 64 bds_39 (dagTraceF m_39 s_39 5 f_39) (cur_39 0) (nh_39 0) s_39 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_39_0 : treeBlockF 0 32 ch_39 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_39_1 : treeBlockF 32 64 ch_39 = true := by decide +kernel
theorem nj_39_1 : ∀ i, 0 ≤ i → i < 64 → ch_39 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_39_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_39_1 h1 h2)
theorem nc_39 : ∀ i, 0 ≤ i → i < 64 → ch_39 i = true := nj_39_1
theorem lb_39 : LowerBin m_39 s_39 g_39 6 :=
  lowerDagV5 (kn_nil) rc_39 nc_39 (by decide +kernel)

def m_40 : Nat := 0xf0f00000f0f0000
def s_40 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_40 : Nat := 0x107000003070000
def ep_40 : Nat := 0x200000000000000000000000006000000040000000000000000000001020000030200000104000000040000
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_40 : Nat → List (Nat × Nat) := fun _ => []
def nh_40 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_40 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV5 m_40 g_40 ep_40 1 1 0 bds_40 (dagTraceF m_40 s_40 4 f_40) (cur_40 0) (nh_40 0) s_40 4 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_40 g_40 ep_40 1 1 bds_40 0 (dagTraceF m_40 s_40 4 f_40) cur_40 nh_40 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_40 : LowerBin m_40 s_40 g_40 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_40 nc_40 (by decide +kernel)

def m_41 : Nat := 0xf000f000f000f00
def s_41 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_41 : Nat := 0x100070003000700
def ep_41 : Nat := 0x200000000000600000004000000000000000000000000000000000001000200030002000100040000000400
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def nh_41 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV5 m_41 g_41 ep_41 1 1 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) (nh_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_41 g_41 ep_41 1 1 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 nh_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_41 nc_41 (by decide +kernel)

def m_42 : Nat := 0xf000f000f000f000
def s_42 : List Nat := [0x5000500050005000, 0x3000300030003000, 0xf0000000f000, 0xf000f000]
def g_42 : Nat := 0x100010005000
def ep_42 : Nat := 0x1000400000001000000040000000000000000000000000000000000000001000100000000000100010005000
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
def cur_42 : Nat → List (Nat × Nat) := fun _ => []
def nh_42 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_42 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV5 m_42 g_42 ep_42 1 1 0 bds_42 (dagTraceF m_42 s_42 4 f_42) (cur_42 0) (nh_42 0) s_42 4 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_42 g_42 ep_42 1 1 bds_42 0 (dagTraceF m_42 s_42 4 f_42) cur_42 nh_42 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagV5 (kn_cons lb_13 (kn_nil)) rc_42 nc_42 (by decide +kernel)

def m_43 : Nat := 0x5555555500000000
def s_43 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_43 : Nat := 0x115155500000000
def ep_43 : Nat := 0x1440000000000014004000000000010404000000000001101000000000000000000000000000
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2), (m_11, s_11, 4, g_11), (m_1, s_1, 4, g_1), (m_7, s_7, 4, g_7)]
def cc_43_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_43_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_43 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_43_1 (Nat.sub p 32)) (cc_43_0 p) (Nat.blt p 32)
def hc_43_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e02200586415a60dad5545a0ad39b942665566b5910608437408a0203a61035944 15 32767 6 63
def hc_43_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e7540e571014d8c00562302 13 8191 6 63
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
  lowerDagV5 (kn_cons lb_2 (kn_cons lb_11 (kn_cons lb_1 (kn_cons lb_7 (kn_nil))))) rc_43 nc_43 (by decide +kernel)

def m_44 : Nat := 0xffff0000
def s_44 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_44 : Nat := 0x13570000
def ep_44 : Nat := 0x440000000000000202000000000000130200000000000010540000
def bds_44 : List (Nat × List Nat × Nat × Nat) := []
def cur_44 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_44 : Nat → Nat := fun _ => 0
def f_44 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_44 : Nat → Bool := dagCheckNodeV5 m_44 g_44 ep_44 1 1 bds_44 1 (dagTraceF m_44 s_44 3 f_44) cur_44 nh_44
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV5 m_44 g_44 ep_44 1 1 1 bds_44 (dagTraceF m_44 s_44 3 f_44) (cur_44 0) (nh_44 0) s_44 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44 : treeBlockF 0 1 ch_44 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 1 → ch_44 i = true := fun _ h1 h2 => treeBlockF_at nb_44 h1 h2
theorem lb_44 : LowerBin m_44 s_44 g_44 4 :=
  lowerDagV5 (kn_nil) rc_44 nc_44 (by decide +kernel)

def m_45 : Nat := 0xff00ff00
def s_45 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_45 : Nat := 0x13005700
def ep_45 : Nat := 0x44000000000000000000000000000200020000000000130002000000000010005400
def bds_45 : List (Nat × List Nat × Nat × Nat) := []
def cur_45 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_45 : Nat → Nat := fun _ => 0
def f_45 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_45 : Nat → Bool := dagCheckNodeV5 m_45 g_45 ep_45 1 1 bds_45 1 (dagTraceF m_45 s_45 3 f_45) cur_45 nh_45
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV5 m_45 g_45 ep_45 1 1 1 bds_45 (dagTraceF m_45 s_45 3 f_45) (cur_45 0) (nh_45 0) s_45 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_45 : treeBlockF 0 1 ch_45 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 1 → ch_45 i = true := fun _ h1 h2 => treeBlockF_at nb_45 h1 h2
theorem lb_45 : LowerBin m_45 s_45 g_45 4 :=
  lowerDagV5 (kn_nil) rc_45 nc_45 (by decide +kernel)

def m_46 : Nat := 0xf0f0f0f0
def s_46 : List Nat := [0x50505050, 0x30303030, 0xf000f0, 0xf0f0]
def g_46 : Nat := 0x10505070
def ep_46 : Nat := 0x40200000000000400020000000000000000000000000100000200000000010505040
def bds_46 : List (Nat × List Nat × Nat × Nat) := []
def cc_46_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_46_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_46 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_46_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_46_0 p) (Nat.blt p 32)
def hc_46_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_46_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_46_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_46 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_46_2 (Nat.sub p 64)) (hc_46_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_46_0 p) (Nat.blt p 32)
def f_46 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_46 : Nat → Bool := dagCheckNodeV5 m_46 g_46 ep_46 1 1 bds_46 64 (dagTraceF m_46 s_46 5 f_46) cur_46 nh_46
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV5 m_46 g_46 ep_46 1 1 64 bds_46 (dagTraceF m_46 s_46 5 f_46) (cur_46 0) (nh_46 0) s_46 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_0 : treeBlockF 0 32 ch_46 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46_1 : treeBlockF 32 64 ch_46 = true := by decide +kernel
theorem nj_46_1 : ∀ i, 0 ≤ i → i < 64 → ch_46 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_46_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_46_1 h1 h2)
theorem nc_46 : ∀ i, 0 ≤ i → i < 64 → ch_46 i = true := nj_46_1
theorem lb_46 : LowerBin m_46 s_46 g_46 6 :=
  lowerDagV5 (kn_nil) rc_46 nc_46 (by decide +kernel)

def m_47 : Nat := 0x3030303030303030
def s_47 : List Nat := [0x1010101010101010, 0x30003000300030, 0x303000003030, 0x30303030]
def g_47 : Nat := 0x10101010101030
def ep_47 : Nat := 0x1000002000001000000000200010000000000020000000000000000000000000000000000010101010101000
def bds_47 : List (Nat × List Nat × Nat × Nat) := []
def cc_47_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_47_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_47 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_47_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_47_0 p) (Nat.blt p 32)
def hc_47_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_47_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_47_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_47 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_47_2 (Nat.sub p 64)) (hc_47_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_47_0 p) (Nat.blt p 32)
def f_47 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_47 : Nat → Bool := dagCheckNodeV5 m_47 g_47 ep_47 1 1 bds_47 64 (dagTraceF m_47 s_47 5 f_47) cur_47 nh_47
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV5 m_47 g_47 ep_47 1 1 64 bds_47 (dagTraceF m_47 s_47 5 f_47) (cur_47 0) (nh_47 0) s_47 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_0 : treeBlockF 0 32 ch_47 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47_1 : treeBlockF 32 64 ch_47 = true := by decide +kernel
theorem nj_47_1 : ∀ i, 0 ≤ i → i < 64 → ch_47 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_47_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_47_1 h1 h2)
theorem nc_47 : ∀ i, 0 ≤ i → i < 64 → ch_47 i = true := nj_47_1
theorem lb_47 : LowerBin m_47 s_47 g_47 6 :=
  lowerDagV5 (kn_nil) rc_47 nc_47 (by decide +kernel)

def m_48 : Nat := 0xf000f000f000f0
def s_48 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_48 : Nat := 0x10005000500070
def ep_48 : Nat := 0x40002000000040000000200000000000000000000000000000000000100000000000200010005000500040
def bds_48 : List (Nat × List Nat × Nat × Nat) := []
def cc_48_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_48_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_48 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_48_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_48_0 p) (Nat.blt p 32)
def hc_48_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_48_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_48_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_48 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_48_2 (Nat.sub p 64)) (hc_48_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_48_0 p) (Nat.blt p 32)
def f_48 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_48 : Nat → Bool := dagCheckNodeV5 m_48 g_48 ep_48 1 1 bds_48 64 (dagTraceF m_48 s_48 5 f_48) cur_48 nh_48
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV5 m_48 g_48 ep_48 1 1 64 bds_48 (dagTraceF m_48 s_48 5 f_48) (cur_48 0) (nh_48 0) s_48 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_0 : treeBlockF 0 32 ch_48 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48_1 : treeBlockF 32 64 ch_48 = true := by decide +kernel
theorem nj_48_1 : ∀ i, 0 ≤ i → i < 64 → ch_48 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_48_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_48_1 h1 h2)
theorem nc_48 : ∀ i, 0 ≤ i → i < 64 → ch_48 i = true := nj_48_1
theorem lb_48 : LowerBin m_48 s_48 g_48 6 :=
  lowerDagV5 (kn_nil) rc_48 nc_48 (by decide +kernel)

def m_49 : Nat := 0xff000000ff000000
def s_49 : List Nat := [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000]
def g_49 : Nat := 0x100000013000000
def ep_49 : Nat := 0x1200000000000000000000000000000000000000010000000200000001000000130000000100000010000000
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_49 : Nat → List (Nat × Nat) := fun _ => []
def nh_49 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_49 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV5 m_49 g_49 ep_49 1 1 0 bds_49 (dagTraceF m_49 s_49 4 f_49) (cur_49 0) (nh_49 0) s_49 4 = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_49 g_49 ep_49 1 1 bds_49 0 (dagTraceF m_49 s_49 4 f_49) cur_49 nh_49 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_49 : LowerBin m_49 s_49 g_49 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_49 nc_49 (by decide +kernel)

def m_50 : Nat := 0xff000000ff0000
def s_50 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_50 : Nat := 0x17000000570000
def ep_50 : Nat := 0x40000000000000000000000000000000000000000600000002000000120000000200000014000000540000
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
def cur_50 : Nat → List (Nat × Nat) := fun _ => []
def nh_50 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_50 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV5 m_50 g_50 ep_50 1 1 0 bds_50 (dagTraceF m_50 s_50 4 f_50) (cur_50 0) (nh_50 0) s_50 4 = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_50 g_50 ep_50 1 1 bds_50 0 (dagTraceF m_50 s_50 4 f_50) cur_50 nh_50 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_50 : LowerBin m_50 s_50 g_50 5 :=
  lowerDagV5 (kn_cons lb_5 (kn_nil)) rc_50 nc_50 (by decide +kernel)

def m_51 : Nat := 0xf0f00000f0f00000
def s_51 : List Nat := [0x5050000050500000, 0x3030000030300000, 0xf0000000f00000, 0xf0f00000]
def g_51 : Nat := 0x10000010500000
def ep_51 : Nat := 0x1040000000000000000000000010000000400000000000000000000000100000100000000010000010500000
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_51 : Nat → List (Nat × Nat) := fun _ => []
def nh_51 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_51 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV5 m_51 g_51 ep_51 1 1 0 bds_51 (dagTraceF m_51 s_51 4 f_51) (cur_51 0) (nh_51 0) s_51 4 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_51 g_51 ep_51 1 1 bds_51 0 (dagTraceF m_51 s_51 4 f_51) cur_51 nh_51 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_51 : LowerBin m_51 s_51 g_51 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_51 nc_51 (by decide +kernel)

def m_52 : Nat := 0x5500aa005500aa
def s_52 : List Nat := [0xaa000000aa, 0x11002200110022, 0x5000a0005000a, 0x5500aa]
def g_52 : Nat := 0x15000200550022
def ep_52 : Nat := 0x40002000000000000000000000000000000000000400020000000000100002000000220000000000000000
def bds_52 : List (Nat × List Nat × Nat × Nat) := []
def cur_52 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb25935b2a73294c80f 7 127 3 7 6 63 9 511
def nh_52 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_52 : Nat → Nat × Nat := unpackForestF 0x1b6c86a33194c80f 3 6
def ch_52 : Nat → Bool := dagCheckNodeV5 m_52 g_52 ep_52 1 1 bds_52 7 (dagTraceF m_52 s_52 4 f_52) cur_52 nh_52
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV5 m_52 g_52 ep_52 1 1 7 bds_52 (dagTraceF m_52 s_52 4 f_52) (cur_52 0) (nh_52 0) s_52 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52 : treeBlockF 0 7 ch_52 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 7 → ch_52 i = true := fun _ h1 h2 => treeBlockF_at nb_52 h1 h2
theorem lb_52 : LowerBin m_52 s_52 g_52 5 :=
  lowerDagV5 (kn_nil) rc_52 nc_52 (by decide +kernel)

def m_53 : Nat := 0x2222222222222222
def s_53 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_53 : Nat := 0x2020202020222
def ep_53 : Nat := 0x200002000000200000000200002000000000020000202020202020000000000000000000000000000000000
def bds_53 : List (Nat × List Nat × Nat × Nat) := []
def cc_53_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_53_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_53 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_53_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_53_0 p) (Nat.blt p 32)
def hc_53_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_53_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_53_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_53 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_53_2 (Nat.sub p 64)) (hc_53_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_53_0 p) (Nat.blt p 32)
def f_53 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_53 : Nat → Bool := dagCheckNodeV5 m_53 g_53 ep_53 1 1 bds_53 64 (dagTraceF m_53 s_53 5 f_53) cur_53 nh_53
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV5 m_53 g_53 ep_53 1 1 64 bds_53 (dagTraceF m_53 s_53 5 f_53) (cur_53 0) (nh_53 0) s_53 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53_0 : treeBlockF 0 32 ch_53 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53_1 : treeBlockF 32 64 ch_53 = true := by decide +kernel
theorem nj_53_1 : ∀ i, 0 ≤ i → i < 64 → ch_53 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_53_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_53_1 h1 h2)
theorem nc_53 : ∀ i, 0 ≤ i → i < 64 → ch_53 i = true := nj_53_1
theorem lb_53 : LowerBin m_53 s_53 g_53 6 :=
  lowerDagV5 (kn_nil) rc_53 nc_53 (by decide +kernel)

def m_54 : Nat := 0x55550000aaaa
def s_54 : List Nat := [0xaaaa, 0x111100002222, 0x50500000a0a, 0x55000000aa]
def g_54 : Nat := 0x155500000222
def ep_54 : Nat := 0x4000000020000004000000020000001000000002220000000000000000
def bds_54 : List (Nat × List Nat × Nat × Nat) := []
def cur_54 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb24b24d2d92a72652532400f 7 127 3 7 9 511 12 4095
def nh_54 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_54 : Nat → Nat × Nat := unpackForestF 0x32db2432a32632532400f 3 9
def ch_54 : Nat → Bool := dagCheckNodeV5 m_54 g_54 ep_54 1 1 bds_54 7 (dagTraceF m_54 s_54 4 f_54) cur_54 nh_54
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV5 m_54 g_54 ep_54 1 1 7 bds_54 (dagTraceF m_54 s_54 4 f_54) (cur_54 0) (nh_54 0) s_54 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54 : treeBlockF 0 7 ch_54 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 7 → ch_54 i = true := fun _ h1 h2 => treeBlockF_at nb_54 h1 h2
theorem lb_54 : LowerBin m_54 s_54 g_54 5 :=
  lowerDagV5 (kn_nil) rc_54 nc_54 (by decide +kernel)

def m_55 : Nat := 0x55005500aa00aa
def s_55 : List Nat := [0xaa00aa, 0x11001100220022, 0x50005000a000a, 0x55000000aa]
def g_55 : Nat := 0x15005500020022
def ep_55 : Nat := 0x40000000200000000000000000000400000002000000100000000200220000000000000000
def bds_55 : List (Nat × List Nat × Nat × Nat) := []
def cur_55 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb24b24d2d92a72652532400f 7 127 3 7 9 511 12 4095
def nh_55 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_55 : Nat → Nat × Nat := unpackForestF 0x32db2432a32632532400f 3 9
def ch_55 : Nat → Bool := dagCheckNodeV5 m_55 g_55 ep_55 1 1 bds_55 7 (dagTraceF m_55 s_55 4 f_55) cur_55 nh_55
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV5 m_55 g_55 ep_55 1 1 7 bds_55 (dagTraceF m_55 s_55 4 f_55) (cur_55 0) (nh_55 0) s_55 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55 : treeBlockF 0 7 ch_55 = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 7 → ch_55 i = true := fun _ h1 h2 => treeBlockF_at nb_55 h1 h2
theorem lb_55 : LowerBin m_55 s_55 g_55 5 :=
  lowerDagV5 (kn_nil) rc_55 nc_55 (by decide +kernel)

def m_56 : Nat := 0x1111111122222222
def s_56 : List Nat := [0x22222222, 0x101010102020202, 0x11001100220022, 0x111100002222]
def g_56 : Nat := 0x111111102020222
def ep_56 : Nat := 0x1000000000200010000000000020010000000202020000000000000000000000000000000000
def bds_56 : List (Nat × List Nat × Nat × Nat) := []
def cur_56 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58b12a44874e0701 0x192440a192430a123434d263a88d9d3a54d883a10d800f 7 127 3 7 10 1023 14 16383
def nh_56 : Nat → Nat := unpackHintV5 0x340c0b00c02c2b02c0b02c015002 0x0 10 1023 5 31
def f_56 : Nat → Nat × Nat := unpackForestF 0xc7463629d6490a6ce3469a10e886c00f 3 10
def ch_56 : Nat → Bool := dagCheckNodeV5 m_56 g_56 ep_56 1 1 bds_56 10 (dagTraceF m_56 s_56 4 f_56) cur_56 nh_56
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV5 m_56 g_56 ep_56 1 1 10 bds_56 (dagTraceF m_56 s_56 4 f_56) (cur_56 0) (nh_56 0) s_56 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_56 : treeBlockF 0 10 ch_56 = true := by decide +kernel
theorem nc_56 : ∀ i, 0 ≤ i → i < 10 → ch_56 i = true := fun _ h1 h2 => treeBlockF_at nb_56 h1 h2
theorem lb_56 : LowerBin m_56 s_56 g_56 5 :=
  lowerDagV5 (kn_nil) rc_56 nc_56 (by decide +kernel)

def m_57 : Nat := 0xa5a5a5a5
def s_57 : List Nat := [0x5050505, 0x21212121, 0xa500a5, 0xa5a5]
def g_57 : Nat := 0x1050525
def ep_57 : Nat := 0x4200000000000040020000000000000000000000000010000200000000000000000
def bds_57 : List (Nat × List Nat × Nat × Nat) := []
def cc_57_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682b1560ac148a80d009c3382704e09c1382704648c1182304607c8f81f03a2740e81b1341680c841c001 0x793875346c2c68245c305d444f484b40453c4130384c3444302c2c24254c2144184c144408100924fe3ffa3be637d233c53fb93bb537ad33a92fa52b91277d23703f643b60375833542f502b3c2728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_57_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707062606052494841404040404040242020202004 0xf54cf140ec4ce840e128dd24d828d424cc38c834c018bc14b130b244a3489f40983c94308d4c894484188014 8 255 3 7 10 1023 16 65535
def cur_57 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_57_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_57_0 p) (Nat.blt p 32)
def hc_57_0 : Nat → Nat := unpackHintV5 0xfa27b13925c04dc2654aea160aa084d1a50d28090248023090c68604112080fc47833a11c08bd25a22b111246902a50d400b0002 0x0 13 8191 5 31
def hc_57_1 : Nat → Nat := unpackHintV5 0xa2351027893c09a24a1a501204900461218d0447e23649a08c845292140e145102230e187003041800a1038c1c00a20500188006 0x0 13 8191 5 31
def hc_57_2 : Nat → Nat := unpackHintV5 0x6 0x0 6 63 3 7
def nh_57 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_57_2 (Nat.sub p 64)) (hc_57_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_57_0 p) (Nat.blt p 32)
def f_57 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c838c834053fbc18bc14053b0537b2440533052f052b97489740943c94300527814c814480188014052375387534043f682c6824043b04375d440433042f042b43484340413c413004272c4c2c442c2c2c240423214c2144041f144c1444041b041709240413000f 6 10
def ch_57 : Nat → Bool := dagCheckNodeV5 m_57 g_57 ep_57 1 1 bds_57 64 (dagTraceF m_57 s_57 5 f_57) cur_57 nh_57
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV5 m_57 g_57 ep_57 1 1 64 bds_57 (dagTraceF m_57 s_57 5 f_57) (cur_57 0) (nh_57 0) s_57 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_0 : treeBlockF 0 32 ch_57 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_1 : treeBlockF 32 64 ch_57 = true := by decide +kernel
theorem nj_57_1 : ∀ i, 0 ≤ i → i < 64 → ch_57 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_57_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_57_1 h1 h2)
theorem nc_57 : ∀ i, 0 ≤ i → i < 64 → ch_57 i = true := nj_57_1
theorem lb_57 : LowerBin m_57 s_57 g_57 6 :=
  lowerDagV5 (kn_nil) rc_57 nc_57 (by decide +kernel)

def m_58 : Nat := 0x5050505050505050
def s_58 : List Nat := [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050]
def g_58 : Nat := 0x10105010505050
def ep_58 : Nat := 0x1040400000001040000040000010004000400000000000000000000000101000100000000000000000000000
def bds_58 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1), (m_10, s_10, 4, g_10), (m_13, s_13, 4, g_13), (m_6, s_6, 4, g_6)]
def cc_58_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_58_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_58 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_58_1 (Nat.sub p 32)) (cc_58_0 p) (Nat.blt p 32)
def hc_58_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e56655092040a6ad8c0011820539b81622002630805682cb74a008803a6b2b0810 15 32767 6 63
def hc_58_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e754ae0732b4dad55068b56 13 8191 6 63
def nh_58 : Nat → Nat := fun p => Bool.rec (hc_58_1 (Nat.sub p 32)) (hc_58_0 p) (Nat.blt p 32)
def f_58 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_58 : Nat → Bool := dagCheckNodeV5 m_58 g_58 ep_58 1 1 bds_58 43 (dagTraceF m_58 s_58 6 f_58) cur_58 nh_58
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV5 m_58 g_58 ep_58 1 1 43 bds_58 (dagTraceF m_58 s_58 6 f_58) (cur_58 0) (nh_58 0) s_58 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_0 : treeBlockF 0 32 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_1 : treeBlockF 32 43 ch_58 = true := by decide +kernel
theorem nj_58_1 : ∀ i, 0 ≤ i → i < 43 → ch_58 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_58_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_58_1 h1 h2)
theorem nc_58 : ∀ i, 0 ≤ i → i < 43 → ch_58 i = true := nj_58_1
theorem lb_58 : LowerBin m_58 s_58 g_58 7 :=
  lowerDagV5 (kn_cons lb_1 (kn_cons lb_10 (kn_cons lb_13 (kn_cons lb_6 (kn_nil))))) rc_58 nc_58 (by decide +kernel)

def m_59 : Nat := 0x55aa000055aa
def s_59 : List Nat := [0xaa000000aa, 0x112200001122, 0x50a0000050a, 0x55aa]
def g_59 : Nat := 0x150200005522
def ep_59 : Nat := 0x402000000000000000000000000000000000000004020000000000001002000000220000000000000000
def bds_59 : List (Nat × List Nat × Nat × Nat) := []
def cur_59 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb25935b2a73294c80f 7 127 3 7 6 63 9 511
def nh_59 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_59 : Nat → Nat × Nat := unpackForestF 0x1b6c86a33194c80f 3 6
def ch_59 : Nat → Bool := dagCheckNodeV5 m_59 g_59 ep_59 1 1 bds_59 7 (dagTraceF m_59 s_59 4 f_59) cur_59 nh_59
set_option maxHeartbeats 0 in
theorem rc_59 : dagCheckRootsV5 m_59 g_59 ep_59 1 1 7 bds_59 (dagTraceF m_59 s_59 4 f_59) (cur_59 0) (nh_59 0) s_59 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59 : treeBlockF 0 7 ch_59 = true := by decide +kernel
theorem nc_59 : ∀ i, 0 ≤ i → i < 7 → ch_59 i = true := fun _ h1 h2 => treeBlockF_at nb_59 h1 h2
theorem lb_59 : LowerBin m_59 s_59 g_59 5 :=
  lowerDagV5 (kn_nil) rc_59 nc_59 (by decide +kernel)

def m_60 : Nat := 0xf0f0f0f0f0f0f0f0
def s_60 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_60 : Nat := 0x10105010505070
def ep_60 : Nat := 0x1040402000001040000040200010004000400020000000000000000000101000100000200010105010505040
def bds_60 : List (Nat × List Nat × Nat × Nat) := [(m_29, s_29, 5, g_29), (m_51, s_51, 5, g_51), (m_48, s_48, 6, g_48), (m_47, s_47, 6, g_47), (m_1, s_1, 4, g_1), (m_58, s_58, 7, g_58), (m_42, s_42, 5, g_42), (m_46, s_46, 6, g_46), (m_39, s_39, 6, g_39), (m_36, s_36, 5, g_36)]
def cur_60 : Nat → List (Nat × Nat) := unpackCursorV5 0x7971696861595851494841390e01 0x204d433810e42488cd824590cc342d0f233b4ce92370cd023104c01f 8 255 3 7 10 1023 14 16383
def nh_60 : Nat → Nat := unpackHintV5 0xaad2a8d6eb736d0736006de2c508eb508004b02c310d0310002b22f124c70009200000 0x18c631aeaa5d43aa5ad6759d6baa86b5ad6318c754f7bd7ddead6b58c631d53def1f3793bcc6318c6b972e1c356aaaa8d1aaab54ea8d5eacaaad6b58c631ce955519a0d635d54baa56aaaaaaccad53abb546acaab5ad7318ea955519a5b18c9be6e80c6318cf1e3c386739ce318c77a0e00000c180000700e00c1e040205c001be89ec6dd019c67aa8f54739cf718ea8380000011000700e06c01810205c009b939ec6f9e0338cf1e3c393aaaaaa87000000001261c0381b00603c0804006b1ae5cb872d6b5dc63bd2d6b5cc639d4ef3 20 1048575 9 511
def f_60 : Nat → Nat × Nat := unpackForestF 0x63314cc523909223310cd824590c42330d0b43104c01f 4 10
def ch_60 : Nat → Bool := dagCheckNodeV5 m_60 g_60 ep_60 3 7 bds_60 13 (dagTraceF m_60 s_60 8 f_60) cur_60 nh_60
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsV5 m_60 g_60 ep_60 3 7 13 bds_60 (dagTraceF m_60 s_60 8 f_60) (cur_60 0) (nh_60 0) s_60 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60 : treeBlockF 0 13 ch_60 = true := by decide +kernel
theorem nc_60 : ∀ i, 0 ≤ i → i < 13 → ch_60 i = true := fun _ h1 h2 => treeBlockF_at nb_60 h1 h2
theorem lb_60 : LowerBin m_60 s_60 g_60 9 :=
  lowerDagV5 (kn_cons lb_29 (kn_cons lb_51 (kn_cons lb_48 (kn_cons lb_47 (kn_cons lb_1 (kn_cons lb_58 (kn_cons lb_42 (kn_cons lb_46 (kn_cons lb_39 (kn_cons lb_36 (kn_nil))))))))))) rc_60 nc_60 (by decide +kernel)

def m_61 : Nat := 0xff00ff00ff00ff00
def s_61 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_61 : Nat := 0x100170013005700
def ep_61 : Nat := 0x1200400000001600000044000000000000000000010006000200020001001200130002000100140010005400
def bds_61 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8), (m_27, s_27, 7, g_27), (m_13, s_13, 4, g_13), (m_41, s_41, 5, g_41), (m_38, s_38, 5, g_38), (m_45, s_45, 4, g_45), (m_35, s_35, 5, g_35), (m_2, s_2, 4, g_2), (m_3, s_3, 4, g_3)]
def cc_61_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xec1d83b0722e41c0780700e01c03616c0d816a663cc094328240c80847082103e27c0f81d1343680c841c001 0x3ad4070280d028160782a0d07d278f24b1b48e3290c60a70b84b14086260ac481197b5f2d6b652d5c95a99225e202bc220503d270695e096c00cd402da404c510849c0d148152f05453076a408d08080a51b4fa169736d1e61a1cba4f954971091dfd21bd23f78476ec8ddd519b814f6e296d851daca1b113f56276604dc40998712f0c2560649c04918001f 11 2047 5 31 11 2047 19 524287
def cc_61_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xa8291a42909ca25882208822088211841d44e912440f2348d034085200801c4430c4300c02100800 0x7d141e4507650205607e971ea4c64171d02468941b14f6a52d99476450eac58a914a6c509697e425b8295dca5370931ba4062131196c3e05171343c051115c3a0516460565b1095c541b0d8144e0b141344c0d0c814300511350469750a55 10 1023 4 15 11 2047 18 262143
def cc_61_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x9c4e2712390482251076ba198c86432174b855231107a3c1e0c6602914084401c8540400 0x2f460ba5b2e06cb44d2c834c2d7efb5bb6d5ec353ae57a625d949663255809462c50a2131f25c9e0929a3fa48ee82379c8ce64606c132556092971a85c8b142185c8b141a04c86d023c608d1422360841b1984c7c971e024 9 511 3 7 11 2047 18 262143
def cc_61_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xb8b8b8b1949089888180808080795c5851504948484848483a38382a0c080801 0x3e024fd14feb5ef694b895ff2093bc52e4d53a353e6d278a3f484cb7814dad474460ce1b32a5cc8093525fd296f3257c694f0134 8 255 3 7 11 2047 18 262143
def cc_61_4 : Nat → List (Nat × Nat) := unpackCursorV5 0x821042083c5780f01bab34660b95702a4540a815028250098912220440790a5122240480901022004003c807 0x5025c9f4a13c57274a84e05c7e49f348ddd0afcc9370a24ed44fd849da59372f2672c939a4a7af94b4828e5a50da0a6af1494428a5850516284804c222b91c052489fc893b8f26f1a4cd9c17ae02b4204e5408e51ae49b518c6a11657228a83313f5b276824dca499c485c6529a7a516140c420147c47d0c4ee0c99b203f59076740dc9819c101f81026f6d3a1d273194f582967251c94a1c0024 11 2047 4 15 11 2047 19 524287
def cc_61_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x3440 0x28a2f5134e 3 7 1 1 11 2047 19 524287
def cur_61 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (cc_61_5 (Nat.sub p 160)) (cc_61_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_61_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_61_2 (Nat.sub p 64)) (cc_61_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_61_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def hc_61_0 : Nat → Nat := unpackHintV5 0xab21956402aa02d4113a82014dc2a978452609a4c01498029082d1c05a2e0b3154a16cc3f9346bb38ca4d146ce28d004c4569444528802143d4062280c00e31e91da918ab008294001000000 0x1b0fb36717b5806c77b5800000000000b5802d6000000000001b00008002006002a802a8000282154440100000aa4555055555005014440046e8286aa82aaaaaa2800155400010aa0154000000046c0002000000600aa00aa000221b818df0c3ec7b3754307c11ea88555dee38329e0c000000554818ea8631800ea8610072002aa0236aa82aaaaaa280154000400000154012a000154000400000046c80800000801540154000141055555555 19 524287 8 255
def hc_61_1 : Nat → Nat := unpackHintV5 0xd38034707d1c034205cbc4f0926ab5725d5096016530594c023b188b03dcc604aa89111944400f12037054cc102f43c97262184486001f02868141148c3e070f8003707014c80005 0x2dee1cbddb1c11b0ea00318c600000000aa00aa00015400000000aa00aa01bddd66ce6d77baeeb00005deeb000000000002000000018004000000001b005504001401540137b8643bd878703bdd0d2daddae66ce6c8a1aef6af6bdee050023810026f600000e1c000abb 18 262143 8 255
def hc_61_2 : Nat → Nat := unpackHintV5 0xc8c171a09c5416fa1bbe802ee0cb3882943a80251b050599296105570155c00530414c004f040ec503941cc52030014b7092706c83191cc40730018c40630012c602526040540010 0xdd6f66ce6c8770f7b0f0e04000070e0000551000000036000001000400c0055005500401100000aa00000000555500000001c3800001555477b3671d81d0000000000000555500437103d8edbb365b1c16d2d9b169b38c3b6cd70ed911b1c736bbd81d362d 18 262143 8 255
def hc_61_3 : Nat → Nat := unpackHintV5 0x89a2285e3c856088332377db672954688a1647415af98502ad4e0224a43c4a40047b293c5b6371542d0a128f411f79814aad135151191c1120710d050ed200e6070e1050c81902c9c0101c0100000010 0xdbeaab70e1cf22a22a387156aaaa80702c903aa18ea87505b0a0080018c06708060aa82aaaaaaa28015400154012a000000000055416c008080020000000000154015401410000000a02dd50002aa81000005500c002d80000000002a8800802a801455555005baaaa87011001041411c15505555555450dbc00d871e001c70e00005538c70f7b0e00401c0e7aa38e8e3a088dd0541c0a0e4aaaaaa82aa2a80154004000000b2015400001540046c00000080000202001540154000141080022aa80d8000aa80141115555554151e808d80442aaaaaa0aa8a00055000011b0002000e00001003001540154010044081ef7b385b0e6f6107d9cda6f7b0e16d000200e000030020e0006c00000550010015500dec6443dee0 20 1048575 8 255
def hc_61_4 : Nat → Nat := unpackHintV5 0xef0a1c91536a2862fa5c362981c52b053cc49c91474fda51d32835c4a6ae0ad4815a9003421068400cc84171282865c46ca0759809a51102321f2123e4007c800f4051de0a3a8144c2900098 0xaa0000550055000aa0000000055005500950000aaaa0000000000080002361000554000000000000008002aa802a806ca876c00e0511b02aaa229e3a1d04000f381c20554155555514aaaa2a21d5baaaa1d555438a8aa555555555555a28aaa223871556aaadd55555445555555511e1555555555555402980000000154015402a8a2aaaa20e1c55555dee1db77436aaa6aaaaaa9555555556a8e739eaaaa9aa9555555540298000000015401540255739aeaa569aa9739aeaaaaaa2a2aaaaaaab755478aa2aaa995555555555555a82aa2238715773bdaeaaaa6aa955ae56aaa96baaaaab75555445555555511e15555555559555 19 524287 8 255
def hc_61_5 : Nat → Nat := unpackHintV5 0x1759c500d4a49c151400054 0x46c000aa020600040000000000aa022000aa0021b012aa00055236140555415555410005047088554155555514aa000000000055550000002aa0000000055005500 18 262143 8 255
def nh_61 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (hc_61_5 (Nat.sub p 160)) (hc_61_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_61_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_61_2 (Nat.sub p 64)) (hc_61_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_61_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def f_61 : Nat → Nat × Nat := unpackForestF 0x169f44d3805a5ce25c9c4a13857270a84e05c0168f328de649b80b430149f2c9380525c4b5c896a31a4fe349dc804c8d26f1c0523499c4b50892b912542242e00a478049d024ee100c42014812670207e0409c002401486f714dedaf3e0247b4a4028fde41200a3b778a4028dc0519b8b5371692e4d51c51f8094f6f0280252db5a88094701286c697d8d2db3c60670d8c695d912e32024634a6024fd5dafb0134576b6b918170b62e06c576aeb24d1641a2bb53572bc024ecc62c18c524e47e9c8ed4426272374f0489c8ccc62826460314be93581252e18a5b428c08514116282136043680841b0c52b9d5603a4b87d140e9261dc503b28074090c52998a4c314806453cc8a59a2503228e6450cc42600937116be5c4d045ad954602a2d8541b045ab93134270584c0d045a988a5e214ba44d40852a8895e1249e2492c71a80e0501248e340a049218914e120962a0f0541a09043120562408c440a009330f49c024bc34af0092b0b6900914c22288424e046a40b148152f023420124e0405004918001f 8 11
def ch_61 : Nat → Bool := dagCheckNodeV5 m_61 g_61 ep_61 3 7 bds_61 164 (dagTraceF m_61 s_61 8 f_61) cur_61 nh_61
set_option maxHeartbeats 0 in
theorem rc_61 : dagCheckRootsV5 m_61 g_61 ep_61 3 7 164 bds_61 (dagTraceF m_61 s_61 8 f_61) (cur_61 0) (nh_61 0) s_61 8 = true := by decide +kernel
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
theorem nb_61_5 : treeBlockF 160 164 ch_61 = true := by decide +kernel
theorem nj_61_1 : ∀ i, 0 ≤ i → i < 64 → ch_61 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_61_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_61_1 h1 h2)
theorem nj_61_2 : ∀ i, 0 ≤ i → i < 96 → ch_61 i = true := block_join nj_61_1 (fun _ h1 h2 => treeBlockF_at nb_61_2 h1 h2)
theorem nj_61_3 : ∀ i, 0 ≤ i → i < 128 → ch_61 i = true := block_join nj_61_2 (fun _ h1 h2 => treeBlockF_at nb_61_3 h1 h2)
theorem nj_61_4 : ∀ i, 0 ≤ i → i < 160 → ch_61 i = true := block_join nj_61_3 (fun _ h1 h2 => treeBlockF_at nb_61_4 h1 h2)
theorem nj_61_5 : ∀ i, 0 ≤ i → i < 164 → ch_61 i = true := block_join nj_61_4 (fun _ h1 h2 => treeBlockF_at nb_61_5 h1 h2)
theorem nc_61 : ∀ i, 0 ≤ i → i < 164 → ch_61 i = true := nj_61_5
theorem lb_61 : LowerBin m_61 s_61 g_61 9 :=
  lowerDagV5 (kn_cons lb_8 (kn_cons lb_27 (kn_cons lb_13 (kn_cons lb_41 (kn_cons lb_38 (kn_cons lb_45 (kn_cons lb_35 (kn_cons lb_2 (kn_cons lb_3 (kn_nil)))))))))) rc_61 nc_61 (by decide +kernel)

def m_62 : Nat := 0xff00ff00ff00ff
def s_62 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_62 : Nat := 0x17005700570077
def ep_62 : Nat := 0x40002000000040000000200000000000000000000600020002000000120002000200220014005400540044
def bds_62 : List (Nat × List Nat × Nat × Nat) := [(m_48, s_48, 6, g_48), (m_5, s_5, 4, g_5), (m_37, s_37, 5, g_37), (m_17, s_17, 5, g_17), (m_21, s_21, 5, g_21), (m_55, s_55, 5, g_55), (m_52, s_52, 5, g_52)]
def cc_62_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xbc2f0a5a90a42909ca348c2308c1f4785d1741d0741d06c9b05595054150541324c1304c0d607001 0x1245e4716904523ed68f3563a558d25c325704b4d36d24c345160f8b35d2ad44a15c040d871441a4d0724a1a918945a23158835e1ed586134161783a340c4d04c5e111682c5208d681b560415aa34f9ed2e23476ed0d914f5c51d293f384dcb84f2611c503f020dc001f 10 1023 4 15 11 2047 18 262143
def cc_62_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x88425d8e8743a1d0b7582c160a242201008032164a25028140a050210582010080400400 0x7c052092a80499f82a7a09a1b5e84d39e234764d5d134720d5c0346a971a05c48d35b34966d15493e62d7583513a4d9785c50111383450d293b465b169645656d795356525793034448d10834 9 511 3 7 11 2047 18 262143
def cc_62_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x8821184201699a0681a0681284451044101400c4300c0300c006c100401000400 0xb0132b14ca6d6a935948536b94512136a845a717a945d5a534f945a24d4904d08116803598132604c9c53a69429613a5042851761b5d92972415d8e571613d3c4d6305d8a170883d060d5f014 10 1023 4 15 11 2047 18 262143
def cur_62 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_62_2 (Nat.sub p 64)) (cc_62_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_62_0 p) (Nat.blt p 32)
def hc_62_0 : Nat → Nat := unpackHintV5 0x84c640a39ca76e500728039401bf16c23b61002fa1d75109649480623c09170e880744002200108107d0e2c6496200b10056052b0013448950a448c1ec7080ec00800000 0x339d39b280274eacc1541469ac00aa0b35ab5059c00a38016aaa0b56acd059b366d3009ce472802a8d41598d1a0b39a33a6ce74e6ca00aa08d1ab3050000550005500055 17 131071 7 127
def hc_62_1 : Nat → Nat := unpackHintV5 0xcf05cc85c60dc600c00cc000ba0c9abf9a809a809a80950b77bb7780740770084bc9458c448241073d87368e3680368032880e490e000e000b850b8002920005 0x4e7553a00a00aa9d00414b214b2053560059bd7a82a82ce0053c00f5eacd07aaa82cd9b369ce720079401599d3a0aa75059cd2733 16 65535 7 127
def hc_62_2 : Nat → Nat := unpackHintV5 0x37006d02da01b00aad6d482a7054e029c038377000e001c0038007000e001c0034086800c0206638a050f0a14141428005 0x5a9d5000282854eaa8000ea03500000aaa9c0000134a134a139ce73 15 32767 7 127
def nh_62 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_62_2 (Nat.sub p 64)) (hc_62_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_62_0 p) (Nat.blt p 32)
def f_62 : Nat → Nat × Nat := unpackForestF 0x2c04caa516b14caa1140b4fa117a845da04d6803502d2e514e9450a604c9413a50428a972295d8a572285d8a1700b4770d79c34e7a4a9e9267a0a9f0147a099c234704d5c134700d5c03402d0d9b4968971a05c66d14094f5ed757b515e17009474d16934564cd7933564c5793b4a4ed193034024fcec5e3b1690a34420d0ec523ad68eb563a558093730d24ca5c32570c3450213ca35d28d44a15c0211c5c5a171585b5e16d586a4a1a918593416178083f05178145a0c8d0313405148135a04d581056020dc001f 7 11
def ch_62 : Nat → Bool := dagCheckNodeV5 m_62 g_62 ep_62 3 7 bds_62 89 (dagTraceF m_62 s_62 7 f_62) cur_62 nh_62
set_option maxHeartbeats 0 in
theorem rc_62 : dagCheckRootsV5 m_62 g_62 ep_62 3 7 89 bds_62 (dagTraceF m_62 s_62 7 f_62) (cur_62 0) (nh_62 0) s_62 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_0 : treeBlockF 0 32 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_1 : treeBlockF 32 64 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_2 : treeBlockF 64 89 ch_62 = true := by decide +kernel
theorem nj_62_1 : ∀ i, 0 ≤ i → i < 64 → ch_62 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_62_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_62_1 h1 h2)
theorem nj_62_2 : ∀ i, 0 ≤ i → i < 89 → ch_62 i = true := block_join nj_62_1 (fun _ h1 h2 => treeBlockF_at nb_62_2 h1 h2)
theorem nc_62 : ∀ i, 0 ≤ i → i < 89 → ch_62 i = true := nj_62_2
theorem lb_62 : LowerBin m_62 s_62 g_62 8 :=
  lowerDagV5 (kn_cons lb_48 (kn_cons lb_5 (kn_cons lb_37 (kn_cons lb_17 (kn_cons lb_21 (kn_cons lb_55 (kn_cons lb_52 (kn_nil)))))))) rc_62 nc_62 (by decide +kernel)

def m_63 : Nat := 0xcccccccc33333333
def s_63 : List Nat := [0x4444444411111111, 0x33333333, 0xc0c0c0c03030303, 0xcc00cc00330033, 0xcccc00003333]
def g_63 : Nat := 0x4044413131333
def ep_63 : Nat := 0x440000000200004004000000020000404000202020000000000000000000004044410101000
def bds_63 : List (Nat × List Nat × Nat × Nat) := [(m_30, s_30, 5, g_30), (m_16, s_16, 5, g_16), (m_19, s_19, 5, g_19), (m_20, s_20, 5, g_20), (m_17, s_17, 5, g_17), (m_18, s_18, 5, g_18), (m_22, s_22, 5, g_22), (m_7, s_7, 4, g_7)]
def cur_63 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0xb4f43701f 4 15 2 3 10 1023 12 4095
def nh_63 : Nat → Nat := unpackHintV5 0x5c794d49d0173c0005 0x156ef5e9d675c38779def77def79dee5ef3bdcbdee5ef72f7bdef7bdef37be6bc0eb3ae1c3bdef74bb72e17bdef7bdef75e9d675ab3b0e1a39870e772efb976e5ee5d772e7b971dcbd72f7 18 262143 8 255
def f_63 : Nat → Nat × Nat := unpackForestF 0x1d3e1b81f 1 10
def ch_63 : Nat → Bool := dagCheckNodeV5 m_63 g_63 ep_63 3 7 bds_63 3 (dagTraceF m_63 s_63 7 f_63) cur_63 nh_63
set_option maxHeartbeats 0 in
theorem rc_63 : dagCheckRootsV5 m_63 g_63 ep_63 3 7 3 bds_63 (dagTraceF m_63 s_63 7 f_63) (cur_63 0) (nh_63 0) s_63 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63 : treeBlockF 0 3 ch_63 = true := by decide +kernel
theorem nc_63 : ∀ i, 0 ≤ i → i < 3 → ch_63 i = true := fun _ h1 h2 => treeBlockF_at nb_63 h1 h2
theorem lb_63 : LowerBin m_63 s_63 g_63 8 :=
  lowerDagV5 (kn_cons lb_30 (kn_cons lb_16 (kn_cons lb_19 (kn_cons lb_20 (kn_cons lb_17 (kn_cons lb_18 (kn_cons lb_22 (kn_cons lb_7 (kn_nil))))))))) rc_63 nc_63 (by decide +kernel)

def m_64 : Nat := 0xffff0000ffff
def s_64 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_64 : Nat := 0x175700005777
def ep_64 : Nat := 0x402000000000000000000000004000000020000006020000020000001202000002220000145400005444
def bds_64 : List (Nat × List Nat × Nat × Nat) := [(m_39, s_39, 6, g_39), (m_9, s_9, 4, g_9), (m_34, s_34, 5, g_34), (m_19, s_19, 5, g_19), (m_14, s_14, 5, g_14), (m_54, s_54, 5, g_54), (m_59, s_59, 5, g_59)]
def cc_64_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xbc2f0a5a90a42909ca348c2308c1f4785d1741d0741d06c9b05595054150541324c1304c0d607001 0x1245e4716904523ed68f3563a558d25c325704b4d36d24c345160f8b35d2ad44a15c040d871441a4d0724a1a918945a23158835e1ed586134161783a340c4d04c5e111682c5208d681b560415aa34f9ed2e23476ed0d914f5c51d293f384dcb84f2611c503f020dc001f 10 1023 4 15 11 2047 18 262143
def cc_64_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x88425d8e8743a1d0b7582c160a242201008032164a25028140a050210582010080400400 0x7c052092a80499f82a7a09a1b5e84d39e234764d5d134720d5c0346a971a05c48d35b34966d15493e62d7583513a4d9785c50111383450d293b465b169645656d795356525793034448d10834 9 511 3 7 11 2047 18 262143
def cc_64_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x8821184201699a0681a0681284451044101400c4300c0300c006c100401000400 0xb0132b14ca6d6a935948536b94512136a845a717a945d5a534f945a24d4904d08116803598132604c9c53a69429613a5042851761b5d92972415d8e571613d3c4d6305d8a170883d060d5f014 10 1023 4 15 11 2047 18 262143
def cur_64 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_64_2 (Nat.sub p 64)) (cc_64_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_64_0 p) (Nat.blt p 32)
def hc_64_0 : Nat → Nat := unpackHintV5 0x84c640a39ca76e500728039401bf16c23b61002fa1d75109649480623c09170e880744002200108107d0e2c6496200b10056052b0013448950a448c1ec7080ec00800000 0x339d39b280274eacc1541469ac00aa0b35ab5059c00a38016aaa0b56acd059b366d3009ce472802a8d41598d1a0b39a33a6ce74e6ca00aa08d1ab3050000550005500055 17 131071 7 127
def hc_64_1 : Nat → Nat := unpackHintV5 0xcf05cc85c60dc600c00cc000ba0c9abf9a809a809a80950b77bb7780740770084bc9458c448241073d87368e3680368032880e490e000e000b850b8002920005 0x4e7553a00a00aa9d00414b214b2053560059bd7a82a82ce0053c00f5eacd07aaa82cd9b369ce720079401599d3a0aa75059cd2733 16 65535 7 127
def hc_64_2 : Nat → Nat := unpackHintV5 0x37006d02da01b00aad6d482a7054e029c038377000e001c0038007000e001c0034086800c0206638a050f0a14141428005 0x5a9d5000282854eaa8000ea03500000aaa9c0000134a134a139ce73 15 32767 7 127
def nh_64 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_64_2 (Nat.sub p 64)) (hc_64_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_64_0 p) (Nat.blt p 32)
def f_64 : Nat → Nat × Nat := unpackForestF 0x2c04caa516b14caa1140b4fa117a845da04d6803502d2e514e9450a604c9413a50428a972295d8a572285d8a1700b4770d79c34e7a4a9e9267a0a9f0147a099c234704d5c134700d5c03402d0d9b4968971a05c66d14094f5ed757b515e17009474d16934564cd7933564c5793b4a4ed193034024fcec5e3b1690a34420d0ec523ad68eb563a558093730d24ca5c32570c3450213ca35d28d44a15c0211c5c5a171585b5e16d586a4a1a918593416178083f05178145a0c8d0313405148135a04d581056020dc001f 7 11
def ch_64 : Nat → Bool := dagCheckNodeV5 m_64 g_64 ep_64 3 7 bds_64 89 (dagTraceF m_64 s_64 7 f_64) cur_64 nh_64
set_option maxHeartbeats 0 in
theorem rc_64 : dagCheckRootsV5 m_64 g_64 ep_64 3 7 89 bds_64 (dagTraceF m_64 s_64 7 f_64) (cur_64 0) (nh_64 0) s_64 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_0 : treeBlockF 0 32 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_1 : treeBlockF 32 64 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_2 : treeBlockF 64 89 ch_64 = true := by decide +kernel
theorem nj_64_1 : ∀ i, 0 ≤ i → i < 64 → ch_64 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_64_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_64_1 h1 h2)
theorem nj_64_2 : ∀ i, 0 ≤ i → i < 89 → ch_64 i = true := block_join nj_64_1 (fun _ h1 h2 => treeBlockF_at nb_64_2 h1 h2)
theorem nc_64 : ∀ i, 0 ≤ i → i < 89 → ch_64 i = true := nj_64_2
theorem lb_64 : LowerBin m_64 s_64 g_64 8 :=
  lowerDagV5 (kn_cons lb_39 (kn_cons lb_9 (kn_cons lb_34 (kn_cons lb_19 (kn_cons lb_14 (kn_cons lb_54 (kn_cons lb_59 (kn_nil)))))))) rc_64 nc_64 (by decide +kernel)

def m_65 : Nat := 0x6666666666666666
def s_65 : List Nat := [0x2222222222222222, 0x606060606060606, 0x66006600660066, 0x666600006666, 0x66666666]
def g_65 : Nat := 0x6064602464666
def ep_65 : Nat := 0x240402000000640000044200006004000440020000606020202020000000000000000000000000000000000
def bds_65 : List (Nat × List Nat × Nat × Nat) := [(m_25, s_25, 7, g_25), (m_31, s_31, 5, g_31), (m_33, s_33, 5, g_33), (m_7, s_7, 4, g_7), (m_37, s_37, 5, g_37), (m_35, s_35, 5, g_35), (m_32, s_32, 6, g_32), (m_53, s_53, 6, g_53), (m_34, s_34, 5, g_34)]
def cur_65 : Nat → List (Nat × Nat) := unpackCursorV5 0x8421084210805f1749c1689a064590605715495050540488e4380e0380e007401 0x385360a71481429a0438c68614de1a34244a4088c1626243c46887091d1fb23b546e68cf127de43b29f550e897cd2b924f048ca21902b1846206c209801f 10 1023 4 15 10 1023 15 32767
def nh_65 : Nat → Nat := unpackHintV5 0x8f3d8e0fd6979b521c4315653de96cd414f6de5248c93f64e0f9c1e3cb0e0ef01e3a00e0e581437c8ccdf200370064d9e1134a0ecb2aff227d1861b420e9ce815927002a9c00005 0x631ec0d81b000018cfb18f7b18c633800f63d8f63d8c638771c00739ce3d8f63d8f6318d18c6800c6318c6319b366cd8c631ef6319f600318f60000358c7b1ec7b1ec01673ac631c3b8e1ec631ec630018c6318c68c6346318ead81b03600003d8f63d8f6318d6338c6010ed8c7bdd0c7300bd787b1ec7b1ec631a318d0018c638638d9b366c7b1ec7b1ec02ab7b876c02aa1db00009751eaa1ec631ec630018c63aaa98726cd9b367daf67daf6000b1ef6b5ef6b9ef6b1ef6000155f76e7bb6011ed9cf4739dfb9edfbd802ce75ad6b56f5b5df1b366cd9f67d9f67d805bb76ed80047b7550f7badee9ef75bd800047aa7ee7b7ef600739cf55533e4d9b366ce3decf3dece7dece3dec0000fb3ecfb3ec002abeedcf76c000e759cf51e7ee7b7ef600779d39ce9ce73d77c6cd9b367d9f67d9f6016eddbb60011edbf73dbf7b0039ce7aa366cd9b3ed7b3ed7b00b76eddb00aa8f43deeb7ba7bdd6f600012ea9fb9edfbd802ce75d554cf9def7bdec7b9ef7bded6b5f7bdef7bd8f73def7b59e5def7bdcf63dedeed3bbdef67def76eddbdafdacf5e503606c7b1cc7b18c007b1cc7b18c01577b46ec00155551bb000056a9d595baaa6cd9b363d8f63d8f6003d8f63d8f600739ceeddbb760009ddaaaaa3ded77b47bdaef600009d656eaa9b366cd8f63d8f63d800f63d8f63d802ce75bb76edd802aa776aa8f7b5ded1ef6bbd80002b595baaa6cd9b363d8f63d8f6003ddb1eed805ebceddbb76000aaced551ef6bbda3ded77b000056a9d57aa9b366cd8f63d8f63d805bb76ed80553b76edd802aaab3b47bdaef68f7b5dec00015aa75655366cd9bdcf73dec0373dcf7b007ee7b7ef600f7bdfb 22 4194303 9 511
def f_65 : Nat → Nat × Nat := unpackForestF 0x64f0c86153c2a1852f0a56149e31a0523786868fda121a3b589868dd21e1f44384868cc221842b0846106c209801f 5 10
def ch_65 : Nat → Bool := dagCheckNodeV5 m_65 g_65 ep_65 3 7 bds_65 25 (dagTraceF m_65 s_65 8 f_65) cur_65 nh_65
set_option maxHeartbeats 0 in
theorem rc_65 : dagCheckRootsV5 m_65 g_65 ep_65 3 7 25 bds_65 (dagTraceF m_65 s_65 8 f_65) (cur_65 0) (nh_65 0) s_65 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_65 : treeBlockF 0 25 ch_65 = true := by decide +kernel
theorem nc_65 : ∀ i, 0 ≤ i → i < 25 → ch_65 i = true := fun _ h1 h2 => treeBlockF_at nb_65 h1 h2
theorem lb_65 : LowerBin m_65 s_65 g_65 9 :=
  lowerDagV5 (kn_cons lb_25 (kn_cons lb_31 (kn_cons lb_33 (kn_cons lb_7 (kn_cons lb_37 (kn_cons lb_35 (kn_cons lb_32 (kn_cons lb_53 (kn_cons lb_34 (kn_nil)))))))))) rc_65 nc_65 (by decide +kernel)

def m_66 : Nat := 0xffffffff
def s_66 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_66 : Nat := 0x13575777
def ep_66 : Nat := 0x44200000000000440020000000000202020000000000130202220000000010545444
def bds_66 : List (Nat × List Nat × Nat × Nat) := [(m_46, s_46, 6, g_46)]
def cur_66 : Nat → List (Nat × Nat) := fun _ => []
def nh_66 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_66 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_66 : dagCheckRootsV5 m_66 g_66 ep_66 1 1 0 bds_66 (dagTraceF m_66 s_66 6 f_66) (cur_66 0) (nh_66 0) s_66 6 = true := by decide +kernel
theorem nc_66 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_66 g_66 ep_66 1 1 bds_66 0 (dagTraceF m_66 s_66 6 f_66) cur_66 nh_66 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_66 : LowerBin m_66 s_66 g_66 7 :=
  lowerDagV5 (kn_cons lb_46 (kn_nil)) rc_66 nc_66 (by decide +kernel)

def m_67 : Nat := 0xffff0000ffff0000
def s_67 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_67 : Nat := 0x117000013570000
def ep_67 : Nat := 0x1240000000000000000000000016000000440000010600000202000001120000130200000114000010540000
def bds_67 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8), (m_26, s_26, 7, g_26), (m_10, s_10, 4, g_10), (m_51, s_51, 5, g_51), (m_50, s_50, 5, g_50), (m_40, s_40, 5, g_40), (m_44, s_44, 4, g_44), (m_33, s_33, 5, g_33), (m_0, s_0, 4, g_0), (m_12, s_12, 4, g_12)]
def cc_67_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xec1d83b0722e41c0780700e01c03616c0d816a663cc094328240c80847082103e27c0f81d1343680c841c001 0x3ad4070280d028160782a0d07d278f24b1b48e3290c60a70b84b14086260ac481197b5f2d6b652d5c95a99225e202bc220503d270695e096c00cd402da404c510849c0d148152f05453076a408d08080a51b4fa169736d1e61a1cba4f954971091dfd21bd23f78476ec8ddd519b814f6e296d851daca1b113f56276604dc40998712f0c2560649c04918001f 11 2047 5 31 11 2047 19 524287
def cc_67_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xa8291a42909ca25882208822088211841d44e912440f2348d034085200801c4430c4300c02100800 0x7d141e4507650205607e971ea4c64171d02468941b14f6a52d99476450eac58a914a6c509697e425b8295dca5370931ba4062131196c3e05171343c051115c3a0516460565b1095c541b0d8144e0b141344c0d0c814300511350469750a55 10 1023 4 15 11 2047 18 262143
def cc_67_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x9c4e2712390482251076ba198c86432174b855231107a3c1e0c6602914084401c8540400 0x2f460ba5b2e06cb44d2c834c2d7efb5bb6d5ec353ae57a625d949663255809462c50a2131f25c9e0929a3fa48ee82379c8ce64606c132556092971a85c8b142185c8b141a04c86d023c608d1422360841b1984c7c971e024 9 511 3 7 11 2047 18 262143
def cc_67_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xb8b8b8b1949089888180808080795c5851504948484848483a38382a0c080801 0x3e024fd14feb5ef694b895ff2093bc52e4d53a353e6d278a3f484cb7814dad474460ce1b32a5cc8093525fd296f3257c694f0134 8 255 3 7 11 2047 18 262143
def cc_67_4 : Nat → List (Nat × Nat) := unpackCursorV5 0x821042083c5780f01bab34660b95702a4540a815028250098912220440790a5122240480901022004003c807 0x5025c9f4a13c57274a84e05c7e49f348ddd0afcc9370a24ed44fd849da59372f2672c939a4a7af94b4828e5a50da0a6af1494428a5850516284804c222b91c052489fc893b8f26f1a4cd9c17ae02b4204e5408e51ae49b518c6a11657228a83313f5b276824dca499c485c6529a7a516140c420147c47d0c4ee0c99b203f59076740dc9819c101f81026f6d3a1d273194f582967251c94a1c0024 11 2047 4 15 11 2047 19 524287
def cc_67_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x3440 0x28a2f5134e 3 7 1 1 11 2047 19 524287
def cur_67 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (cc_67_5 (Nat.sub p 160)) (cc_67_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_67_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_67_2 (Nat.sub p 64)) (cc_67_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_67_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def hc_67_0 : Nat → Nat := unpackHintV5 0xab21956402aa02d4113a82014dc2a978452609a4c01498029082d1c05a2e0b3154a16cc3f9346bb38ca4d146ce28d004c4569444528802143d4062280c00e31e91da918ab008294001000000 0x1f0ff3e71ff7807c7ff7800000000000f7803de000000000001f00008002016002a802a8000282154440100000aa4555055555005014440047e828eaa82aaaaaa2800155400010aa0154000000047c0002000000e00aa00aa000221f839e72c3fd7f3f54709c11ea88555ffe38b2a61c000000554839ea8e73801ea9610072002aa023eaa82aaaaaa280154000400000154012a000154000400000047c80800000801540154000141055555555 19 524287 8 255
def hc_67_1 : Nat → Nat := unpackHintV5 0xd38034707d1c034205cbc4f0926ab5725d5096016530594c023b188b03dcc604aa89111944400f12037054cc102f43c97262184486001f02868141148c3e070f8003707014c80005 0x2ffe5cffdf5c11f0ea00b5ad600000000aa00aa00015400000000aa00aa01ffede7ce7dfbdbf6f00007ef6f000000000002000000058004000000001f00550400140154013ff9643ff879703ffd2d2fbdfbee7ce7c8a5affebfefffe050023810027fe00002e5c000abf 18 262143 8 255
def hc_67_2 : Nat → Nat := unpackHintV5 0xc8c171a09c5416fa1bbe802ee0cb3882943a80251b050599296105570155c00530414c004f040ec503941cc52030014b7092706c83191cc40730018c40630012c602526040540010 0xfd7fe7ce7c87f2fff0f2e04000172e000055100000003e000001000402c0055005500401100000aa00000000555500000005cb80000155547ff3e71f81d000000000000055550043f10bfaefbf3e5f5c17d2f9f1e9f38cbbeddf2ef911f5c73ebff81d3e3d 18 262143 8 255
def hc_67_3 : Nat → Nat := unpackHintV5 0x89a2285e3c856088332377db672954688a1647415af98502ad4e0224a43c4a40047b293c5b6371542d0a128f411f79814aad135151191c1120710d050ed200e6070e1050c81902c9c0101c0100000010 0xfceaabf2e5d322a22a387156aaaa81702c90baa5aea97505f0a0080059c16708160aa82aaaaaaa28015400154012a000000000055417c008080020000000000154015401410000000a02fd50002aa81000005502c002f80000000002a8800802a801455555005faaaa97011001041411c15505555555450fcc00f8726001d72e0000553acf2fff0e00401c0e7aa39e8eba088fd0541c0a0e4aaaaaa82aa2a80154004000000b2015400001540047c00000080000202001540154000141080022aa80f8000aa80141115555554151e808f80442aaaaaa0aa8a00055000011f0002000e0000100b001540154010044083ffff385f0e7fe107f9cfa7fff0e17d000200e000070020e0007c00000550010015500ffd644bffe0 20 1048575 8 255
def hc_67_4 : Nat → Nat := unpackHintV5 0xef0a1c91536a2862fa5c362981c52b053cc49c91474fda51d32835c4a6ae0ad4815a9003421068400cc84171282865c46ca0759809a51102321f2123e4007c800f4051de0a3a8144c2900098 0xaa0000550055000aa0000000055005500950000aaaa00000000000800023e1000554000000000000008002aa802a807ca977c00e0511f02aaa22a6ba5d040013381c20554155555514aaaa2a25d5faaaa5d555478a8aa555555555555a28aaa223871556aaafd55555445555555511e1555555555555402980000000154015402a8a2aaaa20e1c55555ffe5df7f4b6aaa6aaaaaa9555555556a8e739eaaaa9aa9555555540298000000015401540255f7bbeaa569aa9f7bbeaaaaaa2a2aaaaaaabf55478aa2aaa995555555555555a82aa22387157f3ffbeaaaa6aa957be56aaa9efaaaaabf5555445555555511e15555555559555 19 524287 8 255
def hc_67_5 : Nat → Nat := unpackHintV5 0x1759c500d4a49c151400054 0x47c000aa021600040000000000aa022000aa0021f012aa0005523e140555415555410005047088554155555514aa000000000055550000002aa0000000055005500 18 262143 8 255
def nh_67 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (hc_67_5 (Nat.sub p 160)) (hc_67_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_67_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_67_2 (Nat.sub p 64)) (hc_67_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_67_0 p) (Nat.blt p 32)) (Nat.blt p 96)
def f_67 : Nat → Nat × Nat := unpackForestF 0x169f44d3805a5ce25c9c4a13857270a84e05c0168f328de649b80b430149f2c9380525c4b5c896a31a4fe349dc804c8d26f1c0523499c4b50892b912542242e00a478049d024ee100c42014812670207e0409c002401486f714dedaf3e0247b4a4028fde41200a3b778a4028dc0519b8b5371692e4d51c51f8094f6f0280252db5a88094701286c697d8d2db3c60670d8c695d912e32024634a6024fd5dafb0134576b6b918170b62e06c576aeb24d1641a2bb53572bc024ecc62c18c524e47e9c8ed4426272374f0489c8ccc62826460314be93581252e18a5b428c08514116282136043680841b0c52b9d5603a4b87d140e9261dc503b28074090c52998a4c314806453cc8a59a2503228e6450cc42600937116be5c4d045ad954602a2d8541b045ab93134270584c0d045a988a5e214ba44d40852a8895e1249e2492c71a80e0501248e340a049218914e120962a0f0541a09043120562408c440a009330f49c024bc34af0092b0b6900914c22288424e046a40b148152f023420124e0405004918001f 8 11
def ch_67 : Nat → Bool := dagCheckNodeV5 m_67 g_67 ep_67 3 7 bds_67 164 (dagTraceF m_67 s_67 8 f_67) cur_67 nh_67
set_option maxHeartbeats 0 in
theorem rc_67 : dagCheckRootsV5 m_67 g_67 ep_67 3 7 164 bds_67 (dagTraceF m_67 s_67 8 f_67) (cur_67 0) (nh_67 0) s_67 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_0 : treeBlockF 0 32 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_1 : treeBlockF 32 64 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_2 : treeBlockF 64 96 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_3 : treeBlockF 96 128 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_4 : treeBlockF 128 160 ch_67 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67_5 : treeBlockF 160 164 ch_67 = true := by decide +kernel
theorem nj_67_1 : ∀ i, 0 ≤ i → i < 64 → ch_67 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_67_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_67_1 h1 h2)
theorem nj_67_2 : ∀ i, 0 ≤ i → i < 96 → ch_67 i = true := block_join nj_67_1 (fun _ h1 h2 => treeBlockF_at nb_67_2 h1 h2)
theorem nj_67_3 : ∀ i, 0 ≤ i → i < 128 → ch_67 i = true := block_join nj_67_2 (fun _ h1 h2 => treeBlockF_at nb_67_3 h1 h2)
theorem nj_67_4 : ∀ i, 0 ≤ i → i < 160 → ch_67 i = true := block_join nj_67_3 (fun _ h1 h2 => treeBlockF_at nb_67_4 h1 h2)
theorem nj_67_5 : ∀ i, 0 ≤ i → i < 164 → ch_67 i = true := block_join nj_67_4 (fun _ h1 h2 => treeBlockF_at nb_67_5 h1 h2)
theorem nc_67 : ∀ i, 0 ≤ i → i < 164 → ch_67 i = true := nj_67_5
theorem lb_67 : LowerBin m_67 s_67 g_67 9 :=
  lowerDagV5 (kn_cons lb_8 (kn_cons lb_26 (kn_cons lb_10 (kn_cons lb_51 (kn_cons lb_50 (kn_cons lb_40 (kn_cons lb_44 (kn_cons lb_33 (kn_cons lb_0 (kn_cons lb_12 (kn_nil))))))))))) rc_67 nc_67 (by decide +kernel)

def g_68 : Nat := 0x117175713575777
def ep_68 : Nat := 0x1240402000001640000044200016004000440020010606020202020001121202130202220114145410545444
def bds_68 : List (Nat × List Nat × Nat × Nat) := [(m_67, s_67, 9, g_67), (m_61, s_61, 9, g_61), (m_26, s_26, 7, g_26), (m_60, s_60, 9, g_60), (m_43, s_43, 7, g_43), (m_47, s_47, 6, g_47), (m_64, s_64, 8, g_64), (m_66, s_66, 7, g_66), (m_62, s_62, 8, g_62), (m_53, s_53, 6, g_53), (m_30, s_30, 5, g_30), (m_40, s_40, 5, g_40), (m_8, s_8, 4, g_8), (m_58, s_58, 7, g_58), (m_12, s_12, 4, g_12), (m_7, s_7, 4, g_7), (m_29, s_29, 5, g_29), (m_27, s_27, 7, g_27), (m_46, s_46, 6, g_46), (m_32, s_32, 6, g_32), (m_36, s_36, 5, g_36), (m_0, s_0, 4, g_0), (m_65, s_65, 9, g_65), (m_57, s_57, 6, g_57), (m_4, s_4, 4, g_4), (m_10, s_10, 4, g_10), (m_3, s_3, 4, g_3), (m_1, s_1, 4, g_1), (m_13, s_13, 4, g_13), (m_39, s_39, 6, g_39), (m_56, s_56, 5, g_56), (m_23, s_23, 5, g_23), (m_63, s_63, 8, g_63), (m_25, s_25, 7, g_25), (m_48, s_48, 6, g_48), (m_15, s_15, 6, g_15), (m_2, s_2, 4, g_2), (m_11, s_11, 4, g_11), (m_6, s_6, 4, g_6)]
def cc_68_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x92148063831c0881c4021830c0840bf0df80fc0781bb05c84e407203805c00e006823401982cc0640b201900c41582a2280c2001 0x1ed1c0908c06b4704daf8375f8166fe040440673900e11017ad20b45f018230295f8138fe02846010230239c80308c0756803f3f81b9cc0cae405d6201d3780ed7804ce404d6f021af00c9bc054be01a5707ab783b58c1c8de0d45f0622b82adbc126be08357029a380411a358bf19c5b8b62bc5314e286bf12b5785da7c1ad1e044bf002577ad27bc291dd246edf15f6d8abb2453d7f28eb11374f093a5e17d2c0b68d057440299bc13cda096630472fc219760ec5906e2582b0b41383e06c0102e0003f 13 8191 6 63 11 2047 21 2097151
def cc_68_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0eb1a4a90a4281a0280912408c63088620882117152a3ccf0384e0380b32c0b020c802008018806 0x2057e7f1fd884660119ee725e119d568779fdce73715c9bd62661bd9b5e619c9ad6f68d79906f6217d7857955be4d63911be345f8915e096f7c57de1576c51d704652511105c42111586c52d79285e50139134d4cd152836451790b5e5917d54574e519205e461590046 10 1023 4 15 11 2047 18 262143
def cc_68_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xfc1f07a2740e42f6db1b60682d01a02e35c0b8141a80500a012118628448480900146280408800c200c00000 0xbcdb9852f3016f5f0deba05d6daf5c56fb5ac7691baca31d8c62b08bd5d16eb62d56456ab8a74b14a89af4da6f974bf2695e4927c496f822befa55de8a7b11275c0bcb41494c1517026270340405954a22705c4d088ae1b155af2885e5409c9cd3549a2a88364e8bc9ad79622fab4575328ca01793c2b260463b28e6a118e4a39f95f47afc845fcd02222e7233088875a50a2f99046 11 2047 5 31 11 2047 19 524287
def cc_68_3 : Nat → List (Nat × Nat) := unpackCursorV5 0x98215842107c9f0749d07059364190605805c5705c143501405013144901401003c4f00780100000 0x20739404607f6d8fc93cbc133e26f7b4cef35e1aeb03556069ae0ef5a1d9b439b486fadcdf1b195b8373486a6d0d79f9a7392f06e65ad2f19fdd739ba57e72ae6e35c9c2b736d6b6cac6d15899e3733372646c4c6d4174372f017 10 1023 4 15 11 2047 19 524287
def cc_68_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xb02c0ac62988220881c66c5b06c165509404c5304c130485204448920080200801c4700580100000 0x702d435a682344fc5e9e8a53ad9271af4215f600bc0c05a6abf4cc73988b1145fdf0a7828160402d2d9ca56304a36c7b29e0605a0cb7bf1678b4be6609a2e3c48d69908d11f17a3a2946b648c6bd1497d7c2f19026858f1115fa1e39c3458844ff0693cc41318026 10 1023 4 15 11 2047 19 524287
def cc_68_5 : Nat → List (Nat × Nat) := unpackCursorV5 0xd8360d8333c8720b1ab1a866494650815f16d1a16098060162545504c9304c0c7300c006c1000400 0x2f8af5e85ebc0acf249eea3455450b96c8f049cd413048167724f52d42a2305bc58b66a8ea49dd093d246eb36dd329be1cb7b91277124f5f17a7d37c796f7024ede49ebdae36927a38d8d849dac93d4c546924f555baa2b14f26fa746f1c5be989bb4127a46c746d467137c616f6724ec21796c292a82a3404c52068200b4295f 10 1023 4 15 11 2047 19 524287
def cc_68_6 : Nat → List (Nat × Nat) := unpackCursorV5 0x4fb4e04e04e04834804804043e13e03e03e03e03a23a03a03a03a036236036036030330012f0e20e00e00e00e00c1006 0x87d6f8756386c6f85c6e8536f84b5f83b575834d82b4580a6f8025f7fa577f2477da377b16f7a95f7a1577994777937729277186e6f86263856638466e8455f03a2e0366e8566e0466d8446c34569a3767137659276512769e72694606767266c6065e726546d64b606cd6e6bd626b35d563556aa5f6a24f68a376815f6794f66137641276385e6105d6384e618422d9446084460b5e62c5f62457619562d1466105e60046 12 4095 5 31 11 2047 20 1048575
def cc_68_7 : Nat → List (Nat × Nat) := unpackCursorV5 0xf87c3e1c3e070381c0b3582c160b0582c13398486230180401e2f0709288031180c06003 0x1fb5fbf22c7b97ffa8c9f2d963da6fc345f746ebe0dbcabf78c58f04ffced2ba5ac2f044e98dfcf5fbbb39f6d7eec8ffd71bdc22ef5455e86b1ccd2b903f2e846e402fc411b841b70034 9 511 4 15 11 2047 19 524287
def cc_68_8 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0d82c1528fc2a030080401d6e87434d4ca04ca61307c3896cb051280d06030180180000 0x8fd708ed718e37095c6d944619324f91a479094f8f1478d9278b05c8a8448b34d8b45e8ab5e7085e89b4f893437004e8cc5f6f95e8c05e8b8568a0468884477127863557ea377913776927761278335475927308348446c8334e8126f7c16f751278246481b654fb4d813457813730036 9 511 3 7 11 2047 20 1048575
def cc_68_9 : Nat → List (Nat × Nat) := unpackCursorV5 0xc41805e93a1740d89a0b40680c09802e15c0b813214928050081100200400518a01022003084108008410001 0x9f35eaf56faed6bacd67aad63aa46fa8c67a645fa4457a3362a2b5aa1b529fb4a9806f8d8677285f64057310479e83d991279d3459a1379b15f9bb459b2379a25f3a46d9945f98b4a7205e6cc5d5a35d9db4f9ca4f9c2379a94f99937981277184e9705e9685695247949478e92793c7c9294f925709147c9024f 11 2047 5 31 11 2047 20 1048575
def cc_68_10 : Nat → List (Nat × Nat) := unpackCursorV5 0x9d2709c2709c243902318c1c764d90641725c1705c170368d0340d028ca020880200531405014005 0xb0c65b0368af8653c047ae47cadb70ad07c3b047a846fac455abb58a134a7706fab0553a847a745e3a06d7605fa9d71a9370a8673a7d7ea747ea0350a0b489907f7586f3805da685533845a5e72a5360a486da3a4633047a024aa224632047a1563a0c5ea02529886f7305f 10 1023 4 15 11 2047 20 1048575
def cc_68_11 : Nat → List (Nat × Nat) := unpackCursorV5 0xbc2b4a86a099251942509425081600802006d5b06c174585604cd304c1304c130484d50340000000 0xbf468bbc50b484d1d8271d027bb460be458bdb541c8271c027bbd6ebb562b8a6fbaa371b827b9d69b9468b8c527805fb384db7d7eb74589a07fb304db284db6672b5c60b204db2e72b4d6fb445eb3a6fb325fb2257bed6fbd563bcc62bc45aba452b826fb6a5fb52579986f7785f66057b184d1b027 10 1023 4 15 11 2047 20 1048575
def cc_68_12 : Nat → List (Nat × Nat) := unpackCursorV5 0xe0dc0370ee0dc1b07606c0d81913206216ecd81722e05c0b054126148290110a20402784f01e038258cb000b 0xd1464d0b65d0345cf865ca04542037cec7ccd46ccc57ecbc589b07fcb04dca26fda56fd9d6bd7567d6d63d5c6ed536fd4367d3b5fd2b57d1b45cf26fce267cda5fcca57caa379a86f908677a85f67857c9845410371f027c8b45c2a37408371e827c705cc7a4fc6a47c65703f835c4d70c3c6cc184dc1e72c2e72c2460c104dc8562c5b67c535dc4267c324fc0a378f067c005d7a04f3e8371e027 11 2047 5 31 11 2047 20 1048575
def cc_68_13 : Nat → List (Nat × Nat) := unpackCursorV5 0x5e9705c1615815154141411003c4f03c0f03c0f02d0b02c0741846014441100310c0030000000000 0xe8c59e8455e7b55e634fe3a4fe1237df8557b04f4483720827de247dd47cdc570dec6dddc61dca4fdba47dac64d947cd8b7cd827cd787cd6355cc23744037200271f827d4c7cd2354d346cd234ed026f9b86f 10 1023 4 15 11 2047 20 1048575
def cc_68_14 : Nat → List (Nat × Nat) := unpackCursorV5 0xd8760c9311c4310c4310b16c0b02756b5645812448120354d0340d0340761c0701c0700942008002 0x7017ec460ef458eeb540681706017ecd6eec562e216feb93705817ead6fea45ee196fcb15fc1157efd6fee563edc62ed45aeb452e116fca95fc09579c06f7d85f68857e984d05017e734de32374883721827e7469e524f7c84f46835e74684784de68454603521027e5c64e5365e4b45e0065e404545037e3569e2c68e24527b85fe184de0c51e024f 10 1023 4 15 11 2047 20 1048575
def cc_68_15 : Nat → List (Nat × Nat) := unpackCursorV5 0xf83f03e07c0f81f03a2740e81b1350ea0d0398730641c8178ee0b16600a11402804c2889009e13c022c40004 0xffc64fe47cfdb7cfd17cfc87cfb355b79374d0370a01709817f9c7cf7354f846cf734ee496f9d06fe416fff56ffed6bfc567fbd63fac6efa36ff9367f8b5ff7b57f6b45e396fdc967cd95fc3157b69379c86f930678005f6a057f60454b83709017f5345b61374b03708817f385cf414ff3147f2d704a035f4d62f2367f1b5ddb967cc94fb513791867f105d7f84f4983708017f0468ecc50ea84d07817 11 2047 5 31 11 2047 20 1048575
def cc_68_16 : Nat → List (Nat × Nat) := unpackCursorV5 0xb42b40b02b00ac2a63a4171a7006a36816806806616606226203d33443402c42c02c02252201e20aa0a00a0081004000 0x87e363dcd121d8d8d234486e3620cd12084dee696f5349398211224ac711c6e88631c40dba146ad0a34681d37be297e1e49ee616f69cafc3853d4c24e9d86f46431a1217cc50a70d04f2c026c3211618086510351601588c09c2c0360d01752c9388a09c1902f0805d841b6420d394924f0b56e856b1428d7a1469d09a5f7bd27c2457da529ea41278442fc1e174ac0ab0705341c2798810c56056220270a80d83005e0969ab99372841b82e05e098d2d094f40c2793a0d6098d04f84d820229380d41602f0345167ca7c191660b8ab0535581da7b3c53d7026f02855404279360dc1502f0114780e36c031859c29ec4147 12 4095 5 31 11 2047 21 2097151
def cc_68_17 : Nat → List (Nat × Nat) := unpackCursorV5 0xa42a40a40a40a218118007847237016e16836805695604c54a130d1e91e01c10e70a2043040021001000 0x584939720d55f24f1a469859aec74d56394aeff24f77d1bc7055db429ebe937578939b2176370af1b05543c279700dc4a04e0f0178d2b6bfa97db32beae9277ed1fb624fd5c24ed813f7e89fbf24fdaf07ead0178b236c64db2314d8fc24f8c0b635c53d5924f1786c8b830444d79dd46abd9355609396c0d55624f1646e891afc56d15f74beee2376b4afaf44dd5524e8705f8a82296a0dc4904e0e81785a2ec40d39f449ed514f550939681750a09e240270700baa649e278db134617c927bc891da829ec594754493c44d115024ea792711c1383605e22688a7127 12 4095 5 31 11 2047 21 2097151
def cur_68 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_68_17 (Nat.sub p 544)) (cc_68_16 (Nat.sub p 512)) (Nat.blt p 544)) (cc_68_15 (Nat.sub p 480)) (Nat.blt p 512)) (Bool.rec (cc_68_14 (Nat.sub p 448)) (cc_68_13 (Nat.sub p 416)) (Nat.blt p 448)) (Nat.blt p 480)) (Bool.rec (Bool.rec (cc_68_12 (Nat.sub p 384)) (cc_68_11 (Nat.sub p 352)) (Nat.blt p 384)) (Bool.rec (cc_68_10 (Nat.sub p 320)) (cc_68_9 (Nat.sub p 288)) (Nat.blt p 320)) (Nat.blt p 352)) (Nat.blt p 416)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_68_8 (Nat.sub p 256)) (cc_68_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_68_6 (Nat.sub p 192)) (Nat.blt p 224)) (Bool.rec (cc_68_5 (Nat.sub p 160)) (cc_68_4 (Nat.sub p 128)) (Nat.blt p 160)) (Nat.blt p 192)) (Bool.rec (Bool.rec (cc_68_3 (Nat.sub p 96)) (cc_68_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (cc_68_1 (Nat.sub p 32)) (cc_68_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 128)) (Nat.blt p 288)
def hc_68_0 : Nat → Nat := unpackHintV5 0x9e3a7293b2a2898a8a84c9307ab28675415c6b5a7a67590065d8605cfa3858f9005728744daa6048d1363ffa363e38703dc81c3b709637011c32a11829fa2a24496c1da1aa1cf82a17d14a12615c1158420c8136062198019922000066000000 0x7072f070707930707072f070707070307030b2f03030b4b03030b030b030741d0b175271752742d03581ea07a82e0baa83e0faa83ea0ba80ea0fa5a83d40000000000008aaaaaaaaaa9a4002024c1cbc1c1c1c1c1e4c1c1cbc1c1c1c1c0c1c0c7c0c6c0c6d0c0c0d0d2c0c0c1d0747d1b46c5d50c5d40d607a81ea0fa82ea0f83eaa0f83eaa03a83e96a0f5000000003c0f0000022aaaaaaa4384eaa90e690008093030303070707071b2f1b2b1b2b1b430303039303070303030703034b030303030741d1b1752b17546d0340d81ea07a83e0faa83e0faa83ea0ba80ea03a5a83d40000000000008aaaaaaaaaa039a4002024c1c2c1c2c0c0c1c0c0c0c0c0c0c0c2d1741e0782e0ba82e0fa82e0b80e03983d008aa80c0824c2c1c1c7c2c1c1c1c1c7d0c0c0c0c0d2c0c0c0c0c0c0c0e4c0cbc0c0c0cbc0d0747d0b47c5d42c5d40d0360fa81ea0fa82ea0f83eaa0b82eaa03a80e96a0f500000000000022aaaaaaaaaa03a6900080930b07070b0703030303031b03030303031745d07a81ea0f82e0f83ea0f83ea0380e60f4022a86e13a03020930b2f070707071b0b07071b03030303030303032f03032f0303030303931b41d271750b1752742d0340d83ea07a83e0faa82e0baa83ea0ba80ea03a5a83d40000000000008aaaaaaaaaa039a4002024c1c1d41d17171f031b035550781e0f82e0f83ea0f83ea0383e55008aa90c0824c2c7c2c5e4e4c3e0f83e0ba4d507070707171717172f17170703070317170303174b0303031b03564d07541d45d555607a81ea0f83eaa0f83eaa0fa83ea03a83e955540000000000008aaaaaaaaaa954002024c1c5c1c6d41d1b0323035550781e0f83ea0f83ea0f82e0383e55008aa90c0824c6c5c9c5e4e4c3e0f83e0f80f84e4c9c1c1c7c5c1c1c1c1c5c5d50307031f03270317170303174b030345d5559345d5175560fa81ea0fa82ea0f83eaa0f83eaa03a83e9555400000000f03c000008aaaaaaa85e13aaa954002024c2c1c1c2c1d51b0323035175541ea07a83e0b83e0fa83e0fa80e0f9540003c0f22a86e13a020930b1707070707170b07071b546c0c1c0c2d2c0c0c2c5c0c0c2c0c2c0d55175175564d560fa81ea0f83eaa0b82eaa0fa82ea03a83e955540000000000008aaaaaaaaaa954002024e4c2ccc5c2c2cce4c2e0f83e0fa4c3e0fa4e4c6c7c5c5c6c0c8d17930f83e0f83e03e1393030307171b0b0b1b03555541ea07a83e0b80e0383e0fa83e0fa95402203aa1b84e02093331f03031b07071b171703555543e0783ea0ba80e0383e0fa83e0fa95402203aa020930707171707070707171717172f1717170303030303030303555555035035564e0fa81ea0fa82ea0f83eaa0f83eaa03a80e9555400000000000008aaaaaaaaaa03954002024c1c2c1c1e4c1c2c1c1c2c4c4c2c2c4c0c1c0c0c0c0c2c0c8c0c2c0e82d17607aa0b83e0b80c000ea9383c003c0202c1c1c7c2c1c1c1c1c7c0c0c0c4c1c1c4e0b130b1313a82e90747d0b47d0b44d136a81e83eaaaa4e0ba80c01a83d00000003c000081f0b9383e4d42d0c2c5c4c4c4c4c0c1c0c0c0c0c5c0c8c0c0e964c1d0745d13607aa0f83e0f80c000ea935000f008430707175131713271313131303071f0303030303a17564c2d0b6070f83e0faa80c000ea935000f03c0f00837130323a0f24c0f02c1c1d44c2c2c4c0c1c2c0c8c0c0c0c0c0c2c0e82d0b564e070b83eaa0b80c000ea935000f00807074313070713131313130303030307030303030303a907544d1340d036a81e83eaa03000203a2a936a0f400000f0000000080707030703030341d503583ea07a83ea0fa80ea0fa5a83d4000000008aaaaaa9a4002024c0c0c0c0d540d4000c10030350 24 16777215 10 1023
def hc_68_1 : Nat → Nat := unpackHintV5 0xc85314c1c9a2b622eab40088b36028b0a8aeaa8988a479849902de9231b4894a3a88883082598c7be19e7aa84e74c9786c8a106561ca5afa9a5419b84a327a43d9963be9fc35d9842f31aa26d2182021ac1939ba12e1960c31ac0509ca000142 0x2707071f0f070707070f0f000c1c0c7c0c9c0c3c3c0c0c3d5c0c0c4c5c1c1c1c1c5c6c4c5c5c2c4c2c5c7c3c3c3c3c3c3c5cec3c3c4c4c3c3c3c3c0c0c5cec4c5c0c0d55555550f45d555903c0009303c00f000000002aaaaaaa0f84eaaa5559593000b07070b07006c0d2c0c1c1c1c1c1c1c5c6c5c2c2c6c5c4c4c6c5cec5c4c4c6c5c6c0cec5c0d5545d176403c0000aa1b84e95964c2c3c1c1c1c1c3c2c1c1c6c01b0307030b5703030b0f03030b030b03131707070707171b0f0f13130b0b0f0b0b0b0f0b0f0f173b13170b0b0b0b173b0303173b13170303555555555564000f00f0024c00000002aaaaaaaaaa555959300930b330f0b0b330b3b130b130f0f3b9393133b133b93931b1f0f0f1b034b133b131b130f0f3b45c0f9384e4c0c0c1c3c6c2c2c6c0c0070707070707171b170b0b1b030303031713131b173b1713131b171b5590000080ea86e1395964ccc7c0c0c6c1c1c6c3c3c0c01707071b170b170b0b1f171f030303031713131f173b1713131f171f5590000080ea95964c1c1c3c3c1c1c1c1c3c3c3c3d7c3c3c3c0c0c0c0c0c0c0c0c0131707070707173b1317170b130b173b0f0f13130f0f0f0f0f0f0f0f0f0f173b03030303030303035555555555640000030030024c0000012aaaaaaaaa80e555959300070b070793070b07070b13130b0b130307030303030b0353030b03a07070b0b133b0b13130b0b0b0355031303039355135590b03c0f0f0b07071f0b070707071f03030313070713130b130b1313130b82e84c1c1c1c1c4c4c4c2c2c4c7c4c2c2c4e4c2c2c4c4c0c0d555555551355640707c0b07c0b04c1304c3c130f1107c2cec4e4e4c02d0c2c3c3c4c4c3c0c1c0c0c0c0c3c0d4c0c0e81c1c3c3c4cec3c4c4c3c4cec0d540c4c0c0e4d544d56424c1c0703c0f010c1c1c3c03c3c4c9c3c4c4c3c0c1c7c0c0c0c0c0e81c1c4c7c3c3c3c4c4c3c3c3c0d540c4c0c0e4d543d1744d5643c0930b02c037130323073b1364d1742c1c1c04c2c2c4c0c1c2c0d5c0c0c0c0c0c2c0e81c1c2c4c4c2c2c2c4cec2c2c0d540c4c0c0e4d544d5642c0b024c01c1d0c4c1c1c4c4c4c4c4c0c0c0c0c1c0c0c0c0c0c0ea13070707071313131313133b030355540c0c0c4d03030393555544d555556407004c1300c0304c3c130f1101c1c0c1c0c0c0c4c5c1c1c1c1c5cec4c5c5cec4c5c5cec0c0c5cec4c5c0c0d555555901c0030170f0130f0440781e1384e038ec4e55595932807070707070707070707070703030303070303030303030393031f0303031f030741d1f42d1f1750b1750340d000000000000aaaaaaaaaa80e9a40932081ea07a87ea0ba87eaa82e0baa80e03a80ea5a85d42001c1c1c1c1c1c1c1c1c1c1c1c0c0eaa80c0c0c0c0c0eaa80c7c0c03030741d2f1752f1751f42d0340d000000000000aa00a0aaaa039a4001c1c1c1c1c1c1c1c1c1c1c1c0c0c0c0c0c0c0c0c7c0c0c7c0c0c0c0c0e4c1d0749c5d42c5d47d0b40d034000000000002aaaaaaaaa80e69024c8207a81ea2faaa0b82eaa2fa82ea03a80e96a175080070707070707070707070303030707070782c8c2c7c7ea0ba0741d1f42d1f42d2344d0000000000aa07a1faaaa0ba239a85d081c1c1c1c1c1c1c1c1c1c4c4c4c4c0c0c0c0c1c0c0c8c0c0c0c0ea93070707070707374737373737028001d074ed3b44d1340d034dc5d37174000000000000001c1c1c1c1c1c1c1c4cdc4cdc0c0c0c0c1c0c0c0c0c0c0ea0741d3b4ed3744d0340d00000000000aa07aaaa80e29a85d081c1c1c1c1c1c1c1c1c1c1c1c0c0eaa80c0c0c0c0c7c0c0c7c0e03030741d23175231751f42d0340d000000000000aaaaaa2aaa690007070707070707070707a81c1c1c1c4c2cdc2c7cdc4cbcdc2c7cdc0c0c0c0c1c0c0c7c0c0c0c0c0c0c0c0c0c0ea0741d1f42d1f174bc5d3744d0340d00000000000000070707070707070707070707a81c0c1c0c7c0cbc0c7c0c0cbc0c0c1d0747d2f47c5d4bc5d40d3b40000000000002a8aa80282aa6900070707070707070707070707a81c0c1c0c2c2c0c0c2c2c0c0c2c0c2c0c1d0742c5d42c2d42d0b40d0b40000000000002aa8002a2aa9a4001c1c1c1c1c1c1c1c1c1c1c1c7c7c7c0c0c0c0e030303031f030741d1f42d1f1751f1750340d000000000000aaaa00a0a269000707070707070707070703030307070707070782c2c8e4c2c2c7c7eaa0b0ba0741d1f42d1f42d2348d00000000000aaaaaaaa00690007070707070707070707070723370b230b376b0303030307030303030303a81d074ed3b4dc5d48c5d40d0340000000000002aaaa8002a29a4001c1c1c1c1c0c1c0c0c0c1d074ed3b40d3b400000002aaaaaa69024c8207a81eaaaa03aa96a175080 24 16777215 10 1023
def hc_68_2 : Nat → Nat := unpackHintV5 0xef804ce7d9eadd729ad619d6cf29bcc821c2bec258b8d17caff238aa7160a3a1b49e694e98b16e9171d08bb17085b97e80515a7a617c74298e6fc91861e37a5323b044db923e699c30039a2869e61a63821511541330780782ec02315400008c 0x93930383c3c4c9c5c3c0707a131b0b13930b130303030b030307030303931303a0f07071b0f0b0b1f0f0f0f130f0f0f130f130f130f130f270303030351345d03000f03c0344002c1c1d0c4c1c1c1c1c4ea13130707131b030b0b13930b0b131303030303030b0b03030303030307030303030303030303039303130303a90751d0b44c4d131744d1340d0340711c0b04c3c130f04c1300c03100707070707070707070703030307070707070782c2c2e4c2c2c0c0eaa0b0ba0741d0b42d0b42d3744d8888888848aa07a0baaa4e03a82e6a174aa01c1c1c1c1c1c1c1c1c1c4c2c2c2c2c0c0c0c0c0c1c0c0c0c0c0c0ea0741d3b42d3744d0340d8888888848aa07a13a0ba03aaa936a174aa01c1c4c1c1c1c1c4c4c0c0c0c0c1c0c0c0c0c0c0ea41d5175131750340d01c00f0130f00300c401e2b072b84e1380c0c0c0c0ea03a4d84d2807070707070707070707070703030303070303030303030393031f0303031f0355555555558888a0a08844aaaaaaaaaa80e9593652881ea07a87ea0ba87eaa82e0baa80e03a80ea582a8150707070707070707070707070303aaa030303030303aaa031f0340c0d5555555556228282222112a95696aaa80e552807070707070707070707070703030303030303031f03031f030303030393555555555588a0a0888844aaaaaaaaaa039593652881ea07a8beaa82e0baa8bea0ba80ea03a582a815070707070707070707070303030707070782cdc2c7c7ea0ba555555558888888844aa07a1faaaa0ba4b962a80707070707070707070713131313030303030703034b03030303aa4c1c1c1c1c1c1cdd1cdcdcdcdd5a5555555555555588888888a28440707070707070707133713370303030307030303030303a95555555562222222112a81eaaaa039a58aa01c1c1c1c1c1c1c1c1c1c1c1c0c0eaa80c0c0c0c0c7c0c0c7c0e0303555555555588a0a0888844aaaaaa6aaa552807070707070707070707a81c1c1c1c4c2cdc2c7cdc4cbcdc2c7cdc0c0c0c0c1c0c0c7c0c0c0c0c0c0c0c0c0c0ea5555555555558888a28888844070707070707070707070707a81c0c1c0c7c0cbc0c7c0c0cbc0c0d55555555556222282822112a9aa95696aa5528070707070707070707070707a81c0c1c0c2c2c0c0c2c2c0c0c2c0c2c0d55555555556228282222112aa9556a6aa954a01c1c1c1c1c1c1c1c1c1c1c1c7c7c7c0c0c0c0e030303031f0355555555558888a0a08844aaaa55a5a655280707070707070707070703030307070707070782c2c8e4c2c2c7c7eaa0b0ba5555555558888888844aaaaaaaa55552807070707070707070707070723370b230b377f0303030307030303030303a955555555556222282822112aaaa9556a6954a01c1c1c1c1c0c1c0c0c0d55555622222112aaaaaa564d94a207a81eaaaa03aa960aa0541c1d0c1c1c1e4c1c1c1d0c1c1c1c1c0c1c0c2d4c0c0c2d5c0c0c2c0c2c0c1c1c1c1c1c1c1c1c2c2c4c2c5ccc5cec4c5c4c4c2c2c5c2c4c5c2c2c2c2c5ccc0c0c5cec4c5c0c0d555555555590701c0b0f0270f02702c030170f0130f0440781e0707a0707a0781e0381c1e5559593280743070707070793070743070707070307031f031b031b4303034357030307070707070707071317170b130b171f13171313173b173b13171313171b171b0303173b13170303555555545d17555641c0707c1b06c3c10c3c00c05c3c04c3c1101e0781e0781c1e07a07430713a0381c1d0e555959328030303070707071b531b2b1b2b1b430303039303070303030703035703030303070707070707070713171313172b172b13171313171b171b1317170b130b173b03030303030303035555555555641c0706c3c0ac3c01b00c0305c3c04c3c1101e0781c1e81c1e81e0780e0303039556564ca01c2c1c2c0c0c1c0c0c0c0c0c0c0c1c1c1c1c2c2c2c2c5ccc2c4c4c2c2c2c2c2c2c2c0c0c0c0d5642c0f03c0f01e0780c0d5964c2c1c1c7c2c1c1c1c1c7d0c0c0c0c0d5c0c0c0c0c0c0c0e4c0d5c0c0c0d5c0c4c5c1c1c1c1c5c6c4c5c2c2c2c2c5c7c4c5c4c4c2c2c5c2c2c2c4c2c5c7c5cec0c0c0c0c0c0c0c0d5555555555901c1f02c1f0f00b0f00300c170f0130f0440781e1382e1313a0b13a030380c0c0c4e5559593280b07070b0703030303031b0303030303070707070707171b170b0b1b1713131b173b1713131b171b030303035590f03c0f03c0707a1b071380c0d5964c2d4c1c1c1c1c6c2c1c1c6c0c0c0c0c0c0c0c0d5c0c0d5c0c0c0c0c0e4c4c5c1c1c1c1c5c6c4c5c4c4c2c2c5c2c2c2c4c2c5cec5cec4c5c2c2c2c2c5cec0c0c0c0c0c0c0c0d555555555591b01c270f00b0f02702c0300c170f0130f0440781e1313a0b13a1382e0380c0c0e555959328070700703c3c7c0c6c0c1c1c1c1c5c2c2c6c5c4c4c6c5c6c5c4c4c6c5c7c0cec5c0d56400002aa43565930b1f0b0f930f3b130f130b0b239393001c1c1c1c3c3c3c3d7c3c3c1c0c1c0c3c3c0c0c3d5c0c0c0c6c0c1c1c1c1c1c1c1c1c3c3c3c3c3c3c5cec3c3c4c4c3c3c3c3c4c5c5c6c4c5c5cec0c0c5cec4c5c0c0d55555555559024c07001c03c0000000002aaaaaaaaaa555959300070f071b00706c0ccc0c1c1c1c1c5c4c4c6c5ccc5c4c4c6c5c6c5c2c2c6c0cec5c0d56400002aa43565931b0f270f93132b131b0f3b130f45e4e1393 24 16777215 10 1023
def hc_68_3 : Nat → Nat := unpackHintV5 0x8b50927d9b6e7bb8787970926d23146c98226a409669503c68683a65a0b25fb17c5ee8325c38ac5432024e91684dc8324d00324a909c48289a47e01247e00046f83a4119783b716a33e1e43340282c91ac2541d419cade0f02b20781e00001e0 0x4c2c2cdc8c0d5c2c2c5d175139313a4c0d130b0b070707070b0b07070b004c6c1c1c1c1c6c6c2c2c4c4c2c2c2c2c2c2c2c2c2c2cdc2c2c2c2c2c2c2c2c0c0c0c0c1c0c0c2c0c0c0c0c0c0c0c0c0c0c2c0c0c0c0ea1b41d0b1750b0b50b42d175131750340d0002c02c009300000000aa2ba0b84eaaaa0baa80e80eaa936a40004cdc4c5c5c3c8c3c9303c4e930303c4c2c2cdc8c0c8c2c2c3c930f00f13a4c0c0f6307074313130707070713371313133713131337030303030703032303030303a83c8c1c1c1c1c3c3c3c8c3c2c3c2c3c3c0028018d07544cdd44c4d40d0343c3d43c5d40f00000003c0f0000300f002a84e84eaa03a03aaa4e0380c0001a84d00083c0f270f2724c2c4c2c2c0c8c2ccc3c2c3c4c3c9c84e4e0f071b0f270f2720f1b371313279384e4c6c4c4c6c0c8c1c6c3c3c6c3c4c3c9d1703c84e4e0f07130b1b0b13030707031b03070707070f0f0f130f270f0f0f130f130f0b0b1b030303035540c000034402071384eaa07070f079384c4c1c1c1c0e071b0f130f370f0f1b45c0f04e4e0383c0c0c1c0e4c6c0c1c4c6c2c2c6c0c0eaa0707070707070f1b0f0b0b1b030303030f0f0f1b0f270f0f0f1b0f1b40d545d174003000f03c440281e931baa0380eaa1b0707131313030f07071b0f0b0b1f0f0f0f130f270f0f0f130f1303030303551345d40c0003c0f00344002eaa0b1f0f270f1f03c3c3c7e4e13130b230382c3c4c3c9c2c3c2d1703c139380e0f1313230ba0b1f0f130f370f730f1f04e4c0e83ccc2c239307071b1b04c0c0c6c1c1c6c4c4c0ea0f07071b0f0b0f0b0b1f0f1f030303030f0f0f730f270f0f0f1f0f1f40d54003004402aaaa81c1c0c0c6c6c2c8e4c2c8ea0b83c1c1c6c3c2c2c7c3c2c2c7c3c4c3c4c3c8c3c9c11008aea930b80eaa0f83e50071b0707070707071b1b1b1b1b1b03071b03a555070f1b0b0b1b371b37131b13131b131b1b1b03030303031b2303400000081c6e0380ea935aa1b84e01f131393131b07071b1f0b270b1f1f1f03071f03a5551b07071b0f0f371f37131f13131f131f1f1f0303030340000008ac7e0380ea935aa1f84e027070727030303030327030303035555550349c6c1c1c1c1c9c6c9c7c9c2c9c2c9c7c0c0eaa940000000000c000000aa89eaa89556aa80e03a00007071307070707132713270303030307030303030303a83c3c1c1c1c1c3c3c3c3c2c3c2c3c3c3c3c3c3c4c3c4c3c3c3c3c3cdc3c0c0c0c0c0c0c0c0d55555555540d0000000000000c104002a8aeaaa03a03aaa4eaaa0f83e95540002c1c1c2c4c1c1c1c1c4ea0b070707070b0303030303a0380e4c0c4c4c1c1c4c6c0c2c2c2e4c2c2c2c4c0c0c0c0c0c2c2c0c0c0c2c2e82c2e86d0742d0b44c4d131742d0b44d1346c0702c0b04c3c130f02c0b04c131050b1b0b1707071313131317136713a0707131313130b13930b130303030b03030703030303170353031b030303931303a5930741d17544d0f03c0f0f00b1b0b0f07070f0f13130f135b0fa07070f13130f0b13930b130303030b030307030303030f0353031b030303931303a0f45d13170930701c0f003c 24 16777215 10 1023
def hc_68_4 : Nat → Nat := unpackHintV5 0xe7a1aedefa2ad7f9c0c8cbccc0d9fcbe40a6b53a42a67bb09df2229631f08d822c7e4bce70ab686979cc63119a5d81645771845049ca4a218a49583246e09e39336c3201cc2f68a627e1e227183224a09e22c0781583500db9f20731a20001cc 0x141c1c2c6c2c5c0c0c0c0c0c0c1c1c1c1c5c5c5c5c7c7c5ccd9c5c5c5c4c4c0e80d64c1d0745d1745d550f03c0f03c0781e07070380e0303551b231f1b231f070707071317a070707a070707070707131b132355555545d935548c2301c0708c1b08c131101c8e81e07a4c1e07070781d4e0781c0c0c0d55481e23142c6c2c5c1c1c2c5c7c7c5c2c2c5c0c0c1c1c4cdc4c5c2c6e4c2ccc1e82e5930741d1745d0f03c07070707a17071386c1c1e930b80c0d41d507070707170b17170b17170707070707070707131713131717371317131317171717131b1b131b6303030303070303030303030303170303030303030303a959341d5075175545d175555550701c170f0170f006c630f0130f00300c440781c1c1e070781e81c5c1c4e81e0781c0c0c0c0c0ea03a4d55481e01c5c1c6d41d070707071b13131b33331b13131b1b1b1b0b0b1b0307030303031b0323031b03a555550f03c0f03c07070707a1b071386c1c0c0c0e03a4d41d0c4c1c4cdc4c5c1c7c2c5c6d7c5c1c0e931313a4e030b07071f03030303031f03030303271b07070707271b550b0b50303a0380c0d1755555555552701c1f02c0300c270f0270f0440781e132782e2703980c0e1780c0c0c0e955489e2702c1c1c7c5c1c1c1c1c5c5d5131b070707071b131f0b0b0b0b1f1f131713131717371317131317171717030303030703031f030303030303030303030303a91755564d0b542d55555501c1f02c170f0170f00f0130f00300c44078ac1cae134782e3b13171313a131385e80c0c0c0c0ea03a4d5548ee02c1c1c2c1d50707070707071b1b0b0b0b0b1b13131b37371b13131b1b1b03070b03030303031b032303a50b5555403c0f03c0f01c1c2c1c1c1e86c1c4e03030380e935070b07070b03030303030303031b1b070707071b1b0b0b5550303a0380c0d55555555546c0702c0b00c030dc3c0dc3c1101e0782e0b80e60303a0303a555280b07070b0b070707070b030355131b07071b1b0b0b0b0b0b0b0b0b0ba0b0ba5555555551b01c0b02c0b02c23013044078ac1cae0b0b82e0b0b82e930b0ba03030355522388c0b0b070707070b0b07070b544c6c1c1c1c1c6c6c2c2c4c4c2c2c2c2c2c2c2c2c2c2cdc2c2c2c2c2c2c2c2c0c0c0c0c1c0c0c2c0c0c0c0c0c0c0c0c0c0c2c0c0c0c0ea5542d42d55935555551b01c0b0f00b0b00b02c0f0130f00300c44078ac1cae0b0b1313a0b0b82e82c2e0b82c0c0c0c0c0ea03a4d5548ee18c1c1d0c4c4c1c1c1c1c4cdc4c4c4cdc4c4c4cdc0c0c0c0c1c0c0d5c0c0c0c0ea17570707070717171757170b170b1717555a5545d5555551344d5540d44d6301c013370131300300c170f0170f044078ac1c4e131384e370303030303a80e93030303035555555131348de1301c1c01c0f0f070707071b0b0b1b1b13131b1b1b1b13131b1f1f03071b031b031f0303030303a1745d1745d0000081c6e1b84eaa0380ea9390c01c1c1c1c0e0303030303030007070371f1b0b1b0b371f0303aaa0741d46d0340d3717537175000000000000aaaaa2aaaa6900000b1b0b0f070707070f0f0f0f13130f135b0f0f0f1b130303030313030f45d1345d0930701c0f0003c0f2a82e007070b1b0b0f030303030303070707070f0f0f0f1f1f0f335b0f0f0f131303a83d1745d17424c1c0703c0f03c00aaaaa0303001b231f1b231f070707070f0faaa81c1c1e0707131b13232348d0741d5746d2344d00000003c930000223aaa93aa07a53aa80e6a53400002c6c2c3c1c1c2c3c7c7c3c2c2c3c0c0c1c1c3c8c4c3c2c6e4c2c8ea0b83d17424c1c0703c0f207aa0f84e1baa4c2e03a0172727179345c3c5d6c3c3c4c3c4c9c4c5c0d5e4e4c3c84c4e93001c1c1c1c3c2c3c3c2c3c3c1c1c1c1c1c1c1c1c3c3c3c3c3c3cdc3c3c4c4c3c3c3c3c4c6c6c4c6d8c0c0c0c0c1c0c0c0c0c0c0c0c0c3c0c0c0c0c0c0c0c0ea0741d0f0f50f17546d63175131750340d024c07001c03c000f03c00000002a81eaaa83e13aaaa03a03aaa4da9000070f071b00701c1c1c1c6c4c4c6ccccc6c4c4c6c6c6c6c2c2c6c0c1c0c0c0c0c6c0c8c0c6c0e85d1745d1740000207aa1b84e1b80e03aa4e43013070f37130f071f0b0f1b2f0f0703a4c4c3e9380c2c1c1c7c0c0c0c0c0c7e030303271b07070707271b000b0b00303aaa2741d1f42d0340d271752717503c000000000002aa27aaa2aaa0380e9a89d0000f27270f9303c5c3cbc3c4c4c5c3c9c4c3c0c8e4c5d9384c3e930f37130f0f172f0f513930fa4c0d130b07071f0f070707070f0f004c6c1c1c1c1c6c4c7c2c2c2c2c7c7c3c3c3c3c3c3cdc3c3c4c4c3c3c3c3c0c0c0c0c1c0c0c7c0c0c0c0c0c0c0c0c0c0c0c0ea41d1f42d0f0f50f175175131750340d03c0009302c00b000000002a8ae91eaa0f83eaaaa03a03aaa4da90000b07070b07001c1c1c1c1c1c6c6c2c2c2c2c6c4c4c6cdcdc6c4c4c6c6c6c0c1c2c0c0c0c0c0c6c0c8c0e945d1745d17402c000081c2eaa1b84e0380ea93802c1c1c2c0c0c0c0c0c0c0e1b1b070707071b1b0b0b0000303aaa1b41d0b42d0340d3717537175000000000000aaaaa2aaaa690000b07070b0b070707070b030300131b07071b1b82c2c2c2c2eaa0b0ba1b41d0b42d0b42d23513500000000000aa2ba0baaaa9382ea039a95d000 24 16777215 10 1023
def hc_68_5 : Nat → Nat := unpackHintV5 0x962c67a4a61ca8edc77a2fe172874c95a08529c797d131d142966ee8ad198c45c61a092173126e54bd0113cb2c84b4c7c11a425e3e390b0e2e2c034588c0b03426284079897713221309587a11561c5c45060022e13988d03c32460ab48b01af1fc02ec7a0000176 0x7070707070707070707a80c0c0c0c0c0c0c0c0c0c0c0c0c0c1d0747d0b44c5d2f1740d03622228a2212207aaaa0ba0ba039a4a01c1c1c1c1c1c1c1c1c1c1c1ea0303030303030303030303030303030303030741d1f42d1f1752f1750340d8888a0a08848aaaaaaaaaaaa6928070707070707070707070707a80c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c1d0742c5d42c2d42d0b40d036228282222122aa0baaaaa0baaaaa9a4a01c1c1c1c0c0c0c0c0c0c0c0c1d074ed3b40d03622222122a81eaaa03a4ea9a8ed2a881ea07aaaa80e5a85d42a82a03070707030303030303030307070707070707070b0b0707070707070303a0380c0c1d0742d0b40d034cc5d4cc5d41c0702c0b00c030cc3c0cc3c100781e0781e0380e0303a0303a6074a01c0c0c0c0c0c0c1c1c1c0c0c0c1c0c0c1c1c1c1c1c1c2c2e81c1c1e81c2c2c2e4c2c2c2c8c1d0742d0b42d0b48d1341c0702c0b02c0b08c13108c0781c1c1e070ba0781e93070b81e070303036070753481e2301c1c2c1c1c1e4c1c1c1c2c1c1c1c1c1c1c1c1c1c1c1c2c2c2c2c2c2cdc2c2c4c4c2c2c2c2c2c2c2c2c2c2c2c2c2c2d8c0c0c0c0c1c0c0c0c0c0c0c0c0c2c0c0c0c0c2c0c0c0c0ea0741d0b0b50b1750b42d63175131750340d0701c0b0b00b0f00b02c630f0130f00300c401e07070781c1e07a070b0713a070b81e070303030303a80e9360707481e01c1c1c0c0c0c0c0c0c7c0c0c0c0c1c1c1c1c1c1c1c1c1c1c1c1c2c2c1c1c0c0e80e03030741d1f42d0340d37175371750701c1f02c0300c370f0370f0401e0781d0e0781c0e0380c0e80c0e981c1d0d20790c07070703070303030303070703030303070707070707131f0b23071f1f23131ba070707a0741d1f42d2348d231744c5d0701c1f02c2308c230f04c3c42301e07070781d0e0781c1c8e81e07a4c0c0c0d81c1d0d20788c070b07070707079307070b0707070707070707070707131f0b0b431b0b0b1f1f43131b1313434337134313131b1b371b030303030703031f030303030303030303030343030303a81d0747d0b46c5d50c5d50c5d44c5d40d0341c0707c0b06c3c10c3c10c3c04c3c00c03100781c1c1e074381e07070781e81d0c1c4e80c0c0c0c0ea03a4d81c1d0d20790c07071307070707130b131b130b1313030303030703030703031b030303030741d13135131751b46d0340d0701c130f0130f01b06c0300c400e07070781c4c1c1c4e0781c0e03981d280707070707071b1b07070703070b131b0b1b131f0707070707070b0b0b070707030707030703070303030303a1f1b1745d3744d1f1b0f03c3704c0707130713070b81c1e80c0c0e03a4c1c4c1c4c1c1c1c1c1c1c4c4c1c1c1c1c1c1c4c4c4c6c4c4c4cdc0c0c0c0c0c1c0c1c0c0c0c0c0c0ea0707131b1b0b1b0b1b370707070703030303a0381e03030741d46d13375131350340d1b175371750701c06c13370131300300c1b0f0370f0401c1e070707071381c4e0781c0c0c0c0c0ea03a4c0c0e07a03030303a6070713481e1301c1c1c1c0c0c0c0c0c1c0e4c0c0c6c0c0c0c0c1c1c4c6c6c6c2c6c2c6c6c0c0c0e80e0780c0c1d0746d1b40d0346c5d46c5d41c0706c1b00c0306c3c06c3c10070781c1c1c1e4e071b81e070380e030381e03030303a6074a02c1c1c7c4c6c1c1c1c1c4c4c4c4c0c0c0c0c0c0c0c0c0c4c0d0747d0b44c4d44c5d40d0340707c0b04c3c04c3c00c03100781e0382e0b0b0b0380e6134a02c2c1c1c2c7c0c0c0c0c0c0c0c0c0c0c6c6c1c1c1c1c6c6c2c2c4c0c0e80e03031b41d0b42d0340d1f1751f1751b01c0b02c0300c1f0f01f0f0401e0782c4e0b0b80e0380c0e80c0e984d280b0b07070b43131307070707131b0b0b13130b0b0b0b0b0b030303030703030b03830303030303a82d0c1c1c1c1c2c2c2c2c2c2c4c2c0c0c0c0e80e0b80c0c6d0742d0b44cdd44c4d40d0342c2d42c5d46c0702c0b04cdc04c4c00c0302c2c02c3c10078ac1c4e0b0b131382c2e0b0303030303a80e93030382e80c0c0c0e98dc4c4d23784c0b0b07070b1b03030303030b039303030303030b1b070707070b0b0b0b0b030303a0382e03031b41d0b42d0340d0b0b50b1751b01c0b02c0300c0b0b00b0f042701e0782c2c4e4e0b0b82c0e0380c0e0b80c0c0c0e984d280b0b070707070b1b0b07070b0b0b0b03030303030b03030b030303031b41d0b1750b0b50b42d0340d1b01c0b0f00b0b00b02c0300c42701e0782c2c4c2c2e0382c0e03984d280b6307071f431313070707071337131313130b0b0b0b1313030303030703031f030303030303a8cd8c1c1c1c1c7cdc4c4c4c2c2c2c2c0c0ea80e030303036341d1f42d13375131350340d1f175371756301c1f02c13370131300300c1f0f0370f0401e2b071384c4c4c4e0b1380c0c0c0c0c0ea03a4c0c0c0c0e80c0e03a637131348de1301c1c2c0c0c0c0c0c0c0c0c0c0c1c1c1c1c1c1c2c2ccc0e03030741d0b42d0340d1f4cd0701c0b02c0300c1f0cc401e0781c1e070780e0380e03981d2807030303070707071b81c1c1d0748d2347d1f41c0708c2307c1f108c0781e0781e0380e6074a01c1c2c0c0c0c0c0c0c0c0c0c7c0c0c1c7c1c1c1c1c1e4c1c4c4c1c1c1c1c1c1c1c0e03030741d1b47d0340d1f47d0701c1b07c0300c1f07c401e0781c1e07071f071380e0380e03981d28331f03031707071b13540c0c0c0ccc1c1c7c4c4c0e030355071745d1745d543c0f07c7304c4c4e1380e038cc7c0c0c3c1c1c6c3c003a8cc1c1c7c4c4c0ea005d0f47d734070f03c0f03c02aaaa82c1c1c7c0c0c0c0c0c0c0c0c0c0ccc6c1c1c1c1c7c6c4c4c4c0c0e80e030341d1f42d0340d1f17517501c1f02c0300c1f0f00f0401e0784c4e0b1380e0380c0e80c0e984d280707030307131307070793070b13930b1b13330707a0ba0713070b0b1b070707070b1b0b81c1cdd1345d1748c1303c0f01c1c1c1c4c4c1c1e930b80c0c0c1e80c0c0e071307130b07071f131307071333130b0b0b0b87c1c1c7c4c0c0c0c82c2c2e4ccd0747d0b44d1347d1f48c0707c0b04c1307c1f108c0787c1c4e1382c2c2e030303030380e0361f1313487e1302c1c1c7c2c1c1c1c1c7c0c0c0c4c6c1c1c6c4c2c2e0e4c2c2c7c4c2c2e82c2e90747d0b47d0b55d1340707c0b07c0b08c1310078ac1cae1382e1382e930b0ba0303036134a01c1d41d1717070707071b0b0b1b1b13131b1b1b1b13131b1f1f03071b031b031f0303030303a555550f03c0f03c07071b071b071381c1e80c0c0e03a4d41d0c1c1c1c1c0c0c0c0c0c0c0c0d541c1d4dc7c6c2c6c2cdc7c0c0e80e030355555555550701c06c0300c370f0370f0440781e0781e03980c0e80c0e9554a142c6c2c5c1c1c1c1c5c4c5c4c4c4c5c4d9c4c4c4c6c4c0c0c0c0c4c0d64c1d0745d551345d0f03c0f03c0781e0b07 26 67108863 11 2047
def hc_68_6 : Nat → Nat := unpackHintV5 0x8470c14076709f2b440f5a0ee7808b239e4881b9e550d3da466511372f80c2163562caa41da5148f62542d8913e58c7eeac23c20d51c72678cac6345eb9aa2c38c914866588d05cc3e99fa1bc8e10b24b004544f81aa9fe09a8eb031a6e80a639c00014c 0x1c1c1c1c1c1c4d3ea03070303031303033f030341d51317517503501c0130f00f0030401e07a77a4c4e84c0e13984d28070707070707070707070707a81c0c1c0c2c2c0c0c2c2c0c0c2c0c2c0c1d0742c5d42c2d42d0b40d0b6228282222122aa0ba0baaa4ea9a4a01c1c1c1c1c1c1c1c1c1c1c1c0c0c0c0c2c2c0c0c0c1c0c0c0c1c0c0c0c2c0c0c0c2c0c0ea0741d0b42d0b0b50b17503035033b58888a0a0a0a048aa82eaaaaaaaaa9a4a01c1c1c1c1c1c1c1c2c2c2c0c1d074ed0b42d3b622222122aa77aaaa692807070707070307030b030b030741d3b42d034ed88888848aa9de93aaaa692881ea07aa80e03aaa5a85d42a82a07070b07070707070707070307030b0b03030b0b03030b030b030741d0b0b50b1750b42d0342d0701c0b0b00b0f00b02c0302c42701e0781c2c1c1c2e0781c0e07981d2807070707070703030303030307070b0b07070707030703030303030b03030303031b030741d0b42d2317523175030340c8d0701c0b02c230f0230f0030300c8c42301e0781c2e0381c1c1e81c1e80c0e0307981d28070b0707070707070b0707a0781c1c1c0c1c0c2c0c2c0c6c6c0c0c6c0c0c1d0746d0b46c5d46c5d40d41c0706c0b06c3c06c3c00c10070781c1e071b81e070707a0707a0381e6074a02c1c1c2c2c2c1c1c1c1c2c6c0c0e80e0303031b03030303030303030b03030b031b41d0b42d0b1750b0b50340d1b01c0b02c0b0f00b0b00300c401e0782c2e0382c2c4e80c0e80c0e0313984d280b0b070707070b1b0b07070ba85c6c1c1c1c1c5c5d5569542c0c1c0c2c2c0c0c2c2c0c0c2c0c2c0c2c2c0c0c2c2c0c0d17555542d0b5550b50b5546c0702c7c02c2c02c0b05c3c05c3c00c0b1101e0782c2c4c2c2ea0ba4c4c4d5540e0b9544d280b0b070707070b1b0b070707070ba85c6c1c1c1c1c5c5c2c2c5ced50b0307030b0b03030b0b03030b030b030b0b03030b0b030345d55555559342d50b5546c0702c3c02c2c02c0b05c3c05c3c00c0b1101e0782c2c7c2c2ea0ba4c4c4e9680e0b954a02c1c1c2c1e81c1c1c1c1c1c1c5c6c2c2c2c2c5c5c5c6c5d9c5c5c5c6c5c6c0c0c0c0c6c0c8c0d5540d03564c3c0f03c0f11707070b070781e0781e0b07070b03030303030303031b1b070707071b1b0b0ba0b82c2c0c0d55555555555546c0702c0b00c0307c3c07c3c1101e0782e60380e1313a1313a55280b0b070707070b0b07070ba85c5c1c1c1c1c5c6c2c2c5c5c2c2c2c2c2c2c2c2c2c2c5c2c2c2c2c2c2c2c2c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0d55555555540d40d55931b01c0b0f00b0b00b02c170f0170f00300c511701e0782c2cec2c2ea0ba4c4c4e84c4e80e03954a02c2c1c1c1c1c2c6c2c1c1c2ea0f1b070707070f0f000a000b0307030b0b03030b0b03030b030b030b0b03030b0b03031b41d0b1f50b0b50b42d0f0f50f1750342d03c00000b02c0002c02c0000aa82e82eaa93a000aa690080b0b070707070b1b0b070707070ba83c6c1c1c1c1c3c3ea800b0307030b0b03030b0b03030b030b030b0b03030b0b03031b41d0b1750b0b50b42d0f0f50f1750342d03c00000009302c00b00002aa0ba0baaa4ea82aa9a4002c1c1c2c1ea0707070707070f1b0b0b0b0b0f0f0f1b0f5b0f0f0f1b0f1b030303031b03230301745d1743d000300c09303e82eaaaa0b07070b0303030303030386c6c1c1c1c1c6c6c2c2eaa80c0c0006d0742d0b40d0347c5d47c5d4000000000002aa8aaaaaa9a4002c2c1c1c1c1c2c2c1c1c2ea0f0f070707070f1b0b0b0f0f0b0b0b0b0b0b0b0b0b0b0f0b0b0b0b0b0b0b0b03030303030303030303030303030303006d0742c5d42c2d42d0b43c5d43c3d40d03400000000030030024c003caa82e82eaa93aaaaaa69000b07070b07a86c0c8c0c1c1c1c1c1c1c3c6c3c2c2c6c3c3c3c6c3c9c3c3c3c6c3c6c0c9c3c0d545d175170000f03c03d100a1baaaa82c1c1c6c0ea1b03030b0b030f07071b0b0b0b0b0b0f0f0b0b0b0b0b0b0b0f1f03030f23030303035540c0000344002eaaaaa0b07071b1b0307030b030b035555551b1b070707071b1b0f0faaa03031f1f1f2303035000000000000000aa87e2aa956aaa8002c9c1c1c1c1c6c2c1c1c6ea1b0307030b03030b2703030b030b030f0f070707070f1b0f0f0f0f0b0b0f0b0b0b0f0b0f1f0f0f0f0b0b0b0b0f1f03030f270f0f03035555555555174000000000000f041000aa89e89eaa93aaaaaa55000b0b07070b1b0b07070baa4c4c1c1c4e02a930b0307030b0b030b0b030b030b030b030b031b41d0b42d0b42d1344d0342d1b01c0b02c0b02c1304c0302c42702c1c1c1c1c6c2c1c1c6ea1b0307030b03030b03030b030b031b41d1750b17542d0351b01c0f00b0f002c030401e0784c4eaa4c0e13984d2807070707070707070707070703030303070303030303030393030b0303030b030741d0b42d0b1750b0b50340d8888a0a0884881eaaaa0ba4eaaa0b82eaaa03a692881ea07a82e82e13aa80e03aa80e03a80ea5a85d42a82a07070707070707070707070703030303030303030b03030b0303030303030741d0b1750b0b50b42d0340d88a0a088884881eaaaaa0b82eaaa0ba4ea80e692881ea07a82e3f82e80ea03a5a85d42a82a0707070707070793079307930793a81c0c1c0c2c2c0c2c2c0c2e4c0c0c2e4c0c0c1d0742d0b42e4d930b9364c0d0b622229324e9324e2122aa0b9de0baa9a4a01c1c1c1c1c1c1c1c1c1c1c1ea070307030b030b0313130303133f03030741d1f42d1313513175034ed8888a0a0884881eaaa9382ea0baa84e69280707070707070707070703030307070707070780c0c0e4c0c0c0c0e800303a0741d0b42d0b42d2348d8888888848aaaaaa9382eaaa9a4a01c1c1c1c1c1c1c1c1c1c1c1c8c4c0c0c0c0c0c0c0c0c0c0c1c0c0c0c0c0c0ea0741d3b42d37175231750340d8888a0a08848aaaaaaaaaaa6928070707070703070303030741d3b4ed034ed8888884881eaaaaa4eaa692881ea07aa80eaa5a85d42a82a 25 33554431 10 1023
def hc_68_7 : Nat → Nat := unpackHintV5 0xd27328cc498ac3f216b60b7aaf19bca94176a3c160a1b88295830e892b167dfacc7292da6d11606621bc6418825783265490bc4f51504d08924a68a844698043c8283db9843cf8303729742b32fe25098a1b826213e1e80a725c05b92e00016e 0x171707070707171b2f07071f5a55132f07070707131355a8fc0c1c0c5cfc0c0c5c5c0c0c7c0cbc0c4c4c0c0c4cbc0c0d55135175544d13555552f01c170f0170f01f0bc13130132f0030bc511701c4e078bd544c2d62fa4c4c4e84c4c4c0e2f13139544d280713071b0781e070707071717171b17331717171b171b170b0b1b030303035550340d5930f03c0f03c45c1c1c1e0781e0782c1c1cbc0c0c0c0c0c0c0c0cbc6c1c1c1c1cbc6c5e0b0b0b0ba030355555555555552f01c2f02c0300c2f0f02f0f0511701cfe078bd82e0380c0c0e0b0ba130ba55280b0707473f07070707133fa85c5c1c1c1c1c5c6c5c5c2c2c2c2c5c7c4c4c5c4c5cbc5c5c5c5c5c4c4c5c4c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0d55555555540d40d559301c4702c130f03f0f0170f0170f00300c511701cfe078ee0ba4c2c2e82c2c2c4c4e84c4e80e030303954a01c1c0003c2eaa81c1e072f2303032f230303070307031b031b032f1752f1750741d1b46d0356d00000003c000002aaaa07aa2aaa5b9a4000c00b1b0b1b4b2f2f231313232f233f131307070707a0f030703030303031745d1745d00000aa07aa4c2e0ba80e530070707070f0f0f0f233f0f23230f0f0f0b1b0b0f03a80c0c0c0c4c0c6c0c3d1745d17424c1c070003caaaaa0f135b0f0f8b170f132f171393930f24c0070707070f0b0f1b0f0b0f0f07070707070707070f0f0f0f0f0f13130f0f2f0f0f0f0fa81c0c1c0c3c3c0c0c3c0c0c6c0c6c0c4c0c0cbc0c0c1d0743c3d43c5d46d1b44c5d4bc5d40d409301c00700f000000000081eaaaaaaa9386ea1baaa69000b070707071b1b1b07070707131ba83c6c1c1c1c1c3c3c000aa00001b0307030b030b03131f03031f2f03030f0f03030f2f03031b41d1f42d131751f1750f0f50f1750351d03c0009302c00000f03c00b000021baaaa4e0ba82e0aa83e13aaa479a4002c2c1c1c1c1c2c6c2c1c1c1c1c2c01b1b07070707131baaa82c0c1c0c2c2c0c0c2c2c0c0c2c0c2c0c2c2c0c0c2c2c0c0c6d0742c5d42c2d42d0b44c5d4bc5d40d0b4000b00b0024c000000021baa0aaaaa4e0ba82eaa0b9a4003c3c1c1c1c1c3c6cbc1c1c7c28004cbc1c1c1c1c4c4c02a3f0307030f3f03030f0f03031f032f0313130303132f03035f41d0f1750f0f51f4bd13135132f5034fd0003c03c000f03c00000003c84ea80282a9384ea13aa84e690080713071ba0781c1c1c1c3c3c3c6c3ccc3c3c3c6c3c6c3c2c2c6c0c0c0c0c05d1745d0f4000c03024c0faaaaa0b07072f030303030380c0cbc6c1c1c1c1cbc6ea82c2e80c0c0016d074bd0b40d034bc5d4bc5d40000000000003c8fea8aaa80eaaaa690017132f130f870f170f5b0f13931764e4c2c1c1d1cbc1c1c1c1c4cfea0f0f070707070f1b0f0f0b0b0b0b0f1f0f0f0f0f0f2f0f0f0f0f0f0f130f1303030303030303030303030303030303010751d0b44c5d4bc5d43c5d43c3d40d03400000000030030024c003c8feaaa9382ea0baaaaaa80e6900931b0707a81c6c3c9c3c4c3c9c3c6d1745c0f03c9384c4e0713071ba0786c0c8c0c1c1c1c1c3c3c3c6c3c9c3c3c3c6c3c6c3c2c2c6c0c3c0d551700003d100aaaaa1b132b13930f270f1b0f0f1345c0f04e931380ea9303230f270f130f0b0b1f270345c0f24e0b1386c1c1c6c0ea130323030f07071b0f0f0f230f230f0f0f230f270f0b0b1f03030303551745d40c0003c0f0034402aaaaa4c6c9cac6c9c1c1c9c0c1c0c9c0c9c0d5555549c6c1c1c1c1c9c6ea83c2e80c0c9c8c9c8c0c0d4000000000000002a8aaa956aaa8000c8c6c8ccc6c1c1cfe89c0c0c0c0c0d5546c1c1c6c7c2c2c7c4c9c4c9c8c8cbc9cbc4c8c4c0c3d0000000fea930b82e80c8e13aa89c1c1cbc1c1c1c1c4d3ea0307030327031303032f03030f0f070707070f1b0f0f0f0b0f0b0f1f0f0f0f0f0f2f0f0f0f0f0f0f130f1303030f0f0f0303555555545d175551740000000003c0f0000f041000aaaa9389ea27aaa83e13aaaa5500a0b0707079313070707930b07070707a1307070707070707070707070f130f0b0b1b0f130f13033f0f0344d17003c0f4402a07070707070b07070707079307071307070707079307070b07070707070707a81c0c1c0c1c4c0c1c1c0c6c0c6c0c4c0c4c0c1d0741d0746d1b44d1340d3f41c0701c0706c1b04c1300c3f1007070707070707070707aaa070707070707aaa93070307031f1f031f2f031b031b03131303132f030741d1f47d1b46d131344cbd034ed888888a28884807070707070707070707a81c1c0c0c0c0c6c2c2c2c2c6c0c0c0c8cbc0c0c1c0c0c0c1c0c0c0c6c0c0c0c6c0c0c0c4c0c0c0cbc0c0ea0741d1b42d134bd3748d03035033b588888888a0a04807070707070707070707a81c0c1c1c6c6c6c6c4cbcbc0c1d0746d1b44d2f4ed3b622222221201c1c1c1c1c1c1c1c1c1ea070307031b031b0313032f030741d1b46d134bd034ed888888884881eaa0baaaaa6928 24 16777215 10 1023
def hc_68_8 : Nat → Nat := unpackHintV5 0x98f4c8a56f19c92a4632319320884084a0c329a7f68749ede1f878046e9d061f66ff4849b0b1e468647919a90e063f855973039c54e0fc13533ca485c9e10fc2363be9010cf64082e90a909da39422dc91879c2361a448585be1a613e46283483620658d9000032c 0xa81c1c2c2c1c1c1c1c1c1c1c1c1c1c3c1c1c1c1c1c1c1c1c1c2c1c1c1c1c1c6c1c1c1c1c0072b030307070303070307030b2b03030b0f03030b030b0307175070750741d0f1750b0f51b42d034ad00000003c03c0093000081e81eaa93aaaaaaaa2b9a4001c1c1ea0707030323032303070707070f0b0f1b0b1f0f1f0f0f0f6f0f270f0f0f1f0f1f032b0f035545c0000f44001eaaa8aea81c1c1c1c1c0c1c0c9c0c9c0d5555541c1eaa89c7c9c2c9c2c9c7c0c0c9c8c9c8c0c0d40000000000000028aaaa956aaa802a0727070707070707070707072b030307070303070307032b032b0307070f0f070707070707070707070f07070707070707070f0f0f1b0f0f0f3303030f2b0f0f030341d175555555555174001c0f00000000000f04100081e81eaa93aaaa2baaaa95402a07070707070707070707072b030307070303070307032b032b0307175070750741d5034ad070f0070700701c0030ac401c1c1c1c1ea07a4c1e0780e07072b981d2807070707070707070707070703030303070303030303030393031b0303031b030741d1b42d1f1750b1750340d8888a0a08848aa81e9386eaaaaaaaa9a4a207a1ba82ea1faaa0b82eaa0380ea03a96a1750aa0a81c1c1c1c1c1c1c1c1c1c1c1c1c1ea070307031b031b031b03031b1b03030741d1b3b46c6d1b1751b175034ed88a28a0a08848aaaaaaaaaaa69280707070707070707070707070707a81c0c1c0c2c2c0c0c2c2c0c0c2c0c2c0c1d0742c5d42c2d42ced0b0b40d0b62282828a22122aa0baaaaa0baaa93aa69280707070707070707070707071b1b1f03070303030380c0c0c6c0c0c6c0c1d0746d0b47c5d47c5d40d036222282822122aaaaaaaaaa9a4a01c1c1c1c1c1c1c1c1c1c1c1c0c0c0c1c1c0c0c0c0e0b0b1b930b0b1b1faaa0b0b1ba0741d1b42d1f1750b1752348d8888a0a08848aa07a1baaaaaaaaa6928070707070707030303030303231b0b1b0b377b0307030303070303030303031b0303a81d074ed1b4dc5d48c5d40c0d40ced622228282828122a81eaaaaaaaaaa9a4a01c1c1c1c1c1c1c1c1c1c1c1c6c6c7c1c1c0c1c1c1c6c6c6e4c6c6c6c7c6c6c6c1d0746d1b47c5d47c5d48d236222282822122a81e86eaaaaaaaa9a4a01c1c1c1c1c1c0c1c1c1c6c7c6c6c6c6c6e4c1c1c0c0c1c0c1c1c6c6c7c6c6c6c1d0746d1b4dd2347c5d47c5d6222222828122a81e86eaaaaaaaa9a4a01c1c1c1c1c0c1c1c6c6c1d074ed1b4ed3b622222122a81eaaaa9a4a01c1c1c1c1c0c1c0c0c6c0c1d074ed1b40d3b622222122aa07a4eaaaa692881eaaa80e03aaa5a85d42a82a07070b070707930707070b070707070707070707070707070707a81c0c1c0c2c2c0c0c2c2c0c0c2c0c2c0c2c2c0c0c2c2c0c0c1d0742c2d42c5d42d0b44c5d4bc5d40d0b41c0702c2c02c3c02c0b04c3c0bc3c00c0b109c070781e07070b070ba070781ea07a4c1c2e81c2c1c0e07070b981d28070b07070707079307071b1b0707070707070707a81c1c2c1c1c1c1c1c1c1ea81e0781c1c1c1c1c0c1c0c2c0c2c0c4c7c0c0c7d1c0c0c6c6c0c0c6d1c0c0c1d0746d0b44c5d47c5d46c5d46c5d40d4741c0706c0b04c3c07c3c06c3c06c3c00c4710070781e0781e93070ba070b07070781e81c6c1c4e80e070743981d2807071307070707071b07070781c1e81c1c1c1c1c1c1c1c4c4c1c1c1c1ea070307031b1b03031b3303031b031b0313130303132f03030741d1b1751b1751b46d13135132f5034fd0701c1b0f01b0f01b06c13130132f0030bc42f01c1c1c4e070781c1c4c1c2e81c1e07a81e930713a0713070381c1c4e6074a01c1c0c0c0c0c0c0c1c1c1c1c1c1c1c1c1c1c6c6c0c1c0c0c0c0c0c6c0c0c0c0c0c6c0c1d0748c5d48c5d46d0b40d0341c0708c3c08c3c06c0b00c03108c0781e0707a0707a0381e030380c1e6074a01c1c4c1c1c1c1c1c6c1c1c1e0707a070307031b1b03031b03031b031b030741d1b1751b1751b46d0350701c1b0f01b0f01b06c030401c1e070781c1e81c1e81e0780e07981d28030303070707070b0b1b1b0b0b1b1b07070707070707071b1b1b1b131b13131b1b2b2b131b1313a80c0c0e4c0c1c0c0c0c1c0c0c6c0c0c0c0c0c0c0c0c0c0c0c0c1d0746c5d46c5d46d0b44c5d4fc5d40d0341c0706c3c06c3c06c0b04c3c0fc3c00c0310070781e07071b0713a070781ea07a4c1c2e81c2c1c0e030303981d280b07070b1b1b07070707131ba82c2c1c1c1c1c2c6c0c0c0c0c0c0c0ea80e0380c0c0c0c0c6c0c0c0c0c0c0c0e4c0c2c0c0c0c0c0c0c0c0c0c7c0c0c0c0c2c0c6d0742d0b44c5d47c5d42c5d42c2d40d0346c0702c0b04c3c07c3c02c3c02c2c00c0310071b81e1b82e930b0ba0b0b0b030382e82c2c2c2e80c0e03030313984d280b07070b03030303030b030303031b1b070707071b1b0380c0c0c0e80c0e80e03031b41d0b42d0340d2f1752f1751b01c0b02c0300c2f0f02f0f042701c6e0786c0e0b0b0b80e03030380c0e0b80c0c0c0e984d280b0b070707070b1b0b07070b0303031b1b07070707131b0b0b2fa80c0c0c0c0c2c0c0c2c0c0c0c0c0e4c0c0c0c0c0c0c0c0c6d0742c5d42c2d42d0b44c5d4bc5d40d0346c0702c3c02c2c02c0b04c3c0bc3c00c03109c071b81e1b030382e82c2c2c2ea0ba4c2c2e82c2c2c0e030303984d281b1b07071b1b0b07070b0303039380c0c0c0c2c1c1c2c0c080c0c0c0c0c0c0c6d0748d2342d0b42d0b46c0708c2302c0b02c0b108c0781e030382c2e0382e030382c2c2c2e4e6134a08c6c1c1c1c1cfc6c2c1c1d1c0c0e80c0c0e03030303031303030303030341d3f175231754742d0340d01c230f0230f02f02c0300c401e0780c0e82c2e80e0b80c0e0313984d280707555170ba07070781c1c1c1cbc8c0c0cbc8c0c0c1c0c1c0c6c0c6c0d5555551755552f0f02f0f00701c1b06c030bc440707a0707a070781e0760780e070767954a00d50b1b0b1b4b2f2f231313232f233f131307070707a1703070303030303555550f03c0f03c0781e070707a4c2e0b070303030753507070707171717173f3f1723231717170b1b0b170380e0303030313031b035930741d551743c0f03c0f01e0780e0780c1d507070707170b171b170b17170707070707070707171717171317131317172f13171313a81c0c1c0c5c5c0c0c5c0c0c6c0c6c0c4c0c0cfc0c0d59341d507517555555550701c170f0170f01b06c130f05f0f003044070781e070707a0707a81e93071ba071b070381c1e55280b070707071b1b1b07070707131ba85c6c1c1c1c1c5c5d555aa55551b0307030b030b03131f03031f470303171703031747030345d5559342d55551745d50b5546c0707c0b04c3c07c3c05c3c05c3c00c471101c6e0786e0ba4c2c2e82c2c2d617a13171313a0387c4d1e55280b0b070707070b1b0b070707070b546c6c1c1c1c1c4c6c2c2cbceea0b0307030b0b03030b0b03030b030b030b0b03030b0b03035542d42d55935555551b01c0b0f00b0b00b02c130f02f0f00302c44071b81e1b5a0b0ba82e930b0ba0b0b0b0382c2c2e5528 26 67108863 11 2047
def hc_68_9 : Nat → Nat := unpackHintV5 0xf580c677546dba462c9b1e40ad2f8bf6298dcadb872962c160af58415164c92830105278340917849460057a0185d0f0b20270f0ed34ec7199142c4b5726654e0bb28204a11a24dc7db1ec30a1c71838030a0e41c34f3701400cf0380d001b40180001b4 0x1f07071f1f1b070707071f1b131313330307031f031f031f1f03031f2303035555555555000000000000aaaaaaaaaaa1500270707433f0307033f032703131b07070707131313130b130b131303031313133f03035555550500000000000000aa84eaaaa0f85540000c0c0c0c3c3c3c1c3c1c3c3c3c3c3c3c3c0c0c3c3c3c0c0d5555545d000000003c104002a80e83e83c3e95402a07070707070b07070707071b070707070707070707070b0b070707070707070707071b130303030307030303030307031b030303030303030303030393031b0303031b030741d07175070751b42d1f1750b1750340d0701c070f0070701b02c1f0f00b0f00300c4207a4c1c1e81c1c1c1c6e0781c1c1e81c1e80c0e0307981d28a07070707071b13070707070707071b130b07071b03540c0c0c0c5c0c6c0d555543c0703c0f01e930781c1c1e0786c1ea07070707070b07070707071b070707070707070707071713070707070707070707071713541c0c1c0c1c6c0c0c1c1c0c0c6c0c6c0c5c5c0c0c5c0c0d07555555564d17545d550701c070f0070701b06c170f0170f00304481e930707a070707071b81e070707a0707a0381e5528a81c1c1c1c1c2c1c1c1c1c1cfc1c1c1c1c1c1c1c1c1c1c5c4c1c1c1c1c1c1c1c1c1c1c5c4c5c5c5c6c5c5c5ccc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0d55555555540d40d55930701c070f00707006c170f0170f00300c5117207a4c1c1e81c1c1c1cfe0781c1c5c1c4e81c1e07a0380e5528a07070707071b13070707070707071b130b07071b03000c0c0c0c3c0c6c0c5d0745d17400002a4c1e07aa86e1307070f130707130f2f170f93939313aa07070707070b07070707071b070707070707070707070f13070707070707070707070f0f001c0c1c0c1c6c0c0c1c1c0c0c6c0c6c0c3c3c0c0c3c0c0c1d0741c5d41c1d46d1b43c3d43c5d40d407000000024c0f003c0000aa4e07a81e86eaaaaaaa9a4004c1c1c4c3c1c1c4c3d6c3c5e4e4e4c4ea81c1c1c1c1c2c1c1c1c1c1cfc1c1c1c1c1c1c1c1c1c1c3c3c1c1c1c1c1c1c1c1c1c1c3c4c3c3c3c6c3c3c3ccc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c00741d071750707546d0f1750f0f50340d0000000000c00c0093000f2a9381ea07a3faa83e13aaaaaa69000b0707131b03930f0707130f0b0b1f4b0324e82c1c1cfc0c0c0c0d2c0d5541c1c1c1c1cfc4c1c1c1c1c1c1c1c8c4c7c2c2c7c0c3d0000002a4c1e078feaaa81c1c1c1c1c9c1c1c1c1c1d3c1c0c1c0c1c0c0c1c1c0c0c0c6c0c1c1c1c1c1c1c1c1c1c1c3c3c1c1c1c1c1c1c1c1c1c1c3c4c3c3c3c6c3c3c3ccc0c0c3c3c3c0c0d55555555545d0000000000003c104002a9381ea07aaaaaaaaa5500a81c1c1c1c1c1c1c1c1c1d3c1c0c1c0c1c0c0c1c1c0c0c0c6c0c1d0741c5d41c1d51b40d41c0701c3c01c1c01b00c1081e930707a0707070781e070381e6074a01c1c1c1c1c1c1c1c1c1c1c1c1c1ea070307031f031b031f2b03032b2b03030741d1f46d1f1752f175034ad8888a0a0884881eaaaaaaaaaa8ae69280707070707070707070707070707a81c0c1c0c2c2c0c0c2c2c0c0c2c0c2c0c1d0742c5d42c2d42d0b40d0b6228282222122aaaaaaaaaa9a4a01c1c1c1c1c0c1c0cac0cac0c1d074ed3b40d2b62222212207a4eaaaaa8ae692881eaaa80ea2ba5a85d42a82a0707a0781c1c1c1c1c1c1c1c1c1c1c1c0c1c0c2c2c0c0c2c2c0c0c2c0c0c2c0c0c1d0742c2d42c5d42d0b40d0b41c0702c2c02c3c02c0b00c0b109c0781e0707a0707a070781c1e0381e6074a01c1c1c1c1c1c1d50781c1c1c1d503032b0317031f032b031745d1745d55170f03c1f1bc070707070781e0781e072b070707a81c007a81c1c003032b030f031f032b031743d1f5bd0f03c0f03c000f07aaaaaa2b0707070707070707a0781c1c1c1c1c1c0c1c0c7c0c0c6c0c0c7cac0c0cacac0c0c1d0747d1b47c5d45d40d2b41c0707c1b07c3c03c00c2b10070781e07070781c1e0707a0707a0381c1cae6074a01c1e81e07070707070755070750703070327230303272303031f031b0355555555550701c270f0270f01f06c0309c4407981c1e81c1e81e0780e07954a2a070b07070707071f070707070707170707070707070707070717170707070707070707541cac0c0c1c1c0c0c1c0c1c0c7c0c6c0c5c5c0c0c5cac0c0d0745d55550755564d17545d55070f0070700701c1f06c170f0170f0030ac440707070707a81e930781e0707a0707a0381c1cae552800f070707070707a0781c1c1c1d5541c0c1c0c2c0c2c0cac8c0c0cac8c0c0d5517555555550701c1b02c0f06f0f0030ac440707981c1e0781c1e81c1e80e07072b954a2a07070b0b07070707070707070707170707070707070707070b07070707071b07070707541cac0c0c1c1c0c0c1c0c1c0c2cac0c0c2c5c0c0c2c0c2c0d555555175175564d541c3c01c1c01c0705c3c02c3c06c0b00c2b1101c1c1c1c1ea07a4c1c1e81c1e81e0780e07072b954a01c1eaaa07070700070700703070327230303272303031f031b030741d27175271751f46d0349d000000000000a2aaaaaaaa6900a81c2c1c1c1c1c1c7c1c1c1c1c1c1c3c1c1c1c1c1c1c1c1c1c1c3c3c1c1c1c1c1c1c1c1c0072b030307070303070307031f031b030f0f03030f2b030307175070750741d1f46d0f0f50f175034ad01c0f000001c0009303c00f0000207a07aaa4eaaaaaaa8ae690051707070781c1eaa81c1c0001c0c1c0c2c0c2c0cac8c0c0cac8c0c0c1d0746d0b45d5bc5d40d2b4000f000000000081e2aaaaaaaa8ae6900 25 33554431 11 2047
def hc_68_10 : Nat → Nat := unpackHintV5 0x8345963e36db1e243dce8a22070150f3474e5993b3fcc211f25e0cbf2baad7143368899920248c1022114d3102718c7b018e3aa4b71bfa560c5f6785b61e6299d0513206b87f666837e1f41858e60a6073043e3c81b21b40a50d003507600da3380001b4 0x6d3c9c1c1c9e4c1c1c6c9c1c1c1c6c0c1c0c2c9c0c0c2c0c0c2c0c2c0c3c3c1c1c1c1c3c6c2c2c3c2c3c9c3c3c3c3c3c2c2c3c2c3c3c2c2c2c2c3c9c0c0c3c9c3c3c0c0d55555555545d0000000000003c1040001e0782c9e89e89e0b80e83c9e83c3e954001c1c9e4c1c1c1c1c1c1c1c1d3c1c1c0c1c0cac0c6c0c1c1c0c0c1cac0c0c1c1c1c1c1c1c1c1c1c1c3c6c3c3c3c2c3c2c3c7c1c1c1c1c1c1c3c6c1c1c3c3c1c1c1c1c0c0c3cac3c3c0c0d55555555545d0000000000003c1040001e0781e0781c1e81c1e80e0781c1e81c1e954001c0c1c1c2c0c2c2c1c1c070f0f0b0b0b0b0f2307070707070707070f0f0b0b0b0b0f2745d555554003c000000410000781e0781e0781e0707a0707a550007070701c9c1c0c1c0c2c0c2c0d5555545d07070707070707070f0f0b0b0b0b0f0f03032723272303035000000000003c10000400000781e0781e0381e550707a0707a000781c1c1e0707070701c1c0c1c0c1c0c1c0c2c0c2c0c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c3c3c2c2c2c2c3c9c0c0c3c9c3c3c0c0d555555545d00000000003c1040001c1c1c1c1c9c1c1c1c1c1c1c9e4c1c1cac0c0c1c1c0c1c0c0c1c0c1c0c2c0c2c0c1c1c3c3c1c1c1c1c1c1c1c1c1c1c3c1c1c1c1c1c1c1c1c3c3c2c2c2c2c3c9c0c0c3c9c3c3c0c0d0745d55555555545d000703c00000000003c1040001c1c1e81c1e07a0781e0781e0381e0707a0707a55000b030303070303031b0323031b030f07071b0f0b0b1f0f0f0f230f230f0f0f230f2703030303030f0f03551745d50345c0003c0f000c0f44004e1380c8cfe0f86c1c1c1b03070327031b035555551743c2c1c1c1c1c6c2c3c1c3c2c3c2c1c1c0c0c9c8c9c8c0c0d40000000003c0000000781e2786e03a552713a2713a0007a81ea23031303070707070f0b0b1f0f0f0f130f130f0f0f130f1f033f0f035545c0000f44001e1384e84ea83e0f9406c9c1c1c1c1c9e4c6c9c9c1c1c1c6c0c1c0c0c6c0c6d3c0c0d3c0c0c3c3c1c1c3c1c1c1c3c6c3c6c3c3c3c2c3c2c3c7c3c3c3c3c3d3c3c3c3c3c3c3c6c3c6c0c0c3c3c3c0c0d55555551745d5545d0000000000f03c0003c1040001e07a1b86d3e93e80e83d0e83c3e954000c0c0c6c1c1c6c6c9c6cac6c9c6d3c0c0c0e4c0c1c0c0c0c1c0c0c0c0c0c0c3c3c1c1c1c1c3c6c3c3c3c3c3cac3cac3c3c3c3c3c6c3c6c3c3c3c2c3c2c3e3c0c0c0c0c0c0c0c0d55555555540d0000000000000c1040001e0786e8acaea1b80e0383cfe83c3e954001c1c1c0c0c0c1c1c1c0c0c0c0c0c0c0c1c1c1c1c3c2c3c2c2c7c3c7c3c3c3dec3c9c3c3c3c7c3c7c0c0c0c0d5545d1750300000f03c00d100a0781e03070781e07070707030300c0c0c0c0d5555540d0707030303030303271f270b270b271f03030303030303035000000000030400000000781e0781e0380e550707a0707a00030303072707070707070707070703070303070303030303930303030307070f0f070707070707070707070f07070707070707070f0f0f0b0f0b0f330303030303030303555555555503400000000000030410000707a0707a0781e0781e030380c1e0707a0707a5500930b0707030303930323071b0f0b0b1f0f270f1b270345c0f06c2c2c2c0c0c1c0c0c0c0c0c0c0c3c1c1c6c2c2c2c2c3c9c2c3c3c2c2c2c2c2c2c2c0c0c0c0d550300000d1000b84e3f83e03030b1b1b0b930b07070b930b07070b0703030f07071b0f1b0f270f1b0f1b0f0b0b1b0f0b0b1f044006cacfe0f82c1c1c6c0eaa0383c1c1c6c2c2c2c2c2c3c3c2c2c2c2c2c2c2c3c7c0c0c0c0d550300000d1000b82e80ea82cac2c2c8c1c2c1c8d3c0c0c0c0c0c0c0c0c0c0c0e4c0c9c0c0c0c9c0c3c3c3c1c3c1c3c6c3c3c2c2c2c2c3c7c3c3c3c3c2c2c3c2c2c2c3c2c3c7c3c0c0c0c0c3c0c0c0c0c0c0d55555555540d0000000000000c1040022ba0b88e82e80c0e0383cfe83c3e954002c2c2c2c1c0c0c0c0c0c6c0c0c0c0c0c3c1c3c1c1c6c3c6c3c2c2c6c3c3c3c6c3c9c3c3c3c6c3c6c0c0c0c0d545d175030000f03c00d1001384e2783e0b1b0b1b0303030303270300c0d5555540d1b1b270727071b1b0f0f030303030303030303030303030350000000000300000006e2b89e0b80e039549c4e89c4e8006c1c1c4c0ea03a89c0c3c1c1c6c3c3c3c4c3c9c3c3c3c4c3c4c3c2c2c7c0c0c0c0d544d175030000f03c00d1001382e82e030f84eaa0b271b070b071b0b1b0b1b0303030303030303270303270303030303930f0f0f070f070f1b0f0f0f0f0b0b0f0b0b0b0f0b0f270f0f0f0b0b0b0b0f270303030303030303555555555503400000000000030410001b8ae27a0b27a2782e0380e0f27a0f0fa55001b07071b0f0f0303030303031b1b1b0b1b0b1b1b031b03030303030303031b03031b0354555555550000000000000781e1b86e2313a2313a030380c8e55001b071b071b1b1b0307031b031b0355455550f0f0f1b1b1b0b1b0b1b1b03031b1b1b0303500000000000000000781e1b86e03a551b13a1b13a000b0b0b0b0b030b030b030b0355515550b1b0b070b070b0b0b0b0b03030b0b0b0b0303500000000000000001b86e0b82e0382e550b0ba0b13a000b1f0b1f231b23072307231b0f0f030303030303030303032303031f03030303031f035554555555000000000000338ae1f82e2313a2313a0380e5500271f271f8f0333031f0327035555455331b1f0733071f1b0f0f0f03031f47030350000000000000000338ce1f87e03a551f13a1f13a000b07070b930b0b0707270303030303551745d51b07071b1f0b0b1f1b271b2723234f276b1b231b030f40000f03c0003f8fe1384e0b270b270b230b230303035555555231b2323231b23230b0b0b0b23930f0f0f0b0b0b0b0f0b0f40000000000004b8ae2782e2382e55231388c4e000b1f0b1f03030303030303035555451f1b1f071f071f1b1f1f1f03031f50000000000000001f87e1f82e0380e551f13a1f13a00272b2703030303030303030355555156b1b23072b07231b276b230b270b2303030f500000000000000008ae89e0380e552313a4b13a00 25 33554431 10 1023
def hc_68_11 : Nat → Nat := unpackHintV5 0xe86204da6b7ed25206ca0a12bb43b2b3a1e8aba200a521a09cda1298412690e1d88b795a84d9a87ec98472631a6cf95a6631b259fb0e5329b44c79ac404b0c3a817233b9b22e595828f95827e84422815a1be1a81549a60e51be0679f600019e 0x1c1c2c0c0c0c0c0c0c0c0c3c3c1c1c1c1c6c6c2c2c1c1c2c1c2c2c0c0c0006d0742d0b40d034cc5d4cc5d40000000000001e0782e0b80e038cc4e8cc4e98cd000b2b0b07070b9307070b0b0707070f0f070707070f1b0b0b0b0b0b0b0f0b0b0f0f0b0b0b0b0b0b0b0b0b0b0b0b0b0b0f03030303030303030303030303030303006d0742c2d42c5d42d0b43c5d43c3d40d03400000000030030024c003c0781e0b0ba0b3fa0b82e0fa0f0fa0380e64002c1c1c03030303030303030f0b070707070b0b0f070b0b0b0b070703030001b41d4742d0340d5b1755b1750000000000000f01e0791e0b80e0396c4e96c4e99000b070702c0c0c0c1c0c0c0c3c3c1c1c3c6c3c3c2c3c2c3c7c3e4c3c3c0001b41d4742d2348d0f1743c3d000003c0024c030003c0781e4782e2388e0f4383c3e64b4002c2c1c1c1c1c2e4c2c2c2c1c1c1c3c3c1c1c1c1c3c6c3c3c2c2c3c6c2c2c3c7c3c3c3c3c3c3d3c3c3c3c3c3c3c6c3c6c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0d3c0c0c0c01b41d4742d1b1754f1750f1750f0f50340d000000003c0f000c00c0093000f01e0791e0b86cfe93cfe83d0e83c3e80e0399001b07071b030303030300c0c0c0c3c3c3c6c6c6c2c6c2c6c6c0c0c0006d0746d1b40d0346c5d46c5d400000000000001e0786e1b80e0386c4e86c4e99000b0b0b0b0b1b03030303030300c0c0c2c6c2c1c2c1c2c2c2c2c2c0c0c0006d1b42d0b40d0342c2d42c5d400000000000006e1b82e0b80e0382c2e82c4e997d000b1f0b030303030303030303030f070707071b0b0b3303006d0742d0b40d0347d334000000000001e0782e0b80e0387e1f98cd000b0b0b0303030303030303031f0393031b1f070707071f930f0f0f07070f070f070f03006d0746d1f40d0347d1f400000f03c0000000781e1b87e0380e1f87e61f400cc7c0c0c5c1c1c6c3d503030303331f2b1f0f0f0301545c5d1745d1755000001f85e1f87e0b1f0b1f0303030303030303030cc6c7c1cac1c7c6c3c3c3c0c0c0012b47d0b40d0347c5d45d40000000000000ce2b87e0b80e0387c4e87c4e99001b1b50745c5c3c1c1c6c3c2c2c6c3c3c3c6c3c6c3c3c3c6c3c7c0c0c0c0c155554000c03024c44e1390e0f86c1c1c6c0c0c0c0c0c0c0c0d541c1d56c7c6c2c6c2d6c7c0c0c000555555555400000000000101e07a1e1b80e0396c4e96c4e9540146c6c2c6c2c5c0c0c0c0c0c0c6c1c1c6c5c5c5c5c7c7c5ccd9c5c5c5c3c3c0c05930741d1745d17554000005e3384e13951b07071b170b17170b17170f0f070707070f1b0f0f0f0f0f170f0f0f0f0f0f170f170f0f0f1b0f0f0f030303030303030303030303030303030159341d5075175543d175555550000000000c00c00930040781e1717a173fa86e0fa0f0fa0380e550017171b1b50743c1c1c6c3c3c3c6c3ccc3c3c3c6c3c6c3c2c2c6c0c0c0c0c155554000c03024c44e1390e0f82c9c2c9c0c0c0c0c0c0c0c0c9c6c9c1c9c1c9c6d542c2d40c0c00117551555555500000000000045b8ae2782e0380e2713a2713a55000b2b0b4717170717071717543c3c3c1c3c1c3c6c3c3c2c2c2c2c3c7c3c3c3c3c3c5c3c3c3c3c3c3c5c3c5c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c045d5559342d50b555555400000000030030024c0122b91e0b85c5e85cfe83e83c3e80e03954002c2c2c2c1d50f070f07071b0f1b0b0b0b0b0f0f0f1b0f5b0f0f0f1b0f1b030303031b032303050b555540003c0f00c03024c44e13a0f82c2c2c2c0c0c0c0c0c0c0c0c6c6cac1cac1c6c6c2c2d5540c0c0015545555554000000000000106e2b82e0b80e0396c4e96c4e954002c2c2c1c2c1c2c2c2c2c2d50f0f0f070f070f1b0b0b0f0f0b0b0b0b0b0b0b0b0b0b0f0b0b0b0b0b0b0b0b0303030303030303030303030303030301550b50b5564d55555400000000030030024c0106e2b82cfe82c2e82e0b83e83c3e80e03954001c2c1c1e4c1c2c1c1c1c1c1c1c2c2c2c2c4c4c2c4ccc2c2c2c2c2c2c2c0c0c0c0c802d1744d17400001eaa0fa0300b07071f1f1b070707071f1b1313130303030380c0c0ea80c0e8cd0747d0b47c5d47c5d40d03400000000000213aaaaaaaaa2a039a40142d0c2c5c1c1c1c1c5c4c5c4c4c4c5c4d2c4c4c4ccc2c2c4c0c0c0c0c8164c1d0745d55000007aa83e80c10c1c1c5d46c1c1c4c7c2c2c4c5c4c5c4c4c4c5c4c9c4c4c4c0c0c0c0c805d5930b42d55000013aa83e80c06c4d2c4c0c8c0f1382c1c1d46c1c1c4c2c4d2c2c2c2c2c2c2c2c4c4c2c2c2c2c0c0c0c0c802d0b564d5400004e0b84eaa0fa030070743131b07070707131313130b130b131303030303030303030a0041d513135131750340d00000000000084eaaaa0f8a80e690002b2b0f0f0f070f070f0f0f0f0f0f0f0303030303030303012b543c5d43c3d40d0340000030030024c003c8aea0fa0f0fa0380e64006c0c0c0c0c0c1c0c6c0c2c0c0c2c3c1c1c6c2c2c2c2c3c8c2c3c3c2c2c2c2c2c2c2c0c0c3c8c0c0c0c0d550300000d1000b84e03232783e01c9c1c6c9c6c0c1c0c2c0c2c0d5555543c3c1c1c1c1c6c6c3c3c1c1c2c1c3c3c0c0c9c8c9c8c0c0d40000000000000001e0789e0b80e339549c4e89c4e8001eaa0788c0c4c0c1c1c1c1c3c3c3c4c3c4c3c3c3c4c3c9c3c2c2c7c0c9c3c0c4d175551700f03c0003d1000782e82e130f84eaa 24 16777215 10 1023
def hc_68_12 : Nat → Nat := unpackHintV5 0xe76304e0d1a4d3fb36c7cb0cc061dab51ad2afb15aa8e9b2a3895897530e91b9668a99c885215e7c623074e9de7498147478087338506a922a5ca37c54720c4d61c44103183999da2e52d22781b420d1ac1fc0441a595a0e2b0c06b1de0001ac 0x546c1c1c6c5c2c5c6c5c2c5c5c3c6c1c1c1c1c3c3c3c5c3c5c3c3c3c3c3c5c3c3c3c3c3c01b030703171703031703031b031b030f0f03030f0303564d07541d45d555555540f000000024c0f003c00000781e1717a17a1b86e0f0fa0fa03a5500070755507070707000707007030703272303032723030327031b0351555555550000000000000781e0707a0707a0781e0381e5500541c2c1c1c1c1c1c7c1c1c1c1c1c1c3c1c1c1c1c1c1c1c1c1c1c3c3c1c1c1c1c1c1c1c1c0072b030307070303070307032b031b030f0f03030f2b030341d41d55935555555501c0f000001c0009303c00f000001c1e81c1e81e0781e0781c1e81c1e80e07954002c6c7c2c9c6c3c6c3c1c3c1c3c3c0171b17071707171755540000006c0ccc0c2c0c2c0c3c3c0c0c3c9c0c0c5c5c0c0c5c9c0c0d1755564d0b505543d17542d5503c0009302c00b00000f03c000006e1f87e0b83c3e83c7e85c5e85c7e80e1f954002c2c2c2c2c0c2c0c2c0c2c0d550b05551b1b1b071b071b1b000003030b0b0b0b0303500003c00002c000000001b86e0b82e0382e552713a2713a000b0b0b070b070b1b0b0b1b0b0b0b543c6c3c1c3c1c3c3c2c2c3c00b030b030b0b03030b0b03030b030b030b0b03030b0b03035542d42d559355055503c00000009302c00b000006e1b82cbe82c2e82e0b83c3e83c9e80e0b954003c3c6c6c01c1707071b1717171b17331717171b171b170b0b1b030303035550340d5930000001384e4385e0b270b270303030303030303271b27072707271b000b0b00303555555551555503c0000000000000be2b89e0b80e0389c4e89c4e954010c1c1c3c06c1c1c4c7c2c2c4c3c3c3c3c4c4c3c4c9c3c3c3c0c0c0c0d9555543c0930b02c0013aa84e80d42cac2d1c3c3c1c3c1c3c3c0171717071707171b17170b0b0b0b171f0f0f0f0f0f0f170f0f17170f0f0f0f030303030303030303030303030303035555555555035035564c0f00024c0b002c0000000008ae4782e0f0fa0f3fa17a1717a0380e550050b1b0b170707070713131317131f1313131713172017033f03330313035930741d1744d175540002a84e0f9409c1c1c7c4c4c1c1c1c1c4c6c2800fc0c1c0c7c0c9c0c4cfc0c0c4c4c0c0d0747d2744c5d44c4d40d3f4000000000002aa138a83eaa6a1340003c3c1c3c1c3c3c0030303030f0f03030f0303550f0f50f17503503c0009303c00f00002a83c3e83e80e99000b070702c2c0c0c0c0c0c0c1c1c2c2c2c2c2c1c0c6c0c0c0c0c0c0c0c0c0c6c0c6d0742d0b48c5d48c5d40c0d032340000000000001e0782e0b88c4e88c4e80c0e0323992d000b0b07070b02c2c2c1c1c0006c0c1c0c2c0c2c0c6c6c0c0c6c0c0c6d41d46d0b46c5d46c5d40d40000f00000000000781e1b82e1b13a1b13a03a640145e4e4c1c2c2c1d23031764c3c81c1c1c1c1c1c0c0c0c0c0c0c1c1c0000c1c0c03030303030303030303030303030741d0b42d1751750340d0002c0024c000000001e0781e0781c1e81c1e80c0e0307981d0003030307070b0b070707070707070707070b0707070707070707070b07070707070b07070707000c1c0c0c1c0c0c0c0c0e4c0c0c0c0c0c0c0c0c0c0c0c0c1c5d41c1d41d0742c5d42c2d42d0b40d0340000000b00b0024c00001c1e81c1e81e0781c1e81c1e81e0780c0e0307981d000b0b0b0b0b0b0b070b070b1b0303000031b0303030300c0c0c2c0c0c2c0c6d2b42d0b42c5d42c2d40d40d400000000000006e2b82e0b82c4e82c2e80c0e03995d000707070707075550707000070307030b030b032b2303032b23030341d4564d55555554000f00000000000781e0781e0707a0707a0381e5500541c1c2c2c1c1c1c1c1c1c1c1c1c1c3c1c1c1c1c1c1c1c1c1c2c1c1c1c1c1c6c1c1c1c1c0072b030307070303070307030b2b03030b0f03030b030b0341d41d55935555555500000003c03c009300000707a0707a0781e0707a0707a0781e0381e55000b0b0b0b0b030b030b030b0345d54542c551b1b1b071b071b1b000003030b0b0b0b030350000002c00000000006e1b82e0b80e0b9549c4e89c4e8002c2c2c1c2c1c2c6c2c2c6c2c2c2c0171b1707170717170b0b17542c0c2c0c2c2c0c0c2c2c0c0c2c0c2c0c2c2c0c0c2c2c0c0d17550555564d0b542d550002c02c0093000000001b86e0b5fa0b0ba0b82e1717a1727a0382e55000b0b0b0b07005c1c5c1c1c6c5c6c2c2c2c2c5c5c5c6c5d9c5c5c5c6c5c6c0c0c0c0c6c0c8c0d55545d1740d03564c02c000001384e85e0b0b0b0b03030303030303031b1b2b072b071b1b0b0b00003035555555545555500000000000001b8ae0b82e0380e6713a6713a55001b134b13032345c4e0b070701b0707130b134b0b0b0b0b0b0b0b13130b0b0b0b030303036555550b02c093001382e13aa84e80d42c2c2c1c2c1c2c2c2c2c2c0171717071707171b0b0b17170b0b0b0b0b0b0b0b0b0b170b0b0b0b0b0b0b0b030303030303030303030303030303035555555555035035564c000b00b0024c0000000006e2b82cfe82c2e82e0b85e85c5e80e03954004c6c1c1c1c1c4c4c2c1c1c6c28006c0c1c0c4c4c0c0c4cfc0c0c2c0c2c0c6d0744c4d44c5d57d0b40d3f400000000000213aa82e2a0baa84e5a50000b0f0f070b070f0b1b0b1b006c0c0c2c0c0c2c3c0c0c2c0c2c0c6d43c5d42c3d50b40d4000f00f0024c00006e83e82c3ea0b80e9900 24 16777215 10 1023
def hc_68_13 : Nat → Nat := unpackHintV5 0x8fc8df45e480225a2610aca02821cd23dd8cd9e0a388e3f3186e30f235148118fb63cb9a38e58d4ff2a6e7f142444c988a264531c51f3ad78e854606ce9d02f69c315ac8209097343a33861934f90980c683dc3901781d80850dc02b85c00ac2c0000158 0x1b07071b0f0f0f0f0f0f1b0307030f0f03030f0303031b031b41d0f0f50f17546d035024c07001c03c0000001e0783c3e83ea1b80e9900070700001c1c1c1c1c1c1c1c1c0c1c0c2c2c0c0c2c2c0c0c2c0c0c2c0c0c1d0742c2d42c5d42d0b40d0b400000000000001e0781c1e81c1e81e0780e07981d0007070707070707541c00707540c0cac0c5c0c7c0cac0c5d1745d175545c1c000000781e0781e070707070701c1c0001c1c1c1c0c1c0c7c0c0c6c0c0c7cac0c0cacac0c0c1d0747d1b47c5d45d40d2b40700000000000000781e0781e0707a0707a0381e6074001c1c0001c1c1c1d541c1d41c0c1c0c9c8c0c0c9c8c0c0c9c0c6c0d55555455540000000000001e0781c1e81c1e81e0780e07954000070b07070707071f070707070707170707070707070707070717170707070707070707541cac0c0c1c1c0c0c1c0c1c0cac0c6c0c5c5c0c0c5cac0c0d0745d55550755564d17545d5501c01c009300000000000707a0707a0781e0781e0707a0707a0381e55000707070707070000707555070307030b030b032b2303032b2303035545d15555554070009300000000000781e0781e0707a0707a0381e5500001c1c2c2c1c1c1c1c1c1c1c1c1c1c5c1c1c1c1c1c1c1c1c1c2c1c1c1c1c1c6c1c1c1c1d5072b030307070303070307030b2b03030b1703030b030b0355555545d45d55935501c01c009300000000000707a0707a0781e0707a0707a0781e0381e5500001c1c1c1c1c1c1c1c1c1c1cac0c0c1c1c0c0c1c0c1c0cac0cac0c1c5d41c1d41d07540d2b4070070024c0000001c1e81c1e81e0781e0780e07981d000707000000001c2c0b0b0b0b03030b0b03030b0307030b030b0327175271751b41d0b42d0342d02c0700000f00000b000009c4e89c4e81e0782e0b80e0b989d000b1b0b07070b9307070b0b0707070070707070f0f0b0b0f002c0c1c0c2c2c0c0c2c2c0c0c2c0c2c0c2c2c0c0c2c2c0c0c6d0742c2d42c5d42d0b43c3d43c5d40d0b40f0002c0b0000024c0b002c00000781e0b0ba0b2fa0b82e0f0fa0f27a0382e6274001c1c2e4c1c1c1c1c1c1c3c6c01c1c1c1c1c1c0070707071b07070f070f000000070307030b1f030b1b030f0f03030f2b030307070303071b03030741d1b1f42c6d0f0f50f1750707507175034ad01c0009302c00b00000703c000001e0781c1e070781c1e81c1e81c1e81c1e80e07981d00070700001c1c070b0000070307030b0b03030b0b03030b030b030741d27175271750b42d0342d01c000b00000002c00000781e0707a0707a0781e0381e6074001c0c1c1c2c0c2c2c1c1c070b0b03030b0b0b0b0707070700707002d0b41d0742d0b43c3d43c5d4000700024c0b002c000781e0781e0781e0707a0707a6074001d07070b42c2c1c1c070f1750f170f0f0707070700707002c0c2c0c1c0c1c0c2c0c2c0c2c2c0c0c2c2c0c0c000700024c0b002c000781e0781e0781e0707a0707a0381e000781c1c1e0707070701c1c1e81c1c1c1c1c1c1c1c01c1c007030703070307030b030b030b0b03030b0b03030741d0741d0b42d0f0f50f1750342d0001c0009302c00b000001c1c1c1c1c2c1c1c1c1c1c1c2e4c1c1c3c1c1c1c1c01c1c007070b0303070703070303070307030b0b030b0b030b0b03030b0b03030707175070741d41d0742c9d0b0b43c3d43c5d40d0b40703c00000700024c0b002c0000070707a070781e81e0781c1e070781c1e81c1e80e07981d000b0b070707070b930f1b0f1b070707070f070002c2c2c1c1c1c1c1c1c1c0000006c0c1c0c2c0c2c0c3c3c0c0c3d1c0c0c6c6c0c0c6d1c0c0c6d0746d0b43c3d43c5d46c5d46c5d40d4740f00024c0b002c00003c0f000000781e1b82e0f0fa0f1fa1b1ba1b1fa0387e61f4003c3c0c0c0c0c0c0c07071b0b071b1b07071b1b031b03030303031b03030303031b031b41d23175231751b42d0340d0000000000000781e2313a2313a1b82e030380c8e6334003c3c3c071b071b1b00070701b0307031b1b03031b03031b031b031b41d1b1751b1751b46d03500000000000000781e1b13a1b13a1b86e03a64000c0c0c2c1c1c6c2c2c6c6c2c2c6c6c3c6c1c1c1c1c3c3c3c6c3c6c3c3c3c3c3c6c3cac3c3c3c3c00303039303070303030703031b0303030303030303030303031b41d1b1751b1751b42d0f0f50f1750340d03c00000009302c00b000001e0786c6e86cae86e0b83c3e83cfe80e0399000707030303030303070707070007070030300c0c0c0c0c0c0c0c0c0c0c0c0c1d0749c5d49c5d49d0b40d03400000000000001e0781c1e81c1e81e0780e03981d00030303070b07070707071f0707070707070f070707070707070707070f0f0707070707070707000c1c0c0c1c0c0c0c0c0e4c0c0c0c0c0c0c0c0c0c0c0c0c1c5d41c1d41d074cd0b43c3d43c5d40d0340703c00000700024c0b002c00000707a0707a0781e0781e0707a0707a030380c1e6074002c2c7c2c2c2c3c6c3c1c3c1c3c3c00b0b0b070b070b1b03030303030303000000031b0303030303030393030b0303003030303030f030303030b031b4ad0b42d0f0f50f1750b1750b0b50340d03c0009302c00b00000b02c000006e1f82e0b83c3e83c7e82c7e82c2e80c0e031f987d000b0b0b0b03030303030b003031b1b1b071b071b1b000003030001b46d0b42d0340d271752717503c00002c000000001b86e0b82e0380e2713a2713a6274002c2c2c1c2c1c2c6c2c2c6c2c2c2c0c0c0c3c6c3c1c3c1c3c3c2c2c3c003030303030b03030b03030303039303030303003031b46d0b1750b0b50b42d0f0f50f1750340d03c00000009302c00b000006e1b82cbe82c2e82e0b83c3e83c9e80e03989d001b1b23231b1b0b0b0b0b030303930002c2c2c2c00000303031b49d2348d0b42d0b42d0000000002c930006e1f87c4e1f1382e0b82e0b987d00231b2b072307471b0b2b0b47030300003030303030f03030300c0d2b49c5d48c5d49d0b40d03400000000000022b8bc4e88c4e8be0b80e03995d000707555170b0001b07071b27230303272303031b0307031b031b0355551545d555400000f000000002713a2713a0781e1b86e038be550003542c6c2c6c8c3c9c3c3c3c8c3c8c3c3c3c6c1c1c3c05c0c6c0c0c0c0c0d55554003c0930b02c1384e0f8fe032351b07071b1717171727471723231717170b1b0b1703000c0c0c0c3c0c6c0d64c1d075545d00000178fe1384e650b130b1b07070707130f270f0f0f130f130f0f0f0230313030f033f0355550700024c3c0f01e13aaa135 25 33554431 10 1023
def hc_68_14 : Nat → Nat := unpackHintV5 0xf19a3ce87a48d8abf4d0321ec75a36c001d6b6e248b24926aa120ea3d1909b721893f9de8c89dc8549d07cfa147579e06e29d468a9605ad37653f1b84e317048b160431966370b0431a15a2b01a824f1841f9158132b1a0c61b20701580001c0 0x2c1c1d0303030303030303170b070707070b0b17070b0b0b0b0707030355555555555551b01c4702c0300c670f0670f0511701c1c1c1d1c1c2c1c0c0c0c0d9c4c1e6713079540702c1c1d0b0303030703030317170707171b17170b170b171f1793171755555555175559340d1b01c2302c2308c170f05c3c511701c1c1c1d1c1c2c1c8c1c8c1c5d0c1c5c5c1d54072302c2c1c1c1c1c2e4c2c2c2c1c1c1c5c5c1c1c1c1c5c6c5c5c2c2c5c6c2c2c5c7c5c5c5c5c5c5d3c5c5c5c5c5c5c6c5c6c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0d3c0c0c0d5555555545d17540d40d55931b01c4702c1b0f04f0f0170f0170f00300c511701c1c1c1d1c1c2c1c6cfc1e4f3f0785d0c1e17170780c0c0c0d540706c1c1c6c0c0c0c0c0d030303031717171b1b1b0b1b0b1b1b0303555555555555551b01c1b06c0300c1b0f01b0f044070707071b071b07030303031b130786c4c1e5501c0b0b0b0b0b1b03030303030340c0c0c2c6c2c1c2c1c2c2c2c2c2c0c0d555555555555546c1b02c0b00c0302c2c02c3c1106c6c6c6c2c2c2c2c0c0c0c0c2c2c2e0b130b9542f2f02c7c2c0c0c0c0c0c0c0c0c0c0c5c1c1c1c1c6c2c2ccc0d55555555551b01c0b02c0300c1f0cc44070707070b070b07030303031f071f075501ccc0b0b0b0303030303030303031f0393031b1f070707071f9317171707071707170717035555551745d55551b01c1b07c0300c1f07c44070707071b071f07030303031f071f075501c7c331f03030f07071b0f000c0c0c0ccc7cac7c5c5c0d501555540f0f03c0f03c007e0f87e1f82c7c2c7c0c0c0c0c0c0c0c0c0d331b1f072b071f1b1717170303555555555555550ac1f02c0300c1f0f00f044331f2b1f1f0b0b1f030303031f131f87c4c7e5507c070b070793070b0707070707070b0b0b0b13130b13330b0b0b0b0b0b0b030303036555550b03c0f03c07070781e1307030350b07071f1f1b070707071f1b131313030303030303030303030380c0e95555555554cc0707c0b07c3c07c3c00c031101c4e0787c4c4e0b1384c4e84c4e980c0c0e5528070743131b07070707131313130b130b131303030303030303035a55555555555501c0130f0130f00300c44071381e3b1384e13131360303039554a0acac5c5c5c1c5c1c5c5c5c5c5c5c5c0c0c0c0c0c0c0c0d5555540d40d55930ac0170f0170f00300c51170acacececec5c5e17171780c0c0c0d543b06c6c071b1b00070700f0f0f1b0307031b031b031b03031b1b03031b41d1b46d1b1751b17503500000000000000781e1b86e1b13a1b13a03a64001c1c0002c2c2c2c2c1c0b1b0b0b03030b0b03030b0307030b030b030b1750b0b51b41d0b42d0342d02c070000000b24c0000000b13a0b0ba0781e0b82e0382e65f4000c0c0006c2c8c6c2dadac6c1c1c6c0c3c0c0c6c0c03030303030357175231751b41d46d0340d00000000000004b13a2313a0781e86e030380e6574002c1c1c6c001c1c06c6c7c0c6c0c0c0c0c030303031b031b41d1b42d1f1751f1750340d0000000000000781e1b82e1f13a1f13a030380c7e61f40002c2c2c2c1c1c1c1c2c2c2c3c2c7c2c2c2c3c2c3c0ea03030303a0383d1745d0b424c1c0702c00aa0b82e80c00b07071b0b0b0f1b0b0b0f0f0b1b070707071b1b0b0f0b0b0f0f1f0b0f0b0b0f0f0f0f030303031b03030303030303030303030303030393031b0303031b031b41d0f0f50f1751b42d231750b1750340d024c07001c03c00000000001e0783c3e83cfe86e0b88e82e80c0e03990007070000f0b5551b07071b27230303272303031b0307031b031b03555545d5455540000000f0000002713a2713a0781e1b86e0396e550003002c6c2c6d5c5c9c5c5c5c8c5c8c5c5c5c6c1c1c5d43c0c6c0c0c0c0c0d545d5930b42d000001384e178fe035701b07071b0f0f0f0f23470f23230f0f0f0b1b0b0f03540c0c0c0c5c0c6c0d5555424c1c070003c0f8fe1384e00b1b0b0f070707070f0f0f0f131f0f13130f0f0f650f033f032303130355550930701c0f03c0f002a84e1394001b07071b0f0b0f1b0f0b0f0f171b0707070717170f0f0f0f0f0f17170f0f170f0f0f0f546c0c1c0c3c3c0c0c3c0c0c6c0c6c0c5c5c0c0c5c0c0d17555555564d17545d55024c07001c03c00000000001e0783c3e83e86e1b85c5e85e80e954006c6c01c0f0f1707071b170b0b1b1717171b171b1717171b171f030303035550340d5930000001384e4385e1b07071b030303030303030300070705b1f1b0b1b0b5b1f0303555555551555500000000000000781e8b86e0380e5b13a5b13a550001b1b0b1b0b0f0303030303031b07071b0f0f0f0f1f1f0f335b0f0f0f171703555555424c1c0703c0f03c000f8ce1384e00b430b0f070707070f0f0f0f13130f134b0f0f0f330b0b13030303036555550930701c0f0001eaa13a035006c1c1c6c3c2c3c3c2c3c3c5c5c1c1c1c1c5c6c3c3c3c3c3c3c5c3c3c5c5c3c3c3c3c5c5c5c6c5c5c5c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0d55555555540d40d5593024c07001c03c000f03c0000000001e0783c3e83cfea1b85e85c5e80e03954001c1c1e0707aaa131313070307031b031b031f1f03031f2303030741d1b46d1f1751f175034fd00000000000081e2aaaaaaaaa84e6900200b130b1b0707070713172713131313131313171753f03130317033f030755564c5d17400001e0faaa1300a0007070707130b1313130b1307030703133f0303131303033f031b030741d131751313546d034fd00000000000081e2a0faaaa84e69000 24 16777215 10 1023
def hc_68_15 : Nat → Nat := unpackHintV5 0x9579b046ecf4225c4690a1a328049313dec8e1d0d7a4d9eba0682933320e819723790b0223e5059ee2464f2111e4507b835c39c4ff1ad4838c6b3fc5d099429b93312c885095a0284ab00824ac2b0ff698061c77c27da420fb90d05fa7881e04740003c0 0xb1b0b07070b9307070b0b07070750707070717170b0b17542c0c1c0c2c2c0c0c2c2c0c0c2c0c2c0c2c2c0c0c2c2c0c0d175542d0b5555564d0b542d551b01c0b0b00b0f00b02c170f0170f00302c44070707070b0b0782ccc1e0b070b0717170785c9c1e03070b035501c9c07070b93070707070707171b5070707070707541c1c1c1c6c1c1c5c1c5d5555541c0c1c0c2c7c0c2c6c0c5c5c0c0c5cac0c0c1c1c0c0c1c6c0c0d0755564d0b542d55541d175550701c1b1f02c6c170f0170f007070070f0030ac440707070707070707070707070781c1c1e07070781c1c1e030707035501c1c070755541c1d070b5555070307030b0b03030b0b03030b030b0341d550b55555542d550701c270f0270f00b02c0302c440707070707070781c1c1e07070707030707035501c1c070307070b030b0b070741c2c2c0c0c2c2c2c2c1c1c1c1d41c1d55541d5559342d50b42c0b01c0702c0b05c3c05c3c1101c1c1c1c1c1c1c1c1c1c1c1c1c1c1e070707954070701c07070b02c2c1c1d070f0f00f0f0f0f0707070750707542c0c2c0c1c0c1c0c2c0c2c0c2c2c0c0c2c2c0c0d550755564d0b542d5507070707070707070707070707070781c1c1e03070703550707070707070707070741c1c1c1e070707070707070750707541c0c1c0c1c0c1c0c2c0c2c0c2c2c0c0c2c2c0c0d550755564d0b542d550701c0701c0b02c170f0170f00302c4407070707070b0707070707070b930707170707070750707541c1c2c0c0c1c1c0c1c0c0c1c0c1c0c2c2c0c2c2c0c2c2c0c0c2c2c0c0d0745d55550755564d0b542d5507070f0070701c01c0702c9c0b0b05c3c05c3c00c0b1101c1c1c1e070707078ec1c1c1c1c1c1c1c1c1c1c1c1c1e07070780c1c1c0d54070702c2c1c1c1c1c2e4c5c6c5c6c1c1c1c1c5c1d550b0b0b070707070707075555551b0307030b030b0317170303174703031b1b03031b47030345d5559342d50b55551745d5546c0706c0b05c3c05c3c06c3c06c3c00c471101c1c1c1c6c1c2c1c5c5c1e171f0786c6c1e1b1f0780c1c7c0d54071f05c5c0c0c0c0c0c0d07071b0b071b1b07071b1b031b03030303031b03030303031b0355555555551b01c230f0230f01b02c0300c440707070723130788c4c1e1b070b070303030323035501c8c17171741c6c1c6c6d541c1d46c0c1c0c6c6c0c0c6c0c0c6c0c6c0d555555555546c0706c3c06c3c06c1b00c1101c1c1c1c6c4c1e1b130786c1c6c1c0c1c0d540700c0c0c2c1c1c6c2c2c6c6c2c2c6c6c5c6c1c1c1c1c5c5c5c6c5c6c5c5c5c5c5c6c5cac5c5c5c5d50303039303070303030703031b03030303030303030303030345d55555559342d50b5546c0706c3c06c3c06c0b05c3c05c3c00c031101c1c1c1c6c6c1e1b2b0786c1c2c1c5c5c1e173f0780c0c0c0d540701c1c0c0c0c0c0c0c1c1c1c1d541c1d40c0d03030303030303030303030303555555555550701c270f0270f02702c0300c440707070707070781c1c1e07070707030303035501c1c030303070b07070707071f070707070707170707070707070707070717170707070707070707540c1c0c0c1c0c0c0c0c0e4c0c0c0c0c0c0c0c0c0c0c0c0d0745d55550755564d0b542d55070f0070700701c3302c170f0170f00300c4407070781c1c1e070707070707070707070781c1c1e0303030307035501c1c0b0b1f0b0b0b171b170717071717542c2c2c1c2c1c2c6c0c0c0c0c0c0c0d5555540c6c0c0c0c0c0c0c0e4c0c2c0c0d40c0c0c0c0c5c0c0c0c0c2c0d1755564d0b542d55542d0b5551b0ac0b02c170f0170f00b0f00b0b00300c441b1f1f1b0b0b0b0b17171785c7c5e0b1f0b82c2c2e030303031f035507c7c0b0b0b0b03030303030b503031b1b1b071b071b1b5555030355545d55542d5555551b06c0b02c0300c270f0270f0441b1b1b1b0b0b0b0b0303030327131f89c4c7e5507c9c0b0b0b070b070b1b0b0b1b0b0b0b030303171b1707170717170b0b17540c0c0c0c0c2c0c0c2c0c0c0c0c0e4c0c0c0c0d40c0d17555555564d0b542d551b06c0b0f00b0b00b02c170f0170f00300c441b1b1b1b0b470b82c2c2e0b0b0b0b17171785c9c5e030303035507c9c1b1b23231b1b0b0b0b0b030303935542c2c2c2d01550303035555555542d9346c2308c2302c0b02c0b1106c7c7c6c7c4c7c7c4c7c2c2c2c2c2c2c2c2d541f1f08c6cac1c8c1d1c6c2cac2d1c0c0d5540c0c0c0c0c5c0c0c0d0303555555555550ac230f0230f02702c0300c442b2b3b47132388c4cee470b0b3b03030303550ed2c2707071f131307070707131b5a553f0307031f032703133f030313130303555555555501c1f09c130f0130f0030fc440781e131398ec4c4c4c0e1395548ee1305c5c1c5c1c5c5d5030303031717030317030345d5559345d517554005c3c05c3c00c110ecececec5c5c5e171780cec0d543b02c1c1d0b0b03030303030307070b0b0b0b0b07031b0303030303030303031b0355555555551b01c0b02c230f0230f0030300c8c44070707070b070b0723130788c4c1e0303030323035501c8c0b0b07070b42c2c2c1c1d5546c0c1c0c2c0c2c0c6c6c0c0c6c0c0d55517555555551b00701b02c1b0f01b0f003044070707071b070b071b130786c4c1e0307035501c24c0f93070b0b0715c0e4c5d0f01c1c1c1c1c1c1c0c0c0c0c0c0c1c1d5540c1c0d03030303030303030303030303035542d5564d5555541c0702c0b03c03c00c031101c1c1c1c1c1c1c1c1c1c1e07070780c0c0c0c1c0d54070700c0c0c1c1c2c2c1c1c1c1c1c1c1c1c1c1c2c1c1c1c1c1c1c1c1c1c2c1c1c1c1c1c2c1c1c1c1d5030703030703030303039303030303030303030303030355555542d42d559355070f0070700701c0b0f00b0b00b02c0300c4407070781c1c1e0707070707070781c1c1e070707070303030307035501c1c0b0b0b0b0b0b0b070b070b1b0303555031b0303030340c0c0c2c0c0c2c0d555555555546c2b02c0b02c3c02c2c00c00c1106cacac6c2c2c2c2c2c4c2e0b0b0b80c0c0c0c0d543b4b04c6c1c1c1c1c4c4c2c1c1c6d69546c0c1c0c4c4c0c0c4cfc0c0c2c0c2c0d55555555546c0704c3c04c3c0bc0b00c3f1101c4e0786c2c2c2d82c2c2e038ec4c4e5550a00b1717070b07170b1b0b1b546c0c0c2c0c0c2c5c0c0c2c0c2c0d55175175564d546c05c3c02c3c00b00c1106cec6c5c2e0b171782c2cec0cec0d543b107070b03030303030303031717070707071b1b0b0b07070b070b0b030355555555555551b01c0b02c0300c330f0330f044070707070b070b07030303033313078cc4c1e5501ccc0b2b0b07070b9307070b0b070707171707070707171b0b0b0b0b0b0b170b0b17170b0b0b0b0b0b0b0b0b0b0b0b0b0b17030303030303030303030303030303035555555555035035564c6c0702c2c02c3c02c0b05c3c05c3c00c031445c070707070b0b0782cfc1e0b070b07170785c5c1e030303035501c 25 33554431 10 1023
def hc_68_16 : Nat → Nat := unpackHintV5 0x911da846b67621da60505625c7c11a83bc4911cb44b8de59d26a992532aaa89847438b4e3565461842698e6123d43c883a6c3f213f1da67a8dd040c655a4a2e810b15368289d63143fd3b81bb90c0be67d84f93e81ef2360d189804548e011d43400023a 0x2c2c2c2c2c2c2c7c2c2c2c7c0c0c0c5c6c5c1c5c1c5c5c2c2c5d540c8c0c0c0c0c0c0c0e4c0c2c0c0c0c2c0c0c5c0d5555550b42d50b5548c2302c0b02c7c02c2c05c3c05c3c00c031107c7c7c7c2c2c2c2c2c7c2c2c2c2c2c7c5c5c5e171f1780c0c0c0c7c0d541f1f02c2c2c2c2c7c0c8c0c0c0c0c0c2c0c7c7c7c7c000003030393000cd2b42d0b40d0347d1f400000b02c0000001f87e0b82e030380c7e1f87e61f4002c2c2c2c2c2c2c7c2c2c2c7c0c0c0c3c6c3c1c3c1c3c3c2c2c3c000c8c0c0c0c0c0c0c0e4c0c2c0c0c0c2c0c0c3c0ccd2b42d0b42c7d42c2d43c3d43c5d40d0340000000b02c00b000007e1f82e0b82c7e82c2e83c3e83c7e80c0e031f987d000b0b07070b1f032303030303030b031f07071f030303030300c80c0c0e4e031f03033341d0b42d0340d1f47d2301c0b02c0300c1f07c42301e0780c0e0b0b0b0b0b80c0e031380e03984d280b07070b0b0b070707070b1f0303031f1b07070707131b0b0b1faa03230303030303030393030b0303030b03031f033341d0b42d0b1f50b0b5131751f1750340d2301c0b02c0b1f00b0b0130f01f0f00300c42301e0780e0ba0b82c2c2c2c2e82c2c2c0c0e0313984d280b07070b0b0b070707070b1b0303a0380c0c0c0c0c0c0c0c0c0c0c0c0e0303a41d0b42d0b1750b0b50340d01c0b02c0b0f00b0b00300c401e0782c2e0382c2c2c4c0e030303984d2807070707070707070707070703030303070303030303030393030b0303030b030741d0b42d0b1f50b0b50340d8888a0a08848aaaaaaa82e0baaa692881ea07a82e3f82e1380e5a85d42a82a0b2b0b0b2b070b074f03030303030303030303039303030303034ad42d1750b1750340d0ac02c0f00b0f00300c40acac2c2c2e0b80c0c0c0c0d402c6c2c0c1c1c2c2c2c2c0c0c0c0c0c2c0c0c2c0c0c0c0c6d0742c2d42c5d42d0b40d0346c0702c2c02c3c02c0b00c03109c070707070b0b0782c4c1e0b070b070303030341d4d01cbc0b0b07070b030b0b0b0707030303030303030303030303031b0303030303030303030303031b41d1b42d1b1751b1750340d1b01c1b02c1b0f01b0f00300c401c1c1c1c6c1c2c1c6c4c1e1b130780c0c0c0d0740702c2c2c2c2c6c2c2c2c2c0c0c0e4c2c2c2c2c0c0030303931b46d0b42d0b42d0b42d1b06c0b02c0b02c0b02c42706c6c6c6c2c2c2c2c2c2c2c2c2c2c2c2c2d1f5741f2f02c2c2c6c2c2c2c6c5c6c5c1c5c1c5c5d542c2c2c2c0c0c0c0c0d5540c0c0c0c0c2c0c0c0d5540c2c0c0c0c0c0e4d17555542d0b542d550b5540d1b06c0b2700b0b0170f0170f00b02c0300c441b1b1b1b0b470b0b0b0b0b3b17171785c9c5e0b0b0b0b030303035509c9c0b0b0b1b0b0b0b1b0f1b0f070f070f0f000b0b0b0b030303030300003030303030b030303000030b0303030303931b46d0b2750b0b50f0f50f1750b42d0340d03c00000b02c00b0002c00030006e1b82cbe82c2e83c3e83c8e82e0b80e03989d000b0b070707070b1b1b1b07070707131baa0b07070b0303030303a0303030303030303030b030303a03030303030b0303030303931b41d0b4750b0b5131752f1750b42d0340d1b01c0b2f00b0b0130f02f0f00b02c0300c42701c6e0786e0b82c2c2c2c2e82c2c2c0e0b0b0b80e030303984d28131b070713130b07070b030380c0c0c2c1c1c2c0e80c0c0c0c0c0c6d0744d1342d0b42d0b46c0704c1302c0b02c0b109c071381e1b0b0b0b0382c2c2e0382c2c2e6134a04c6c1c1c1c1c4c4c2c1c1c6c0c0e80c0c0e030303030303a03030380c0c0c0c0c6d0744c4d44c5d51d0b40d0346c0704c3c04c3c0bc0b00c0310071381e1b0b0b0b0382c2c2e0380c0c0e6134a01c1c1c1c1c1c1c1c1c1c1c1c0c0c0c0c0c0c0c0c2c0c0c2c0c0c0c0c0e4c1d0742ced42c2d42d0b40d03622828222212207aaaaa82e0baa0baa80e692881ea07a82e1382ea03a80ea03a5a85d42a82a0b1b070b071b0b1b0b1b030303030303030303030303030303931b4ad1750b17542d0340d1b0ac0f00b0f002c0300c406cacac6c2e0b82c2c0c0c0c0d406c6d071b1b55070751717171b0307031b031b031b03031b1b0303555555555551b01c1b06c1b0f01b0f003044070707071b071b071b130786c4c1e0307035501c07075550b0b0b0b0b0742c6c2c2c0c0c2c2c0c0c2c0c1c0c2c0c2c0d0b41d5555542d93555542c3c02c2c06c0702c0b00c0b1102c4c1e0b0b0781c1c1c1c2c1c2c1c0c1c2c0d54072f00c0d5546c2c8c6c2dfdec6c1c1c6c0c5c0c0c6c0d03030303030355555555555230f0230f01b01c06c0300c444b130788c4c1e07070707071b0703030303035501d2c0b07071b55070751b1b1f031b0303030340c0c0c0c6c0d55555555546c0706c0b07c3c07c3c00c031101c1c1c1c6c1c2c1c7c4c1e1f130780c0c0c0c7c0d54071f142c2c2c2c1c1c1c1c2c2c2c5c2c7c2c2c2c5c2c5c0e80c0c0c0c0c0e03964c1d0742d550f03c0f02c0781e0b070b070303542c1c1c6c2c2c5c6c2c2c5c5c2c6c1c1c1c1c6c6c2c5c2c2c5c5c7c2c5c2c2c5c5c5c5c0c0c0c0c6c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0e4c0c6c0c0c0c6c0d59341d507517555555551b01c170f0170f01b02c330f00b0f00300c440707070717170785cfc1e1b070b07330782c1e03030303035501c070707070707a0781c1c4c4c4c1c0c1c0c6c0c6c0c7c7c0c0c7c8c0c0d55555555541c0706c1b07c3c07c3c00c3f1101c1e607070781c1e0707a0707a0381c1c4e55285a5507070707130b1313130b1307030703133f0303131303033f031b0355555555550701c130f0130f006c030fc440707981c1c4c1c1e0780e0707139554a151b07071b1717171717171b03070317170303170303031b03564d07541d45d55546c0705c3c05c3c01b00c1101c1c1c1c5c5c1e170781c6c1c0c1c0d540701c1d5550707070707070707070307030b0b03030b0b03030b03030b0303555555555550701c0b0b00b0f00b02c0302c440707070707070781c1c1e07070707030707035501c1c07070707070707001d50707000c0cac0c3c0c7c0cac0c1d555550f03c0f03c000f0781e0781e070707070741c1d5541c1c1c1c0c1c0c7c0c0c6c0c0c7cac0c0cacac0c0d07555555555550701c1f06c1f0f00f0030ac44070707070707070707070781c1c1e030707035501c1c541c1c1c1c1c1c1c1c1c1c1cac0c0c1c1c0c0c1c0c1c0cac0cac0d075075564d55541c3c01c1c01c07000c2b1101c1c1e07070781c1c1c1c1c1c1c1c0c1c1c0d54070701c1d5555555070b42c2c2c2c0c0c2c2c0c0c2c0c1c0c2c0c2c0d0b41d55545d55542d55270f0270f01b01c0b02c0302c4427130789c4c1e070707070b070b0703070b035501c9c 25 33554431 10 1023
def hc_68_17 : Nat → Nat := unpackHintV5 0x8540aa9faa34c78acbf9c5f3986cb4991a301fa63b4a197bc2625c4455964919056046414d6156519039130d2ae4730a090732b23cc4a10e2421a33fc928b9e2c228c4b6890425a1b45198588292108cb2824a3b2041ca1800020e 0x2c6c0c0c0c0c0c0c0c1c1c2c0c0c0c0c1c1c0c0c0c6c0c0c0c0c0c2c0c0c0c0c0c2c0c6d0742c2d42c5d42d0b40d0346c0702c2c02c3c02c0b00c0310070707070b0b0782c4c1e0b070b07030303030341d5d01d2c17175550b1b0b5507070b9307070b0b55070750707070b0307030b0b03030b0b03030b0b03030b0b03030b030b0345d550b50b42d555542d551b01c170f0170f00b0b00b2700b02c0302c440707070717270785c5c1e0b0b07070b3307070b070b0703070b035501c9c0f0f0000b1b0b0007070b9307070b0b00070700707070b0307030b0b03030b0b03030b0b03030b0b03030b030b031b41d0f1750f0f50b0b50b2750b42d0342d03c000b00b02c000002c00000781e0f27a0f0fa0b0ba0b2fa0b82e0382e6274001c1e81c1c1c1c1c1c2ea81c1c1e4c1c1c1c2c1c1c1c1c1c1e81c1c1c1c0c1c0c2c2c0c0c2c2c0c0c2c2c0c0c2c2c0c0c2c0c2c0c1d074bc5d44c5d42c2d42ccd42d0b40d0b41c070bc3c04c3c02c2c02cbc02c0b00c0b109c070781e07070b07070b070ba81e070781c1c2e0381c1c2e6074a01c1e81e07070707070707070781c1e81c0c1c0c4cfc0c0c4c4c0c0c2c0c2c0c1d0744c5d44c4d4cd0b40d3f41c0704c3c04c3c0bc0b00c3f10070781e07070b070781c1c2e0381c1c4e6074a06d3d3c1c1e4c1c1c6d3c1c1c1c6c0c1c0c2c0c0c2c0c0c2c0c2c0c6d0742c5d45d50b40d46c0702c3c03c00b00c10070707070b0781e070b0703070341d01c070707070b074f070b070b030b030b9303930b930393070307030b42d0b9364c2e4d930741d0342d0b02c0b9324c2e4c930701c0302c42701c1c1c1c1e4c1e4c1e4c1e4c1c1c1c1c0c1c1c0d07074070701c1e4c1c1c1c1c1c1c1c1d3c1c1c0c1c0cac0c6c0c1c1c0c0c1cac0c0c1d0751b41c1d41c5d40d2b41c0701b01c1c01c3c00c2b10070707070707070707070781c1c1e0307070341c1d01c1c070307070b030b0b070707072b42d0741d42d2b02c0701c02c401c1c1c1c1c1c1c1c1c1c1c1d07074070701d07070b42c5c1c1c1c1c5c0c5c0c1c0c1c0c2c0c2c0c5c1701c0700b00c2b01c1c1c1c1c1c1c1c1c1c1c1c0c1c1c0c070701c07070b02c3c1c1c1c1c3c0c3c0c1c0c1c0c2c0c2c0c3d0f41d0750b40d2b41c1c1c1c1c1c1c1c1c1c1c1c0c1c1c0d070741c1c1c1c1c1c1c1c1c1c1c1c1c0c1c0c1c0c1c0c2c0c2c0c1d0741d0750b40d2b41c0701c0700b00c2b1007070707070307030b030b030741d3b42d034ad88888848aaaaaa692807070707070707070707074f9307072b0303070703070303070307030b030b030707175070741d41d0750b40d2b41c1c3c01c1c0700701c02c030ac401c1c1c1e0707070781c1c1c1c1c1c1c1c0c1c1c0d07074070701c1c2c1c1c1e4c1c1c1c2c1c1c1c1c0c1c0c2c2c0c0c2c2c0c0c2c0c2c0c1d0742c2d42c5d42d0b40d0b41c0702c2c02c3c02c0b00c0b109c0707070707070781c1c1e070707070307070341c1d01c1c0b0707030b0b0303030303030707030303030303031b030303030303030303031b031b41d4742d4717523175030340d1b01c4702c230f0230f0030300c401c1c1c1d1c1c2c1d1c4c1e23130780c0c0c0c0d07574074b01c1c1c1c1c1e81e07070707a0781c1c1c0c1c0c7c0c6c0c4cfc0c0c4c4c0c0c1d0747d1b44c5d44c4d40d3f41c0707c1b04c3c04c3c00c3f10070781e07071381e070713070381c1c4e6070713481e1306d3c1c1c1c1d3e4c6d3c1c1c1c6c0c1c0c0c6c0c6d3c0c0d3c0c0c6d0751b46c5d53c5d40d46c0701b06c3c13c3c00c1007070707071b071b4f0793c1e03070341d01c0303031b07071b1b1b2b1b2b1b4f030303930307030303070303030303031b41d1b1752b17546d0340d1b01c1b0f02b0f006c0300c401c1c1c1c6c1e2b2b0781c6c1c0c0c0c0d0740701c1c0c0c0c0c0c0c0c1c1c1c1c1c1c1c1c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c1d0742c2d42c5d42d42d40d0341c0702c2c02c3c02c02c00c03109c0707070707070781c1c1e0707070707070303030341c1d01c1c070707070703070703030303030307070703070303030303030303030303030303030303030741d1f50b51f1757b1750340d0701c1f00b01f0f07b0f00300c401c1c1c1c1c1c1c1c1c1c1c1c1e07070780c0c0c0c1c0d07074070700c0c0c1c1c1c1c1c1c1c1c1c1c0c1c0c0c1c0c0c0c0c0e4c0c0c0c0c1c5d41c1d41d07540d0341c3c01c1c01c07000c031007070781c1c1e070707070707070703030303070341c1d01c1c0b0b070707070b930b0b0b0b070707070b0703030303030b0b0b07070707070707030303030303030303030303031b0303030303030393030b0303030b03030303030303031b0303031b41d0b42d0b1750b0b51b1751b1750340d1b01c0b02c0b0f00b0b01b0f01b0f00300c401c1c1c1c2c1c2c1c2c7c1e0b0b0786c6c1e1b1f0780c0c0c0c7c0d071f4071f02c6c2c0c1c2c1c2c2c0c0c0c0c1c1c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c6d0742c2d42c5d42d0b40d0346c0702c2c02c3c02c0b00c0310070707070b0b0782c4c1e0b070b070303030341d01c0b0707030b0b0b0b07070b03030303030b0b03030303070303039303030303070300c030303031b41d0b42d0b1f42c2d2348d1b01c0b02c0b1f02c2c2308c42301c1c1c1c2c1c2c1c2c7c1c2c2c1c7c4c1c7c4c1d071f4071f02c1c1c0c2c2c2c2c1c1c1c1c2c2c0c0c0c2c2c2c2c2c6cac1c1c1c1c0c6c0c0c0c0c0c0c0e4c0c2c0c0c0c2c0c0c6c0c6d0742d0b42c7d42c2d46c5d46c5d40d0346c0702c0b02c7c02c2c06c3c06c3c00c03108c070707070b070b070b1f07070b0b07071b1b0786c7c1e030303031f0341c7d01c7c0303030b07071b0b0b1b1b0b1b0b931b0b0b070707070b931b0b0b07070b070b071b0303031b41d1b46d1b42d2342d1b01c1b06c1b02c2302c401c1c1c1c6c6c1c6cac1c6c1c2c1c8c1c2c1d07574074b02c2c2c2c2c7c0c8c0c0c0c0c0c2c0c7c7c7c7d55110303039355555550b42d55552308c0b02c0300c1f07c441f1f1f1f0b0b0b0b030303031f031f1f1f1f5507c7c 26 67108863 11 2047
def nh_68 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_68_17 (Nat.sub p 544)) (hc_68_16 (Nat.sub p 512)) (Nat.blt p 544)) (hc_68_15 (Nat.sub p 480)) (Nat.blt p 512)) (Bool.rec (hc_68_14 (Nat.sub p 448)) (hc_68_13 (Nat.sub p 416)) (Nat.blt p 448)) (Nat.blt p 480)) (Bool.rec (Bool.rec (hc_68_12 (Nat.sub p 384)) (hc_68_11 (Nat.sub p 352)) (Nat.blt p 384)) (Bool.rec (hc_68_10 (Nat.sub p 320)) (hc_68_9 (Nat.sub p 288)) (Nat.blt p 320)) (Nat.blt p 352)) (Nat.blt p 416)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_68_8 (Nat.sub p 256)) (hc_68_7 (Nat.sub p 224)) (Nat.blt p 256)) (hc_68_6 (Nat.sub p 192)) (Nat.blt p 224)) (Bool.rec (hc_68_5 (Nat.sub p 160)) (hc_68_4 (Nat.sub p 128)) (Nat.blt p 160)) (Nat.blt p 192)) (Bool.rec (Bool.rec (hc_68_3 (Nat.sub p 96)) (hc_68_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (hc_68_1 (Nat.sub p 32)) (hc_68_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 128)) (Nat.blt p 288)
def f_68 : Nat → Nat × Nat := unpackForestF 0x46cd56364af1b1578d82bc6c154018bf1a56d0062dc5cdb22e4d91716c8b83645c180018af1546e8a9a2c54114018a600b5f89a36c4d184016af0c56386237444d12188c70c36e87e3643093e1d8d90c14f86e3643013e1808b0c043005a7c1d5ba0eac50734e8392fc1c57e0e0bf0834e8382ec1c14c0168f02c598162ac0ad56088d104045815a7c0d146050aa00a5f80636c0451e018c200a577fe323d95bdecad6fcc7c7e5be3f25f1f90f8f65677b2b1becd55ec8dcf636f7ce3e3d8d9dec6bef846c7b1abbdcd39ec68af604500527bd4d15e2ac4f314f79c2e3cc51de5ae0f1367789aebc41740148ef046874eb7bbb161dd6a8e9d6374e313a7169d7adcebd6275c9bba7149d4adeea45e74c268028ddbf8b2dfc556fdaab9b1a1cd08adfb4f72232390d95c868ae40456fd27b875a5c38d0e1c5270c26b7e8ddc08a2e024f6fc2a80257db78dade2476de30b751f1b749edc5706dd2380255db58c8c9d6f64eb5b5f1f1af6f8d7a7c6bc3e32759d93ac6d635564e37326dbda98f8c9b6764dafb4d1b1936aed234e64da2b3f1919f6cacfb4567c32b269bd9d8f8c9a6764d2fb351b1934aecb57e65a2c32c1359346eca26f64c2280253d9168ac056263527b1c1718d48ec6570601b3b00d7589ae0c026761e3630093d82ce4c146060f393041358046ec005d004a3afd1a163adebdc585edaa2c758d638c4b1c5a5d6b72eb5897546eb1c525c6b4ae31a1718a4b1a6f5babf2dd161634beb5e725ae302c695d64adeb245e59137ac897d65ce4b225758c268024dd5f8caafb6857c32a7b5bd3dad6ad47c569b82b41f13daceab455559ac2ac1553dac69ec6f54ab8aa4dc13d8cea6e73536bf29b1f94d0aa9ec5f52739292d81490da9ec5751d2327ad893d6b4a22464f5a928158d408bca02524f5a527cd793d07a009274c1a7a74d153049e982374d9a2a6c8dd3029e9a25f4c09ba6317d31694981270042fa5a1792d0ac0085b46e36a5291d2928e8dc6149e3e23693d2529e9257046d23a451f11b29e9024f47eb823651d1cae28e37046c9380215d118be8885e4442b22b179156bc88846449a7a24d0d110880085337eb79bf58cdf8de8635537e371bedbcdf6be8446c37daba0cd38df68a81464409b2a04d14df4de6fa5f37d2b9be91cfcafc7e45837d1b9ef190f76ca7bb453dd1b9be5bcdf2be6f95737ca39e15f8f08b07827f37c9b9cd9cce6afc7347f39a379cd154e98de7335839ebf1ccd28df24e7201737c371c0118e006c7003437c3100213cdb0ac6d84636c2200212cc7adc6c34531eb118ed74c74be63a4f34b391a5180c746e6395f31ca799b9c8cd8c063937327391931b4c96c06392731c2700211cc08be60457300ab180178c16bc6004600421978578bc0bc5e0560041d9731a0b96c82d56f2da2c16cd505aac62d46e2cdb70b518c5a8c42d45e2bdae0b516c5a8b42d45616a2994d5b8a98a8535622991b94c4dc5a8a451b6328da88b4d789cad24e4682722f1391489c6c84e35e169379315f8988e64c4581692f9299c8948c04a36c1692b8b493c8aad24546822a2f1151488a6c84535e22e3c11497c5a2de41d7e20e39907160858f041a7f20d278b457c7ece43f4601f9b60fc93c5a2ae3da6f1ed338b453c79af031e7f1dab40ecda063ce631d7e1cda40c75cc63ae431d6e1ba360dcd2063ad631d631a73f0d4da069ce431d6218e370c6dc865ad231b6218da80b449c5d4bc2e96f174378bcdb85d02e2d05e16daf0b41480106e2645f15c3609915c546bc2a04e130a30a2d145106c2605e1302b09b1784d6bc260460041585d5bc2eac61746f11ebf05d17c45ce41745710ab488517c2e2de1fd7e0fe3f85c57c3dce4171570df3f8755a037ce61bd720deb105c51c2fade17b5e0cdaf05e1bc2f0be186720bc2b85c1180104e1045f0ac3604115c286bc1404e080a304ad142506c1005e0802b043178216bc100460040d8055bc02ac60146f06ebf00517c19ce40145705ab482d17c026de09d7e04e3f804d7c11ce40135702f3f81d5a00bce605d7202eb1004d1c03ade01b5e01daf0069bc034be0267200d2b8041180102e0003f 10 11
def ch_68 : Nat → Bool := dagCheckNodeV5 fullMask g_68 ep_68 6 63 bds_68 571 (dagTraceF fullMask rootStock 11 f_68) cur_68 nh_68
set_option maxHeartbeats 0 in
theorem rc_68 : dagCheckRootsV5 fullMask g_68 ep_68 6 63 571 bds_68 (dagTraceF fullMask rootStock 11 f_68) (cur_68 0) (nh_68 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_0 : treeBlockF 0 32 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_1 : treeBlockF 32 64 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_2 : treeBlockF 64 96 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_3 : treeBlockF 96 128 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_4 : treeBlockF 128 160 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_5 : treeBlockF 160 192 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_6 : treeBlockF 192 224 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_7 : treeBlockF 224 256 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_8 : treeBlockF 256 288 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_9 : treeBlockF 288 320 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_10 : treeBlockF 320 352 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_11 : treeBlockF 352 384 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_12 : treeBlockF 384 416 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_13 : treeBlockF 416 448 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_14 : treeBlockF 448 480 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_15 : treeBlockF 480 512 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_16 : treeBlockF 512 544 ch_68 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_68_17 : treeBlockF 544 571 ch_68 = true := by decide +kernel
theorem nj_68_1 : ∀ i, 0 ≤ i → i < 64 → ch_68 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_68_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_68_1 h1 h2)
theorem nj_68_2 : ∀ i, 0 ≤ i → i < 96 → ch_68 i = true := block_join nj_68_1 (fun _ h1 h2 => treeBlockF_at nb_68_2 h1 h2)
theorem nj_68_3 : ∀ i, 0 ≤ i → i < 128 → ch_68 i = true := block_join nj_68_2 (fun _ h1 h2 => treeBlockF_at nb_68_3 h1 h2)
theorem nj_68_4 : ∀ i, 0 ≤ i → i < 160 → ch_68 i = true := block_join nj_68_3 (fun _ h1 h2 => treeBlockF_at nb_68_4 h1 h2)
theorem nj_68_5 : ∀ i, 0 ≤ i → i < 192 → ch_68 i = true := block_join nj_68_4 (fun _ h1 h2 => treeBlockF_at nb_68_5 h1 h2)
theorem nj_68_6 : ∀ i, 0 ≤ i → i < 224 → ch_68 i = true := block_join nj_68_5 (fun _ h1 h2 => treeBlockF_at nb_68_6 h1 h2)
theorem nj_68_7 : ∀ i, 0 ≤ i → i < 256 → ch_68 i = true := block_join nj_68_6 (fun _ h1 h2 => treeBlockF_at nb_68_7 h1 h2)
theorem nj_68_8 : ∀ i, 0 ≤ i → i < 288 → ch_68 i = true := block_join nj_68_7 (fun _ h1 h2 => treeBlockF_at nb_68_8 h1 h2)
theorem nj_68_9 : ∀ i, 0 ≤ i → i < 320 → ch_68 i = true := block_join nj_68_8 (fun _ h1 h2 => treeBlockF_at nb_68_9 h1 h2)
theorem nj_68_10 : ∀ i, 0 ≤ i → i < 352 → ch_68 i = true := block_join nj_68_9 (fun _ h1 h2 => treeBlockF_at nb_68_10 h1 h2)
theorem nj_68_11 : ∀ i, 0 ≤ i → i < 384 → ch_68 i = true := block_join nj_68_10 (fun _ h1 h2 => treeBlockF_at nb_68_11 h1 h2)
theorem nj_68_12 : ∀ i, 0 ≤ i → i < 416 → ch_68 i = true := block_join nj_68_11 (fun _ h1 h2 => treeBlockF_at nb_68_12 h1 h2)
theorem nj_68_13 : ∀ i, 0 ≤ i → i < 448 → ch_68 i = true := block_join nj_68_12 (fun _ h1 h2 => treeBlockF_at nb_68_13 h1 h2)
theorem nj_68_14 : ∀ i, 0 ≤ i → i < 480 → ch_68 i = true := block_join nj_68_13 (fun _ h1 h2 => treeBlockF_at nb_68_14 h1 h2)
theorem nj_68_15 : ∀ i, 0 ≤ i → i < 512 → ch_68 i = true := block_join nj_68_14 (fun _ h1 h2 => treeBlockF_at nb_68_15 h1 h2)
theorem nj_68_16 : ∀ i, 0 ≤ i → i < 544 → ch_68 i = true := block_join nj_68_15 (fun _ h1 h2 => treeBlockF_at nb_68_16 h1 h2)
theorem nj_68_17 : ∀ i, 0 ≤ i → i < 571 → ch_68 i = true := block_join nj_68_16 (fun _ h1 h2 => treeBlockF_at nb_68_17 h1 h2)
theorem nc_68 : ∀ i, 0 ≤ i → i < 571 → ch_68 i = true := nj_68_17
theorem lb_68 : LowerBin fullMask rootStock g_68 12 :=
  lowerDagV5 (kn_cons lb_67 (kn_cons lb_61 (kn_cons lb_26 (kn_cons lb_60 (kn_cons lb_43 (kn_cons lb_47 (kn_cons lb_64 (kn_cons lb_66 (kn_cons lb_62 (kn_cons lb_53 (kn_cons lb_30 (kn_cons lb_40 (kn_cons lb_8 (kn_cons lb_58 (kn_cons lb_12 (kn_cons lb_7 (kn_cons lb_29 (kn_cons lb_27 (kn_cons lb_46 (kn_cons lb_32 (kn_cons lb_36 (kn_cons lb_0 (kn_cons lb_65 (kn_cons lb_57 (kn_cons lb_4 (kn_cons lb_10 (kn_cons lb_3 (kn_cons lb_1 (kn_cons lb_13 (kn_cons lb_39 (kn_cons lb_56 (kn_cons lb_23 (kn_cons lb_63 (kn_cons lb_25 (kn_cons lb_48 (kn_cons lb_15 (kn_cons lb_2 (kn_cons lb_11 (kn_cons lb_6 (kn_nil)))))))))))))))))))))))))))))))))))))))) rc_68 nc_68 (by decide +kernel)

def wg : List Gate := [⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [5, 9]⟩, ⟨GateOp.and, [6, 10]⟩, ⟨GateOp.or, [5, 12]⟩, ⟨GateOp.and, [2, 13]⟩, ⟨GateOp.or, [1, 14]⟩, ⟨GateOp.and, [8, 15]⟩, ⟨GateOp.and, [11, 12]⟩, ⟨GateOp.or, [16, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 3970476168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276676776 * 2 ^ 32 + 3970476168)) (13 - 1) := by
  rw [show canon fullMask (4276676776 * 2 ^ 32 + 3970476168) = g_68 by decide]
  exact lb_68

end PEqualNP.Outside.L_meta_47825

theorem PEqualNP.Outside.L_meta_47825 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676776 * 2 ^ 32 + 3970476168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 3970476168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_47825.table2_from_lowerBin (4276676776 * 2 ^ 32 + 3970476168) 13 PEqualNP.Outside.L_meta_47825.root_lb PEqualNP.Outside.L_meta_47825.wg 18 rfl PEqualNP.Outside.L_meta_47825.wfits PEqualNP.Outside.L_meta_47825.weval
