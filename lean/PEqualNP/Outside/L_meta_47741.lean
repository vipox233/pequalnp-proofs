import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_47741

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

def m_0 : Nat := 0xcc00cc00
def s_0 : List Nat := [0x44004400, 0xc000c00, 0xcc00]
def g_0 : Nat := 0x4004c00
def ep_0 : Nat := 0x48000000000000000000000000000400080000000000000000000000000004004000
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

def m_1 : Nat := 0x4444444400000000
def s_1 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_1 : Nat := 0x4044400000000
def ep_1 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
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

def m_2 : Nat := 0xc0c0c0c00000000
def s_2 : List Nat := [0x404040400000000, 0xc000c00000000, 0xc0c00000000]
def g_2 : Nat := 0x4040c00000000
def ep_2 : Nat := 0x408000000000004000800000000000000000000000000000000000000000004040000000000
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

def m_3 : Nat := 0xcc00cc00000000
def s_3 : List Nat := [0x44004400000000, 0xc000c00000000, 0xcc00000000]
def g_3 : Nat := 0x4004c00000000
def ep_3 : Nat := 0x48000000000000000000000000000400080000000000000000000000000004004000000000
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

def m_4 : Nat := 0xcccc0000
def s_4 : List Nat := [0x44440000, 0xc0c0000, 0xcc0000]
def g_4 : Nat := 0x44c0000
def ep_4 : Nat := 0x480000000000000408000000000000000000000000000004400000
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

def m_5 : Nat := 0xc000c000c000c00
def s_5 : List Nat := [0x400040004000400, 0xc0000000c00, 0xc000c00]
def g_5 : Nat := 0x40004000c00
def ep_5 : Nat := 0x400080000000400000008000000000000000000000000000000000000000000000000000000040004000000
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

def m_6 : Nat := 0x222200002222
def s_6 : List Nat := [0x20200000202, 0x2200000022, 0x2222]
def g_6 : Nat := 0x200000222
def ep_6 : Nat := 0x22000000000000000000000000200000020000000020000020000000000000000000000000000000000
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

def m_7 : Nat := 0x202020202020202
def s_7 : List Nat := [0x2000200020002, 0x20200000202, 0x2020202]
def g_7 : Nat := 0x200020202
def ep_7 : Nat := 0x2020000000002000002000000000200020000000000000000000000000000000000000000000000000000
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

def m_8 : Nat := 0x808080808080808
def s_8 : List Nat := [0x8000800080008, 0x80800000808, 0x8080808]
def g_8 : Nat := 0x800080808
def ep_8 : Nat := 0x8080000000008000008000000000800080000000000000000000000000000000000000000000000000000
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

def m_9 : Nat := 0x4040404040404040
def s_9 : List Nat := [0x40004000400040, 0x404000004040, 0x40404040]
def g_9 : Nat := 0x4000404040
def ep_9 : Nat := 0x40400000000040000040000000004000400000000000000000000000000000000000000000000000000000
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

def m_10 : Nat := 0x22002200220022
def s_10 : List Nat := [0x2000200020002, 0x2200000022, 0x220022]
def g_10 : Nat := 0x200020022
def ep_10 : Nat := 0x2002000000002000000200000000000000000000000020002000000000000000000000000000000000000
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

def m_11 : Nat := 0x4400440044004400
def s_11 : List Nat := [0x400040004000400, 0x440000004400, 0x44004400]
def g_11 : Nat := 0x40004004400
def ep_11 : Nat := 0x400400000000400000040000000000000000000000004000400000000000000000000000000000000000000
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

def m_12 : Nat := 0xcccc00000000
def s_12 : List Nat := [0x444400000000, 0xc0c00000000, 0xcc00000000]
def g_12 : Nat := 0x44c00000000
def ep_12 : Nat := 0x4800000000000004080000000000000000000000000000044000000000
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

def m_13 : Nat := 0x22222222
def s_13 : List Nat := [0x2020202, 0x220022, 0x2222]
def g_13 : Nat := 0x20222
def ep_13 : Nat := 0x2200000000000020020000000000002020000000000000000000000000000000000
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

def m_14 : Nat := 0xcc000000cc00
def s_14 : List Nat := [0x440000004400, 0xc0000000c00, 0xcc00]
def g_14 : Nat := 0x40000004c00
def ep_14 : Nat := 0x480000000000000000000000000000000000000004000000080000000000000000000000040000004000
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

def m_15 : Nat := 0x4444000044440000
def s_15 : List Nat := [0x404000004040000, 0x44000000440000, 0x44440000]
def g_15 : Nat := 0x4000004440000
def ep_15 : Nat := 0x440000000000000000000000004000000400000000400000400000000000000000000000000000000000000
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

def m_16 : Nat := 0xcc000000cc0000
def s_16 : List Nat := [0x44000000440000, 0xc0000000c0000, 0xcc0000]
def g_16 : Nat := 0x40000004c0000
def ep_16 : Nat := 0x48000000000000000000000000000000000000000400000008000000000000000000000004000000400000
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

def m_17 : Nat := 0xc0c00000c0c0000
def s_17 : List Nat := [0x404000004040000, 0xc0000000c0000, 0xc0c0000]
def g_17 : Nat := 0x40000040c0000
def ep_17 : Nat := 0x408000000000000000000000004000000080000000000000000000000000000000000000004000004000000
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

def m_18 : Nat := 0xff0000ff
def s_18 : List Nat := [0x55000055, 0x33000033, 0xf00000f, 0xff]
def g_18 : Nat := 0x1500007f
def ep_18 : Nat := 0x400000800000000100000200000000015000040
def bds_18 : List (Nat × List Nat × Nat × Nat) := []
def cur_18 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb24b24d2d92a72652532400f 7 127 3 7 9 511 12 4095
def nh_18 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_18 : Nat → Nat × Nat := unpackForestF 0x32db2432a32632532400f 3 9
def ch_18 : Nat → Bool := dagCheckNodeV5 m_18 g_18 ep_18 1 1 bds_18 7 (dagTraceF m_18 s_18 4 f_18) cur_18 nh_18
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsV5 m_18 g_18 ep_18 1 1 7 bds_18 (dagTraceF m_18 s_18 4 f_18) (cur_18 0) (nh_18 0) s_18 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_18 : treeBlockF 0 7 ch_18 = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 7 → ch_18 i = true := fun _ h1 h2 => treeBlockF_at nb_18 h1 h2
theorem lb_18 : LowerBin m_18 s_18 g_18 5 :=
  lowerDagV5 (kn_nil) rc_18 nc_18 (by decide +kernel)

def m_19 : Nat := 0xff0000000000ff
def s_19 : List Nat := [0x55000000000055, 0x33000000000033, 0xf00000000000f, 0xff]
def g_19 : Nat := 0x1500000000007f
def ep_19 : Nat := 0x400000000000800100000000000200015000000000040
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

def m_20 : Nat := 0xff00000000ff
def s_20 : List Nat := [0x550000000055, 0x330000000033, 0xf000000000f, 0xff]
def g_20 : Nat := 0x15000000007f
def ep_20 : Nat := 0x4000000000800001000000000200000150000000040
def bds_20 : List (Nat × List Nat × Nat × Nat) := []
def cur_20 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb24b24d2d92a72652532400f 7 127 3 7 9 511 12 4095
def nh_20 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_20 : Nat → Nat × Nat := unpackForestF 0x32db2432a32632532400f 3 9
def ch_20 : Nat → Bool := dagCheckNodeV5 m_20 g_20 ep_20 1 1 bds_20 7 (dagTraceF m_20 s_20 4 f_20) cur_20 nh_20
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV5 m_20 g_20 ep_20 1 1 7 bds_20 (dagTraceF m_20 s_20 4 f_20) (cur_20 0) (nh_20 0) s_20 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_20 : treeBlockF 0 7 ch_20 = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 7 → ch_20 i = true := fun _ h1 h2 => treeBlockF_at nb_20 h1 h2
theorem lb_20 : LowerBin m_20 s_20 g_20 5 :=
  lowerDagV5 (kn_nil) rc_20 nc_20 (by decide +kernel)

def m_21 : Nat := 0xffff00000000
def s_21 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_21 : Nat := 0x155f00000000
def ep_21 : Nat := 0x4a000000000000040a0000000000001000000000000000155000000000
def bds_21 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cur_21 : Nat → List (Nat × Nat) := fun _ => []
def nh_21 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_21 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV5 m_21 g_21 ep_21 1 1 0 bds_21 (dagTraceF m_21 s_21 4 f_21) (cur_21 0) (nh_21 0) s_21 4 = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_21 g_21 ep_21 1 1 bds_21 0 (dagTraceF m_21 s_21 4 f_21) cur_21 nh_21 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_21 : LowerBin m_21 s_21 g_21 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_21 nc_21 (by decide +kernel)

def m_22 : Nat := 0xaa00aa00aa00aa
def s_22 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_22 : Nat := 0xa000a002a
def ep_22 : Nat := 0xa00200000000a0000002000000000000000000000000a000a000800000000000000200000000000000000
def bds_22 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_22 : Nat → List (Nat × Nat) := fun _ => []
def nh_22 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_22 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV5 m_22 g_22 ep_22 1 1 0 bds_22 (dagTraceF m_22 s_22 4 f_22) (cur_22 0) (nh_22 0) s_22 4 = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_22 g_22 ep_22 1 1 bds_22 0 (dagTraceF m_22 s_22 4 f_22) cur_22 nh_22 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_22 : LowerBin m_22 s_22 g_22 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_22 nc_22 (by decide +kernel)

def m_23 : Nat := 0xff00ff00000000
def s_23 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_23 : Nat := 0x15005f00000000
def ep_23 : Nat := 0x4a0000000000000000000000000004000a0000000000100000000000000015005000000000
def bds_23 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
def cur_23 : Nat → List (Nat × Nat) := fun _ => []
def nh_23 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_23 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV5 m_23 g_23 ep_23 1 1 0 bds_23 (dagTraceF m_23 s_23 4 f_23) (cur_23 0) (nh_23 0) s_23 4 = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_23 g_23 ep_23 1 1 bds_23 0 (dagTraceF m_23 s_23 4 f_23) cur_23 nh_23 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_23 : LowerBin m_23 s_23 g_23 5 :=
  lowerDagV5 (kn_cons lb_3 (kn_nil)) rc_23 nc_23 (by decide +kernel)

def m_24 : Nat := 0xcccccccc00000000
def s_24 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_24 : Nat := 0x4044c00000000
def ep_24 : Nat := 0x448000000000004004800000000000404080000000000000000000000000004044000000000
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3), (m_12, s_12, 4, g_12), (m_1, s_1, 4, g_1), (m_2, s_2, 4, g_2)]
def cc_24_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_24_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_24 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_24_1 (Nat.sub p 32)) (cc_24_0 p) (Nat.blt p 32)
def hc_24_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_24_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_24 : Nat → Nat := fun p => Bool.rec (hc_24_1 (Nat.sub p 32)) (hc_24_0 p) (Nat.blt p 32)
def f_24 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_24 : Nat → Bool := dagCheckNodeV5 m_24 g_24 ep_24 1 1 bds_24 43 (dagTraceF m_24 s_24 6 f_24) cur_24 nh_24
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV5 m_24 g_24 ep_24 1 1 43 bds_24 (dagTraceF m_24 s_24 6 f_24) (cur_24 0) (nh_24 0) s_24 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_24_0 : treeBlockF 0 32 ch_24 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_24_1 : treeBlockF 32 43 ch_24 = true := by decide +kernel
theorem nj_24_1 : ∀ i, 0 ≤ i → i < 43 → ch_24 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_24_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_24_1 h1 h2)
theorem nc_24 : ∀ i, 0 ≤ i → i < 43 → ch_24 i = true := nj_24_1
theorem lb_24 : LowerBin m_24 s_24 g_24 7 :=
  lowerDagV5 (kn_cons lb_3 (kn_cons lb_12 (kn_cons lb_1 (kn_cons lb_2 (kn_nil))))) rc_24 nc_24 (by decide +kernel)

def m_25 : Nat := 0x33003300330033
def s_25 : List Nat := [0x11001100110011, 0x3000300030003, 0x3300000033, 0x330033]
def g_25 : Nat := 0x11001300130033
def ep_25 : Nat := 0x2002000000002000000200000000000000000000000020002000000000000000000000011001000100000
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_25 : Nat → List (Nat × Nat) := fun _ => []
def nh_25 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_25 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV5 m_25 g_25 ep_25 1 1 0 bds_25 (dagTraceF m_25 s_25 4 f_25) (cur_25 0) (nh_25 0) s_25 4 = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_25 g_25 ep_25 1 1 bds_25 0 (dagTraceF m_25 s_25 4 f_25) cur_25 nh_25 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_25 : LowerBin m_25 s_25 g_25 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_25 nc_25 (by decide +kernel)

def m_26 : Nat := 0xcc00cc00cc00cc
def s_26 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_26 : Nat := 0x4004c004c004c
def ep_26 : Nat := 0x48000000000048000000000000000000000000000400080008000800000000000000000004004000400040
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
def cur_26 : Nat → List (Nat × Nat) := fun _ => []
def nh_26 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_26 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV5 m_26 g_26 ep_26 1 1 0 bds_26 (dagTraceF m_26 s_26 4 f_26) (cur_26 0) (nh_26 0) s_26 4 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_26 g_26 ep_26 1 1 bds_26 0 (dagTraceF m_26 s_26 4 f_26) cur_26 nh_26 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_26 : LowerBin m_26 s_26 g_26 5 :=
  lowerDagV5 (kn_cons lb_3 (kn_nil)) rc_26 nc_26 (by decide +kernel)

def m_27 : Nat := 0xcccc0000cccc0000
def s_27 : List Nat := [0x4444000044440000, 0xc0c00000c0c0000, 0xcc000000cc0000, 0xcccc0000]
def g_27 : Nat := 0x40000044c0000
def ep_27 : Nat := 0x448000000000000000000000004000000480000000400000408000000000000000000000004000004400000
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16), (m_4, s_4, 4, g_4), (m_15, s_15, 4, g_15), (m_17, s_17, 4, g_17)]
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
  lowerDagV5 (kn_cons lb_16 (kn_cons lb_4 (kn_cons lb_15 (kn_cons lb_17 (kn_nil))))) rc_27 nc_27 (by decide +kernel)

def m_28 : Nat := 0x5555000055550000
def s_28 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_28 : Nat := 0x1115000015550000
def ep_28 : Nat := 0x440000000000000000000000004000000400000000400000400000011100000100000000000000000000000
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
def cur_28 : Nat → List (Nat × Nat) := fun _ => []
def nh_28 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_28 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV5 m_28 g_28 ep_28 1 1 0 bds_28 (dagTraceF m_28 s_28 4 f_28) (cur_28 0) (nh_28 0) s_28 4 = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_28 g_28 ep_28 1 1 bds_28 0 (dagTraceF m_28 s_28 4 f_28) cur_28 nh_28 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_28 : LowerBin m_28 s_28 g_28 5 :=
  lowerDagV5 (kn_cons lb_15 (kn_nil)) rc_28 nc_28 (by decide +kernel)

def m_29 : Nat := 0xff000000ff00
def s_29 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_29 : Nat := 0x150000005f00
def ep_29 : Nat := 0x4a00000000000000000000000000000000000000040000000a0000001000000000000000150000005000
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
def cur_29 : Nat → List (Nat × Nat) := fun _ => []
def nh_29 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_29 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV5 m_29 g_29 ep_29 1 1 0 bds_29 (dagTraceF m_29 s_29 4 f_29) (cur_29 0) (nh_29 0) s_29 4 = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_29 g_29 ep_29 1 1 bds_29 0 (dagTraceF m_29 s_29 4 f_29) cur_29 nh_29 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_29 : LowerBin m_29 s_29 g_29 5 :=
  lowerDagV5 (kn_cons lb_14 (kn_nil)) rc_29 nc_29 (by decide +kernel)

def m_30 : Nat := 0xf0f00000f0f0
def s_30 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_30 : Nat := 0x105000005070
def ep_30 : Nat := 0x402000000000000000000000004000000020000000000000000000001000000000200000105000005040
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

def m_31 : Nat := 0xf0f00000f0f0000
def s_31 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_31 : Nat := 0x1050000050f0000
def ep_31 : Nat := 0x40a0000000000000000000000040000000a0000000000000000000001000000000000000105000005000000
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 4, g_17)]
def cur_31 : Nat → List (Nat × Nat) := fun _ => []
def nh_31 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_31 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV5 m_31 g_31 ep_31 1 1 0 bds_31 (dagTraceF m_31 s_31 4 f_31) (cur_31 0) (nh_31 0) s_31 4 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_31 g_31 ep_31 1 1 bds_31 0 (dagTraceF m_31 s_31 4 f_31) cur_31 nh_31 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagV5 (kn_cons lb_17 (kn_nil)) rc_31 nc_31 (by decide +kernel)

def m_32 : Nat := 0xcccc0000cccc
def s_32 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_32 : Nat := 0x44c00004c4c
def ep_32 : Nat := 0x480000000000000000000000004800000000000004080000080800000000000000000000044000004040
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cur_32 : Nat → List (Nat × Nat) := fun _ => []
def nh_32 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_32 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV5 m_32 g_32 ep_32 1 1 0 bds_32 (dagTraceF m_32 s_32 4 f_32) (cur_32 0) (nh_32 0) s_32 4 = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_32 g_32 ep_32 1 1 bds_32 0 (dagTraceF m_32 s_32 4 f_32) cur_32 nh_32 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_32 : LowerBin m_32 s_32 g_32 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_32 nc_32 (by decide +kernel)

def m_33 : Nat := 0x333300003333
def s_33 : List Nat := [0x111100001111, 0x30300000303, 0x3300000033, 0x3333]
def g_33 : Nat := 0x111300001333
def ep_33 : Nat := 0x22000000000000000000000000200000020000000020000020000000000000000000000111000001000
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cur_33 : Nat → List (Nat × Nat) := fun _ => []
def nh_33 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV5 m_33 g_33 ep_33 1 1 0 bds_33 (dagTraceF m_33 s_33 4 f_33) (cur_33 0) (nh_33 0) s_33 4 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_33 g_33 ep_33 1 1 bds_33 0 (dagTraceF m_33 s_33 4 f_33) cur_33 nh_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_33 nc_33 (by decide +kernel)

def m_34 : Nat := 0xaaaa0000aaaa
def s_34 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_34 : Nat := 0xa00000a2a
def ep_34 : Nat := 0xa2000000000000000000000000a000000200000000a00000a0800000000000000200000000000000000
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cur_34 : Nat → List (Nat × Nat) := fun _ => []
def nh_34 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV5 m_34 g_34 ep_34 1 1 0 bds_34 (dagTraceF m_34 s_34 4 f_34) (cur_34 0) (nh_34 0) s_34 4 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_34 g_34 ep_34 1 1 bds_34 0 (dagTraceF m_34 s_34 4 f_34) cur_34 nh_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_34 nc_34 (by decide +kernel)

def m_35 : Nat := 0xcc00cc00cc00cc00
def s_35 : List Nat := [0x4400440044004400, 0xc000c000c000c00, 0xcc000000cc00, 0xcc00cc00]
def g_35 : Nat := 0x40004004c00
def ep_35 : Nat := 0x400480000000400000048000000000000000000000004000400080000000000000000000000040004004000
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14), (m_0, s_0, 4, g_0), (m_11, s_11, 4, g_11), (m_5, s_5, 4, g_5)]
def cc_35_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_35_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_35 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_35_1 (Nat.sub p 32)) (cc_35_0 p) (Nat.blt p 32)
def hc_35_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_35_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_35 : Nat → Nat := fun p => Bool.rec (hc_35_1 (Nat.sub p 32)) (hc_35_0 p) (Nat.blt p 32)
def f_35 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_35 : Nat → Bool := dagCheckNodeV5 m_35 g_35 ep_35 1 1 bds_35 43 (dagTraceF m_35 s_35 6 f_35) cur_35 nh_35
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV5 m_35 g_35 ep_35 1 1 43 bds_35 (dagTraceF m_35 s_35 6 f_35) (cur_35 0) (nh_35 0) s_35 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_0 : treeBlockF 0 32 ch_35 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35_1 : treeBlockF 32 43 ch_35 = true := by decide +kernel
theorem nj_35_1 : ∀ i, 0 ≤ i → i < 43 → ch_35 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_35_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_35_1 h1 h2)
theorem nc_35 : ∀ i, 0 ≤ i → i < 43 → ch_35 i = true := nj_35_1
theorem lb_35 : LowerBin m_35 s_35 g_35 7 :=
  lowerDagV5 (kn_cons lb_14 (kn_cons lb_0 (kn_cons lb_11 (kn_cons lb_5 (kn_nil))))) rc_35 nc_35 (by decide +kernel)

def m_36 : Nat := 0xf000f000f000f00
def s_36 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_36 : Nat := 0x100050005000f00
def ep_36 : Nat := 0x4000a000000040000000a000000000000000000000000000000000001000000000000000100050005000000
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
def cur_36 : Nat → List (Nat × Nat) := fun _ => []
def nh_36 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV5 m_36 g_36 ep_36 1 1 0 bds_36 (dagTraceF m_36 s_36 4 f_36) (cur_36 0) (nh_36 0) s_36 4 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_36 g_36 ep_36 1 1 bds_36 0 (dagTraceF m_36 s_36 4 f_36) cur_36 nh_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagV5 (kn_cons lb_5 (kn_nil)) rc_36 nc_36 (by decide +kernel)

def m_37 : Nat := 0xcccccccc
def s_37 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_37 : Nat := 0x44c4c4c
def ep_37 : Nat := 0x48000000000000480000000000000408080800000000000000000000000004404040
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_37 : Nat → List (Nat × Nat) := fun _ => []
def nh_37 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV5 m_37 g_37 ep_37 1 1 0 bds_37 (dagTraceF m_37 s_37 4 f_37) (cur_37 0) (nh_37 0) s_37 4 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_37 g_37 ep_37 1 1 bds_37 0 (dagTraceF m_37 s_37 4 f_37) cur_37 nh_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_37 nc_37 (by decide +kernel)

def m_38 : Nat := 0x5555555500000000
def s_38 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_38 : Nat := 0x1115155500000000
def ep_38 : Nat := 0x440000000000004004000000000000404000000000011101000000000000000000000000000
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def nh_38 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV5 m_38 g_38 ep_38 1 1 0 bds_38 (dagTraceF m_38 s_38 4 f_38) (cur_38 0) (nh_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_38 g_38 ep_38 1 1 bds_38 0 (dagTraceF m_38 s_38 4 f_38) cur_38 nh_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_38 nc_38 (by decide +kernel)

def m_39 : Nat := 0xffff0000
def s_39 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_39 : Nat := 0x155f0000
def ep_39 : Nat := 0x4a000000000000040a000000000000100000000000000015500000
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cur_39 : Nat → List (Nat × Nat) := fun _ => []
def nh_39 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_39 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV5 m_39 g_39 ep_39 1 1 0 bds_39 (dagTraceF m_39 s_39 4 f_39) (cur_39 0) (nh_39 0) s_39 4 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_39 g_39 ep_39 1 1 bds_39 0 (dagTraceF m_39 s_39 4 f_39) cur_39 nh_39 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_39 : LowerBin m_39 s_39 g_39 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_39 nc_39 (by decide +kernel)

def m_40 : Nat := 0xff00ff00
def s_40 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_40 : Nat := 0x15005f00
def ep_40 : Nat := 0x4a0000000000000000000000000004000a0000000000100000000000000015005000
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_40 : Nat → List (Nat × Nat) := fun _ => []
def nh_40 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_40 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV5 m_40 g_40 ep_40 1 1 0 bds_40 (dagTraceF m_40 s_40 4 f_40) (cur_40 0) (nh_40 0) s_40 4 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_40 g_40 ep_40 1 1 bds_40 0 (dagTraceF m_40 s_40 4 f_40) cur_40 nh_40 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_40 : LowerBin m_40 s_40 g_40 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_40 nc_40 (by decide +kernel)

def m_41 : Nat := 0xf0f0f0f0
def s_41 : List Nat := [0x50505050, 0x30303030, 0xf000f0, 0xf0f0]
def g_41 : Nat := 0x10505070
def ep_41 : Nat := 0x40200000000000400020000000000000000000000000100000200000000010505040
def bds_41 : List (Nat × List Nat × Nat × Nat) := []
def cc_41_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_41_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_41 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_41_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_41_0 p) (Nat.blt p 32)
def hc_41_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_41_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_41_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_41 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_41_2 (Nat.sub p 64)) (hc_41_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_41_0 p) (Nat.blt p 32)
def f_41 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_41 : Nat → Bool := dagCheckNodeV5 m_41 g_41 ep_41 1 1 bds_41 64 (dagTraceF m_41 s_41 5 f_41) cur_41 nh_41
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV5 m_41 g_41 ep_41 1 1 64 bds_41 (dagTraceF m_41 s_41 5 f_41) (cur_41 0) (nh_41 0) s_41 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_0 : treeBlockF 0 32 ch_41 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_41_1 : treeBlockF 32 64 ch_41 = true := by decide +kernel
theorem nj_41_1 : ∀ i, 0 ≤ i → i < 64 → ch_41 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_41_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_41_1 h1 h2)
theorem nc_41 : ∀ i, 0 ≤ i → i < 64 → ch_41 i = true := nj_41_1
theorem lb_41 : LowerBin m_41 s_41 g_41 6 :=
  lowerDagV5 (kn_nil) rc_41 nc_41 (by decide +kernel)

def m_42 : Nat := 0x33333333
def s_42 : List Nat := [0x11111111, 0x3030303, 0x330033, 0x3333]
def g_42 : Nat := 0x11131333
def ep_42 : Nat := 0x2200000000000020020000000000002020000000000000000000000000011101000
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
def cur_42 : Nat → List (Nat × Nat) := fun _ => []
def nh_42 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_42 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV5 m_42 g_42 ep_42 1 1 0 bds_42 (dagTraceF m_42 s_42 4 f_42) (cur_42 0) (nh_42 0) s_42 4 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_42 g_42 ep_42 1 1 bds_42 0 (dagTraceF m_42 s_42 4 f_42) cur_42 nh_42 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagV5 (kn_cons lb_13 (kn_nil)) rc_42 nc_42 (by decide +kernel)

def m_43 : Nat := 0xaaaaaaaa
def s_43 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_43 : Nat := 0xa0a2a
def ep_43 : Nat := 0xa2000000000000a002000000000000a0a0800000000000000200000000000000000
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
def cur_43 : Nat → List (Nat × Nat) := fun _ => []
def nh_43 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_43 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV5 m_43 g_43 ep_43 1 1 0 bds_43 (dagTraceF m_43 s_43 4 f_43) (cur_43 0) (nh_43 0) s_43 4 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_43 g_43 ep_43 1 1 bds_43 0 (dagTraceF m_43 s_43 4 f_43) cur_43 nh_43 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_43 : LowerBin m_43 s_43 g_43 5 :=
  lowerDagV5 (kn_cons lb_13 (kn_nil)) rc_43 nc_43 (by decide +kernel)

def m_44 : Nat := 0xf000f000f000f0
def s_44 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_44 : Nat := 0x10005000500070
def ep_44 : Nat := 0x40002000000040000000200000000000000000000000000000000000100000000000200010005000500040
def bds_44 : List (Nat × List Nat × Nat × Nat) := []
def cc_44_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_44_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_44 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_44_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_44_0 p) (Nat.blt p 32)
def hc_44_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_44_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_44_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_44 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_44_2 (Nat.sub p 64)) (hc_44_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_44_0 p) (Nat.blt p 32)
def f_44 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_44 : Nat → Bool := dagCheckNodeV5 m_44 g_44 ep_44 1 1 bds_44 64 (dagTraceF m_44 s_44 5 f_44) cur_44 nh_44
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV5 m_44 g_44 ep_44 1 1 64 bds_44 (dagTraceF m_44 s_44 5 f_44) (cur_44 0) (nh_44 0) s_44 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_0 : treeBlockF 0 32 ch_44 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44_1 : treeBlockF 32 64 ch_44 = true := by decide +kernel
theorem nj_44_1 : ∀ i, 0 ≤ i → i < 64 → ch_44 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_44_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_44_1 h1 h2)
theorem nc_44 : ∀ i, 0 ≤ i → i < 64 → ch_44 i = true := nj_44_1
theorem lb_44 : LowerBin m_44 s_44 g_44 6 :=
  lowerDagV5 (kn_nil) rc_44 nc_44 (by decide +kernel)

def m_45 : Nat := 0x5500550055005500
def s_45 : List Nat := [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500]
def g_45 : Nat := 0x1100150015005500
def ep_45 : Nat := 0x400400000000400000040000000000000000000000004000400000011001000100000000000000000000000
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_45 : Nat → List (Nat × Nat) := fun _ => []
def nh_45 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV5 m_45 g_45 ep_45 1 1 0 bds_45 (dagTraceF m_45 s_45 4 f_45) (cur_45 0) (nh_45 0) s_45 4 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_45 g_45 ep_45 1 1 bds_45 0 (dagTraceF m_45 s_45 4 f_45) cur_45 nh_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin m_45 s_45 g_45 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_45 nc_45 (by decide +kernel)

def m_46 : Nat := 0xff000000ff0000
def s_46 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_46 : Nat := 0x150000005f0000
def ep_46 : Nat := 0x4a00000000000000000000000000000000000000040000000a000000100000000000000015000000500000
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16)]
def cur_46 : Nat → List (Nat × Nat) := fun _ => []
def nh_46 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_46 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV5 m_46 g_46 ep_46 1 1 0 bds_46 (dagTraceF m_46 s_46 4 f_46) (cur_46 0) (nh_46 0) s_46 4 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_46 g_46 ep_46 1 1 bds_46 0 (dagTraceF m_46 s_46 4 f_46) cur_46 nh_46 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_46 : LowerBin m_46 s_46 g_46 5 :=
  lowerDagV5 (kn_cons lb_16 (kn_nil)) rc_46 nc_46 (by decide +kernel)

def m_47 : Nat := 0x5050a0a05050a0a0
def s_47 : List Nat := [0xa0a00000a0a0, 0x1010202010102020, 0x5000a0005000a0, 0x5050a0a0]
def g_47 : Nat := 0x1010000010500020
def ep_47 : Nat := 0x40002000000000000000000000000000400020000000000000000010100000100000200000000000000000
def bds_47 : List (Nat × List Nat × Nat × Nat) := []
def cur_47 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb2ca1cc2e82962242122000f 7 127 3 7 9 511 12 4095
def nh_47 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_47 : Nat → Nat × Nat := unpackForestF 0x1bab86931184c00f 3 6
def ch_47 : Nat → Bool := dagCheckNodeV5 m_47 g_47 ep_47 1 1 bds_47 7 (dagTraceF m_47 s_47 4 f_47) cur_47 nh_47
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV5 m_47 g_47 ep_47 1 1 7 bds_47 (dagTraceF m_47 s_47 4 f_47) (cur_47 0) (nh_47 0) s_47 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47 : treeBlockF 0 7 ch_47 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 7 → ch_47 i = true := fun _ h1 h2 => treeBlockF_at nb_47 h1 h2
theorem lb_47 : LowerBin m_47 s_47 g_47 5 :=
  lowerDagV5 (kn_nil) rc_47 nc_47 (by decide +kernel)

def m_48 : Nat := 0x5555aaaa
def s_48 : List Nat := [0xaaaa, 0x11112222, 0x5050a0a, 0x5500aa]
def g_48 : Nat := 0x15550a2a
def ep_48 : Nat := 0x4000200000000004000a0800000000100000200000000000000000
def bds_48 : List (Nat × List Nat × Nat × Nat) := []
def cur_48 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58b12a44874e0701 0x192440a19343061234349263d88d5d2a549882a109800f 7 127 3 7 10 1023 14 16383
def nh_48 : Nat → Nat := unpackHintV5 0x340c0b00c02c2b02c0b02c015002 0x0 10 1023 5 31
def f_48 : Nat → Nat × Nat := unpackForestF 0xc7a63529564d0a4ce3469210a884c00f 3 10
def ch_48 : Nat → Bool := dagCheckNodeV5 m_48 g_48 ep_48 1 1 bds_48 10 (dagTraceF m_48 s_48 4 f_48) cur_48 nh_48
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV5 m_48 g_48 ep_48 1 1 10 bds_48 (dagTraceF m_48 s_48 4 f_48) (cur_48 0) (nh_48 0) s_48 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48 : treeBlockF 0 10 ch_48 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 10 → ch_48 i = true := fun _ h1 h2 => treeBlockF_at nb_48 h1 h2
theorem lb_48 : LowerBin m_48 s_48 g_48 5 :=
  lowerDagV5 (kn_nil) rc_48 nc_48 (by decide +kernel)

def m_49 : Nat := 0x5500aa005500aa
def s_49 : List Nat := [0xaa000000aa, 0x11002200110022, 0x5000a0005000a, 0x5500aa]
def g_49 : Nat := 0x15000a0055002a
def ep_49 : Nat := 0x400020000000000000000000000000000000000004000a0000000800100000000000200000000000000000
def bds_49 : List (Nat × List Nat × Nat × Nat) := []
def cur_49 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58952244890e8701 0x1d283091e342090d34206263d88d592a549902a109800f 7 127 3 7 10 1023 14 16383
def nh_49 : Nat → Nat := unpackHintV5 0x340c0b00c0300c0300c02c215002 0x0 10 1023 5 31
def f_49 : Nat → Nat × Nat := unpackForestF 0xc7a635f1a14a8a4c42a49a206084c00f 3 10
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
def g_50 : Nat := 0x4044404444444
def ep_50 : Nat := 0x440400000000440000040000004004000400000000404000400000000000000000000000000000000000000
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1), (m_15, s_15, 4, g_15), (m_11, s_11, 4, g_11), (m_9, s_9, 4, g_9)]
def cc_50_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_50_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_50 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_50_1 (Nat.sub p 32)) (cc_50_0 p) (Nat.blt p 32)
def hc_50_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e56655092040a6ad8c0011820539b81622002630805682cb74a008803a6b2b0810 15 32767 6 63
def hc_50_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e754ae0732b4dad55068b56 13 8191 6 63
def nh_50 : Nat → Nat := fun p => Bool.rec (hc_50_1 (Nat.sub p 32)) (hc_50_0 p) (Nat.blt p 32)
def f_50 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_50 : Nat → Bool := dagCheckNodeV5 m_50 g_50 ep_50 1 1 bds_50 43 (dagTraceF m_50 s_50 6 f_50) cur_50 nh_50
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV5 m_50 g_50 ep_50 1 1 43 bds_50 (dagTraceF m_50 s_50 6 f_50) (cur_50 0) (nh_50 0) s_50 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_0 : treeBlockF 0 32 ch_50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_1 : treeBlockF 32 43 ch_50 = true := by decide +kernel
theorem nj_50_1 : ∀ i, 0 ≤ i → i < 43 → ch_50 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_50_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_50_1 h1 h2)
theorem nc_50 : ∀ i, 0 ≤ i → i < 43 → ch_50 i = true := nj_50_1
theorem lb_50 : LowerBin m_50 s_50 g_50 7 :=
  lowerDagV5 (kn_cons lb_1 (kn_cons lb_15 (kn_cons lb_11 (kn_cons lb_9 (kn_nil))))) rc_50 nc_50 (by decide +kernel)

def m_51 : Nat := 0x8888888888888888
def s_51 : List Nat := [0x808080808080808, 0x88008800880088, 0x888800008888, 0x88888888]
def g_51 : Nat := 0x800080808
def ep_51 : Nat := 0x8080000000008000008000000000800080000000000080008080800000000000000000000000000000000
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_51 : Nat → List (Nat × Nat) := fun _ => []
def nh_51 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_51 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV5 m_51 g_51 ep_51 1 1 0 bds_51 (dagTraceF m_51 s_51 4 f_51) (cur_51 0) (nh_51 0) s_51 4 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_51 g_51 ep_51 1 1 bds_51 0 (dagTraceF m_51 s_51 4 f_51) cur_51 nh_51 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_51 : LowerBin m_51 s_51 g_51 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_51 nc_51 (by decide +kernel)

def m_52 : Nat := 0x50505050a0a0a0a0
def s_52 : List Nat := [0xa0a0a0a0, 0x1010101020202020, 0x50005000a000a0, 0x50500000a0a0]
def g_52 : Nat := 0x1010105000000020
def ep_52 : Nat := 0x40000000200000004000000020000000000000000010101000000000200000000000000000
def bds_52 : List (Nat × List Nat × Nat × Nat) := []
def cur_52 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xb2cb2cd2e92972252132000f 7 127 3 7 9 511 12 4095
def nh_52 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_52 : Nat → Nat × Nat := unpackForestF 0x32eb2c32932232132000f 3 9
def ch_52 : Nat → Bool := dagCheckNodeV5 m_52 g_52 ep_52 1 1 bds_52 7 (dagTraceF m_52 s_52 4 f_52) cur_52 nh_52
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV5 m_52 g_52 ep_52 1 1 7 bds_52 (dagTraceF m_52 s_52 4 f_52) (cur_52 0) (nh_52 0) s_52 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52 : treeBlockF 0 7 ch_52 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 7 → ch_52 i = true := fun _ h1 h2 => treeBlockF_at nb_52 h1 h2
theorem lb_52 : LowerBin m_52 s_52 g_52 5 :=
  lowerDagV5 (kn_nil) rc_52 nc_52 (by decide +kernel)

def m_53 : Nat := 0x55550000aaaa
def s_53 : List Nat := [0xaaaa, 0x111100002222, 0x50500000a0a, 0x55000000aa]
def g_53 : Nat := 0x155500000a2a
def ep_53 : Nat := 0x40000000200000040000000a0800001000000000200000000000000000
def bds_53 : List (Nat × List Nat × Nat × Nat) := []
def cur_53 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58b12a44874e0701 0x192440a19343061234349263d88d5d2a549882a109800f 7 127 3 7 10 1023 14 16383
def nh_53 : Nat → Nat := unpackHintV5 0x340c0b00c02c2b02c0b02c015002 0x0 10 1023 5 31
def f_53 : Nat → Nat × Nat := unpackForestF 0xc7a63529564d0a4ce3469210a884c00f 3 10
def ch_53 : Nat → Bool := dagCheckNodeV5 m_53 g_53 ep_53 1 1 bds_53 10 (dagTraceF m_53 s_53 4 f_53) cur_53 nh_53
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV5 m_53 g_53 ep_53 1 1 10 bds_53 (dagTraceF m_53 s_53 4 f_53) (cur_53 0) (nh_53 0) s_53 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53 : treeBlockF 0 10 ch_53 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 10 → ch_53 i = true := fun _ h1 h2 => treeBlockF_at nb_53 h1 h2
theorem lb_53 : LowerBin m_53 s_53 g_53 5 :=
  lowerDagV5 (kn_nil) rc_53 nc_53 (by decide +kernel)

def m_54 : Nat := 0x55005500aa00aa
def s_54 : List Nat := [0xaa00aa, 0x11001100220022, 0x50005000a000a, 0x55000000aa]
def g_54 : Nat := 0x150055000a002a
def ep_54 : Nat := 0x4000000020000000000000000000040000000a000800100000000000200000000000000000
def bds_54 : List (Nat × List Nat × Nat × Nat) := []
def cur_54 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58b12a44874e0701 0x192440a19343061234349263d88d5d2a549882a109800f 7 127 3 7 10 1023 14 16383
def nh_54 : Nat → Nat := unpackHintV5 0x340c0b00c02c2b02c0b02c015002 0x0 10 1023 5 31
def f_54 : Nat → Nat × Nat := unpackForestF 0xc7a63529564d0a4ce3469210a884c00f 3 10
def ch_54 : Nat → Bool := dagCheckNodeV5 m_54 g_54 ep_54 1 1 bds_54 10 (dagTraceF m_54 s_54 4 f_54) cur_54 nh_54
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV5 m_54 g_54 ep_54 1 1 10 bds_54 (dagTraceF m_54 s_54 4 f_54) (cur_54 0) (nh_54 0) s_54 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54 : treeBlockF 0 10 ch_54 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 10 → ch_54 i = true := fun _ h1 h2 => treeBlockF_at nb_54 h1 h2
theorem lb_54 : LowerBin m_54 s_54 g_54 5 :=
  lowerDagV5 (kn_nil) rc_54 nc_54 (by decide +kernel)

def m_55 : Nat := 0x2222222222222222
def s_55 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_55 : Nat := 0x200020222
def ep_55 : Nat := 0x2022000000002000002200000000200020020000000020002020000000000000000000000000000000000
def bds_55 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6), (m_13, s_13, 4, g_13), (m_7, s_7, 4, g_7), (m_10, s_10, 4, g_10)]
def cc_55_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_55_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_55 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_55_1 (Nat.sub p 32)) (cc_55_0 p) (Nat.blt p 32)
def hc_55_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_55_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_55 : Nat → Nat := fun p => Bool.rec (hc_55_1 (Nat.sub p 32)) (hc_55_0 p) (Nat.blt p 32)
def f_55 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_55 : Nat → Bool := dagCheckNodeV5 m_55 g_55 ep_55 1 1 bds_55 43 (dagTraceF m_55 s_55 6 f_55) cur_55 nh_55
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV5 m_55 g_55 ep_55 1 1 43 bds_55 (dagTraceF m_55 s_55 6 f_55) (cur_55 0) (nh_55 0) s_55 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_0 : treeBlockF 0 32 ch_55 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_1 : treeBlockF 32 43 ch_55 = true := by decide +kernel
theorem nj_55_1 : ∀ i, 0 ≤ i → i < 43 → ch_55 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_55_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_55_1 h1 h2)
theorem nc_55 : ∀ i, 0 ≤ i → i < 43 → ch_55 i = true := nj_55_1
theorem lb_55 : LowerBin m_55 s_55 g_55 7 :=
  lowerDagV5 (kn_cons lb_6 (kn_cons lb_13 (kn_cons lb_7 (kn_cons lb_10 (kn_nil))))) rc_55 nc_55 (by decide +kernel)

def m_56 : Nat := 0x5050505050505050
def s_56 : List Nat := [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050]
def g_56 : Nat := 0x1010105010505050
def ep_56 : Nat := 0x40400000000040000040000000004000400000000000000000000010101000100000000000000000000000
def bds_56 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_56 : Nat → List (Nat × Nat) := fun _ => []
def nh_56 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_56 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV5 m_56 g_56 ep_56 1 1 0 bds_56 (dagTraceF m_56 s_56 4 f_56) (cur_56 0) (nh_56 0) s_56 4 = true := by decide +kernel
theorem nc_56 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_56 g_56 ep_56 1 1 bds_56 0 (dagTraceF m_56 s_56 4 f_56) cur_56 nh_56 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_56 : LowerBin m_56 s_56 g_56 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_56 nc_56 (by decide +kernel)

def m_57 : Nat := 0xc0c0c0c0c0c0c0c
def s_57 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_57 : Nat := 0x4040c040c0c0c
def ep_57 : Nat := 0x408080000000408000008000004000800080000000000000000000000000000000000000004040004000000
def bds_57 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2), (m_17, s_17, 4, g_17), (m_5, s_5, 4, g_5), (m_8, s_8, 4, g_8)]
def cc_57_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_57_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_57 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_57_1 (Nat.sub p 32)) (cc_57_0 p) (Nat.blt p 32)
def hc_57_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e56655092040a6ad8c0011820539b81622002630805682cb74a008803a6b2b0810 15 32767 6 63
def hc_57_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e754ae0732b4dad55068b56 13 8191 6 63
def nh_57 : Nat → Nat := fun p => Bool.rec (hc_57_1 (Nat.sub p 32)) (hc_57_0 p) (Nat.blt p 32)
def f_57 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_57 : Nat → Bool := dagCheckNodeV5 m_57 g_57 ep_57 1 1 bds_57 43 (dagTraceF m_57 s_57 6 f_57) cur_57 nh_57
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV5 m_57 g_57 ep_57 1 1 43 bds_57 (dagTraceF m_57 s_57 6 f_57) (cur_57 0) (nh_57 0) s_57 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_0 : treeBlockF 0 32 ch_57 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_57_1 : treeBlockF 32 43 ch_57 = true := by decide +kernel
theorem nj_57_1 : ∀ i, 0 ≤ i → i < 43 → ch_57 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_57_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_57_1 h1 h2)
theorem nc_57 : ∀ i, 0 ≤ i → i < 43 → ch_57 i = true := nj_57_1
theorem lb_57 : LowerBin m_57 s_57 g_57 7 :=
  lowerDagV5 (kn_cons lb_2 (kn_cons lb_17 (kn_cons lb_5 (kn_cons lb_8 (kn_nil))))) rc_57 nc_57 (by decide +kernel)

def m_58 : Nat := 0x55aa55aa
def s_58 : List Nat := [0xaa00aa, 0x11221122, 0x50a050a, 0x55aa]
def g_58 : Nat := 0x150a552a
def ep_58 : Nat := 0x4020000000000000000000000000040a000800000000100000200000000000000000
def bds_58 : List (Nat × List Nat × Nat × Nat) := []
def cur_58 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58952244890e8701 0x1d283091e342090d34206263d88d592a549902a109800f 7 127 3 7 10 1023 14 16383
def nh_58 : Nat → Nat := unpackHintV5 0x340c0b00c0300c0300c02c215002 0x0 10 1023 5 31
def f_58 : Nat → Nat × Nat := unpackForestF 0xc7a635f1a14a8a4c42a49a206084c00f 3 10
def ch_58 : Nat → Bool := dagCheckNodeV5 m_58 g_58 ep_58 1 1 bds_58 10 (dagTraceF m_58 s_58 4 f_58) cur_58 nh_58
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV5 m_58 g_58 ep_58 1 1 10 bds_58 (dagTraceF m_58 s_58 4 f_58) (cur_58 0) (nh_58 0) s_58 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58 : treeBlockF 0 10 ch_58 = true := by decide +kernel
theorem nc_58 : ∀ i, 0 ≤ i → i < 10 → ch_58 i = true := fun _ h1 h2 => treeBlockF_at nb_58 h1 h2
theorem lb_58 : LowerBin m_58 s_58 g_58 5 :=
  lowerDagV5 (kn_nil) rc_58 nc_58 (by decide +kernel)

def m_59 : Nat := 0x55aa000055aa
def s_59 : List Nat := [0xaa000000aa, 0x112200001122, 0x50a0000050a, 0x55aa]
def g_59 : Nat := 0x150a0000552a
def ep_59 : Nat := 0x4020000000000000000000000000000000000000040a0000000800001000000000200000000000000000
def bds_59 : List (Nat × List Nat × Nat × Nat) := []
def cur_59 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58952244890e8701 0x1d283091e342090d34206263d88d592a549902a109800f 7 127 3 7 10 1023 14 16383
def nh_59 : Nat → Nat := unpackHintV5 0x340c0b00c0300c0300c02c215002 0x0 10 1023 5 31
def f_59 : Nat → Nat × Nat := unpackForestF 0xc7a635f1a14a8a4c42a49a206084c00f 3 10
def ch_59 : Nat → Bool := dagCheckNodeV5 m_59 g_59 ep_59 1 1 bds_59 10 (dagTraceF m_59 s_59 4 f_59) cur_59 nh_59
set_option maxHeartbeats 0 in
theorem rc_59 : dagCheckRootsV5 m_59 g_59 ep_59 1 1 10 bds_59 (dagTraceF m_59 s_59 4 f_59) (cur_59 0) (nh_59 0) s_59 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59 : treeBlockF 0 10 ch_59 = true := by decide +kernel
theorem nc_59 : ∀ i, 0 ≤ i → i < 10 → ch_59 i = true := fun _ h1 h2 => treeBlockF_at nb_59 h1 h2
theorem lb_59 : LowerBin m_59 s_59 g_59 5 :=
  lowerDagV5 (kn_nil) rc_59 nc_59 (by decide +kernel)

def m_60 : Nat := 0x50a050a050a050a0
def s_60 : List Nat := [0xa000a000a000a0, 0x1020102010201020, 0x50a0000050a0, 0x50a050a0]
def g_60 : Nat := 0x1000100010005020
def ep_60 : Nat := 0x402000000000000040200000000000000000000000000000000010001000100000200000000000000000
def bds_60 : List (Nat × List Nat × Nat × Nat) := []
def cur_60 : Nat → List (Nat × Nat) := unpackCursorV5 0x72e18b060c0681 0xbcbcde997251300f 7 127 3 7 5 31 8 255
def nh_60 : Nat → Nat := unpackHintV5 0xe81d03a0648a90d402c002 0x0 11 2047 5 31
def f_60 : Nat → Nat × Nat := unpackForestF 0x3ebc393231300f 3 5
def ch_60 : Nat → Bool := dagCheckNodeV5 m_60 g_60 ep_60 1 1 bds_60 7 (dagTraceF m_60 s_60 4 f_60) cur_60 nh_60
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsV5 m_60 g_60 ep_60 1 1 7 bds_60 (dagTraceF m_60 s_60 4 f_60) (cur_60 0) (nh_60 0) s_60 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60 : treeBlockF 0 7 ch_60 = true := by decide +kernel
theorem nc_60 : ∀ i, 0 ≤ i → i < 7 → ch_60 i = true := fun _ h1 h2 => treeBlockF_at nb_60 h1 h2
theorem lb_60 : LowerBin m_60 s_60 g_60 5 :=
  lowerDagV5 (kn_nil) rc_60 nc_60 (by decide +kernel)

def m_61 : Nat := 0x3333333333333333
def s_61 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_61 : Nat := 0x1111111311131333
def ep_61 : Nat := 0x2022000000002000002200000000200020020000000020002020000000000000000001111111011101000
def bds_61 : List (Nat × List Nat × Nat × Nat) := [(m_55, s_55, 7, g_55)]
def cur_61 : Nat → List (Nat × Nat) := fun _ => []
def nh_61 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_61 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_61 : dagCheckRootsV5 m_61 g_61 ep_61 1 1 0 bds_61 (dagTraceF m_61 s_61 7 f_61) (cur_61 0) (nh_61 0) s_61 7 = true := by decide +kernel
theorem nc_61 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_61 g_61 ep_61 1 1 bds_61 0 (dagTraceF m_61 s_61 7 f_61) cur_61 nh_61 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_61 : LowerBin m_61 s_61 g_61 8 :=
  lowerDagV5 (kn_cons lb_55 (kn_nil)) rc_61 nc_61 (by decide +kernel)

def m_62 : Nat := 0xff00ff00ff00ff00
def s_62 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_62 : Nat := 0x1100150015005f00
def ep_62 : Nat := 0x4004a000000040000004a0000000000000000000000040004000a0011001000100000001100150015005000
def bds_62 : List (Nat × List Nat × Nat × Nat) := [(m_35, s_35, 7, g_35)]
def cur_62 : Nat → List (Nat × Nat) := fun _ => []
def nh_62 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_62 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_62 : dagCheckRootsV5 m_62 g_62 ep_62 1 1 0 bds_62 (dagTraceF m_62 s_62 7 f_62) (cur_62 0) (nh_62 0) s_62 7 = true := by decide +kernel
theorem nc_62 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_62 g_62 ep_62 1 1 bds_62 0 (dagTraceF m_62 s_62 7 f_62) cur_62 nh_62 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_62 : LowerBin m_62 s_62 g_62 8 :=
  lowerDagV5 (kn_cons lb_35 (kn_nil)) rc_62 nc_62 (by decide +kernel)

def m_63 : Nat := 0xf0f0f0f0f0f0f0f
def s_63 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_63 : Nat := 0x105050f050f0f0f
def ep_63 : Nat := 0x40a0a000000040a00000a000004000a000a0000000000000000000001000000000000000105050005000000
def bds_63 : List (Nat × List Nat × Nat × Nat) := [(m_57, s_57, 7, g_57)]
def cur_63 : Nat → List (Nat × Nat) := fun _ => []
def nh_63 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_63 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_63 : dagCheckRootsV5 m_63 g_63 ep_63 1 1 0 bds_63 (dagTraceF m_63 s_63 7 f_63) (cur_63 0) (nh_63 0) s_63 7 = true := by decide +kernel
theorem nc_63 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_63 g_63 ep_63 1 1 bds_63 0 (dagTraceF m_63 s_63 7 f_63) cur_63 nh_63 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_63 : LowerBin m_63 s_63 g_63 8 :=
  lowerDagV5 (kn_cons lb_57 (kn_nil)) rc_63 nc_63 (by decide +kernel)

def m_64 : Nat := 0x5555555555555555
def s_64 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_64 : Nat := 0x1115155515555555
def ep_64 : Nat := 0x440400000000440000040000004004000400000000404000400000011101000100000000000000000000000
def bds_64 : List (Nat × List Nat × Nat × Nat) := [(m_50, s_50, 7, g_50)]
def cur_64 : Nat → List (Nat × Nat) := fun _ => []
def nh_64 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_64 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_64 : dagCheckRootsV5 m_64 g_64 ep_64 1 1 0 bds_64 (dagTraceF m_64 s_64 7 f_64) (cur_64 0) (nh_64 0) s_64 7 = true := by decide +kernel
theorem nc_64 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_64 g_64 ep_64 1 1 bds_64 0 (dagTraceF m_64 s_64 7 f_64) cur_64 nh_64 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_64 : LowerBin m_64 s_64 g_64 8 :=
  lowerDagV5 (kn_cons lb_50 (kn_nil)) rc_64 nc_64 (by decide +kernel)

def m_65 : Nat := 0xaaaaaaaaaaaaaaaa
def s_65 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_65 : Nat := 0xa000a0a2a
def ep_65 : Nat := 0xa0a200000000a00000a200000000a000a00200000000a000a0a0800000000000000200000000000000000
def bds_65 : List (Nat × List Nat × Nat × Nat) := [(m_55, s_55, 7, g_55)]
def cur_65 : Nat → List (Nat × Nat) := fun _ => []
def nh_65 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_65 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_65 : dagCheckRootsV5 m_65 g_65 ep_65 1 1 0 bds_65 (dagTraceF m_65 s_65 7 f_65) (cur_65 0) (nh_65 0) s_65 7 = true := by decide +kernel
theorem nc_65 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_65 g_65 ep_65 1 1 bds_65 0 (dagTraceF m_65 s_65 7 f_65) cur_65 nh_65 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_65 : LowerBin m_65 s_65 g_65 8 :=
  lowerDagV5 (kn_cons lb_55 (kn_nil)) rc_65 nc_65 (by decide +kernel)

def m_66 : Nat := 0xff00ff00ff00ff
def s_66 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_66 : Nat := 0x15005f005f007f
def ep_66 : Nat := 0x4a00200000004a0000002000000000000000000004000a000a000800100000000000200015005000500040
def bds_66 : List (Nat × List Nat × Nat × Nat) := [(m_44, s_44, 6, g_44), (m_46, s_46, 5, g_46), (m_23, s_23, 5, g_23), (m_26, s_26, 5, g_26), (m_25, s_25, 5, g_25), (m_22, s_22, 5, g_22), (m_49, s_49, 5, g_49), (m_3, s_3, 4, g_3), (m_10, s_10, 4, g_10)]
def cur_66 : Nat → List (Nat × Nat) := unpackCursorV5 0xb2691e71c7131c1 0x205d305595d205925a3558856751d447105c01f 6 63 2 3 10 1023 14 16383
def nh_66 : Nat → Nat := unpackHintV5 0xda80a669a60071e971806a8e638e365b006c0000 0xaf39c6778c60000b56aed384f9ab9ce33cc6300005eae5d5b8e10edc37682deb19ce3004684c38159538ce3000005a8d3a00ba1c78019 16 65535 7 127
def f_66 : Nat → Nat × Nat := unpackForestF 0x205d151d95d111ca5a2558856105c01f 4 10
def ch_66 : Nat → Bool := dagCheckNodeV5 m_66 g_66 ep_66 3 7 bds_66 9 (dagTraceF m_66 s_66 7 f_66) cur_66 nh_66
set_option maxHeartbeats 0 in
theorem rc_66 : dagCheckRootsV5 m_66 g_66 ep_66 3 7 9 bds_66 (dagTraceF m_66 s_66 7 f_66) (cur_66 0) (nh_66 0) s_66 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66 : treeBlockF 0 9 ch_66 = true := by decide +kernel
theorem nc_66 : ∀ i, 0 ≤ i → i < 9 → ch_66 i = true := fun _ h1 h2 => treeBlockF_at nb_66 h1 h2
theorem lb_66 : LowerBin m_66 s_66 g_66 8 :=
  lowerDagV5 (kn_cons lb_44 (kn_cons lb_46 (kn_cons lb_23 (kn_cons lb_26 (kn_cons lb_25 (kn_cons lb_22 (kn_cons lb_49 (kn_cons lb_3 (kn_cons lb_10 (kn_nil)))))))))) rc_66 nc_66 (by decide +kernel)

def m_67 : Nat := 0xffff0000ffff
def s_67 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_67 : Nat := 0x155f00005f7f
def ep_67 : Nat := 0x4a2000000000000000000000004a000000200000040a00000a0800001000000000200000155000005040
def bds_67 : List (Nat × List Nat × Nat × Nat) := [(m_30, s_30, 6, g_30), (m_21, s_21, 5, g_21), (m_29, s_29, 5, g_29), (m_32, s_32, 5, g_32), (m_33, s_33, 5, g_33), (m_34, s_34, 5, g_34), (m_53, s_53, 5, g_53), (m_14, s_14, 4, g_14), (m_6, s_6, 4, g_6)]
def cur_67 : Nat → List (Nat × Nat) := unpackCursorV5 0xb2691e71c7131c1 0x205d305595d205925a3558856751d447105c01f 6 63 2 3 10 1023 14 16383
def nh_67 : Nat → Nat := unpackHintV5 0xda80a669a60071e971806a8e638e365b006c0000 0x15739c6798c60000b9756e382f6579ce33bc6300009f2d5abb4e08dda3b702deb19ce3008702a34265538ce3000005d0e3c00b51a74025 16 65535 7 127
def f_67 : Nat → Nat × Nat := unpackForestF 0x205d151d95d111ca5a2558856105c01f 4 10
def ch_67 : Nat → Bool := dagCheckNodeV5 m_67 g_67 ep_67 3 7 bds_67 9 (dagTraceF m_67 s_67 7 f_67) cur_67 nh_67
set_option maxHeartbeats 0 in
theorem rc_67 : dagCheckRootsV5 m_67 g_67 ep_67 3 7 9 bds_67 (dagTraceF m_67 s_67 7 f_67) (cur_67 0) (nh_67 0) s_67 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_67 : treeBlockF 0 9 ch_67 = true := by decide +kernel
theorem nc_67 : ∀ i, 0 ≤ i → i < 9 → ch_67 i = true := fun _ h1 h2 => treeBlockF_at nb_67 h1 h2
theorem lb_67 : LowerBin m_67 s_67 g_67 8 :=
  lowerDagV5 (kn_cons lb_30 (kn_cons lb_21 (kn_cons lb_29 (kn_cons lb_32 (kn_cons lb_33 (kn_cons lb_34 (kn_cons lb_53 (kn_cons lb_14 (kn_cons lb_6 (kn_nil)))))))))) rc_67 nc_67 (by decide +kernel)

def m_68 : Nat := 0xffffffff00000000
def s_68 : List Nat := [0x5555555500000000, 0x3333333300000000, 0xf0f0f0f00000000, 0xff00ff00000000, 0xffff00000000]
def g_68 : Nat := 0x1115155f00000000
def ep_68 : Nat := 0x44a000000000004004a000000000004040a0000000011101000000000001115155000000000
def bds_68 : List (Nat × List Nat × Nat × Nat) := [(m_24, s_24, 7, g_24)]
def cur_68 : Nat → List (Nat × Nat) := fun _ => []
def nh_68 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_68 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_68 : dagCheckRootsV5 m_68 g_68 ep_68 1 1 0 bds_68 (dagTraceF m_68 s_68 7 f_68) (cur_68 0) (nh_68 0) s_68 7 = true := by decide +kernel
theorem nc_68 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_68 g_68 ep_68 1 1 bds_68 0 (dagTraceF m_68 s_68 7 f_68) cur_68 nh_68 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_68 : LowerBin m_68 s_68 g_68 8 :=
  lowerDagV5 (kn_cons lb_24 (kn_nil)) rc_68 nc_68 (by decide +kernel)

def m_69 : Nat := 0xffffffff
def s_69 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_69 : Nat := 0x155f5f7f
def ep_69 : Nat := 0x4a2000000000004a002000000000040a0a0800000000100000200000000015505040
def bds_69 : List (Nat × List Nat × Nat × Nat) := [(m_41, s_41, 6, g_41), (m_39, s_39, 5, g_39), (m_40, s_40, 5, g_40), (m_37, s_37, 5, g_37), (m_42, s_42, 5, g_42), (m_43, s_43, 5, g_43), (m_48, s_48, 5, g_48), (m_0, s_0, 4, g_0), (m_13, s_13, 4, g_13)]
def cur_69 : Nat → List (Nat × Nat) := unpackCursorV5 0xb2691e71c7131c1 0x205d305595d205925a3558856751d447105c01f 6 63 2 3 10 1023 14 16383
def nh_69 : Nat → Nat := unpackHintV5 0xda80a669a60071e971806a8e638e365b006c0000 0x15739c6798c60000b9756e382f6579ce33bc6300009f2d5abb4e08dda3b702deb19ce3008702a34265538ce3000005d0e3c00b51a74025 16 65535 7 127
def f_69 : Nat → Nat × Nat := unpackForestF 0x205d151d95d111ca5a2558856105c01f 4 10
def ch_69 : Nat → Bool := dagCheckNodeV5 m_69 g_69 ep_69 3 7 bds_69 9 (dagTraceF m_69 s_69 7 f_69) cur_69 nh_69
set_option maxHeartbeats 0 in
theorem rc_69 : dagCheckRootsV5 m_69 g_69 ep_69 3 7 9 bds_69 (dagTraceF m_69 s_69 7 f_69) (cur_69 0) (nh_69 0) s_69 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_69 : treeBlockF 0 9 ch_69 = true := by decide +kernel
theorem nc_69 : ∀ i, 0 ≤ i → i < 9 → ch_69 i = true := fun _ h1 h2 => treeBlockF_at nb_69 h1 h2
theorem lb_69 : LowerBin m_69 s_69 g_69 8 :=
  lowerDagV5 (kn_cons lb_41 (kn_cons lb_39 (kn_cons lb_40 (kn_cons lb_37 (kn_cons lb_42 (kn_cons lb_43 (kn_cons lb_48 (kn_cons lb_0 (kn_cons lb_13 (kn_nil)))))))))) rc_69 nc_69 (by decide +kernel)

def m_70 : Nat := 0xffff0000ffff0000
def s_70 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_70 : Nat := 0x11150000155f0000
def ep_70 : Nat := 0x44a0000000000000000000000040000004a000000040000040a000011100000100000001115000015500000
def bds_70 : List (Nat × List Nat × Nat × Nat) := [(m_27, s_27, 7, g_27)]
def cur_70 : Nat → List (Nat × Nat) := fun _ => []
def nh_70 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_70 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_70 : dagCheckRootsV5 m_70 g_70 ep_70 1 1 0 bds_70 (dagTraceF m_70 s_70 7 f_70) (cur_70 0) (nh_70 0) s_70 7 = true := by decide +kernel
theorem nc_70 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_70 g_70 ep_70 1 1 bds_70 0 (dagTraceF m_70 s_70 7 f_70) cur_70 nh_70 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_70 : LowerBin m_70 s_70 g_70 8 :=
  lowerDagV5 (kn_cons lb_27 (kn_nil)) rc_70 nc_70 (by decide +kernel)

def g_71 : Nat := 0x1115155f155f5f7f
def ep_71 : Nat := 0x44a4a200000044a00004a200004004a004a00200004040a040a0a0811101000100000201115155015505040
def bds_71 : List (Nat × List Nat × Nat × Nat) := [(m_70, s_70, 8, g_70), (m_68, s_68, 8, g_68), (m_66, s_66, 8, g_66), (m_63, s_63, 8, g_63), (m_57, s_57, 7, g_57), (m_64, s_64, 8, g_64), (m_62, s_62, 8, g_62), (m_44, s_44, 6, g_44), (m_27, s_27, 7, g_27), (m_41, s_41, 6, g_41), (m_65, s_65, 8, g_65), (m_61, s_61, 8, g_61), (m_67, s_67, 8, g_67), (m_55, s_55, 7, g_55), (m_35, s_35, 7, g_35), (m_30, s_30, 6, g_30), (m_69, s_69, 8, g_69), (m_56, s_56, 5, g_56), (m_46, s_46, 5, g_46), (m_38, s_38, 5, g_38), (m_43, s_43, 5, g_43), (m_50, s_50, 7, g_50), (m_24, s_24, 7, g_24), (m_23, s_23, 5, g_23), (m_40, s_40, 5, g_40), (m_34, s_34, 5, g_34), (m_31, s_31, 5, g_31), (m_9, s_9, 4, g_9), (m_36, s_36, 5, g_36), (m_53, s_53, 5, g_53), (m_28, s_28, 5, g_28), (m_48, s_48, 5, g_48), (m_51, s_51, 5, g_51), (m_58, s_58, 5, g_58), (m_29, s_29, 5, g_29), (m_54, s_54, 5, g_54), (m_59, s_59, 5, g_59), (m_49, s_49, 5, g_49), (m_19, s_19, 5, g_19), (m_20, s_20, 5, g_20), (m_18, s_18, 5, g_18), (m_47, s_47, 5, g_47), (m_60, s_60, 5, g_60), (m_52, s_52, 5, g_52)]
def cc_71_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xd406a03405904c60e3031818c0c606207005800c005f06e85701b805c02e01700b805a0ad01641aa25406611300960bd380f8001 0x1e4680e814088978424ac1f24e0e12306cb002c4ec178d80a960048200264ec1126e0802402e360141b0082a80695f030ad81255c072a60314008daf834d5c194be0c25b0512b81e94c0e47602a3700e3309d1bc4b8d624c6711631886dbc416d61f3670d5b1866d3c3269618347091a18084900209d70c5fb822ddbd15ed58a76a35fb45adda0d5ecf6a76734fb35a5d98d1ecb68764a5fb1d2dd8695ec14a76024faf925d7a91ebc4875c23fadd1dd6c8deb34675715fa94add3455e902a74794fa2ca5d1451e892873f93f9e49dcda4de652672f92f96495c8a49e2c2470d85f8082dbbe15db90a6dc04f6c025b5c11dad086cd83f62c1dab40dd410669782f474159e009ca10464781f1f40d8a005c010260003f 13 8191 6 63 11 2047 21 2097151
def cc_71_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x8dc4612fa753a1c2d95aa89409948a4104803c9c4d2682d160a250210902410080402002 0x815f0a1247e1f1e25872911e35c26051c24022051ca4c70d51ea4f7692dd2476e90c80141e491b0346811071240a491885c5a9e14a645adf15d7c509814a6c50dd13a645c9bd626b5499d32635ed9128343c481003c 9 511 3 7 11 2047 18 262143
def cc_71_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xccb21c0af1b0ec0ac6a19ce2580a00801e23fcf0348d0340b22c0832008018851140320c01200400 0x2e9781a082c964ba9f0603016082dd7cb05804820b25b04020b09d2b9640e0c2f16fb85aed167ac58c3020aa9402810a71ba9456f95bfd567f11bf7c67db15f5b6fd2daf2b67c6d8f0b5bc0d5efb4ba8d1e8a420804119249e1926c6498110d124941f0184c908ee3a338c110c92488190c124840d0b924 10 1023 4 15 11 2047 18 262143
def cc_71_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xc02799c270986608ce12805e2709c0689824d512440f23c0d2340b2284911c843100220801104001 0x8d8df1719e25b7c3b6b846cf04d8e05a5bfb477e09cf69c1e53429a4023020ec52088103993476498420c1c8980f820732783c081c9220e0307727eea4edd09bb89331b040e09c068083726052480d89a0640835238180202e04058183394b15040d15f199380a010644701e041891c07010 10 1023 4 15 11 2047 19 524287
def cc_71_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xc05c6e161b0546a150994c24320904462089401c4e06130144a041201004420088402001 0x9e2f938592689a4c57c972f92a4d248ae4fc6f9d8cf36dbe65b5cb367946c726d2e45a3c814e8e0c9181f228324403486af90a1f20c1a4005c 9 511 4 15 11 2047 19 524287
def cc_71_5 : Nat → List (Nat × Nat) := unpackCursorV5 0xb82e0b0a849c6709c2709c26190a409023184a018020080200801e2781d165181421003c41e04001 0x2f91a5e814c225f824aefc93de123bb4c16c8eede365aa60b2481660eec41bd8014ab8d9541b2a12a56a5fac4b75295e9d29d3240c36bf74d5ee4afdc15bb42af5e54eb89dd2937a38cddd1bfae35f4c67e58c7c69bf8535ef267d54c7a693f4925e8247c4487484d2882750164 10 1023 4 15 11 2047 19 524287
def cc_71_6 : Nat → List (Nat × Nat) := unpackCursorV5 0x8dc4612fa753a1c2d95aa89409948a4104803c9c4d2682d160a250210902410080402002 0x382be5a134df0f9b856364a26e25cb3089b0502c41a6c94cd84a9ba53f6ca5ed147d7287600d2bca26b024d40895c512949a6885ccd2f192593353e65d7cc82c1925b3213a63964ce2df985af28b3e3163cf4c98a092f8906003c 9 511 3 7 11 2047 19 524287
def cc_71_7 : Nat → List (Nat × Nat) := unpackCursorV5 0xd0740cc712c06e2b46a3a8291a0653815e23fcf0348d0340b22c0832008018851140320c01200400 0x7f94c570307d278568307b2647d37c56040558307c57c7aa60548307b26c540307ab747a264538407da6f7ca6b7ba6779a635303079350528208e56f8d5678c46f87c6786c57853428416f8316b81167801637f15b7e9577e14b7894752020619347786476c64760445d1347507c5184c7413b73933730445c934720645c144710245b934 10 1023 4 15 11 2047 20 1048575
def cc_71_8 : Nat → List (Nat × Nat) := unpackCursorV5 0xc02799c270986608ce12805e2709c0689824d512440f23c0f0348d02c8b0248811c45208c2000800 0x96c6f95c6794a6f93a6b922679126390a4b8fa478f04e8db708cb6886340618208b13861040899248b23c60840891205f8408992c5f030892345e0408b92f8a92b8a127889235d830883705d0208736085b408646e85c5684b685c8208394c5c0305b8205b0408224b5a83082d7c81b705a0208094c57830 10 1023 4 15 11 2047 20 1048575
def cc_71_9 : Nat → List (Nat × Nat) := unpackCursorV5 0xc05c6e170b0d82a350a84ca6121904822289401c4e06130144a041201004420088402001 0x9f27c9da649c9349bd7c9b27c9a13498a5c9fc6f9ec679e24e9d16f9c16b9a967999639914b98147970649607c95064940249357c9287c918249005c 9 511 4 15 11 2047 20 1048575
def cc_71_10 : Nat → List (Nat × Nat) := unpackCursorV5 0xb12b1ac292771d0705c06c5a168191641815c561545415012248111440f22d092240902041704001 0xb2a5fb225bb0a57afa53af240aea34ae15cc4a6fc3a6bc1267c0263bf16fbe16bbb967ba963b992fb892bb3127ad923ac834ab92bab034aa024a913fa8824a7178a5164a727ca657ca4960a516ca4a74a4164a796fa696ba5967a3963a1864a3024a1923ac36baab63a9a6ba8263a2a33a205ca1054a0264 10 1023 4 15 11 2047 20 1048575
def cc_71_11 : Nat → List (Nat × Nat) := unpackCursorV5 0x80c01f2f87c3e1d4da6c345a0c96430564a94d244f678389a4a62d0d06030180c0281001 0xbfc68be95cbd23fbca33bdd7cbc470bb15cba25cb915cb7a78b2930b5a64b7b7cb2140b1930b6d7cb5260b0930b5a6cb0130b5374b4a64af940b826fb726bb6267b4263af130b3b50ae920b1c6cb116cb0254 9 511 3 7 11 2047 20 1048575
def cc_71_12 : Nat → List (Nat × Nat) := unpackCursorV5 0x84610805795c1705c16158160581605455054150505404c47c1c0611805114050140320481000400 0xcf944ce944d656fd5567d426bd3263d225bd116bd0163cf15bce123cc57cc9d7cc6a30c6b44cd36fccb6bcbb67cb363caa6fca26bc9267c8a63c823fc7a3bc7237c6233c5468c425cc293fc2133c357cc1c70c0a5c 10 1023 4 15 11 2047 20 1048575
def cc_71_13 : Nat → List (Nat × Nat) := unpackCursorV5 0x8c621755b26c0ed380e0344d0304c02c4b01d070184601806014450104400c430084200441000400 0xdfa99be9538f1a7194fe1a97c051f7aa1f2344de049ddd3fb9a5f6b47ebe87d593fa925f4a47e7c87cd8ff971df2637ddc67ba13b6e226d444d9899b6d3f6927eca37d889daf49f57be6a644d3c89a591346a268544 10 1023 4 15 10 1023 19 524287
def cc_71_14 : Nat → List (Nat × Nat) := unpackCursorV5 0xb156a54a3426c991162448301eb970d5a3160a929e3260a8e1824100 0x3bc2276c5ceca57d80d3ac2274c5ce8a7fd00939c1a73024e4461ca1338e127153be0a6fc45637ea271744e24b9c2903831a6f940 7 127 2 3 10 1023 19 524287
def cc_71_15 : Nat → List (Nat × Nat) := unpackCursorV5 0x9c261982609824288a2084610842107c9d2741d06c9b06c19260571549234451044101388e02cc0b 0x3fd5f1fb27efd1337f2be3f31c1f7af8fa23f7cd19beb5f1f28e0f857c7bd3e3db5f1ec2f8f2920790a03d292de3260f557c7a1b83c4481e5468f223b796363c6981e6af8f1234784be4031b2008c0ffb617f51dbf08ddf6276f89377b897bd64ade724ef0123 10 1023 4 15 11 2047 21 2097151
def cc_71_16 : Nat → List (Nat × Nat) := unpackCursorV5 0xb02c0a8a1984201802007c5f0785e0745d0741c1701b16c1a168191641725c170549502340800000 0x87a34875648af598aa3b8a23789d3b8953788d2f8852b87d27871238684485c5c8543484c448405c83824830348282481a308204c81b44814248674f8634b85b478534384a4f8464b83e478364382e3f8263b81e378123380c4e7fa3b7f2377dd3b7d5377c12f7b52b7a92779923 10 1023 4 15 10 1023 20 1048575
def cc_71_17 : Nat → List (Nat × Nat) := unpackCursorV5 0xa4e90a427298660982609824290240889e474558541411b860180601445014041100310c02108002 0x8c11a47e5f22e2991e83b8f019c76512362791a0208d09a4660923805f1b82b8d413c6408e314c11cb5f8c1abc3c17e060b6f105772029b1a0ed5d06f1746690e37c811ae3e8cf1d4638bd1a45a53a1c0df0206b78033b7618d9c09ec604b56c23a8a10e298d11346889132444592206d10f120 10 1023 4 15 11 2047 21 2097151
def cc_71_18 : Nat → List (Nat × Nat) := unpackCursorV5 0xe0371dc361d82d9b42d0b06c0a4e729864288a20809e2655725c152541504c84f100220802000800 0x978b24b85f25d8df2dc67968a74421be090d6f586772c31b1e12d7108f2bb70955b4490d02392411c1409481c49e092374812913c8d4a049c082342612782c8c92049c4d2312612982f94415ca009e4d047263708c090494d82476812446e91e2b4b15be56acf2a46f92e33c9315e466851792087c37c0e1ade70cee48636c82db5e15d8e096b30478e51a488592428c920944 10 1023 4 15 11 2047 21 2097151
def cc_71_19 : Nat → List (Nat × Nat) := unpackCursorV5 0xd8360d8351d429ca4281a02719c2709c2528ca308856c58151541414c530484b72c0a12809124009 0x27caf93f36f9f5b5cf6d9e7a6c71386f84435bec19dd40c69903f4841d9f80dcd20673c4689d92e4e60fe720673a57c9c6384de972774df3aa6b9c133cdc98e250df0786b7c433ba418d3005e8f82b3c4139a008e6c2693502b9a49a19e08e6b6d73436399cae4cc5520d0d6e786331019cc8992624f931c6f98633cc093a230df0586b7b833b9a18d90096b9847 10 1023 4 15 11 2047 21 2097151
def cc_71_20 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc330c4af292e408c6308c22188211806004f5304c121480e4344d0340d0304c02c4b0284a024409 0x53c0fe9d0674fd7ca72385491b2a38c151361a811dd368dd92076bb8374d417a480ad0204e6f023a64a252c5729405749934a61a7d2ed2e9568f49343a44a734013d91096ba84754021a660fd220768003735419d1c5128d69f4614e678279fc0dcfd04f43b7ca1522506912814894456fa1ab3d089ae824c74025b84835baa18db40b669823 10 1023 4 15 11 2047 21 2097151
def cc_71_21 : Nat → List (Nat × Nat) := unpackCursorV5 0x9c9346684d09a13061cb7c578ac150a374608c118221332640c09803005c4b81612c02740c01002004000800 0x2bf49d4014f690278c205c6002f5d37caeeb7d7359eac2d74c163a34adc321addd0c6db05b0cc09d625beab2d750167a5cb1c541be180d6fe8677703192607c810362f8170c809d5e5bea92d74d967a54b1c501be160d6fc0677683192207c7f0362a0170c00985e04eb54b95a254a9cb5d2458e140d6eb86309009d611a2b26b358a3babd1bb2a0ed7e06e9d02f4a415a1009ce304756944aa8ae5504d2ac69f55b4baa5a3d4ed0ea629cd104f65025af811d530869c03f49c1da0c0dce106750a3ba7d1bb260ed7b06e9b82f49815a0a09ce004750d7c 11 2047 4 15 11 2047 21 2097151
def cc_71_22 : Nat → List (Nat × Nat) := unpackCursorV5 0xc8f90320640c8190320640c81722865009a7215e6393720e41b1b606c0b656820d310600c00db1a003400000 0x5bed86b947f4313f95893b540fd1a04e3d017b75a45b8d12db4916d244b64a45b0512d70916b04498c97cba4ae5424f219234fc17a5a0ad1804e7702327c0f91a06c7802e27013908919da08c4d02769b5cb49aa48048ceb0462581398497cb64ae4b24f1f1234f417a560ad0f04e748232740f91606c6f02e248138e8919ca08c4502724927434138da05eca6b33f13b9dc9bb340ed8906e4d81f2240d8d605c430276424ea10a7cfa52e7528f359436a027b3212d8708eac0432640f90e06c6902e208139f09dce84dd98076c30372600f90c06c6802e20013b1a3658b182c46c33d93b9c09bb2e0ed8206e4b01f2100d8ca05c3e0276124ea08a7cf452e6e28f3414369827b2c12d8008eaa8432500f90406c6302e1a813 11 2047 4 15 11 2047 21 2097151
def cc_71_23 : Nat → List (Nat × Nat) := unpackCursorV5 0x6000 0xaee3fa213f961276b03f470271f017 6 63 3 7 10 1023 20 1048575
def cur_71 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_71_23 (Nat.sub p 736)) (cc_71_22 (Nat.sub p 704)) (Nat.blt p 736)) (cc_71_21 (Nat.sub p 672)) (Nat.blt p 704)) (Bool.rec (Bool.rec (cc_71_20 (Nat.sub p 640)) (cc_71_19 (Nat.sub p 608)) (Nat.blt p 640)) (cc_71_18 (Nat.sub p 576)) (Nat.blt p 608)) (Nat.blt p 672)) (Bool.rec (Bool.rec (Bool.rec (cc_71_17 (Nat.sub p 544)) (cc_71_16 (Nat.sub p 512)) (Nat.blt p 544)) (cc_71_15 (Nat.sub p 480)) (Nat.blt p 512)) (Bool.rec (Bool.rec (cc_71_14 (Nat.sub p 448)) (cc_71_13 (Nat.sub p 416)) (Nat.blt p 448)) (cc_71_12 (Nat.sub p 384)) (Nat.blt p 416)) (Nat.blt p 480)) (Nat.blt p 576)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_71_11 (Nat.sub p 352)) (cc_71_10 (Nat.sub p 320)) (Nat.blt p 352)) (cc_71_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (Bool.rec (cc_71_8 (Nat.sub p 256)) (cc_71_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_71_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (cc_71_5 (Nat.sub p 160)) (cc_71_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_71_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_71_2 (Nat.sub p 64)) (cc_71_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_71_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)) (Nat.blt p 384)
def hc_71_0 : Nat → Nat := unpackHintV5 0xe22021c3c023814196a716ebf257163c6a27c52d4b39149630111aa471fcce23f78087eb010fbc069c38d02eea624b04b49500412800824e0084980108fc0d11e80422e03c3d920c6046b89a09a0c39c208e3e400047000000000000 0xa78f8f1f0b072b1b0301c1c1c1c0c0c0c030b0303070303030b0b0b0b07070707030303030b0b0b0b0707070703030303000000000000003030b03070303030303070707070703030303030303030b03a70303070303030380c0c0e030f0b0b0b0b070707070303030303031b1b0303030303031b0b0b0b0b07070707030303031b1b1b1b0000000000000006ca783e170b0b17a81e17a1f0b0b13a86e03a1713171382ea7aaaaaaa86c2c2c7ea2786e85c5c5c5c4c6c6c4eaa2700000000000009ca70b0b0b0b0b0b0b0b1717171782ea7a0b0b83c3e170f83e0fa82c1c2c2c2c5c2c1c2c6c2c0c2c0c2c2c2c3c2c2c2c2c2c5c5c5c5c6c6c6c6c3e83c2c2c2c9c2c6c2c2c00000000000002729c2c2c2c2c2c2c2c2c8c4c8c4e8aaaa82c2c2c2c6c8c6c8c4c6c6c4ea8000000002729e9c2c2c2c2c2c2c2c2c5c4c5c4ea20ba17aaa82c2c2c2c5c5c5c5c4dec4ea800000000000282e85eaa81c5c2c2c2c2e03aa86c2c2c2c2c5c4c5c4eaaa82ea7a17aaaa86c6eaa89c2c2c2c2c5c5c5c5c4c6c6c4ea800000000000002729e9e9e0ba71b170b0b171f0b0b1b1717171782c2e0b20f83e0f83e005c5c5c5c6c6c2c01b0b0b1f171717171b1b1b1b0f89e0f0f0f27270f0f0f170b0b171f0b0b1b17171717a0b0b82ea783e0f83e0fa83c1c3c3c3c5c3c1c3c6c3c0c3c0c3c3c2c2c2c6c2c2c7c5c5c5c5c6c6c6c6c3e2783c3c3c3c3c9c3c6c3c3c000000000000f002729c1c1c1c1c0c0c0c0c0c0c0c0e0f83e0781e03a9e80c0c0c7c0c0c0c2c0c0c0c1c0c0c0c1c0c0ea030f031b1b1b1b0707070703030303031b0fa0f0303031b031b0303000000000000006ca7a7a7a7a7a7a707031383e9e9ca7a7a70713030f88f070707070303030303030303aaaaaa203a9c1c1c1c1c0c0c0c0ea80000000000001c1c1c1ea0ba87ea07a81c0c0c0c0c0c0c0c0e80eaaaaaaa80ea71b1b1b1b07070707a1b1baaa1b03030303aa000000000000006ca7171717171b1b17171717171717171b1b1b271b27171717171b1b1b1b1b271b270000000009ca703030b03030303070707070303130b0b0b0b02c2c4e9c1c1c1c1c1c1c0c0c0c0c2c2c2c2c1c1c1c1c4c4c4c4c0000000000155555555554005c1c5c1c0c4c4c0c4c0c1c0c1c4c7c4c2c4c2c4c4c1c1c4c4c4c5c1c1c01313131307131307130303131384c3c4e130f0000000000000555555555555500171717171717171717171717000000005555555500041f002c007005c0000c00f020004 23 8388607 10 1023
def hc_71_1 : Nat → Nat := unpackHintV5 0xbb0425748062e80045cc010b8105d6fa022de4045a8850a8034529e98a210cb3cb9da65b4f0b2a63125cfe1f495c3dd0307b2020f340c1e48083a5090742020e74041cc8083750905406a857d41008a9c00d01001202002400000012 0x282e85eaa81c5c2c2c2c2e03aa86c2c2c2c2c5c4c5c4eaaa82ea7a17aaa882700000000000064dd555555555554001200088000b002c007005c013000c080f022000413031ba7031382c4c0c9c3769e9c4c7c172b0f00c0f43c6c5c2c2c5c7c2c2c7c5c5c5c5e0b0b82c83e0f83e0fa0001707171717171707130303130b0b0000000000000005555555555550004170b0b171f0b0b1f17171717a0b0b82ea783e0f83e0fa83c1c3c3c3c5c3c1c3c6c3c0c3c0c3c3c2c2c2c00000000000155555555555400107c00b001c017004c003003c0800f03c000f0000105c1c5c1c0c4c0c4c0c1c0c1cfc7cfc2cfc2cfc7c1c1c5c5c5c5c1c1c3c3c002aaa880ea00a00000000000005555555555550017071707031303130307030787ea0ba81ea17a83eaaaa80ea7aaa80000000000015555555555540011b07c00b001c017004c00302200200080800101c1c1c1c0c0c0c0c0c0c0c0e0f83e0781e03a9e80c0c0c7c0c0c0c2c0c0c0c1c0c0c0c1c0c0ea030f0300000000000055555555555500041f002c007001c003000c00f03c08800300c000304c000101c1c1c1cfc7cfc2cfc2cfc7c1c1c1c1c1c1c1c1c0c0c0c0c0c0c0c0c0c0c002aaaa800288000000000001555555555554001c1c1c1ea0ba87ea07a81c0c0c0c0c0c0c0c0e80eaaaaaaa80ea70000209c0000000155559375555555500041f002c007001c0800220000c0030203c08800108c8c8c8c0c4c0c4c0e031383e0f80e0f80e000000001555555540011b07c00b008c023004c003003c0800107c2c6e9c2c7c6c6c1c0e80c7c2c9c1b46e9e9c6c7c1c4c0f02c0f43c6c5c1c5c1c0c4c0c4c0c1c0c1e0f83e0f81e030380c1f0b0b1f0707171717170707a000030300000000000000055555555555500046c17071707031303130307030783e0f83e07a030380ea70f1f0f0b0f0b0f0f07070f170f0f0f170f0707a80c0c0c0000000000015555555555540011b07c00b001c017004c003003c0800f03c000f0000100c6c0c1c1c1c1c0c0c0c1c0c1c0c0c0c2c0e9c0c0c0c0c0c0c0c0c0c0c0c7c2c2c7c0e030f0380c0c1c1c1c1c0c0c0c0c6c2c2c6c0c0c0c6c0c6c0c0c1c1c1c1c0c0c0c0c0c6c6c6c6c6c00000000000001b29e9e9c0c6c 23 8388607 10 1023
def hc_71_2 : Nat → Nat := unpackHintV5 0xb87018b83010b7d018b7b008b6784eb63810b5f810b5d808b4d042acf9f6a26aa499025a8e3ab28322c67b29fe73b1de6902ac62e9865b71de5002dc48c9ce3d0af03c80223ba83633d1f62952a022f9961bb1d21509aa0b0a8006313600018c 0xa71f0ba7a7a70b1fa707031383e9c9c1f0b1b69e9e9e9e9e9c7c1c4c0c3e10b4070707070303030303030303aaaaaaa03a9c9c2701c0700c032207c2c2c7c1c1c1c1c1c1c1c1c0c0c0c0c0c0c0c0eaaa816406d1b41d0740d03664160416141c1c1c1ea0ba87ea07a81c0c0c0c0c0c0c0c0e80eaaaaaaa80ea71b1b1b0b1b0b1b1f0707070707070707a1b1baaaaa1b0303030303030303aaaa2709c0701c89c2800c0322151b46d0741d86d6940d03664005040c4c0c1c1c1c1c0c0c0c0c1c0c4c2c2c4c0c0c3c0c0c0c1c1c1c1c7c0b00c0c032701c0704c1304c2c2c2c2c4c0c0c4c1c1c1c1c4c1c4c4c4c4c40c1b42d030340c6d0741d1344d103040d03030303031f0723070707070303071313131303030303030f0707070713071705c031700c0c070701c5c1304c13130b130b130303130707070707071307071313131310306d1b40c6d030341c1d071b44d13440c10358c1cec1c0c4c0c4c4c0c1c4c0c1c4c4c4c4c1c4c4c1c4c0c4c0c4c4c9c2701c1704c4c032704c1304c7c4c2c4c2c4c4c1c1c4c1c4c4c4c8c4c8c1c1c4c4c4c4c3c4e1384c3c144d01b46d0746d131340c6d1344d11b0144c517171b1b171b1717171b1b1b1f270b1b0b271f170727231b2317071b271b031b031b1b0f2786e270f2709c1705c1b09c2709c546d1b45d1b46d1b46d1b4005046c4c0001c1c1c1c1c1c1c1c1c1c1c1c030b0303030003030030303031f0b0b1f3b8ec3cee3b0f070707070303030300000000000055555555555500031b03070707070303030703070303030b03a703030303030303030303031f0b0b1f0380c3c0e0303070707070303030300000000000055555555555500041f07c00b02c00300c000300007001c003000c00f0200040b0b03070300c2c0c4c0c4c2c2c2c2c4c8c4c8c4c0c0c4c00000001555555540011b02c00b008c023004c003003c0800102c1c2c1c0c0c03030b030703070003030070717171717070713130000b0b0b0b07171307130303131390c3c4e430f000000000000555555555555000b070b07030b03a703030b0b03071703170703030307070b170b0b0b170b07070b1b0b0b0b0b0b07171307130303130b82c3c2e0b0b00000000000055555555555500046c0b002c007005c01304c00300c00b02c000b0000f0200040b0b0000707070707070707070707070303000030300c0c0c0c0d0e430f4390c3c2c2c2c2c1c1c1c1c0c0c0c0c000000000001555555555554000c0c2c0c1c0c0c0c0c0c1c1c1c1c1c0c0c0c0c0c0c0c0c2c0e9c0c0c1c0c0c0c0e03030380c3c2c2c2c2c1c1c1c1c0c0c0c0c0309c000000000001034dd55555555555400100c0000c030002c1f002c0b001c007000c000c03003c0800129c4c3e1ba70f1381344c6c5c1c2c1c0c0c2c2c0c2c0e9c03070307030300007071717171707070b0b000130b0b1f07171307130303131383c4e0f00000000000055555555555500046c17070b0703030b0b030b03a70307030703030307071317171707070b0b0b130b0b1f07171307130303131384c3c4e130f00000000000055555555555500046c1f002c007005c013000c01304c001b0000f0200040f0f000170b0b1717171707171717071f0b0b133f0313133f0313131713171320ba80282aaa8000000000001555555555554020f85c2c2c5ea0785e87c2c2c4ea1b80e85c4c5c4e0ba9eaaaaaaa00000000000055555555555500041f002c0880080001c017004c003020200040b0b0b0b0b0b0b0b17171717882e0f83e0f83c02805c1c5c5c5c5c5c1d0c4d0c0d0c0d0c4c3c3c000000000000001555555555554002c2c2c2c2c2c2c2c5c5c5c5e0ba9e82c2e0f0f85c3e0f83ea0b070b0b0b170b070b1b0b030b030b0b0b0f0b00000000000055555555555500040b002c007005c013000c00f03c08800b02c000b0000102c2c2c2c2c2c2c2c8c4c8c4e8aaaa8000000015555555400102c00b008c023004c003020200040b0b00017171707171717070b0b0b0b3f0313133f0313130b0b0b0b17131713a000a2aaaa00000000000055555555555500 24 16777215 10 1023
def hc_71_3 : Nat → Nat := unpackHintV5 0x8d2c8fa28e17a8195149f1629e7455009bce28e67150499c000a66f00219b700a66800b999c008667000197b04260c0a5962b40a5300b5927b48a45fc7e10232b83bcc980d153bc30807a8c140182c388309b12ba22449006943fa15b094035b42207a8b880003d4 0x4f073b070313031303070307131f130b130b13130707131313230707544c4c4c4c1c4c4c1c4c0c0c4c4e130f1384c3c9c2701c1704c4c032704c4c04c9c04c1315555555514154513c5d3c5ccccc5ccd3c5c5d3d3c5ccccc9c2705c1709c2709c271555555541a75047d50b541d52355503543d5952740070707070b07a70b0b07070b0b0b070b071b07031b1b07031b1b0717070723071f0b0b1f1f87c3c7e1f0f0717231707171b07071b1b1f0b0b0b0b1f1f1b1f1b1b1f1f274b1b1f1b1b1f1f1f1f0707171723231717070717071b27070307031b631b0f2786e270f1702c17170171700701701701c1705c546d0b46c6d46c6d41d45d46d0746d1b4005045c2c2c1c2c1c2c1c2c1c2c1c1c1c1c2c2c2c2c1c5c5c1c6c1c1c6c2c0b01c1705c0705c1702c2c1c1c2c1c2c2c1c1c5c5c5c5c1c1c6c4c1c0c1c0c6c4cbc3dde778bc3c142d00b42d0745d1b41d1b46d10b0142c50707070b0b170b0b0707070b07a707030b0b07030b1b070b070b070707070b82c2c2e0b0f0b0b0b0b071717071b07071b0b0b1b1b0b0b0b0b0b0b0b0b0b0b270b0b0b0b0b0b0b0b07071717171707071b27070307031b3b1b0f2786e270f0b1700b0b00b02c0705c1701c1705c542c6d42c2d42d0b41d1746d0746d1b4005045c1c1c1c1c0c0c0c0c0c0c0c0c7c2c2c7c1c1c1c1c0c0c0c0c7c0b01c0700c0309c2706c4c2c2c2c2c6c4c1c1c1c1c1c1c1c1c0c0c0c0c0c0c0c0cec3cee3b8ec3c140d01b42d0741d0340d1b46d1030140c5031b03070707070303030703070303030b03a703030303030303030303031f0b0b1f0380c3c0e030307070707030303031b1b0b0b0b0b1b1f0303030303031b03031b1b030303030707070707070707030303030303030303031b1b0f1b86e1b0f1f02c03030032700701c0300c2709c546d0b40c0d40c6d41d0740d0346d1b4005043ea783c0c6c9c0f86da70f1f0b072b1b031901c1c1c1c0c0c0c0c0c2c0c0c1c0c0c0c2c2c2c2c1c1c1c1c0c0c0c0c2c0b01c0700c0309c2702c2c2c2c2c2c2c2c1c1c1c1c1c1c1c1c0c0c0c0c0c0c0c0c3e83c140d00b42d0741d0340d1b46d050304140c503030b03070303030303070707070703030303030303030b03a70303070303030380c0c0e030f0b0b0b0b070707070303030303031b1b030303030303030303031b0b0b0b0b0b0b0b0b070707070707070703030303030303031b0f1b86e1b0f03270030300b02c0701c0300c2709c540c6d40c0d42d0b41d0740d0346d1b4005041c8c1c1c1c1c0c0c0c0c0c0c0c0cacacacac1c1c1c1c0c0c0c0c5c1701c1c071700c0305c170ac7cac2cac2cac7c1c1c1c1c1c1c1c6c4c1c1c0c0c0c0c0c0c0c0cbc3d8e638bc3c140d01b46d070741c6d0340d1b46d1030140c50303030b0303031f07230707070703030703031b03030303030303030303030703a72b2b2b2b0380c0c0e030f070707072307030303031b1b1b0b1b0b1b1f03031b1b030303030303030303031b07070707070707071b1b0707030303030303030303031b1b0f1b86e1b0f1705c0317003030070701c5c0300c1705c546d1b40c6d40c0d41c1d071b40d0346d1b4005045c7c2c2c5c7c2c2c4c5c4cac4eaaaaa87c0b05c1704c272207c3c2c2c2c2c3c3c5c1cac8cac8c5c1c4c4d1c0d1c0c4c4eaaa816406d0b45d1b44d1b6646016160f87c2c2c5ea0788e87c2c2c4ea1b80e85c4cac4e0ba9eaaaaaaa1b1f0b0b0b0b1f1faaa27a1b1baa170727231b23170713131b031b031313aaaaa270f1f02ca089c05c1704c2722151b42da586d45d1b44d1b664005042c2c2c2c2c2c2c2c5c6cac5e0b0b82c2e0f0f8ac3e0f83c2c0b05c1706c2703c80b0ba0b82c2c5c1cac8cac8c5c1c6c4d5c0d5c0c6c4c3c3ea83c3c142d00b42d1746d1b46d0f6442c050b142c2c2c2c2c2c2c2c5c6cac5e0ba9e82c2e0f0f8ac3e0f83ea0b070b0b0b230b070b1b0b030b030b0b0b0f0b0b0b0b0b0b0b0b0b170727231b2317071b131b031b031b130f0faa0f0f0b0b0b0b0b0b270b0b1b1b0b0b0b0b0b02c1705c1b09c0f202c2c02c9c150b42d1746d1b46d0f642c2d42c6d4005042c2c2c2c2c2c2c2c8c4c8c4eaaaaa82c2c2c2c2c2c2c2c6c8c8c8c6c8c8c8c4c4c6c0c6c0c4c4eaaa82c0b08c2304c2722150b42d1b46d1346d99001411303130b0b0b0b0b0b0b0b17132b13aa82e8aeaaa0b02c1705c1309c880b0b0b0b0b0b0b0b17072b232b2317071313037b031313aaaa05900b42d1746d1346d9905810585a0ba23aaa07170b0b0b0b80eaa1b0b0b0b0b17132b13aaaa0ba9e8aeaaaa1b1baaaaa270b0b0b0b0b0b0b0b170727231b23170713131b031b031313aaaa89c2802c0b05c1704c27221586d6942d0b45d1b44d1b664005047c2c2c5c7c2c2c6c5c6cac5e0b83e0f83e0f83c7c0b05c1706c2703c81f82c2c2c2e85c1cac8cac8c5c1c6c4d1c0d1c0c6c4c3c2ea82c2c143d01b42d1746d1b46d0f6443c050f147c2c2c5c7c2c2c6c5c6cac5e82c2e0ba9e0f83e0f83ea0f070f0f0f230f070f1b0f030f030f0f0b0b0b1b1f0b0b0b0b1f1f170727231b2317071b131b031b031b130f0fa27a83c3c3c3c3c3c3c3c3c3c9c3c3c6c6c3c3c3c3c7c0b05c1706c2703c80f0f03c03c3c9c9c151b42d1746d1b46d0f643c3d0f50f0f1b1b500141172307170717071b071b0707070783e0f83e0781e0f1705c0705c1701c0f20ac7cac2cac2cac7c1c1e85e07071b13070307031b130f07aa0707050f406d1b41d1746d0743d910f0143c5172307170717071b071b0707070783c3e2b0f81ea7a070781e0f0f1f0f0b0f0b0f0fa83c6c1c0c1c0c3c3c1c1c1c6c7c9c2c6c2c9c7c1c1c5c5c5c5c1c1c6c4c1c0c1c0c6c4c3c3e89ea0f0f0f0f0f0f0f0f0f0f270f0f1b1b0f0f0f0f1705c0705c1701c0f203c3c0f00f0f17270546d1b41d1746d0743d90f0f43d43c3c6c6d4005045ea0ba87c5c1c5c1e83c1c4c1c4e03aa86c1c5c1c1c8c1e8aeaaaaa07a9ea86c7c9c2c6c2c9c7e86c6eaaaa89cbc1c1c5c5c5c5c1c1c4c4c1c0c1c0c4c4eaaaa89c3c5c172170a00705c1301c88546d1b61b5a50745d1341d99001411707070707030303030303030383e0f81e0780ea7a0303031f0303030b03030307030303070303a80c3c0c6c6c6c2c6c2c6c7c1c1c1c1c1c1c1c1c0c0c0c0c0c0c0c0c0c0c6c4c3c3ea83c3c0c0c0c0c0c0c6c4c0c0c6c4c0c0c0c0c9c2701c0700c0303c80303003270546d1b41d0740d0343d903035031b500141 26 67108863 11 2047
def hc_71_4 : Nat → Nat := unpackHintV5 0x86550d4012c61f2b378f1320a74c0f6379eb09b1b2d0d1d9c064911730587c16c958cab62ba5230e0270086126147c8d217a42650b1e44bb8e15434644b182eacde154c8289b03d8427ac21e6cb40d767005a445c2561f00d256303d8ae810c380000218 0xb0b0000707070707070707070707070303000030300c0c0c0c0d7e5f0f5f97c3c2c2c2c2c1c1c1c1c0c0c0c0c0000000000006c6d40c0d42d0b41d0740d0346d1b41000c0c2c0c1c0c0c0c0c0c1c1c1c1c1c0c0c0c0c0c0c0c0c2c0e9c0c0c1c0c0c0c0e03030380c3c2c2c2c2c1c1c1c1c0c0c0c0c000000000000030000300c000b002c007001c003000c00f020000c0c6c6d40c0d0350b42d0741d0340d1b46d069c0006c3c3c0005c2c2c5c5c5c5c1c5c5c5c1c7c2c2c4cfc0c4c4cfc0c4c4c5c4c5c4ca80282aaa80000000000006d0b6946c6d45d1744d1b664020f85c2c2c5ea0785e87c2c2c4ea1b80e85c4c5c4e0ba9eaaaaaaa00000000000007c00b02200200007005c013000c0808001b42da586d45d1744d1b6641a7000270b0b0b0b0b0b0b0b17171717882e0f83e0f83c02805c1c5c5c5c5c5c1c6c4d5c0d5c0c6c4c3c3c0000000000000002d0b45d1746d1b43d90b0b51b1b5000b0b0b0b0b0b0b0b1717171782ea7a0b0b83c3e170f83e0fa82c1c2c2c2c5c2c1c2c6c2c0c2c0c2c2c2c3c2c0000000000000b002c007005c013000c00f02002c0b0002c00002d0b45d1746d1b43d90b0b50b1b5069c0009c2c2c2c2c2c2c2c2c8c4c8c4e8aaaa8000000000b002c023008c013000c0808000b42d1b46d1346d99069c0009c2c2c0005c5c5c1c5c5c5c1c2c2c2c2cfc0c4c4cfc0c4c4c2c2c2c2c5c4c5c4e80028aaaa80000000000006c6d6942d0b45d1744d1b66410282e85eaa81c5c2c2c2c2e03aa86c2c2c2c2c5c4c5c4eaaa82ea7a17aaa8000000000000800220002c00b001c017004c003020200286c6d69942d0b45d1744d1b6641a700027170b0b171f0b0b1b1717171782e20f83e0f83e80005c1c5c5c5c5c5c1c6c4d1c0d1c0c6c4c2c2c0000000000000006d0b45d1746d1b43d90f0f51b1b5000170b0b171f0b0b1b17171717a0b0b82ea783e0f83e0fa83c1c3c3c3c5c3c1c3c6c3c0c3c0c3c3c2c2c2c000000000000f09c01f002c007005c013000c00f02003c0f0003c00006d0b45d1746d1b43d90f0f50f1b5069c0009c1c1c1c1c0c0c0c0c0c0c0c0e0f83e0781e03a9e80c0c0c7c0c0c0c2c0c0c0c1c0c0c0c1c0c0ea030f0300000000000007c00b001c007000c003003c0800300c000304c0001b46d0741d0340d0f640c0d40c6d41a70001b070707073f1f3f0b3f0b3f1f070707070707070703030303030303030303000aaaaa000a20000000000001b46d0741d1b1b5a50340d9904007070707a82ea1fa81ea070303030303030303a03aaaaaaaa03a9c0000000000001f002c007001c0800220000c00302020006d1b41d07686c6d69940d036641a70001b170717070313031303070307131f130b130b13130707131313170707004c4c4c4c1c4c4c1c4c0c0c4c4e130f1384c3c00000000000006d1b41d1744c4d031b44c4d44c6d44d134005c5c5c5c6c6c5c5c5c5c5c5c5c5c6c6c000000001f002c007005c0000c00f020006d1b45d1746d1b46d1b41a7000271b1355507070707070707070707070740c0c0d540c0d40c0c0c0c7c2c2c7cee3b0f3b8ec3c1c1c1c1c0c0c0c0c7c0b00c0c06c6c01c0700c0309c271554151555554500c6c0c1c1c1c1c0c0c0c1c0c1c0c0c0c2c0e9c0c0c0c0c0c0c0c0c0c0c0c7c2c2c7c0e030f0380c0c1c1c1c1c0c0c0c0c7c0b00c0c00c9c01c0700c0309c2715555555555541a75047d50b540d035540d5541d507540d503543d5951b400b0b5550707070707070707070707070303555030340c0c0c0c0d0e430f4390c3c2c2c2c2c1c1c1c1c0c0c0c0c6c6c00c0c02c0b01c0700c0309c2715141555555541400c0c2c0c1c0c0c0c0c0c1c1c1c1c1c0c0c0c0c0c0c0c0c2c0e9c0c0c1c0c0c0c0e03030380c3c2c2c2c2c1c1c1c1c0c0c0c0c0c0c9c9c00c0c0300b02c0701c0300c2709c555555555555069d41035550340d550b542d507541d503540d50f56546d003c3d5547c2c2c5cac8c5c1cac8c5c1c7c2c2c4d4c0c4c4d4c0c4c4c5c4cac4da95696aaa87c0b2809c6c05c1704c27221554151555554520f87c2c2c5ea0788e87c2c2c4ea1b80e85c4cac4e0ba9eaaaaaaa1f02ca089c05c1704c272215555555555541a75047d50b56655655507548d513540d5959527400b0b0b0b0b0b0b0b172b2b17982e0f83e0f83d56945c1cac8cac8c5c1ccc4d0c0d0c0ccc4c3c3d5542c0b05c1709c2703c80b0b0271b0555555555054140b0b0b0b0b0b0b0b172b2b1782ea7a0b0b83c3e2b0f83e0fa82c1c2c2c2c8c2c1c2c6c2c0c2c0c2c2c2c3c2c2c0b05c1709c2703c80b0b00b270555555555555069d410b542d507548d513540d50f56542d0b5542d5549d002c2c2c2c2c2c2c2c8c4c8c4e9aaaa82c0b08c2304c27221555555541a75042d50b548d523544d5035656549d002c2d554ac8c5c1cac8c5c1c2c2c2c2d0c0c4c4d0c0c4c4c2c2c2c2c5c4cac4e95569aaaa89c6c2802c0b05c1704c2722151415555555414282e88eaa81c5c2c2c2c2e03aa86c2c2c2c2c5c4cac4eaaa82ea7a2baaaa89c9c28802c0b05c1704c272215555555555541a750655599550b542d507548d513540d5959527401f0b0b171f0b0b1f172b2b1782e60f83e0f83e95545c1cac8cac8c5c1ccc4d6c0d6c0ccc4c2c2d5547c0b05c1709c2703c80f0f0271b05555555550541541f0b0b171f0b0b1f172b2b17a0b0b82ea783e0f83e0fa83c1c3c3c3c8c3c1c3c6c3c0c3c0c3c3c2c2c2c7c0b05c1709c2703c80f0f00f2705555555555543d375069d411f542d507548d513540d50f56543d0f5543d5549d001c1c1c1c0c0c0c0c0c0c0c0e0f83e0781e03a9e80c0c0c7c0c0c0c2c0c0c0c1c0c0c0c1c0c0ea030f032709c0701c0300c0f200c0c00c9c15555555555541a75047d50b541d507540d503543d5950340d550344d551b4007070707531f530b530b531f070707070707070703030303030303030303555aaaaa555a62709c0701c1b1b0a00300c8855555450555505007070707a82ea1fa81ea070303030303030303a03aaaaaaaa03a9c9c2701c07289c9c28800c032215555555555541a75047d50b541d50756555995503540d595951b40 25 33554431 10 1023
def hc_71_5 : Nat → Nat := unpackHintV5 0xeb2021d5c023a54196f814ace542d80a702d70a95768deae901149e4d2554fa4a880894d01128605231c7c41014e77a298ee4041da8083b3008762010e960b9d1c043960366a0230b7473154c6722720a32b48c5045485dd0b0002ee 0xa793931f0b072b130341c1c1c1c0c0c0d030b03030703030382e81c1c1c1e03a0b0b0b0b0707070703030303555555555555503030b03070303030303070707070703030303030303030b03a7030307030303aaaa80eaaaaaa03270300c0c0c0b0b0b0b0707070703030303aa555555555555669d5401f0b0b171f1f17071f2317071f0b0b131f0313131f03131317132b13aaaaaaaaaa02ca70b0b00b0b0b1705c1309ca225555555555669c502c2c2c2c2c2c2c2c5c4c5c4eaaaaa80b29c00005c000002c01c017004c00302020015555559a700401100b02c2c2c2c2c2c8c4c8c4eaaaaa82c41f08c1309c88555555669c529c2c2c2c2c2c2c2c2c5c4cac4e285cacac5c4dcc4c2c2c40b170ac5c9c1309c1f2155555555455000b0b230b070b0b0b0b072f0b0b0b0b0b030b0b0b030b130b0b0b0b17132b13aaaa82eaaaaaa0b0b1f0b0b002ca7170ac5c9c1309c885555555555669c5529e9e2729c5c2c2c5c7c2c2c4c5c4c5c4eaaaaa8002c00002001f545c5c5c5c4c4e800005c2c2c5c7c2c2c4c5c4c5c4eaaaaa8000b29c00008001f007005c013000c080800555555669c0001410070707070303030303030303aaaaaaa000000ca7000007c00b001c007000c2020015555559a70040110a7a7a7a7a7a70703a9c9ca769e9c1c4ca704d93070707070303030303030303070707078a2709c0701c0303040329c4c8555555555154070707070303030b0303031f0303030703030307030303030303030302aaaaaaaa03aa89c2701c0700c0c4c0c0c00329e2155555555559a71542f2f2f2f13132f132f13aaaaaa2f2f2f2f1313aa555555669d540c0c2c0c0c0c0c1c1c1c1c0c0c4c2c2c2c2d0b0b13a707070707070780c0e030f82e0b81e0780e0f030303030b0b0b0b07070707131313130fa0f55555555555552f072f07031313031303070307131f130b130b13130707131313230707560f83e0f81e030f83c3e83c3e83c3ccccccccc1cbcbc1c4c0c0c4c4c4c4c13271303e83d555555555555554bcbcbcbcbcbcbcbe0f83e0f83e0f83cbcbcbcbc3e83d5555555595547d50b541d52355503543d4549d151b1300007070707070707070707070700c0c0c000c0c00c0c0c0c7c2c2c7cee3b0f3b8ec3c1c1c1c1c0c0c0c0c0000000000006d0b40c0d46c6d41d0740d0346d1b4000c6c0c1c1c1c1c0c0c0c1c0c1c0c0c0c2c0e9c0c0c0c0c0c0c0c0c0c0c0c7c2c2c7c0e030f0380c0c1c1c1c1c0c0c0c0c0000000000001f002c00300c000300007001c003000c00f020006d0b40c0d40c6d41d0740d0346d1b41a70001b 23 8388607 10 1023
def hc_71_6 : Nat → Nat := unpackHintV5 0xc1361d80e06300c045fd810be405d7c0022f70045dd044ae335d3c480a390fe3c5ab267f430b127b1059731b11683560306a4020d180c1a100831b09c62e020c4c041878082f107842c6d842d0b0071fa00a01000c0200180000000c 0x2c2c8c2c1c2c2c2c2c1cbc2c2c2c2c2c0c2c2c2c0c2c4c2c2c2c2c5cacac5e0ba0b0ba0b0b0f0f82e0b83e0f83e0f0b0b1f0b0b002ca7170ac5c9c2709c0f210b4dd55555555555591442d5542d0b5542d50b541d52354cd503543d04549d270544c0c4e9c0c4e0f2704c0cdda7a7131f45cac3c103134170b0b171f0b0b1f1717171782e0f83e0f83e0f000b00000007c7d5545c1c5c5c5c5c5c1c4c0c0c4c3c3c000000155555555900014005c2c2c5c7c2c2c7c5c5c5c5e0b83e0f83e0f83c000b29c0000001f007005c013000c00f0200155555555900011047d50b541d51754cd503543d00000005040152f072f0703130313030703075f1f5f0b5f0b5f1f07072f232f230707055483e0f83e0780e0fa0f0fa0f0f2709c0705c40303031400c0c03c8555555555555142f072f070313031303070307131f130b130b13130707131313230707020f83e0f81e0383e83c3e83c3c9c2701c1700329c0c0c00c0c0c3c8555555555555644c511f542d507548d513540d51344d55135550f415270541c1c1c1c0c0c0c0c0c0c0c0e0f83e0781e0380c00000329c00001f002c007001c00300f0200155555555900011047d50b541d507540d503543d000049c0001413300541c1c1c1d9c7d9c2d9c2d9c7c1c1c1c1c1c1c1c1c0c0c0c0c0c0c0c0c15160f83e0781e80c0e83c3e0380c9c2701c0704c4c1400c40f21555555555554501c1c1c1c0c0c0c2c0c0c0c7c0c0c0c1c0c0c0c1c0c0c0c0c0c0c0c0c083e0f81e0780e80c0e80c0c3c3e0380c9c2701c0700c0c4c0c0c00329c3c8555540d375555555564511f542d507541d5035550340d5503540d50f41152749c1517171717031303130313031383e0f83e0f80e0f0000000055555555644c011f542d517545d513540d50f4000151f0b13a70b1f131307031383c9c1f0b1b44e9e9c4c7c1c4d0f042c4d05c1c5c1c0c4c0c4c0c1c0c1e0f83e0f81e0383c0000000c001f0b0b1f070717171717070713135550f0f000000055555555644c00050017071707031303130307030783e0f83e0780e0f00000000ca70007c00b001c2f005c004c03c080055555555644c0004411f542d507545d513540d50f400000014100540c4c0c1c1c1c1c0c0c0c1c0c1c0c0c0c2c0e9c0c0c0c0c0c0c0c0c0c0c0eaaaaaaaaaa87c2c2c7c0c0c0c03270301c1c1c1c0c0c0c0ea9555555555559a755a7a7039 23 8388607 10 1023
def hc_71_7 : Nat → Nat := unpackHintV5 0xbb824eafe2e8a76a1ea70818a6c810a66818a64808a52848a4e810a4a810a48808a368489ba9f09102aa8bd94a834226775afa7069bc67d2265b2b2a52d21645c3444538224460363b6a3e2fb2ee27c1fc1d1aaa1629bc0dc21a07b1840001ec 0x5c8c1c5c1c5c1c4c1c4c1c1c1c1ea0ba87ea17a81ea03a8ceaaaaa95002b00729c000082700000007c00b005c04c00302000880080f0220006d1b41d1744d07683e9592f0000501b1b0171f170b170b171717071707001c4c1c4c1c0c4c4c1c0c4c4c1c5c1c1c8c1ea0ba87eaa1788eaa1785ea17a81ea03a8ceaaaaaaaaa951705c5c9c0707070707001ca71301ca17270a20881b46d17175171b50745d1341da0fa564bc45c070707070303030303030303a82ea1fa81ea07a80e03a80e33aaaaaa5400000329c000000001f002c007001c00308330022002020006d1b41d0740d03683e959000106c07c2e9e9e9c2c7e9e9c1c0e80c7c2c9ca71b69e9e9e9e9c7c1c4c0f42e9c1343c1c1c1c1c0c0c0c0c0c0c0c0eaaaaa87c2c2c7c1c1c1c1c1c1c1c1e822a96689c2701c0700c0c200ca78813130a01b46d0741d0340da5990f0f50303511b01c1c1c1c0c0c0c2c0c0c0c7c0c0c0c1c0c0c0c1c0c0c0c0c0c0c0c0c0a82ea1fa81ea07aa80e03aa80ea80ea03aaaaaaaaaa549c2701c0700c0c4c0c0c00329e270a0881b46d0741d031b5030350340da0fa56446c2f2f13132f1313a82ea1fa88ea07a80eaaaaaaa54bcbc4c4e278a8aa1b46d1b46d1346da0fa5646d1b44c4d5541c1c1c1c1c1c1c1c1c1c1c1d030b03030355030350303030382e0fa0f0fa030381e0780e031f0b0b1f3b273b0ec9cec07070707030303030fa0f55555555555555031303070707070303030703070303030b03a7030303030303030303030382e0fa030fa030381e0780e031f0b0b1f03030300c9c0c07070707030303030fa0f55555555555565551f47d50b42d50340d550355507541d503540d50f515274542c2c0c1c0d030b0313031382e0b83e0f80e0f0b0b0b0b23232323130303130fa0f55555555644d550b542d523548d513540d50f515274542c1c2c1c0c0d03030b03070307550303507072b232b230707131355582e0b83e0780e0fa0f0fa0b0b0b0b0b0b072b2b07130303133327430cc9d0c0fa0f555555555555550b070b07030b03a703030b0b030713032b0703030307070b2f0b0b0b230b07070b130b82e0b83e0780e0fa0b0fa0b0b0b0b0b0b072b2b07130303130b0b0b02c9c2c0fa0f555555555555644d550b542d507548d51344d50340d50b42d550b5550f515274542c2d5541c1c1c1c1c1c1c1c1c1c1c1c0c0d5540c0d0303030303a0303a0f0f82e0b81e0780e0343274310c9d0c0b0b0b0b07070707030303030fa0f5555555555555503030b03070303030303070707070703030303030303030b03a703030703030380e80c0e80c0c3c3e0b82e0781e0380c0c9c0c03030302c2c2c2c1c1c1c1c0c0c0c0c3e83d034dd55555555555595540d5540d035542d1f542d0b541d507540d540d03543d4549d15a73309c4e9c33270f84d131f070b0703030b0b030b03a740c1c0c1c0c0d5541c1cac8cac8c1c1c2c2d5560b83e0f81e0383e83c3e83c3c7c2c2c7c1cacac1c4c0c0c4ccc9c332703e83d5555555555559135547c1c2c1c0c0c2c2c0c2c0e9c0c1c0c1c0c0c0c1c1c4c4c4c8c1c1c2c2c2e0b83e0f81e0383e83c3e83c3c7c2c2c7c1cacac1c4c0c0c4c4c4c4c13271303e83d5555555555559135547d50b541d523544d503544d135544d5543d4549d1505541f0b0b172b2317072b2317071f0b0b1f6f0333136f033313172b2b1782e0fa0f0fa0f0f83e0f83e0f40b0b0b1402c2c05c1709c2703c855555555555514007c2c2c5c7c7c5c1c7c8c5c1c7c2c2c7c7c0c7c4c7c0c7c4c5cacac5e0b83e83c3e83c3e0f83e0f83c0b29c2c2c02c2c2c5c1709c2703c855555555555564511f542d51f47d551f55507548d533540d50f415270542c2c2c2c2c2c2c2c5c5c5c5e0b82e0f83e0f83c00000001542c2d45c1c5c5c5c5c5c1d0c4d0c0d0c0d0c4c3c3c0000001555555500014002c2c2c2c2c2c2c2c5c5c5c5e0b82e0f83e0f83c0b29c00005c000002c01c017004c003003c080055555555640004410b542d507545d533540d50f400012700005040150b02c2c2c2c2c2c8c8c8c8e0b82e0f83e0f83c2c41f08c2709c0f215555555591442d50b548d52354cd503543d0549c1505452b2317072b2317070b0b0b0b43033313430333130b0b0b0b172b2b17a0b0ba0f0f82e0b83e0f83e0f1f1f0500b105c1709c2703c855555555555514 24 16777215 10 1023
def hc_71_8 : Nat → Nat := unpackHintV5 0xd511ead00144c33b32baa226aeeaeea692169acaf29aa00a9a80089a580a99b82899980899980098604e8fea1e8412f67b12406dfb4665e2065cb24c52ba7e4b09ec402ab838e9d030ba0c2aa9842a4818221a0c16d2d20fe1bc07322c0001cc 0x13c1cec1c0c4c0c4c0c1c0c1c4c7c4c2c4c2c4c4c1c1c4c4c4c8c1c1d5aaaaaaaaaaa33333333073333071303031313131304c9c4caa5555555555555554f2f4f2f13132f134f13aaaaaa2f4f4f2f1313aa555555669d55551f542d507548d5540d594549d15070707070b07a70b0b07070b0b0b070b07130703131307031313072f07072307a82ea1faa87e4baa87e1fa88e23a81e07a80ea63aaaaaaaaaaa547c2c2c5c7c7c5c1f271701c5c8c5c1cbc4c1c1c4e278a8aa1b42d1b1b51b1b50751b51341da0fa564bc5d1b42c2c1e070b070b070b07070707aaaaaaa0707aaa1f1faa1313070307031313a59a0b0b0b0b0717170713070713aa7727171dc9c5c0b42d0746d1341d990f0f50b0b51746d0707070b0b1f0b0b0707070b07a707030b0b07030b13070b070b07070707aa82e0baa82ea82ea0ba88ea07a80ea3baaaaaaaaaa542c9c2c0b0b0b02c2c2c2c1c5c5c1c4c1c1c4e278a8aa0b1b50b0b50b42d0746d1341da0fa564bc5d1b41c1c1c1e03030303030303aaaaaaaaa13130707070707070707a0303aaa59a1f0b0b1f0707070703030303aa3b273b0ec9cec1b42d0741d0340d990f0f5030351b46d031303070707070303030703070303030b03a70303030303030303030303a82ea1faa80eaa80e03a81ea07a80e03a80eaaaaaaaaaa547c2c2c7c0c0c0c03270301c1c1c1c0c0c0c0e278a8aa1b42d03035031b50741d0340da0fa5646d1b427a709c0e80c271b69c1f0b072b13030f49d0f0707070703030380c2c0c0c1c0c0c0eaaaaaa82c2ea81c1c1c1c1c1c1c1e80c0eaa96682c2c2c2c1c1c1c1c0c0c0c0ea89c2702d0b41d0740d03696643c3d40c0d46d1b40c0c2c0c1c0c0c0c0c0c1c1c1c1c1c0c0c0c0c0c0c0c0c2c0e9c0c0c1c0c0c0eaa0380eaa03aa0ba82ea07a81ea03a80eaaaaaaaaa9503270300c0c0c0b0b0b0b070707070303030389e2a2a80c6d40c0d42d0b41d0740d03683e9591b46d07230707070703030303030380eaaaaaa8ac7cac2cac2cac7ea0707aaaa0303aaa59a2b172b170707070703030303aa63271718c9c5c1b46d070741c6d0340d990f0f5030351746d0303030b0303031f07230707070703030703031303030303030303030303030703a7a82ea1faa80e03aa80eaa81eaa07a80e03a80eaaaaaaaaaaa54ac5cac5c0c9c0c03030301c1c1c1c8c1c0c0c0c0e278a8aa1b46d031b503035070741c6d0340da0fa564bc5d1b40c4c0c1c1c1c1c0c0c0c0c1c0eaaaaaaa0b0b0b0b130303130707070713079a1f0b0b1f030300c0c07070707aa131313131b42d030340c6d0741d990f40d1b46d03030303031f072307070707030307aaaaaaaa13130b130b130303130707070707a07079a2b172b17030300c0c070707072307aa131313131b46d031b40c0d070741c6d990f40d1746d63073b0703130313130307130307aaaaaaa131f130b130b1313070713071313132313230707aa9668cccccccc1ccccc1c4c0ccc0c4c4ea84c4c4c13271306d1b41d1b44c4d031b6643c3d44c3d46d1b47c2c2c5c7c2c2c4c5c4cac4eaaaaaa2a805c1cac8cac8c5c1c4c4d1c0d1c0c4c4e966a02c1705c1309c880b0b0a01b42d1746d1346d990f0f51b0f511b001f0b0b171f1f17071f2317071f0b0b131f0313131f03131317132b13a82ea1faa87eaa87e1fa88ea07a80ea33aaaaaaaaaa540b29c2c2c02c2c2c5c1704c27289c9c2882206d0b46c6d46c6d45d1b44d1b683e95911b02c2c2c2c2c2c2c2c5c4c5c4eaaaaaa82c2ea85c1c5c5c5c5c5c1c4c4cfc0cfc0c4c4c14000b0000170000000002d0b45d1744d1b6443c3c000002c2c2c2c2c2c2c2c5c4c5c4ea0ba82ea17a81ea03a8ceaaaaa9502ca70000170000000000b007005c013000c080022002020002d0b45d1744d1b683e959000106c02c0b0b0b0b0b0b23132313a82ea0ba88ea23a80ea33aaaaaa542c81f08c1309c89c282202d0b46d1b44d1b683e95911b04c0c4c2c2c2c2c2c2c2c2c5c4cac4eaaaaaa82285c1cac8cac8c5c1c4c4c0dcc0c4c4e96682c2c80b170ac5c9c1309c881f1f0a00b42d1746d1346da5990f0f50b0b511b000b0b230b070b0b0b0b072f0b0b0b0b0b030b0b0b030b130b0b0b0b17132b13aa82e0baa82ea82ea0ba88ea07a80ea33aaaaaaaaaa542c2c7c2c2c00b29c5c2b172704c272270a0880b1b50b0b50b42d1746d1346da0fa56446c170b0b171f0b0b1317131713aaaaaaaaa1f1f170717171717170713133f033f03131305000000000000001b42d1745d1346d910f0f00000170b0b171f0b0b1317131713a82ea1fa85ea07a80ea33aaaaaa54000b29c000082700000007c01c017004c00302000880080f0220006d0b45d1744d1b683e9590000501b1b01723071707170713071307070707aaaaaa2b1f2b0b2b0b2b1fa1717aa131307030703131305000000000000001b46d0745d1341d910f0f00000 24 16777215 10 1023
def hc_71_9 : Nat → Nat := unpackHintV5 0x9254a4a27f42c84f0a1a01c2407908ed1d461f86facad9ad123466bc9117b43f65ad87f15592ba4ffcad12dd24443d8f38fdf22e3be0738da82a032fc748b5d2c42a206a895326a223463079b1e41bb45706161ae130ca983fb1900c1c7a02161e204fc6b800027e 0xb0b0b0b0b0b0b0b07070707070707070707070703030303030303030303030303030303a036960b82e0781e0380d4c9d4c53275302c2c2c2c1c1c1c1c0c0c0c0c3e83e940e50b42d0741d0340d035946d1b40c0c2c0c1c0c0c0c0c0c1c1c1c1c1c0c0c0c0c0c0c0c0c2c0e9c0c0c1c0c0c0e80c0e80c3e0b82e0781e0380c0c0c3c0c0c0c0c0c0c0c0c0c0c3c3c2c2c2c2c2c2c2c2c1c1c1c1c1c1c1c1c0c0c0c0c0c0c0c0d503270300c0c0c0b0b0b0b07070707030303030fa0f0f0f0f03c9c3c03031b1b5030340d42d0b41d0740d0359a7a5a86d1b4bc1cbc1c0c4c0c4c0c1c0c1c4c7c4c2c4c2c4c4c1c1c4c4c4c8c1c1c3c3c3e0f83e0f81e030f83c3e83da533333333072f2f071303031313131304c9c4c0fa0f1b46d0746d131340c6da513943d91b46d0b0b00b0b0f0ac8c5c1cac8c5c1c7c2c2c5d1c0c6c4d1c0c6c4c7c2c2c6c5c6cac5e9683d82e0f83e0f83e0f0f0b00b0b00f02c1705c1b09c0f206e5a51b42d1746d1b46d0f6446c007c2c2c5c7c7c5c1c7c8c5c1c7c2c2c6c7c0c6c4c7c0c6c4c5c6cac5e0b83e83c3e83c3e0f83e0f83c3c7c2c2c2c2c3c3c3c7c3c7c3c3c3c3c3c7c3c3c3c3c3c3c1c3c3c3c8c3c1c3ccc3c0c3c0c3c3d502ca70b0b00b0b0b1705c1b09c0f203c3c03c9c06d0b46c6d46c6d45d1b46d1b59a7a5a846c0b0b0b0b0b0b0b0b171717170b0b0b0b0b0b0b0b17071717171717071b13530353031b1382e0b83e0f83e0f05000000000000000b42d1745d1b46d00a019000b0b0b0b0b0b0b0b1717171782e0b83e0f83e0f0b0b0b0b0b0b0b0b0f070f0f0f170f070f330f030f030f0f540b29c00005c0000000002c01c017004c003003c0800f03c000f00000b42d1745d1b46d669e96a000106c02c0b0b0b0b0b0b231b231b82e0b83e0f83e0f0b0b0b0b0b0b0b0b0f230f0f0f230f0f0f330f030f030f0f542c0b07c2306c2703c80f0f00f2700b42d1b46d1b46d669e96a11b02c2c02c0b0b0b0b0b0b2b2317072b2317070b0b0b0b53031b1353031b13171b2b1782e0ba0b6960f83e0f83c2c0b07c7c03c3c05c1706c2703c80b42da50b945d1b46d1b42d6511b000b0b230b070b0b0b0b072f0b0b0b0b0b030b0b0b030b130b0b0b0b171b2b17a0b0ba0b0f82e0b83e0f83e0f0b0b0f0b0b0b0b0b0b0b0b0b0b0f0f0b0b0b0b0b0b0b0b0f070f0f0f230f070f330f030f030f0f542c2c7c2c2c00b29c5c2b172706c2703c80f0f00f2700b0b1b1b50b0b42d42d0b45d1b46d1b59a7a5a846c170b0b171f0b0b1b171717171f1f0b0b0b0b0f0f17071717171717071b13470347031b1382e0f83e0f83e0f05000000000000001b42d1745d1b46d00a01a900170b0b171f0b0b1b1717171782e0f83e0f83e0f0f1f0b0b0b0b0f0f0f070f0f0f170f070f330f030f030f0f54000b29c00000000001f007005c013000c00f03c08800f03c000f00001b42d1745d1b46d669e96a000106c01c1c1c1c0c0c0c0c0c0c0c0e0f83e0781e0380c3c7c3c2c3c2c3c3c1c1c1c1c1c1c1c1c0c0c0c0c0c0c0c0d5000000ca70000000007c00b001c007000c03c0800f03c000f0cc0001b46d0741d0340d669e96a000106c01c1c1c1c0c0c0c0c0c0c0c0d4c7d4c2d4c2d4c7c1c1c1c1c1c1c1c1c0c0c00c030383e0f81e0780e03a036949c2701c0700c0304c4c03c3c03c81b46d0741d0340da503940d6511b01c1c1c1c0c0c0c2c0c0c0c7c0c0c0c1c0c0c0c1c0c0c0c0c0c0c0c0c083e0f81e07a0303a030f80e030f1f0f0b0f0b0f0f070707070707070703030f030303030303030303030f0f0303030303030303549c2701c0700c0c4c0c0c00329c3c80f0f00f2701b46d0741d03031b1b5030340d40d0359a7a5a846c2f2f2f2f1b1b2f1b2f1b83e0f83e0f83e0f0f1f0f0b0f0b0f0f0f070f0f0f230f070f0f030f030f0f54bcbcbcbc6c6c3e83c3c3c3c0f270f06d1b46d1b46d1b59a7a5a86d1b44c4d5541c1c1c1c1c1c1c1c1c1c1c1d030303550303503030303aaaaaaaaaa1f0b0b1f3b273b0ec9cec0707070703030303aa55555555555555031303070707070303030703070303030b03a70303030303030303030303aaaaaaaaaa1f0b0b1f03030300c9c0c0707070703030303aa5555555555669d55551f542d50340d550355507541d503540d594549d150b0b5550707070707070707070707070303555030340c0c0c0c0eaaaaaaaaa90c9d0c43274302c2c2c2c1c1c1c1c0c0c0c0ea95555555555955540c0c2c0c1c0c0c0c0c0c1c1c1c1c1c0c0c0c0c0c0c0c0c2c0e9c0c0c1c0c0c0eaaaa0383eaaaaa80c9c0c03030302c2c2c2c1c1c1c1c0c0c0c0ea955555555559a7555540d5540d035542d50b541d507540d503565152745415507c2c2c5cac8c5c1cac8c5c1c7c2c2c4d5c0c4c4d5c0c4c4c5c4cac4eaaaaaaaaa902c500b0b01705c1309c8855555555555514007c2c2c5c7c7c5c1c7c8c5c1c7c2c2c4c7c0c4c4c7c0c4c4c5c4cac4eaaaaaaaaa80b29c2c2c02c2c2c5c1704c2722155555555559a7551447d50b547d1f5547d5541d52354cd50356415270542c2c2c2c2c2c2c2c5c4c5c4eaaaaa800000001542c2d45c1c5c5c5c5c5c1c4c4cfc0cfc0c4c4c02800001555555140014002c2c2c2c2c2c2c2c5c4c5c4eaaaaa80b29c00005c000002c01c017004c00302020015555559a75500011042d50b541d51754cd50356400000014100542c0b0b0b0b0b0b23132313aaaaaa0b107c2304c272215555559a7551442d50b548d52354cd50356415270541514ac8c5c1cac8c5c1c2c2c2c2d0c0c4c4d0c0c4c4c2c2c2c2c5c4cac4eaaaaaaaaa87c7c1402c41705c1309c88555555555565514002c2c8c2c1c2c2c2c2c1cbc2c2c2c2c2c0c2c2c2c0c2c4c2c2c2c2c5c4cac4eaaaa0b83eaaaaa82c2c7c2c2c00b29c5c2b172704c2722155555555559a7551442d5542d0b5542d50b541d52354cd50356415270545c2c2c5c7c2c2c4c5c4c5c4eaaaaa8000000007c7d5545c1c5c5c5c5c5c1c4c4cfc0cfc0c4c4c028000015555554540014005c2c2c5c7c2c2c4c5c4c5c4eaaaaa8000b29c0000001f007005c013000c080800555555669d5400014137047d50b541d51754cd50356400000014100541c1c1c1c0c0c0c0c0c0c0c0eaaaaa800000329c00001f002c007001c003080800555555669d540004411f542d507541d503540d590000000504cc01507070707571f570b570b571f070707070707070703030303030303030545aaaaaaaaaa2709c0701c13130500312215555555555954501c1c1c1c0c0c0c2c0c0c0c7c0c0c0c1c0c0c0c1c0c0c0c0c0c0c0c0c0aaaaaaaa80e0faa2709c0701c0303130303000ca7885555555555669d54511f542d507541d5035550340d5503540d590549c15 26 67108863 11 2047
def hc_71_10 : Nat → Nat := unpackHintV5 0xb5c08c57487329b83d93692e691d12f449c899f34634f890227319263394bf17f23b0acc25a55d81126fc7e113c48489201844700422080610fc01085704e429804213c02109601082d03c3a90db191c858b262d04df1682178b00d2073840251c000402 0x70707070303030303030303070707079a0000000001b46d0741d0303510369c4d9000070707070303030b0303031f0303030703030307030303030303030356aaaaaaaa03aa800000000008a71b46d0741d0303130303540da799000070707070303030303030303571f570b570b571f0707070707070707050083e0f81e0780e03a0303a0f0f0000000000001b46d0741d03444c4c0003d900070707070303030b0303031f03030307030303070303030303030303560f83e0781e03a0303a03030f0f80e03000000c2700000000201f002c007001c0030000300c0003000c00f001b46d0741d0303130303540da70f640001406c6c01c1c1c1c0c0c0c2c0c0c0c7c0c0c0c1c0c0c0c1c0c0c0c0c0c0c0c0d5070707070380c0c0e030f030303030707070703270300c0c0c030303031b46d0741d0303370303540da71b46d1b46d0b070b07030b030b03070307a682e0f81e0383d56941c1cac8cac8c1c1c4c4c0c0c0c0c2c2c3c3d5542c2c2c2c1cacac1c4c0c0c4c3e83ccc9cec33273b1555555555555542c1c2c1c0c2c0c2c0c1c0c1e0ba9e82c2e0f0f84c1e0383ea07070b0b0b2307070b13030303030b0b0b0f0b0b0b0b0b072b2b07130303130fa0f0b0b0b02c9c2c55555540da75555555542d50b541d2f548d2b544d43d0f566542d0b5542d554549d15a73309e9c7c1c2c1c0c2c0c4c0c1c0c1e82c2e0ba9d83e0780e0fa55507072b232b2307071313030303030f0f0b0b5551f0b0b1f072b2b07130303130fa0f33270cc9e7c55555540da75555555547c1c2c1c0c2c0c4c0c1c0c1e82c2e0ba9e0f81e0383ea07070f0f0f2307070f13030303030f0f0b0b0b1f0b0b1f072b2b07130303130fa0f0f0f0f03c9c3c55555540da75555555547d50b541d2f548d2b544d43d5950f43d550f55515274542c1c2c1c0c2c0c2c0c1c0c1c2c2c2c2c1c5c4c1c4c0c0c4c000000001542c2d41c1c5c5c5c5c1c1c4c4c000ec3c4e138ec3c0001555551540014002c1c2c1c0c2c0c2c0c1c0c1c2c2c2c2c1c5c4c1c4c0c0c4c0b29c00005c000002c01c017004c003003c080055555540da75500011042d50b541d17545d2b54cd43d5940001270000504015a7130fa9c5c1c2c1c0c2c0c4c0c1c0c1c4c2c2c7c1c5c4c1c4c0c0c4c000b29c0000001f1f555070717171717070713130000f1384e9b0f000055555540da71540014005c1c2c1c0c2c0c4c0c1c0c1c4c2c2c7c1c5c4c1c4c0c0c4c000b29c0000001f007005c013000c00f020015555550369d540004411f542d50745d5174ad53350f5650000000504015131f0ba7130b1f1307031383c9c131f0b1b69e9c4c4c7c1c4c0f442d05c1c5c1c0c4c0c4c0c1c0c1e0f83e0f81e0383c0000000081307c2c2c7c1c1c5c5c5c5c1c1c4c4c0003c3d55400015555540c5500050017071707031303130307030783e0f83e0780e0f00000000204c1f002c007005c013000c00f0055555540da75500011047d50b541d17545d544d43d59400000014100541c1c1c1c0c1c0c1c0c1c0c1c4cbc4cbc1c1c1c1c1c0c0c1c5c5c5c5c1c1c1c1c1c0c0c1c5c4c4c5d55555555548c8c8c8c0c4c0c4c0c4c0c4e0f83e0f83e0383c0000000081307c00b008c023004c003003c01555551540004408c8c8c8c0c4c0c4c0c4c0c4c4cac4cac4c8c4c8c4c0c0c4cacacacac8c8c8c8c4c0c0c4ccc4c4d55555555553c1d3c1c0c4c0c4c0c1c0c1c4c4c1d3c4c1c4c0c0c4ccccc1d3ccc1c4c0c0c4ccc4c4d5555550369d55551f542d5075523553750f5654549d1513130b0b0b0b0f0f0707070707070707070707070303030303030303030303030303030382e0fa5a0360781e0380c7c2c2c7cec9cec3b273b01c1c1c1c0c0c0c0c3e83c6d0b40e5a50741d0340d03646d1b40c4c0c1c1c1c1c0c0c0c1c0c1c0c0c0c2c0e9c0c0c0c0c0c0c0c0c0c0c0e0b83e80c3e80c0e0781e0380c3c7c2c2c2c2c3c3c0c0c0c0c0c0c3c3c0c0c3c0c0c0c0c1c1c1c1c1c1c1c1c0c0c0c0c0c0c0c0d51f0b0b1f03030300c9c0c07070707030303030fa0f0f0f0f03c9c3c1b42d03035031b50741d0340d669e96a1b46d 25 33554431 11 2047
def hc_71_11 : Nat → Nat := unpackHintV5 0x91fa0e44908d9f565e4e7027673180d39300b99de574ada42a4e491120e8c78e304885313ce22d0d70c6c9f861e03030701017d80c0bdc0205a60902cb0101618080afc0205360901a31f0027155011804007c02003a00801b004007c0b8036010000036 0x707070707070707070707070303030b0303031f03030303031f0303030303031f031f030303070303030703030303030303030303030303030303547c2c2c7c7e1f0f1f87c3c1c1c1c1c0e03030380c3c0c0c0c0c0b29c2c2c02c2c2c1c0700c0c9c9c00c0c0300300c2709c1b42d1b1b51b1b50741d0303330303540da71b46d11b01c1c1c1c0c0c0c0c0c0c0c0c0c0c2c2c0c0c0c0c1c1c1c1c1c1c1c1c14002c2c2c2c1c1c1c1c0c0c0c0d6e5b0f5b96c3c0b0000070000000002d0b41d0740d11b130001b46d00070707070303030b0303030b03030307030303070303030303030303542c2c2c2c1c1c1c1c0e03030380c3c0c0c0c0c0b29c00001c0000000002c01c007000c0000c030000c003003c08000b42d0741d0303330303540da71b46d000106c01c07070303030b0303030b03030323030303230303030303030303542c2c2c2c8c8c8c8c0e03030380c3c0c0c0c0c2c0307c0700c9c00c0c00c0309c2702d0b46d1b40c0ccc0c0d50369c6d1b446c0f73a9c3dce07e9d1b070707070303030303030303030300300c0c1c1c1c1c1c1c1c1c0c0d40d03030b0b0b0b07070707030303039cc3dce0f0b0b00c0b0701c1c1c0300c1f1f0030302709c0b42d0741d030350340da71b1350b0b51b46d11b00070b0707070707070707070707070703030303030b030b03030303030b030303030b0303030b030303070303030703030303030303030303030303030303542e0b0b0b82c3c2c2c2c2c1c1c1c1c0e03030380c3c0c0c0c0c2c2c7c2c2c00b29c1c07070700c9c00c0c00c0309c2702c6d42c2d42d0b41d0740c0ccc0c0d50369c6d1b446c0707070703030303030303030303030303031f1f070707070707070705001f0b0b1f07070707030303034791c3d1e470f0000000000001b42d0741d03446c4c0006d1b4001c1c1c1c0c0c0c2c0c0c0c7c0c0c0c1c0c0c0c1c0c0c0c0c0c0c0c0d51f0b0b1f070707070380c0c0e030f030303030002ca70000c270000000007c01c007000c0000c030000c1b000c03003c08001b42d0741d0303330303540da71b46d0000501b1b00707070703030303030303033f1f3f0b3f0b3f1f0707070707070707030350340c0e0f83e0781e0380e80ca02709c0701c0300ca003800c201b46d0741d0340d131350f0f50f6446c070707070303030b0303031f03030307030303070303030303030303560f83e0781e80c0e80c3e0380c3c7c3c2c3c2c3c3c1c1c1c1c1c1c1c1c0c0c3c0c0c0c0c0c0c0c0c0c0c3c3c0c0c0c0c0c0c0c0c02709c0701c030327270030300c00c0308a7a0a86d1b41d0740c0c4c0c0d50369c3d90f0f50f1b511b01c1c1c1c0c0c0c0c0c0c0c0d7c7d7c2d7c2d7c7c1c1c1c1c1c1c1c1c1402aaaaaaaaa800000000008006d1b41d0740d113130009900070707070303030b0303031f0303030703030307030303030303030356aaaaaaaa0383ea800000000008a70007c00b001c007000c0000c030000c00302001b46d0741d0303130303540da799000106c07c2e9e9e9c2c7e9e9c1c0e80c7c2c9c1b69e9e9e9e9e9c7c1c4d0f02c0fa744c1c1c1c1c0c0c0c0c0c0c0c0eaaaaa87c2c2c7c1c1c1c1c1c1c1c1e966a82289c2701c0700c03282203c3c00c0c06d1b41d0740c0d640da79913135a511b01c1c1c1c0c0c0c2c0c0c0c7c0c0c0c1c0c0c0c1c0c0c0c0c0c0c0c0d5a82ea1fa81ea07aa80e03aa80ea80ea03aaaaaaaaaa009c2701c0700c9c00c0c00c03283e8081b46d0741d0303130303540da786d6966446ca7a7a7a7a7a70703a9c1b69e9e9c1c4d25e9d13 25 33554431 11 2047
def hc_71_12 : Nat → Nat := unpackHintV5 0x90b8c0a3301fc875caca09c2767e048d9e0130074ec631c0b2606a24c119112f05fc49017161b655e8ce14582444bf8ad120d1e243f887905814c3d30860e8319235c8888bf42fc2a74ab88944121df48b877001a1d640b863824212e4bf837228e051d15800028e 0x1c8c1c1c1c1c0c1c0c1c0c1c0c1cac7c4c2cac2c4c7c1c1c1c1c1c1c1c1d5132b132b07070707070303071384c3c4e130f002b00729c00000000001f002c007007000c01304c00330000f020006d1b41d0750369c0c0d40c0c0c6d13400041b017071707571f570b570b571f07071717171707070313031303070307050083e0f83e07a0f0fa0f0f80e0f0000000000001b46d0745d0003030103030343d900170717070313031303070307131f130b130b13130707131313170707560f83e0f81e0383e83c3e83c3c00000000000081307c00b001c017004c003004c130004c0003c006d1b41d1750369c0c0d40c0c0c3d9000106c01c1c0c4c0c4c0c1c0c1cdc7c4c2cdc2c4c7c1c1c4c8cdc8c1c1d51313071307130303131384c3c4e130f3333073307130303131327330cc9c4c3313131b46d0746d40da7030350303031b44d1b46d83e07070707a81e07a03030303a80e03a0303030382ea7aaaaaaa87c2c2c7ea22780707070703030303aa5555555540da755555547d50b56655646d5507541d5035959515274541c1c1c1c0c0c0c0c0c0c0c0e0ba9e82c2e070781c1e0380ea070707070707070703030303030303030b0f0b0b0b0b0b07070707030303030fa0f0b0b0b02c9c2c555540da7555555555542d50b541d507540d43d5950b42d550b46d5515274541c2c1c1c0c0c0c0c0c0c0c0e9aaaa82c2c2c2c8c8c8c8c0c0c0c0ea955550369d5555550b542d523548d50359595152745682e81eaa81c1c1c1c1c1e80c0eaa80c6c0c0c0c0c0c0c0c0eaaa82ea7a07aaaa278a80b0b0b0b0707070703030303aa5555555540da7555555646d5599550b542d507541d5035959515274541c1c1c1c0c0c0c0c0c0c0c0e82c2e0ba9e0781e0380ea070707070707070703030303030303030b0b0b1f0b0b1f07070707030303030fa0f0f0f0f03c9c3c555540da7555555543d1b55547d50b541d507540d43d5950f43d550f46d5515274540070707070707070707070707030303030303030303030303030303031f0b0b1f1f87c3c7e1f0f070707070303030302ca70b0b00b0b0b0701c0300c2709c5555555540da755551447d50b547d1b5547d1b5541d507540d43d59415270541c1c1c1c0c0c0c0c0c0c0c0c2c2c2c2c1c1c1c1c0c0c0c0c0b29c00001c000002c01c007000c003003c0800555540da7555500011042d50b541d507540d43d5940000001411b00541c070703030303030303030b0b0b0b23232323030303030b107c0700c0309c27155550369d5554510b542d523548d50350f5650549c15001c2c1c1c1c1c1c1c1c1c1c1c1c1c1c0c0c0c0c0c0c0c0c0c2c0c6c0c0c0c0c0c0c0c0c2e0b0b0b82c3c2c2c2c2c1c1c1c1c0c0c0c0c2c2c7c2c2c00b29c1c07070700c0309c271555555550369d5554510b46d550b42d550b542d507541d50350f5650549c150707070703030303030303031f0b0b1f07070707030303030002ca700000007c01c007000c003003c0800555540da7555500005046c11f542d507541d50350f56500000005046c01507070707030303030303030383e0f81e0780e030f1f0f0b0f0b0f0f07070707070707070303030303030303009c2701c0700c0308a7a0a955550369d55555554511f542d507541d50350f56543d0f5543d1b550549c15070707070303030303030303aaaaaa000000229c001f002c007001c003000c080155550369d55540004411f542d507541d503595940000001411b00541c1c1c1c0c0c0c0c0c0c0c0ea0ba87ea07a81ea0380ea0386eaaaaa802709c0701c0300ca0fa02155550369d55555554511f542d507541d503591b55665565650549c15070707070303030303030303aaaaaaa000000229d55550369d55540011f542d507541d503595940001507070707030303030303030383e0f81e0780e0300000000201f002c007001c003000c00f00555540da7555500005046c11f542d507541d50350f56500000005046c01507070707030303030303030307070707030303030707070703030303555540da755555547d50b541d507540d43d59515274541c1c1c1c0c0c0c0c0c0c0c0c0c0c0c0c0c0c3c3c1c1c1c1c1c1c1c1e966aaaaaaaaaa87c2c2c7c1c1c1c1c0c0c0c0d1c9d1c4727472a86d0b41d0740d913135a5991b46d83e07070707a81e07a0303030b0303031faaa03a0303aa030303070303030703030303a80e03a03030303560ba9eaaaaaaaaa80e0faa1f0b0b1fa889e01c1c1c1c0c9c0c03030300c0c0c0ea86d0b6961b50741d0303130303540da7991b46d0707070703030303030303030303a0380c0c1c1c1c1c1c1c1c1c0c0d40d030382c0e0b0b81c1e070780e03a0303a0f0f0b0b0b0b070707070303030357275715c9d5c0fa0f0b42d0741d0340d131350b0b50f646d1b41c1c1c1c0c0c0c2c0c0c0c2c0c0c0c1c0c0c0c1c0c0c0c0c0c0c0c0d582ea7a0b0b81c1e0707a0303a030f80e03a81c1c1c1c1c1c1c1c0c0c2c0c0c0c0c0c0c0c0c0c0c2c2c0c0c0c0c0c0c0c0c2c3c2c2c2c2c2c1c1c1c1c0c9c0c03030300c0c0c0c3e83c2c2c2c0b270b02d0b41d0740c0c4c0c0d50369c3d90b0b50b1b51b46d070b07070303030b0303030b0303032303030323030303030303030356aaaaaaaaa82c2c2c2c8c8c8c8c0c9c0c03030300c0c0c0ea82d0b46d1b40c0c4c0c0d50369e646d1b47b27a71ec9c3ea744c1c1c1c1c0c0c0c0c0c0c0c0c0c0c2c2c0c0c0c0c1c1c1c1c1c1c1c1e966aaa0ba07aaaaaaa82c2c2c2c1c1c1c1c0c0c0c0c9dec7b272a82d0b41d0740c0d640da713135a5991b46da0ba07aaa070707070707a0303aaaaa030303030b0303030b030303070303030780eaa03030303030303030356aaa82ea7a07aaaaaaaa278a80b0b0b0b0707070703270300c0c0c03030303aa86d6942d0b41d0740c0c4c0c0d50369e646d1b41c1c1c1c0c0c0c0c0c0c0c0c0e03030303a0707070707070707030350340c0e0b80e0781e0380e80c0e82c2c7c2c2c7c1c1c1c1c0c0c0c0d1c9d1c47274703e83c6d0b41d0740d0344c4d43c3d43d91b46d070707070303030b0303031f030303070303030703030303030303035682c2e0ba9e0781e03a0303a03030f0f80e03a81c1c1c1c1c1c1c1c0c0c3c0c0c0c0c0c0c0c0c0c0c3c3c0c0c3c6c0c0c0c0c0c0c0c0c2c2c2c7c2c2c7c1c1c1c1c0c9c0c03030300c0c0c0c3e83c3c3c3c0f270f06d0b41d0740c0c4c0c0d50369c3d90f0f43d43c3c6c6d46d1b41c1c1c1c0c0c0c0c0c0c0c0c0c0303030300707070707070707030350340c0c7c2c2c7c1c1c1c1c0c0c0c0d1e470f4791c3c0c0b01c0700c0302c2c00c0c09c2706d0b41d0740d0346c4d46c4d46d1b446c 26 67108863 11 2047
def hc_71_13 : Nat → Nat := unpackHintV5 0xa29c0228850449eb86ba6ad2029560aaa49318a8cb0b3a2381e88450921ff923679e0c09d921cc71ac939b2e27a68e07b18c42e85d64b596582024ffd2c92862f241391c0f0728e33f9048baf29e267908884d2a218f108852b2220ec8bc8299232046cbf0000236 0x29c4c4c7c172b0f440d05c2c2c5c7c2c2c7c5c5c5c5e0b83e0f83e0f83c00000000807c6c0005c1c5c5c5c5c5c1c4c0c0c4c3c3d5540001542c555555000500170b0b171f0b0b1f1717171782e0f83e0f83e0f00000000201f002c007005c01b000c00f005542da755555500011047d41d517544d503543d59400000014100547c1c2c1c0c7c2c0c4c4c0c1c4c0cac1c4c7c2c0c0c0c4c4c1c1c4c4c4c8c1c1d5130b0b13071313071313030313131384c3c4e130f1f0b0b1f072b2b0713130303331313131304c9c4c131313135555555555555551f0b0b1f1f0b0b1f2b2b2b2b1f0b0b1f2b2b2b2b1f0b0b1f2b2b2b2b5542da75555555547d41d52355503543d59515274541c1c1c1c1c7c1c1c1c2c1c1d50707070707070707070707030707070307072b2f2f2b070707070781c3c1e070707070707171717170707070707070701c5c1c07070707171717171b46d41da7070750707230741d1b46d1745d07230707070703070307030703072b1f2b0b2b0b2b1faa0707a0707555aaaa6a55a52b172b1707070707070303073327170cc9c5caa555555555555555072307070707030703070307030787ea0ba81ea07a81eaaaa80ea7aaa8ac5cac5c1c1c1c1c1c0c0c1ea2278aa551b50769d5555555555551f542d507507540d5995595565654549d1507230707070703070307030703072b1f2b0b2b0b2b1f07070707070707070554132b132b0707070707030307138bc3c4e2f0f1705c0701c4031400c0c05c1315555555555554501c8c1c1c1c1c0c1c0c1c0c1c0c1c6c7c4c2c6c2c4c6c1c1c1c1c1c1c1c1c0132b132b07070707070303071384c3c4e130f1705c0701c00ca7030300303031704c551b50769d5555555554511f542d507507540d51344d551b5550f5650545c1517230717071707130713070707072b1f2b0b2b0b2b1fa1717aa1313070307031313aaaaaa05451705c0705c1301c0f0f05084555555555555141723071707170713071307070707a82ea1fa85ea07a80ea1baaaaaa005c1701c1704c07283e80817552b50769d55559375555551447d50b545d44d50356555995590f566504545d270541c1c1c1c0c1c0c1c0c1c1c0c1c1c4c7c4c2c4c2c4c4c0c0c1c1c1c1c1c0d51313131307070707070303071384c3c4e130f2b172b17070707070703030713131304c9c4c1313131355555555555555523230723072b072b072b070707072b2b2b2b0723230707072f2b172b17071717070707172f1717552b50769d555555551f542d5235540d50f5654549d151b1f230b1b0b231f17071707541c4c1c4c1c0c4c4c1c0c4c4c1c5c1c1c8c1ea0ba87eaa1b86eaa2393ea17a81ea03a86eaaaaaaaaa801705c17170171700705c1301ca0fa0205c6d2b1b2b41c1c1c1c1d50769c4d07686c6d69966445c1b1f230b1b0b231f23072307541c6c1c6c1c0c6c8c1c0c6d3c1d3c1c1c8c1cacacacac8e1b0f1b88c3c1c8c8c1c6c1c1c6cac5cac5c8c9c5c1b231701c5c5c1c6c1c1c5cbc5c5c6d2b1b2b41c1c1c1c1d50769c6d0746d1b45d1b41d2c1c1c1c1c1c1c1c1c1c1c1c1cacbcbcac1c1c1c1c1c1c1c1c5c5c5c5c1c1c1c1c1c1c1c1c5c5c5c5d55550769d5555551f542d507507540d50f5654545d15070707070707a7070b0707070b070307030703030707030307070303070303071f1f0b0b0b0b131f1f1f1f1f131f13131f1f374b131f1313070707070707070723230707544c2c2c7c4e1f0f1387c3c1c1c8c1c1c1c1c0c0c1c4e130f1384c3c7c2c2c5c7c7c5c1f271701c1c8c1c1c1c1c0c0c1c4c9c5c3327130bc4c4c5c6d0b46c6d46c6d41d41d50369c0c0d40c0c0c6d1345d1b41c1c2c2c1c1c1c1c1c1c1c1c1c1c1c1c1c2c1c1c1c1c0c0c1d030350307030703070307138bc3c4e2f0f0b0b0b0b07070707070303073327170cc9c5c0b0b0b0b07070707070303072f13131703035070350b42d0741d0740d1b44d1746d070707070b07070b0707070707a7030307070303070703070307030703070b0b370b0b0b0b0b0b0b0b0b0b13130b0b0b0b0b0b0b0b0707070707070707542e0b0b0b82c3c2c2c2c2c1c1c1c1c1c0c0c1c4e130f1384c3c2c9c2c0b0b0b02c2c2c2c1c1c1c1c1c0c0c1c4c9c5c3327130bc4c4c5c2c2c6c6d42c2d0b50b42d0741d40da7030350303031b44d1746d0b070b070b0b0ba82c2c1c1cac8cac8c1c1c0c2c0c2c0c1c0c1c0c0d40c0c2d82e0b83e07a0f0fa0f0f80e0f0b0b0b0b072b2b0733273b0cc9cec130303130fa0f0b42d0746d0b035030350b40d0f646d1b42c1c2c1c0c2c0c2c0c1c0c1c2c2c2c2c2c2c2c2c1c1c4c4c4c8c1c1d582ea7a0b0b83c3e130780e0fa0f0fa0f0fa81c1c2c2c2c8c1c1c2c4c0c0c0c0c2c2c2c4c2c4c2c2c2c2c2c4c2c2c2c2c2c2c3c2c2c2c2c2c1cacac1c4c0c0c4c4c4c4c13271303e83c2c2c2c0b270b02d0b41d1b50369c0c0d40c0c0c3d90b0b50b1b51b46d1f070b07a0b0b0b0b1381c1cac8cac8c1c1c0c2c0c4c0c1c0c1c0c0d40c0c3d82e0f83e07a0b0ba0f0b80e0f1f0b0b1f072b2b073327470cc9d1c130303130fa0f1b42d0746d0f035030350f40c0c0d0f646d1b47c1c2c1c0c2c0c4c0c1c0c1c4c7c2c2c2c2c4c4c1c1c4c4c4c8c1c1d5a0b0b82ea783e0780e0fa0f0fa0f0fa81c1c3c3c3c8c1c1c3c4c3c4c0c0c0c0c3c0c3c3c3c4c3c4c3c3c3c3c3c4c3c3c3c3c3c2c2c2c7c2c2c7c1cacac1c4c0c0c4c4c4c4c13271303e83c3c3c3c0f270f06d0b41d1b50369c0c0d40c0c0c3d90f0f50f1b51b46d0723070707072b1f2b0b2b0b2b1f070707a81c1c0c1c0c1c0c1c0c1c0c0d40c0c1d83e0fa07a07a0707a070780e072b172b17070707073327170cc9c5c070303070fa0f1b46d0741d07035030350740d0f645d1b41c8c1c1c1c1c0c1c0c1c0c1c0c1c4c7c4c2c4c2c4c4c1c1c1c1c1c1c1c1d583c3e130f81ea7a070780e07a0f0fa0f0f0f1f0f0b0f0b0f0fa81c1c0c0c0c0c1c1c3c4c3c4c3c3c3c3c3c4c3c3c3c3c3c1c1c1cac5cac5c1c1c1c1c1c0c0c1c4c4c4c13271303e83c3c3c3c0f270f06d1b41d0750369c0c0d40c0c0c3d90f0f50f1b51746d0b070b070b0b0b0b0b0b0b0b0707171717170707030b030b0307030705000b0b0b0b07171307138ec3c4e3b0f130303130000000000000b42d0745d000303010346d134002c1c2c1c0c2c0c2c0c1c0c1c2c2c2c2c2c2c2c2c1c1c4c5c5c5c1c1d50b0b0b0b07171307130303131384c3c4e130f02ca70000170000000000b007005c013000c01304c00330000f020002d0b41d1750369c0c0d40c0c0c6d13400041b017070b071f1f0b0b0b0b1f1f0707171717170707030b0313030703070500130b0b1f071713071391c3c4e470f130303130000000000001b42d0745d0003030103030346d134005c1c2c1c0c2c0c4c0c1c0c1c7c7c2c2c2c2c4c7c1c1c4c5c5c5c1c1d5130b0b1f07171307130303131384c3c4e130f0002ca7000000000007c01c017004c13000c03004c13000cc0003c08001b42d0745d40da7030350303031b44d000106c01c8c1c1c1c1cac7cac2cac2cac7c1c1c1c1c1c1c1c1c0c1c0c1c0c1c0c1c14004cac4cac1c1c1c1c4e2f0f138bc3c1c0c0c1c00000000000006d1b41d074000c0c040d1b44d00 26 67108863 11 2047
def hc_71_14 : Nat → Nat := unpackHintV5 0xbb71deb26a42a672fe9f21d495aa5e9520228bf24c7fd308770a326b1afc620a445982224d0b1e4c802244a1f83b9a4233a9fc28c2ba2281901ae1e813f1bc0b422c06094e0228f801c81801a80801880801481001280800d81400202e000008 0x7c1c2c1c0c2c0c4c0c1c0c1c6c6eaa81c1cac8cac8c1c1c3c3d556aaa980ea55a51f0b0b1f072b2b07130303133327530cc9d4caa555555555555551f070b07030b03130307030787ea0ba81ea23a83eaaaa80ea7aaa87c2c2c7c1cacac1c4c0c0c4ea2278aa5542da755555555555546d41d523544d13540d03566556555959515274541c1c1c1c0c0c0c0c0c0c0c0e0b83e0781e03a9e80c0c0c7c0c0c0c2c0c0c0c1c0c0c0c1c0c0ea030f031f0b0b1f07070707030303030fa0f03030300c9c0c5542da755555555555546d41d507540d503543d0f566540d035540d13554549d1507070707aaa1b1b070707070707070703030303030303030303555aaaaa555a61f0b0b1f0707070753275314c9d4c03030303aa5555555555555507070707a82ea1fa81ea070303030303030303a03aaaaaaaa03a9c7c2c2c7c1c1c1c1e278a803030303aa5542da75564dd55555555551b507541d5955665540d13540d035643d599515274569ccc27a71f070b07030b03130307030782e0f83e07a030380ea746c6c2c2c2c2c3c3c1c1cac8cac8c1c1e95540c0d5547c2c2c7c1cacac1c4c0c0c4c3e83ccc9c3327a31550b69d5555555555551f070b07030b03130307030782e0f83e07a030380ea70f1f0b0b0b0b0f0f07070f4b0f0f0f230f2b0707a80c0c0c7c2c2c7c1cacac1c4c0c0c4c3e83c3c3c3c0f270f1550b69d5555555555551b507548d513540d50f56543d0f5543d554549d151f070b07030b0313030703071b1b0b0b0b0b1b1b07072b232b2307070554130b0b1f072b1307130303131396c3c4e5b0f1f02c0705c40303031400c0c09c131555555555554507c1c2c1c0c2c0c4c0c1c0c1c6c7c2c2c2c2c4c6c1c1c4c6c6c8c1c1c0130b0b1f072b1307130303131384c3c4e130f1f02c0705c00ca7030300303032704c5542da755555555551446d41d523544d13540d03544d135546d5543d59415270541c1c1c1c0c0c0c0c0c0c0c0c7c2c2c7c1c1c1c1c0c0c0c0c00000329c00001f002c007001c00300f02001550b69d5555540004411b507541d503540d50f565000049c0001413300541c1c1c1c0c0c0c0c0c0c6c6c1c1c1c1c1c1c1c1c0c0c0c0c0c0c0c0c15147c2c2c7c1c1c1c1d6e5b0f5b96c3c0c0c0c0c7c0b01c0706c4c1400c42709c55555555555514070707070303030b0303031f03030307030303070303030303030303007c2c2c7c1c1c1c1c0e03030380c3c0c0c0c0c7c0b01c0700c0c6c0c0c00329c9c271550b69d55034dd55555554511b507541d5035550340d55034cd50340d50f56504549d270569c4c3ea717070b07030b031303070307130b0b1f071713071303031300000000ca70006c6c0001c1c5c5c5c5c1c1c4c4d5543c4e13a8c3c0001550b69c55555500050017070b07030b031303070307130b0b1f071713071303031300000000ca70007c00b001c4b005c2b006c03c08005542da755555500011046d41d517544d503543d59400000014100547c2c2c5c7c2c2c7c5cacac5e0b83e0f83e0f83c7c6c2c2c2c2c3c3c5c1cac8cac8c5c1ccc4cfc0cfc0ccc4c15507c0b05c1709c2712a14281555555555554507c2c2c5c7c2c2c7c5cacac5e0b83e0f83e0f83c3c7c2c2c2c2c3c3c3c1c3c3c3c8c3c1c3c6c3c0c3c0c3c3c01f02c1705c2709c229e82a5542da755555555551447d41d523544d503543d0f566543d0f5543d550549c15170b0b171f0b0b1317131713aaaaaa0000000001f1b0001707171717171707131353035303131355a5000054555555000500170b0b171f0b0b1317131713aaaaaa000000229c001f002c007005c01b000c0801550b69d5555540004411f507545d513540d5959400012700005040151f0b0b171f0b0b1317132b13aaa1f1b17072b232b2317071313530353031313aaaaaa05451f02c1705c1309c0f0f05084555555555555141f0b0b171f0b0b1317132b13a82ea1fa88ea07a80ea1baaaaaa007c0b05c1704c27283e8085542da7555564dd555554511f507548d513540d59556655643d59941152749c15170b0b171f0b0b1317131713aaaaaa000000229d550b69d5555954011f507545d513540d5959400010545c2c2c5c7c2c2c4c5c4c5c4eaaaaa87c0171717171313a55550b15555954404c4c0e9e9c0c4e9ea73760f2704c0cdda7 24 16777215 10 1023
def hc_71_15 : Nat → Nat := unpackHintV5 0xefc93b6f4114b5ea36dae801ad6881766b492304a62174a1b6ad719c51cc9da8cc03544f02e97915d43750a9f86468ea12446531fb2fe057164235c9ce2a64860c22400060ff44186912d22e78c21580378ab80104c21341e40fa0b487b029661c000296 0x741c1c0c0c0c0c0c0c0c0e0b82e0f83e03a9e80c0c0c2c0c0c0c2c0c0c0c8c0c0c0c8c0c0ea030f030b0b0b0b23232323030303030fa0f03030300c9c0c0b40d1b41d0340d0f640c0d40c6d46d1b55070b070707070707070707070707070303030303030303030b03130303030303030303a0b0ba0b0f82e0b81e0780ea7a0303030b031303030303030b030b03030303030b0303030b03030307030303070303a80c3c0c2c9c2c0b0b0b02c2c2c2c1c1c1c1c0c0c0c0c3e83c0c0c0c03270302c2c6c2c2d50b69c1d07070740d0343d903035031b51b46d0741c1ea0ba82ea23a88c0c0c0c0c0c0c0c0e80eaaaaaaa80ea70b0b0b0b2323232389e2a00c0c0c0ea82d91b41d86d6940d036646d1b4a78327a720c9c3e46c1c1c1c1c0c0c0c0c0c0c0c0e96681c1c1c1c1c1c1c1c0c0c0c0c0c0c0c0eaaaaaa80ea7aaaa0b0b0b0b0707070703030303278320c9caa0b0b642c1d07070740d0346c6d696646d1b55070b07070707070707070707070707aa82e0baa82ea82ea0ba81ea0703030303030303030303030303030303a03aaaaaaaaaaaa03a9c2c9c2c0b0b0b02c2c2c2c1c1c1c1e278a803030303aa0b0b1b0b0b542da70741c1c1d86d6940d036646d1b41d070703030303030303030b0b0b0b2323232303030303000000ca7000002c00b008c023000c03c08000b446d0740d0346d1b400041b0541c2c1c1c1c1c1c1c1c1c1c1c1c1c1c0c0c0c0c0c0c0c0c0c2c0ccc0c0c0c0c0c0c0c0c2e0b0b0b82c3c2c2c2c2c1c1c1c1c0c0c0c0c000000000329c00000b0cc000b02c000b002c007001c00300f020002c2c6c2c2d50b69c1d07070740d0346d1b400041b00741c1c0c0c0c2c0c0c0c2c0c0c0c8c0c0c0c8c0c0c0c0c0c0c0c0c00b0b0b0b232323230380c0c0e030f030303030b02c2308c03031b0303000ca72709c0b40d1b41d031b5030350340d1b46d11b03daea70f6ba9c1b46c1c1c1c1c0c0c0c0c0c0c0c0c0c0d40d03030707070707070707030300300c0c2c2c2c2c1c1c1c1c0c0c0c0e6b0f6b83c2c0b01c0700c0c00c0329c6c4c02c2c09c2702c2d0342c1d07070740d0346c6d40c0d46d1b446c541c2c1c1c1c1c1c1c1c1c1c1c1c1c1c0c0c0c0c0c2c0c2c0c0c0c0c0c2c0c0c0c0c2c0c0c0c2c0c0c0c1c0c0c0c1c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c00b82c2c2e0b0f0b0b0b0b070707070380c0c0e030f030303030b2700b0b00b02c0701c03031b0303000ca72709c0b0b1b0b0b542da70741c1c1d031b5030350340d1b46d11b02d0b0b0b0b0b0b231b231b82e0b83e0f83e0f0b0b0b0b0b0b0b0b0f230f0f0f230f0f0f1b0f030f030f0f002c0b08c2306c2708a7a0a82d0b46d1b46d1b43d90f0f50f1b511b02c2d42d0b0b0b0b0b0b2b2317072b2317070b0b0b0b3f031b133f031b13171b2b1782e0ba0b2820f83e0f83c2c0b2802e01705c1b09c0b0802d0b46c6d43c3d45d1b46d1b43d911b150b0b230b070b0b0b0b07170b0b0b0b0b030b0b0b030b130b0b0b0b171b2b17a0b0ba0b0f82e0b83e0f83e0f0b0b0f0b0b0b0b0b0b0b0b0b0b0f0f0b0b0b0b0b0b0b0b0f070f0f0f230f070f1b0f030f030f0f002c2c9c9c02c2c0b00b02c1705c1b09c229e82a0b0b1f0b0b542da7174ac6cad1b46d0f643c3d43c6d446c0b42c2c2c2c2c2c8c4c8c4eaaaaa80000008a70002c00b008c023006c00302000b446d1744d1b66400041b005000b0b0b0b17171707171717070b0b0b0b6f0313136f03131317131713aaaaaaaaaa00000000002000b446c6c0005d1744d1b6640150b0b170b070b0b0b0b07170b0b0b0b0b030b0b0b030b130b0b0b0b17131713aaaa82e0faaaaaa0000000000229c000b0000b02c000b002c007005c01b000c08002c2c7c2c2d50b69c5d17171744d1b66400041b00b42c2c2c2c2c2c8c4c8c4ea0ba82ea23a88ea03a86eaaaaa800b02c2308c1309ca0fa0202d91b46d1346d86d6966446c1303130b0b0b0b0b0b0b0b17132b13aaaaaaa59a17072b232b2317071313036b031313a08a0b02c1705c1309ca0880f0f00b0b00b0b642c5d2b1b2b44d1b6646c6d69446c542c2c8c2c1c2c2c2c2c1c5c2c2c2c2c2c0c2c2c2c0c2c4c2c2c2c2c5c4cac4eaa0b82eaa0baa0ba82ea23a81ea03a86eaaaaaaaaa800b2700b0b00b02c1705c1309ca0fa0202c2c7c2c2d50b69c5d2b1b2b44d1b61b5a59911b02d0b0b0b0b0b0b231b231b82e0b83e0f83e0f00000000200b002c023008c01b000c00f000b446d1746d1b43d9000106c02d0b0b0b0b0b0b23132313aaaaaa000000229c2d11b45d1346d9900a70b0b0b0b0b0b0b0b171317139a17171717136b130000000000b0b442c5d17171744d1b46d9000542c2c5c2c1c2c2c2c2c1c5c2c2c2c2c2c0c2c2c2c0c2c4c2c2c2c2c5c4c5c4eaaaa0baaaaaa800000000008a70b0b1f0b0b542da71745c5c5d1346d9900005000b0b0b0b17171707171717070b0b0b0b57031b1357031b131717171782e0ba0b0ba0f0f83e0f83e0f0000000000000b446c6c0005d1746d1b43d900542c2c5c2c1c2c2c2c2c1c5c2c2c2c2c2c0c2c2c2c0c2c4c2c2c2c2c5c5c5c5e0ba0b0ba0b0b0f0f82e0b83e0f83e0f02c27000000000000200b0000b02c000b002c007005c01b000c00f000b0b1f0b0b542da71745c5c5d1b46d0f640001406c6c150b0b230b070b0b0b0b070b0b0b0b0b030b0b0b030b0b0b0b0b4b1b2b1b0b82c2c2e0b0f0b0b0b0b4b2b2b4b1b1b0b270b02c2c2c0b0b0b0b4b2b2b4b1b1b0b0b1f0b0b542da71b4ac6cad1b46d1b46d1b46d 25 33554431 11 2047
def hc_71_16 : Nat → Nat := unpackHintV5 0x86e4e041767f1f66554f15a767504ea384a8e1aa85f4cda1e862611c2f0a8995f264ca70a224da179249090112d46c7da2f23b20ec1b36968c9f3f05a22b629f8c613187908a43a03cf20c1bd4a90c2e6f050a4341e6a7a0c0cca04a857817d35c0002fa 0x15170b0b1717171707171717071f0b0b131b0313131b03131317131713aaaaaaaaaa0000000000229d0b69c2c2d42c2c2c5d1744d1b69980014005c5c5c1c5c5c5c1c5c2c2c5d0c0c6c4d0c0c6c4c7c2c2c6c5c5c5c5e83c3e83c3e0b83e0f83e0f83c000000000000002c2c042c2c2d1745d1b46d0f64015170b0b1717171707171717071f0b0b1b1b031b131b031b131717171782e0fa0f0fa0f0f83e0f83e0f000000000000201f002c01b06c001f00007005c01b000c00f0042da70b0b50b0b0b1745d1b46d0f6400041b0547c2c2c7c6c7c7c1c7c8c6c1c7c2c2c6c6c0c6c6c0c6c7cac6cac6c7c2c2c7c6e1f0f1f86c3cacacacac6c6c7c2c2c7c6c7c7c1f271b0acacacac6c6d0b69c2c2d42c2c2c6d1b46d1b46d1b46d1b42c1c2c1c0c2c0c2c0c1c0c1ea82c2e81c1cac8cac8c1c1c3c3d556aaa9a956942c2c2c2c1cacac1c4c0c0c4ccc9cec33273b2a9555555555555542c1c2c1c0c2c0c2c0c1c0c1e0ba82ea07a88ea0faaaaa03a9eaaa0b0b0b0b072b2b0713030313a889e2a90b69d55546d555555555542d41d523544d503566556555959515274541c1c1c1c0c0c0c0c0c0c0c0e0b82e0781e03a9e80c0c0c2c0c0c0c2c0c0c0c1c0c0c0c1c0c0ea030f030b0b0b0b07070707030303030fa0f03030300c9c0c42da7555507555555555550b507541d503540d50f56540d035540d13554549d1507070707a0b0baa070707070707070703030303030303030303555aaaaa555a60b0b0b0b0707070747274711c9d1c03030303aa42d55541d555555555507070707a82ea0ba81ea070303030303030303a03aaaaaaaa03a9c2c2c2c2c1c1c1c1e278a803030303aa42da7555507555555555550b507541d5955665540d503565654549d150b070b07030b030b0307030782e0b83e0780e42c2c2c2c2c2c2c2c1c1cac8cac8c1c1e95540c0d5542c2c2c2c1cacac1c4c0c0c4c3e83ccc9cec33273b15555555555555542c1c2c1c0c2c0c2c0c1c0c1e0b82e0f81e80c0e03a9c2c2c2c2c2c2c2c2c1c1c3d2c3c3c3c8c3cac1c1ea0303030b0b0b0b072b2b07130303130fa0f0f0f0f03c9c3c42da755551b555555550f4dd5550b507548d513540d50f56543d0f5543d554549d150b070b07030b030b030703070b0b0b0b0b0b0b0b07072b232b23070705540b0b0b0b072b130713030313138ec3c4e3b0f0b02c0705c4031400c0c09c131555555555554502c1c2c1c0c2c0c2c0c1c0c1c2c2c2c2c2c2c2c2c1c1c4c6c6c8c1c1c00b0b0b0b072b1307130303131384c3c4e130f0b02c0705c00ca7030300303032704c42da755551b555555554510b507548d513540d51344d551b5550f5650549c150707070703030303030303030b0b0b0b0707070703030303000000ca7000002c00b001c007000c03c080042da7555507555540004410b507541d503540d50f5650000000504cc0150707070703030b0b030303030707070707070707030303030303030305450b0b0b0b070707074791c3d1e470f030303030b02c0701c1b1305003109c2710b555507555555554501c1c1c1c0c0c0c2c0c0c0c2c0c0c0c1c0c0c0c1c0c0c0c0c0c0c0c0c00b0b0b0b070707070380c0c0e030f030303030b02c0701c03031b0303000ca72709c42da7555507555555554510b507541d5035550340d5503540d50f5650549c150b070b07030b030b030703070b0b0b0b071713071303031300000000000b0b0070717171717070713135553b0f1384e3b0f00005155555550005000b070b07030b030b030703070b0b0b0b071713071303031300000000ca70002c00b001c4b005c2b006c03c080042da75555175555400014137042d41d517544d503543d59400000014100542c2c2c2c2c2c2c2c5cacac5e0b82e0f83e0f83c2c2c2c2c2c2c2c2c5c1cac8cac8c5c1ccc4cfc0cfc0ccc4c15502c0b05c1709c271214281555555555554502c2c2c2c2c2c2c2c5cacac5e0b82e0f83e0f83c2c2c2c2c2c2c2c2c3c1c3c3c3c8c3c1c3c6c3c0c3c0c3c3c00b02c1705c2709c229e82a42da755552b555555554510b507548d513540d50f56543d0f5543d550549c150b0b0b0b0b0b0b0b17131713aaaaaa00000000000b0b01707171717171707131347034703131355a50000455555550005000b0b0b0b0b0b0b0b17131713aaaaaa000000229c000b002c007005c01b000c08010b69d55545d555500011042d41d517544d5035656500000005040150b0b0b0b0b0b0b0b17132b13a0b0baa17072b232b2317071313470347031313aaaaaa05450b02c1705c1309c0f0f0508442d5554ad55555555140b0b0b0b0b0b0b0b17132b13a82ea0ba88ea07a80ea1baaaaaa002c0b05c1704c27283e80842da755552b555555554510b507548d513540d5955665565650549c150b0b0b0b0b0b0b0b17131713aaaaaa000000229d0b69d55545d555500042d41d517544d503565650000542c2c2c2c2c2c2c2c5c5c5c5e0b82e0f83e0f83c00000000002c2c05c1c5c5c5c5c5c1d1c4d1c0d1c0d1c4c3c3d5540001155555540014002c2c2c2c2c2c2c2c5c5c5c5e0b82e0f83e0f83c00000000802c00b001c017006c003003c010b69d55545d55550000504dc10b507545d513540d50f56500000005040150b070b07030b0b030b0b0307030703030b0b0b0b0b030707131313230707542c2c2c2c1c4c4c1c4c0c0c4c4e130f1384c3c2c2c2c2c1cacac1c4c0c0c4c4c4c4c13271304c4c4c4d5555555555555542c2c2c2c2c2c2c2d2cacad2c2c2c2c2d2cacad2c2c2c2c2d2cacad2d0b69d5554ad55555542d41d52355503543d59515274542d0b0b0b0b0b0b231b231b0b0b0b0b232323231b1b0b0b0b0b232323231b1b0b42d1b46d1b46d1b46d1b46d0741c1c1c1c1c1c1c1c1c1c2c2c2c2c1c1c1c1c1c1c1c1c2c2c2c2c1c1c1c1c1c1c1c1c5c5c5c5c2d0b41d07070741d0746d1b45d1742c1c2c1c0c2c2c0c2c2c0c1c0c1c0c0d42d0b0307071313132307070b0b0b0b0b0b0b071313071303130313131384c3c4e130f0b0b0b0b072b2b0713033303131313131304c9c4c131313130b42d0746d131340c6d13135131b51344d1b46d 25 33554431 10 1023
def hc_71_17 : Nat → Nat := unpackHintV5 0xd899a26c0808b5ce06d9c823ec289775d507eaea001174c008ba60005d18032e7c02173a008b9081959f052aae242d50a0cea029054b8891a4722a50b430a757a0536788898465ecaab2f04b21471d59070c6c48045c3b41c38d509489a82b83d80002b8 0xc0c2c0c1c0c0c0c0c0c1c1c1c1c1c0c0c0c0c0c0c0c0c2c0e9c0c0c1c0c0c0e03a0303a03030f0f82e0b81e0780e0300c2700000000000020030000300c000b07c00b02c007001c003000300c00f0003370340c0c0d0b0b0b0b07070707030303030fa0f000106c29c4c6d1ba71346c6c3e04c5c1c2c1c0c0c2c2c0c2c0e9c03070307030300007071717171707070b0b00082e0f83e0780e0fa0f0fa0f0f000000000000204c1b0b0b1f07171707130303131b1b46c6d0fa0f0017070b0703030b0b030b03a70307030703030307071313131707070b0b0b82e0f83e0780e0fa0f0fa0f0f000000000000204c1f002c007005c013000c01304c00130000f001b0b0b1f071717071303031313131344cdc4d0fa0f000106c00c4c0c1c1c1c1c0c0c0c1c0c1c0c0c0c2c0e9c0c0c0c0c0c0c0c0c0c0c0eaaaaaaaaaa8000000000008a71f0b0b1f03030340cdc0d0707070703030303aa00a7a7038a797971f0b072b130301c1c1c1c0c0c0c030b03030703030382e81c1c1c1e03a000000000000b0b0b0b07070707030303030003030b03070303030303070707070703030303030303030b03a7030307030303aaaa80eaaaaaa000000000000229c0cdc0d03030342c2c2c2c1c1c1c1c0c0c0c0ea8005c5c5c5c4c4c5c4c5c4eaaaaa80000008a7171717171313aa0003030b03030303070707070303130b0b0b0b02c2c4e9c1c1c1c1c1c1e030380c3e0b82e0781e0383c000000000000c0c0c0c2c2c2c2c1c1c1c1c4c4c4c4c3e83c005c1c5c1c0c4c4c0c4c0c1c0c1c4c7c4c2c4c2c4c4c1c1c4c4c4c5c1c1c083e0f83e0780c3e0f0fa0f0fa0f0f00000000000001b1b1b1b071717071303031313131344c6c4d0fa0f00171717171717171783e0f83e0f83e0f00000000201f002c007005c0000c00f00171717170fa0f00010dc07c1c2c1c0c7c2c0c4c4c0c1c4c0cac1c4d0b0303035070713071313132313230707131313130b0b1307131307130303131384c3c4e130f1f0b0b1f072b2b071303031313131304c9c4c131313131b42d0746d131340c6d0b0b5130b51344d1b46d541c1c1c1c1c1c1c1c1c1c1c1c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0e0b83e83c3e83c3e0781e03a9e80c0c0c7c0c0c0c2c0c0c0c6c0c4c0c0c0c0c0c6c0c4c0c0c0c0c0c1c0c0c0c1c0c0ea030f031f0b0b1f1b1b1b06c9c6c07070707030303030fa0f03030300c9c0c42da70b0b50b0b0b0741d0340d0f640c0d40c6d46d1b41c1c1c1c0c0c0c0c0c0c0c0e6a941c1c1c1c1c1c1c1c0c0c0c0c0c0c0c0eaaaaaaaaa87c2c2c7c1c1c1c1c0c0c0c0d0c9d0c4327432aa42d0741d0340d0b0b5a5991b46d541c1c1c1c1c1c1c1c1c1c1c1ea0ba87eaa1baaa1b86ea07a81c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0e80eaaaaaaaaaaa80ea71f0b0b1f1b1b1b06c9c6c0707070789e2a00c0c0c0ea90b69c2c2d42c2c2c1d07686c6d69940d036646d1b55070707070707070707070707030303030303030303030303030303031f0b0b1f1b86c3c6e1b0f07070707030303030000000000ca7000007c00b006c1b0006c330001c007000c03c080042da70b0b50b0b0b0741d0340d1b46d000106c01c1c1c1c0c0c0c0c0c0c0c0c0d0303030350707070707070707030300300c0c7c2c2c7c1c1c1c1c0c0c0c0d0e430f4390c3c7c0b01c0700c0306c4c06c4c09c2700d0b41d0740d0342c2d40c0d46d1b446c541c1c1c1c1c1c1c1c1c1c1c1c0c0c0c2c0c0c0c7c0c0c0c0c0c6c0c0c0c0c0c0c6c0c6c0c0c0c1c0c0c0c1c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c01f0b0b1f1b86c3c6e1b0f070707070380c0c0e030f030303031f02c1b1b01b2700701c03031b0303000ca72709c42da70b0b50b0b0b0741d03031b1b5030340d40d0346d1b446c0b0b50b0b0f4ac8c5c1cac8c5c1c7c2c2c5cfc0c6c4cfc0c6c4c7c2c2c6c5c6cac5e8283c82e0f83e0f83e0f1f82807c0b05c1706c2703c80f0b50b0b50f42d1746d1b46d0f6446c547c2c2c5c6c7c5c1c7c8c5c1c7c2c2c6c6c0c6c4c6c0c6c4c5c6cac5e0b83e83c3e83c3e0f83e0f83c3c7c2c2c2c2c3c3c3c6c3c6c3c3c3c3c3c7c3c3c3c3c3c3c1c3c3c3c8c3c1c3c6c3c0c3c0c3c3c01f02c1b1f01f2701705c1b09c229e82a42da70b0b50b0b0b1746d1b46d0f643c3d43c6d446c05001717170717171707170b0b1743031313430313131f0b0b1317131713aaaaaaaaaa000000000000000b0b010b45d1744d1b664015170b0b1717171707171717071f0b0b131b0313131b03131317131713aaaaaaaaaa0000000000229c001f002c01b06c001f00007005c01b000c08010b69c2c2d42c2c2c5d1744d1b66400041b01f0b0b171f0b0b1317132b13aaaaaa9aa517072b232b2317071313430343031313a08a1f02c1705c1309c880f0f01f0f090b45d1b44d1b6642c2d69446c547c2c2c5c6c7c5c1c7c8c5c1c7c2c2c4c6c0c4c4c6c0c4c4c5c4cac4ea0ba87eaa1faaa1b86ea23a81ea03a86eaaaaaaaaa801f02c1b1f01f2701705c1309ca0fa0210b69c2c2d42c2c2c5d1b44d1b686c6d69966446c 25 33554431 11 2047
def hc_71_18 : Nat → Nat := unpackHintV5 0xe509ceda8aa0d341d2c832c4c089eabb7944aeb332a61a269a62ee920a168642f286180a85f80885d00a85302885100885100083d84e7b621e6f8af6668a40597346515a06482a4c3e327e39094a307226248afa1d99bc150226085b2a000216 0x131300007070707070707070707070700c0c0c000c0c00c0c0c0eaaaaaaaaa80000000000007c2c2c7cec6ced3b1b3b41c1c1c1c0c0c0c0ea8000c4c0c1c1c1c1c0c0c0c1c0c1c0c0c0c2c0e9c0c0c0c0c0c0c0c0c0c0c0eaaaaaaaaa800000000008a70007c00b000c030000c0001c007000c00302001f0b0b1f03030340cdc0d0707070703030303aa000106c02c2c0001c1c1c1c1c1c1c1c1c1c1c1c0c0c0000c0c0303030303aaaaaaaaaa00000000002005f1b5f57c6d7d0b0b0b0b0707070703030303aa0003030b03070303030303070707070703030303030303030b03a7030307030303aaaa80e0faaaaaa0000000000229c00030000300c000b002c007001c003000c08000cdc0d03030342c2c2c2c1c1c1c1c0c0c0c0ea800041b0170717070313031303070307131f130b130b1313070713131317070702aaaaaaaaaa800000000000006c6c6c6c1c5c5c1c4c0c0c4c4c4c4d131b136a8005c5c5c5c4c4c5c4c5c4eaaaaa80000008a70007c00b001c017000030200171717171313aa00010dc01c1c1c1c2c1e9c2c2c1c1c2c2c2c1c2c1c4c1c0c4c4c1c0c4c4c1c5c1c1c8c1ea0ba87eaa1f92eaa1f87ea1788ea0781ea03a98eaaaaaaaaaa801702c17170171700701701301ca0fa0205c7c2c2c7c7c7c7d1f371f41c5c8c5c1c5c4c1c1c4e379a9aa05c5c0b0b0781c2c1c2c1c2c1c1c1c1eaaaaaa81c1eaa85c5ea84c4c1c0c1c0c4c4e82282c0b01c1704c072203c3c02c2c02c2c2c2c1c5c5c1c4c1c1c4ea9dc6d3d771b4f4171701c1c1c2c2c5c2c2c1c1c1c2c1e9c1c0c2c2c1c0c2c4c1c2c1c2c1c1c1c1eaa0b82eaa0baa0ba82ea17a81ea03a8eeaaaaaaaaa800b1700b0b00b02c0705c1301ca0fa0205c2cdc2d0b0b0b42c2c2c2c1c5c5c1c4c1c1c4e379a9aa05c5c0707070780c0c0c0c0c0c0eaaaaaaaa84c4c1c1c1c1c1c1c1c1e80c0eaa82287c0b01c0700c032203c3c00c0c07c2c2c7c1c1c1c1c0c0c0c0ea8ec6ced3b1b3b4272700c4c0c1c1c1c1c0c0c0c1c0c1c0c0c0c2c0e9c0c0c0c0c0c0c0c0c0c0c0ea0ba87eaa03aaa0380ea07a81ea0380ea03aaaaaaaaaa801f02c03030032700701c0300ca0fa0207c2c2c7c0c0c0d03370341c1c1c1c0c0c0c0e1b9a9aa09c9c46e9d1b03a0349c1ba747c2c1cac4c0c3c1b03c1c1c1c1c0c0c0e030b030307030303aaaaaaa0b0baa0707070707070707a0303aaa08a0b02c0701c0300ca0880f0f0030300b0b0b0b0707070703030303aa1b46d09c9c03030b03070303030303070707070703030303030303030b03a7030307030303aa80e03aa80ea82ea0ba81ea07a80ea03aaaaaaaaaa000c9c00c0c02c0b01c0700c03283e80803370340c0c0d0b0b0b0b070707070303030386e6a6a8272701c8c1c1c1c1c0c0c0c0c0c0e03aaaaaaa2b1f2b0b2b0b2b1fa81c1eaaa80c0eaa82285c1701c1c071700c032203c3c00c0c0acacacac1c1c1c1c0c0c0c0ea98c6d3d631b4f4171700c0c0c2c0c0c0c7c1c8c1c1c1c1c0c0c1c0c0c4c0c0c0c0c0c0c0c0c0c0c0c1c0e9ea0ba87eaa0380eaa03aaa07aa81ea0380ea03aaaaaaaaaaa801705c0317003030070701c5c0300ca0fa0205cacacacac0cdc0d03030341c1c1c1c8c1c0c0c0c0e1b9a9aa05c5c03130307070707030303030703aaaaaaa82c2c2c2c4c0c0c4c1c1c1c1c4c1e287c0b00c0c032701c072203c0306c2c2c6c0c0d030341c1c1c1ea84c4c4c4c1b1b00c0c0c0c0c7c1c8c1c1c1c1c0c0c1eaaaaaaa84c4c2c4c2c4c0c0c4c1c1c1c1c1e81c1e285c1700c5c030301c1c07172203c0306c6c6c6c0c0d030341c1c1c1c6c1ea84c4c4c4c171718c1cec1c0c4c0c4c4c0c1c4c0c1eaaaaaa84c7c4c2c4c2c4c4c1c1c4c1c4c4c4c8c4c8c1c1eaa08a2709c0705c131300c9c880f0f0130f01b1b1b1b071b1b0713031b031313aa13131344c6c4d06c6c17171313171313a82ea1fa88ea07a80eaaaaaaa009c2705c1704c27283e808171713138de6a6a8272704c4c0001c1c1c1c1c1c1c1c1c1c1c1c030b03030300030300303030382e0fa0f0fa030381e0780e030000000000001f0b0b1f3b1b3b4ec6ced07070707030303030fa0f00031303070707070303030703070303030b03a7030303030303030303030382e0fa030fa030381e0780e03000000000000201f07c00b02c00300c000300007001c003000c00f001f0b0b1f03030340cdc0d07070707030303030fa0f000106c02c2c0c1c0c030b0313031382e0b83e0f80e0f00000000204c0b002c023008c013000c00f000b0b0b0b1b231b23130303130fa0f000106c02c1c2c1c0c0c03030b0307030700030300707171717170707131300082e0b83e0780e0fa0f0fa0b0b0000000000000b0b0b0b07171707130303131b1b6f46c6dbd0fa0f000b070b07030b03a703030b0b03071303170703030307070b170b0b0b170b07070b130b82e0b83e0780e0fa0b0fa0b0b000000000000204c0b002c007005c01304c00300c00b02c000b0000f000b0b0b0b07171707130303130b0b0b42cdc2d0fa0f000106c02c2c0001c1c1c1c1c1c1c1c1c1c1c1c0c0c0000c0c0303030303a0303a0f0f82e0b81e0780e030000000000005f1b5f57c6d7d0b0b0b0b07070707030303030fa0f00 24 16777215 10 1023
def hc_71_19 : Nat → Nat := unpackHintV5 0x93348da34d3008a1c6321572607f54c11f0c19277ec889c7d2fc6c98ab991d41260188b97f901a5f880b96c12425508bf93fb28e47411590a125e3e38898e0131a37c0088cca24c2d30bf0a9816827a05809011ce1ee8a385b940211c0a4825a42c045ca1800022e 0x83e07070707a81e07a03030303a80e03a0303030382ea7aaaaaaa8000000000329c00001f002c088008330001c007000c2020007c2c2c7ea61b90707070703030303aa00010dc01c1c1c1c0c0c0c0c0c0c0c0e0ba9e82c2e070781c1e0380ea070707070707070703030303030303030b0f0b000000ca70000000002c00b001c007000c03c0800b02c000b0cc0000b0b0b0b07070707030303030fa0f0b0b0b42c6c2d00010dc01c2c1c1c0c0c0c0c0c0c0c0e8aaaa800000329c00000b002c023008c0030808000b0b0b0b2323232303030303aa00010dc282e81eaa81c1c1c1c1c1e80c0eaa80ccc0c0c0c0c0c0c0c0eaaa82ea7a07aaa8000000000329c000083300220002c00b001c007000c2020021b9a90b0b0b0b0707070703030303aa00010dc01c1c1c1c0c0c0c0c0c0c0c0e82c2e0ba9e0781e0380ea070707070707070703030303030303030b0b0b000000ca7000000003c27007c00b001c007000c03c0800f03c000f0cc0001f0b0b1f07070707030303030fa0f0f0f0f43c6c3d00010dc01c1c1c1c0c0c0c0c0c0c0c0c1c1c1c1c0c0c0c0c00000329c00001f002c007001c00300f020001c1c1c1c0c0c0c0c00043700707070703030303030303030303030303030f0f0707070707070707a08aaaaaaaaaaa1f02c0701c03204c4c282207c2c2c7c1c1c1c1c0c0c0c0d6c6d6d5b1b5b6a8272720f81c1c1c1ea0781e80c0c0c2c0c0c0c7eaa80e80c0ea80c0c0c1c0c0c0c1c0c0c0c0ea0380e80c0c0c0c082ea7aaaaaaaaaa0383ea87c0b2822700701c0303130303000ca7881f0b0b1fa986e41c1c1c1c0cdc0d03030340c0c0c0ea8272701c1c1c1c0c0c0c0c0c0c0c0c0c0e80e03030707070707070707030300300c0e0b0382c2e070781c1e0380e80c0e83c3c2c0b01c0700c0304c4c02c2c03c80b0b0b0b0707070703030303671b6759c6d9d0fa0f09c9c070707070303030b0303030b03030307030303070303030303030303020ba9e82c2e070781c1e80c0e80c3e0380ea070707070707070703030b030303030303030303030b0b03030303030303030b0f0b0b02c0701c0303130303000ca70f202c2c02c9c02c2c2c2c1c1c1c1c0cdc0d03030340c0c0c0c3e83c2c2c2d0b1b0b4272701c2c1c1c0c0c0c2c0c0c0c2c0c0c0c8c0c0c0c8c0c0c0c0c0c0c0c0c0aaaaaaaaaa0b02c2308c0303130303000ca7880b0b0b0b2323232303370340c0c0d03030303aa09c9c69e1c6e9d871b0f81307070707030303030303030303030b0b030303030707070707070707a08aaa82e81eaaaaaaa0b02c0701c0303080329c4c4c282202c2c2c2c1c1c1c1c0c0c0c0c6e1d871b6a82727282e81eaa81c1c1c1c1c1e80c0eaaaa80c0c0c0c2c0c0c0c2c0c0c0c1c0c0c0c1e03aa80c0c0c0c0c0c0c0c0c0aaaa0ba9e81eaaaaaaa89c2802c0b01c0700c0c4c0c0c00329e221b9a90b0b0b0b0707070703370340c0c0d03030303aa09c9c0707070703030303030303030380c0c0c0e81c1c1c1c1c1c1c1c0c0c00c030382e0381e0780e03a0303a0b0b1f02c0701c0300c131300f0f00f207c2c2c7c1c1c1c1c0c0c0c0d6c6d6d5b1b5b43e83c272701c1c1c1c0c0c0c2c0c0c0c7c0c0c0c1c0c0c0c1c0c0c0c0c0c0c0c0c0a0b0b82ea781e0780e80c0e80c0c3c3e0380ea070707070707070703030f030303030303030303030f0f03030f3303030303030303030b0b0b1f02c0701c0303130303000ca70f203c3c0f00f0f272701f0b0b1f0707070703370340c0c0d030303030fa0f0f0f0f43c6c3d09c9c070707070303030b0303031f03030307030303070303030303030303001c1c1c1c0e03030380c3c0c0c0c0c9c2701c0700c0c9c0c0c00329c9c2701c1c1c1c0cdc0d03030340c0c0c0c272702c1c2c1c0c2c0c2c0c1c0c1e8a0b83e0780e0f00a007071717171707071313030303030b0b0f0f0000000000000000b0b0b0b07171707130303130fa0f1b1b3b46c6ced000b070b07030b030b0307030782ea7a0b0b83c3e130780e0fa81c1c2c2c2c5c1c1c2c4c0c0c0c0c2c2c2c3c2c0000000329c0000000b002c0070bc0170ac01300f03c08800b02c000b00000b0b0b0b07171707130303130fa0f0b0b0b42c6c2d00010dc29e9c6d1b17070b07030b031303070307a0b0b82ea720f81e0383e80001c1c5c5c5c5c1c1c4c4c0c0c0c0c3c3c2c2c0000000000329c0000001b0b0b1f07171707130303130fa0f1b1b46c6e7d0017070b07030b031303070307a0b0b82ea783e0780e0fa81c1c3c3c3c5c1c1c3c4c0c0c0c0c3c3c2c2c2c0000000329c0000001f002c0070bc0170ac01300f02003c0f0003c00006c2c2c7c1c5c5c1c4c0c0c4c3e83c3c3c3d0f1b0f40004370070707070307030703070307132f132f0707070707030307000000001b4b1b4b07070707070303071b13132f00171717170313031303130313132b132b1317131713030313000000001b2b1b2b17171717130303131b1313001707170703130313030703071313071713071303031300000000ca70007c00b001c005c009c03c08001b1b07171707130303131b131300010dc04c4c2c2c2c2c3c3c1c1c1c1c1c1c1c1c1c1c1c1c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0e0b83e8280c81e0780e031f02c0382801c0700c0300c81f0b0b1f3b1b3b4ec6ced07070707030303030fa0f09c9c031303070707070303030703070303030b03a7030303030303030303030382e0fa030fa030381e0780e030f1f0b0b0b0b0f0f0303030303030f0f03030f0303030307070707070707070303030303030303007c0b00c0c00c9c01c0700c0308a7a0a87c2c2c7c0c0c0d03370341c1c1c1c0c0c0c0c3e83c3c3c3d0f1b0f4272702c2c2c2c2c2c2c2c1c1c1c1c1c1c1c1c1c1c1c1c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0e80ca082e0b81e0780e03a003802c0b01c0700c0300c203f1b3f4fc6cfd0b0b0b0b07070707030303030fa0f09c9c03030b03070303030303070707070703030303030303030b03a7030307030303a0303a030f82e0b81e0780e0303030f030303030303030303030f0f0b0b0b0b0b0b0b0b07070707070707070303030303030303000c0c9c9c00c0c0300b02c0701c0300c229e82a03370340c0c0d0b0b0b0b07070707030303030fa0f0f0f0f43c6c3d09c9c2f072f070313031303070307131f130b130b131307071313132307070f0f0f83e0f83e0780c3e0f0fa0f2809c2701c1704c4c03272804e00f206c6c6c6c1c6c6c1c4c0c0c4c4c4c4d131b1343e83c1b1b0bc5cbc5ccccc5cbcbc5e0f83e0f83e0f83c3c7c3c2c3c2c3c3c3c1c3c3c3c8c3c1c3c3c0c3c0c3c3c02709c1705c2709c229e82a172f2f1733330fa0f0f0f0f43cdc3d09c9c 26 67108863 11 2047
def hc_71_20 : Nat → Nat := unpackHintV5 0xa00006a7e902e9b1492253d3108fc8a5a3031de878890a0632fe7de4751e4a25e78e4089d1324c6e3cc21a3a2aa65d462980e2ce5c687a15f624852e49e93c31ec4960b591572023bf92c8d852f22d351c0a0628e1ff50486ae29e127508834c2a204ed088000276 0x1a78b1ba762c6c3e07c1c1c1c1c0c0c0c0c0c0c0c0e82281c1c1c1c1c1c1c1c0c0c0c0c0c0c0c0eaaaaaa80ea7aaaa0b0b202c1c07070700c0307c7c282202c2c2c2c1c1c1c1c0c0c0c0c6e2d8b1b6a8272700070b07070707070707070707070707aa82e0baa82ea82ea0ba81ea0703030303030303030303030303030303a03aaaaaaaaaaaa03a9c2c2c7c2c2c00b29c1c0707072270a00300c880b1b0b42c2c2d0b0b0b0b070707078de6a40c0c0c0ea82727000b0b230b070b0b0b0b070b0b0b0b0b030b0b0b030b0b0b0b0b172b2b170b82c2c2e0b0f0b0b0b0b172b2b1733330b0b1f0b0b002ca7170ac5c9c2709c2709c0b370b42c2c2d0b0b0b0b172b2b17333309c9c17070b07030b0313030703071f1faaa07071717171707070f0f000aaaa203a802800000000000006c2c2c7c1c5c5c1c4c0c0c4c6c6cfd1b1b3f6a8005c1c2c1c0c2c0c4c0c1c0c1e1fa82ea07a85ea0faaaaa03a9eaaa0002ca7000000000007c01c017004c13000c03022002000808001b0b0b1f0717170713030313a98de6a800041b007070707030303030303030382e0f81e0780ea7a0303031f0303030b03030307030303070303a80c3c0c000b29c00000000001f007001c003000c00f03c08800300c000304c0001f0b0b1f07070707030303030fa0f03030340cdc0d000106c01c1c1c1eaa87c7c1c1c1c1c1c1c1c1c0c0c0c0c0c0c0c0c0c0c002aaaa8002880000000000007c2c2c7c1c1c1c1cfc6cfd3f1b3f40c0c0c0ea8001c1c1c1ea0ba87ea07a81c0c0c0c0c0c0c0c0e80eaaaaaaa80ea70002ca700209c000000001f007001c0800220000c13000c030203c088001f0b0b1f070707078de6a40c0c0c0ea800041b0a7a71b46c5c1c2c1c0c2c0c4c0c1c0c1e0b83e0f81e80c0e03a9c1f1f0b0b0b0b0f0f0707171717170707a00003030000002ca7000000000006c2c2c7c1c5c5c1c4c0c0c4c3e83c6c6d1b1b9b4005c1c2c1c0c2c0c4c0c1c0c1e0b83e0f81e80c0e03a9c3c7c2c2c2c2c3c3c1c1c3c5c3c3c3c5c3cac1c1ea0303030002ca7000000000007c01c017004c003003c0800f03c000f00001b0b0b1f07171707130303130fa0f0f0f0f43cdc3d000106c05c1c2c1c0c7c2c0c4c4c0c1c4c0c5c1c4c7c2c0c0c0c4c4c1c1c4c4c4c5c1c1c0130b0b13071313071313030313131384c3c4e130f00000000000001b0b0b1b07171707131303031b1313131344c6c4d1313131300170b0b171f0b0b1f171717171f0b0b1f171717170002ca700000007c01c01700003003c08001f0b0b1f1717171700010dc01c1c1c1c1c7c1c1c1c2c1c1c00707070707070707070707030707070307072b2f2f2b070707070781c3c1e0707070707071705c01ca7070700707170701c1705c2b4b4b2b0707070707070741cdc1d070707072f2f2f2f05c5c07230707070703070307030703072b1f2b0b2b0b2b1faa0707a0707000aaaa2a00a000000000000001b2b1b2b07070707070303071b1b3f46c6cfdaa00072307070707030703070307030787ea0ba81ea07a81eaaaa80ea7aaa800ac01ca7000000000007c00b001c01c003022002000808001b2b1b2b0707070707030307a98de6a800041b00707070703070307030707030707131f130b130b13130303070707070703004c4c4c4c1c1c1c1c1c0c0c1c4e130f1384c3c00000000000006c6c6c6c1c1c1c1c1c0c0c1c4c4c4d131b1344c4c4c4c005c8c1c5c1c5c1cac1cac1c1c1c1cacacacac1c5c5c1c1c1cbc00ac01ca700000007c00b005c0003003c08002b2b2b2b0717170707074f2f4f2f00010dc05c7c5c2c5c2c5c5c5c1c5c1c0072b072b07031723070317170717070723072b2b2b2b1785c3c5e170f071717073307072f1705c5c9c0707070707001ca71701c1705c2b2b2b2b17171745c8c5d07171707330707332f4f2f05c5c074b0707070707070707070707072b2f2f2b0707070707070707000001ca7000007c00b001c01c003003c08002b4b4b2b07070707070707072f2f2f2f00010dc01c1c1c1c1c1e9c1c2c1c1c1c2c1c0c1c0c1c0c0c1c1c0c0c1c1c0c0c1c0c0c1c7c7c2c2c2c2c4c7c7c7c7c7c4c7c4c4c7c7c9d2c4c7c4c4c1c1c1c1c1c1c1c1c8c8c1c1c0130b0b1f1387c3c4e1f0f070723070707070303071384c3c4e130f1702c171701717007007000ca7030300303031704c1b0b0b1f1b1b1f46c6c7d0707230707070703030713271b46cdc4d1b13132f05c5c07070b0b070707070707070707070707070b0707070703030700c0c00c1c0c1c0c1c0c1c4e2f0f138bc3c2c2c2c2c1c1c1c1c1c0c0c1c0c0c01c0c02c0b01c0701c0305c1306c6ced1b1b3b42c2c2c2c1c1c1c1c1c0c0c1c6c4c4cbc171701c1c1c1c2c1c1c2c1c1c1c1c1e9c0c0c1c1c0c0c1c1c0c1c0c1c0c1c0c1c2c2c9c2c2c2c2c2c2c2c2c2c2c4c4c2c2c2c2c2c2c2c2c1c1c1c1c1c1c1c1c00b82c2c2e0b0f0b0b0b0b07070707070303071384c3c4e130f0b0b172700b0b02c02c0b01c0700329c0c0c00c0c0c5c1302c6c2d0b0b0b42c2c2c2c1c1c1c1c1c0c0c1c4c9c6d1b371346c4c4cbc171702c1c2c1c2c2c2ea0b0b07072b232b230707030b030b030703070303003030b20b82e0f81e83c3e83c3e0383c2c0b01c1702c0c00c0c02c0303c80b0b0b0b072b1b071b1b3b46c6ced130303130fa0f09c6c0b070b07030b030b030703070b0b0b0b0b0b0b0b0707131313230707020ba9e82c2e0f0f84c1e0383e83c3e83c3ea07070b0b0b2307070b13030303030b0b0b130b130b0b0b0b0b130b0b0b0b0b0b0f0b0b02c0705c00ca7030300303030f202c2c02c9c02c2c2c2c1cac6c1c4c0c0c4c4c4c4d13371343e83c2c2c2d0b1b0b4271b07c1c2c1e82c2c2c2c4e07072b232b230707030b0313030703070303003030f20b83e0f81e82c2e83c2e0383c7c0b01c1703c0c00c0c03c03030303c81b0b0b1f072b1b071b1b5b46c6d6d130303130fa0f09c6c1f070b07030b031303070307131f0b0b0b0b131307071313132307070282c2e0ba9e0f81e0383e83c3e83c3ea07070f0f0f2307070f130f13030303030f030f0f0f130f130f0f0f0f0f130f0f0f0f0f0b0b0b1f02c0705c00ca7030300303030f203c3c03c9c06c2c2c7c1cac6c1c4c0c0c4c4c4c4d13371343e83c3c3c3d0f1b0f4271b01c8c1c1c1c1cac7cac2cac2cac7c1c1c1ea070703070307030703070303003030720f83e81e81e81c1e81c1e0381c5c1701c0701c0c00c0c01c0303c81b2b1b2b070707071b1b4f46c6d3d070303070fa0f05c5c0723070707070307030703070307131f130b130b13130707070707070707020f0f84c3e07a9e81c1e0381e83c3e83c3c3c7c3c2c3c2c3c3ea07070303030307070f130f130f0f0f0f0f130f0f0f0f0f0707071705c0701c00ca7030300303030f203c3c03c5c06cac6cac1c1c1c1c1c0c0c1c4c4c4d13371343e83c3c3c3d0f1b0f4171701c1c0c4c0c4c0c1c0c1c9c7c4c2c9c2c4c7c1c1c4c8c9c8c1c1c01313071307130303131384c3c4e130f2709c0705c00ca7030300303032704c1b1b071b071303031313271b46cdc4d1b131309c6c 26 67108863 11 2047
def hc_71_21 : Nat → Nat := unpackHintV5 0x960cafa4812048c68b3a15d37a80b0989e8d33e76e06a9c8925e6f00649af119e68986598d32a65d38c2954940a50e08892bd2f646089d90981d43df08e0dff2fa342c7a0bef2382b7089894932620309e87421941a4c5785bc1ae10fcbe8304276036d1480001b6 0x23230723072b072b072b0707070783c3e2b0f81ea7a070781e0f0f1f0f0b0f0b0f0fa83c1c0c1c0c3c3c1c1c1cac5cac5c1c5c5c1c1c1c5c3e83c3c3c3c0f270f0acacacac1c8c8c1c1c1d3c3e83c3c3c3d0f370f45d3c5ea0ba87c8c1c8c1e83c1c4c1c4e03aa8bc1cbc1c1c8c1e8aeaaaaa07a9ea8ac5cac5e278a80717170713070713aa2b2b2b2b8be6a41c8c8c1c4c1c1c4ea85d3c5c1d2c1c1c1c1c1c1c1c1c1c1c1c1e0f83e81c1e07a9e0781c1c7c1c1c1c2c1c1ea0707070307030707070f071717171707070707070707070fa0f07070701c5c1c2b4b4b2b07070707070707070fa0f07070741cdc1d17171717070707070707a7070b0707070b0703070307030307070303070703030703030787ea0ba87e1faa87e4baa81e07a81e23a81eaaaaaaaaa80ea7aaa87c2c2c5c7c7c5c1f271701c1c8c1c1c1c1c0c0c1ea2278aa1b0b0b1f1b1b1f46c6c7d07072307070707030307a98de6a85ccc6c5c1c1eaa81c1eaa81c2c1e070703030707030307070307030703070307aaaaaaaaaa3327170cc9c5c0b0b0b0b0707070707030307aa1b1b3b46c6ced0b0b0b0b0707070707030307aa17331b17070707070b07070b0707070707a70303070703030707030703070307030782eaa82e0baa82ea0ba81ea07a81eaaaa82e0faaaa80ea7aaa82c9c2c0b0b0b02c2c2c2c1c1c1c1c1c0c0c1ea2278aa0b1b0b42c2c2d0b0b0b0b0707070707030307a98de6a85ccc6c5c1c1c0c4c0c4c0c1c0c1e1fa82ea07a88ea0faaaaa03a9eaaa333307330713030313a889e2a86c6c1c6c1c4c0c0c4ea6379aa1b331b07070707030303030303030383e0f81e0780ea7a0303031f0303030b03030307030303070303a80c3c0c1c1c1c1c0c0c0c0c3e83c0c0c0c03270301c1c1c1c0c0c0c0c3e83c0c0c0d03370341c1c1c1ea0ba87ea07a81c0c0c0c0c0c0c0c0e80eaaaaaaa80ea70707070789e2a00c0c0c0ea81c1c1c1e379a903030303aa0707070703070307030703a0f83e0780e0381c5c5c5c5c1c1c1c1c1c0c0c1c3e83c6d2c6d2c1c1c1c1c1c0c0c1c3e83c5c5c5c5c8c8c8c8c0c4c0c4c0e031383e0f80e0f80e0f2b2b2b2b23232323130303130fa0f1b2b1b2b1b231b23130303130fa0f1b331b2f072f07031303130307030783e0f83e07a030380ea70f1f0f0b0f0b0f0f07070f0f0f0f230f0707a80c0c0ccccc1cbcbc1c4c0c0c4c3e83c3c3c3c0f270f06c6c1cbc6c1c4c0c0c4c3e83c3c3c3d0f370f46ccc6c7c1c2c1c0c7c2c0c4c4c0c1c4c0cac1c4c0b0303030070713071313132313230707131313130b0b1307131307130303131384c3c4e130f1f02c0705c131300c9c0b0b0130b01304c1b0b0b1b071b1b071303031313131344c6c4d1313131306c6c001c1c1c1c1c1c1c1c1c1c1c1c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0e0b83e83c3e83c3e0781e03a9e80c0c0c7c0c0c0c2c0c0c0c7c0c4c0c0c0c0c0c7c0c4c0c0c0c0c0c1c0c0c0c1c0c0ea030f0302ca70b0b00b0b0b0701c0300c0f200c0c00c9c07c2c2c7c7c6c7d1f1b1f41c1c1c1c0c0c0c0c3e83c0c0c0d0337034272701c1c1c1c0c0c0c0c0c0c0c0e2a801c1c1c1c1c1c1c1c0c0c0c0c0c0c0c0eaaaaaaaaaa02c0701c0300c0b0b0a0881f0b0b1f07070707030303036f1b6f5bc6dbdaa09c9c001c1c1c1c1c1c1c1c1c1c1c1ea0ba87eaa1faaa1f87ea07a81c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0e80eaaaaaaaaaaa80ea702ca70b0b00b0b0b0701ca27270a200300c881f0b0b1f1f1b1f47c6c7d070707078de6a40c0c0c0ea82727001f0b0b171f1f17071f2317071f0b0b1f1f031f1f031f1f172b2b171f0b0b1f1f87c3c7e1f0f172b2b17333302ca70b0b00b0b0b1705c2709c2709c1f0b0b1f1f1f1f47cdc7d172b2b17333309c9c0b070b07030b030b03070307aa0b0ba07071717171707070f0f000aaaa2a00a00000000000000b0b0b0b07171707130303131b1b3b46c6cedaa000b070b07030b030b0307030782ea0ba81ea17a83eaaaa80ea7aaa80b29c00005c0000000002c01c017004c003022002000808000b0b0b0b0717170713030313a98de6a800041b007070707030303030303030382e0b81e0780ea7a0303030b0303030b03030307030303070303a80c3c0c0b29c00001c0000000002c01c007000c003003c0800300c000304c0000b0b0b0b07070707030303030fa0f03030340cdc0d000106c01c1c1c1e82c2ea81c1c1c1c1c1c1c1c0c0c0c0c0c0c0c0c0c0c002aaaa8002880b0000070000000002c2c2c2c1c1c1c1cfc6cfd3f1b3f40c0c0c0ea8001c1c1c1ea0ba82ea07a81c0c0c0c0c0c0c0c0e80eaaaaaaa80ea702ca70000070000000000b007001c0800220000c00302020002c2c2c2c1c1c1c1e379a903030303aa000106c02c1c2c1c0c2c0c2c0c1c0c1e0b82e0f81e0380b0b0b0b0b0b0b0b0707171717170707a000030300000000000000000b0b0b0b07171707130303130fa0f1b1b3b46c6ced000b070b07030b030b0307030782e0b83e07a030380ea70b0b0b0b0b0b0b0b07070f170f0f0f170f2b0707a80c0c0c0b29c00005c000000003c27002c01c017004c003003c0800f03c000f00000b0b0b0b07171707130303130fa0f0f0f0f43cdc3d000106c02c1c2c1c0c2c2c0c2c2c0c1c0c1c0c0c2c2c2c2c2c0c1c1c4c4c4c5c1c1c00b0b0b0b07131307130303131384c3c4e130f00000000000000b0b0b0b071717071303031313131344c6c4d13131313000b0b0b0b0b0b0b0b171717170b0b0b0b1717171702ca7000017000000b007005c0000c00f020002c2c2c2c5c5c5c5c00043700b02c2c2c2c2c2c8c8c8c8c2c2c2c2c8c8c8c8ccccc2c0b07c2309c2709c2702c2c2c2c8c8c8c8ccccc272701c070707070707070707070b0b0b0b07070707070707070b02c0701c1c1c0701c1705c0b0b0b0b07070707070707072f2f2f2f05c5c0b070b07030b0b030b0b03070307030300b02c0c1c1c4c4c4c8c1c1c2c2c2c2c2c2c2c1c4c4c1c4c0c4c0c4c4c4e130f1384c3c2c0b01c1704c4c032704c4c04c7c04c1302c2c2c2c1c6c6c1c4c0c6c0c4c4c4c4c4d131b1344c4c4c4c1b1b01c0707030303030303030382e0b83e0f80ea7a0303030b0303030b03030323030303230303a80c3c0c2c0307c0700c0303c803030032700b0b0b0b23232323030303030fa0f03030340cdc0d09c9c001c2c1c1c1c1c1c1c1c1c1c1c1c1c1c0c0c0c0c0c0c0c0c0c2c0c4c0c0c0c0c0c0c0c0e82c2e82c3e0b82e0781e03a9e80c0c0c2c0c4c0c0c0c0c0c2c0c2c0c0c0c0c0c2c0c0c0c2c0c0c0c1c0c0c0c1c0c0ea030f030b0b1f0b0b002ca70701c1c1c0300c0f200c0c00c9c02c6c2d0b0b0b42c2c2c2c1c1c1c1c0c0c0c0c3e83c0c0c0d0337034272701c0707a82ea0ba88ea230303030303030303a03aaaaaaaa03a9c2c81f01c89c2800c032202c2c2c2c8c8c8c8e379a903030303aa09c9c 26 67108863 11 2047
def hc_71_22 : Nat → Nat := unpackHintV5 0x90496a46347c222a3c109d1e081f0be3f905a1ec8400f0a168745100369ce319f8558c801f06070e42d24c515345789dd2f44851a6210cc70ee46886af30c30255516686a89c75b444a2662000940e8e5c85fa53428f1b80e658504dc95816d4040002da 0x707070b0b1f0b0b0707070b07a707030b0b07030b070b070b070707070b82c2c2e0b0f0b0b0b0b0723230707072f0b270b02c2c2c0b0b0b0b071717070707172f17170b370b42c2c2d0b0b0b0b0723230707074f2f4f2f174f170707070707070707070707070707130b0b1f0707070707070707170b0b170707070707070707171313171b0b0b1f07070707070707071b13132f171717170707070703030303030303031f0b0b1f0707070703030303170b0b170707070703030303171717171f0b0b1f07070707030303032f2f2f2f171717170707070707070707070707070f0b0b0f0707070707070707170b0b1707070707070707070f0f0f0f1f0b0b1f07070707070707070f0f0f0f1717171707070707aaaaa07070707070707070707aa170b0b1707070707aa070707071f0b0b1f07070707aa07070707171717170707070707070707070707071f0b0b1f0707070707070707000000001f0b0b1f07070707070707072f2f2f2f0007070707170b0b1707071707070707070707070707070707070707071f0b0b1f0707070717171717070707071f0b0b1f0707070717171717070707072f2f2f2f0707070707070707070707071f0b0b1f0707070707070707170b0b170707070707070707171717175555555555070707071b0b0b1f07072b07070707070707070707070707070707071f0b0b1f070707072f1b1b2f07070707170b0b170707070717171717070707071717171707070707070b07a7071f0707070707070707070707070707070307070707070307071f0b0b1f07072b0707070781c1c3c1c1e070707070707170b0b170707170707070707070701c1c5c1c07070707171717171f0b0b1f07072b0707070707070741c1cdc1d070707072f2f2f2f17171717031f03070707070303030703070303030b03a703030303030303030303031f0b0b1f0380c3c0e030307070707030303031f0b0b1f03030300c9c0c07070707030303031f0b0b1f03030340cdc0d070707070303030307030707030703070307070307070b0b0b0b07070707070303070b0b0b0b0707070707030307171313170b0b0b0b07070707070303071b13132f171717170b0b0307030b030b031303130b0b0b0b13231323130303130b0b0b0b23232323130303133313130b0b0b0b1b231b23130303131b13131b331b0b070b07030b03a703030b0b03072b032b0703030307070b0b0b0b230b07070b1f0b0b0b0b0b072b1307130303130b82c3c2e0b0b0b0b0b0b072b2b07130303130b0b0b02c9c2c3313130b0b0b0b072b1b07130303130b0b0b42cdc2d1b13131b331b03030b03070303030303070707070703030303030303030b03a70303070303030380c0c0e030f0b0b0b0b070707070303030303270300c0c0c0b0b0b0b070707070303030303370340c0c0d0b0b0b0b07070707030303031f070b0703030b0b030b03a7030703070303030707131f1f2307070b0b0b130b0b1f072b1307130303131384c3c4e130f1f0b0b1f072b2b0713030313131f1f07c9c4c3313131b0b0b1f072b1b0713030313131f1b46cdc4d1b13131b331b074b07070707031f0303030b030303070303030303030703a7030303030303032b2f2f2b070707072f070380c3c0e0303030303031717171707070707170703030300c5c0c03030303171717172b4b4b2b070707074f0703030340cdc0d030303032f2f2f2f171717170707070703072b030707030703a7030307070707070b0707071f030303070707132b132b07070707070303070781c1c1e070f2b172b17070707070703030707230701c1c1c2f1313171b2b1b2b070707070703030707230741c1c1d1b13132f17331b170303030b0303031f07230707070703030703032b03030303030303030303030703a72b2b2b2b0380c0c0e030f070707072307030303032b172b1703270300c0c0c070707072307030303032f17172b2b2b2b03370340c0c0d070707072307030303032f4f2f174f17070707070307030703030707030703a7071f0707070b0707030303070707132f132b07070707070303070781c3c1e070717171717070707070703030707070701c5c1c171313171b4b1b2b070707070703030707070741cdc1d1b13132f171717171f070b07031f0b031313030713032b07130f0b0303030f0f070713071313132313230707aaaaaaaaaaaa87c2c2c7c1cacac1c4c0c0c4c4c4c4c1327132a86c2c2c6c1c6c6c1c4c0c0c4c4c4c4d131b136a86c6c6c6e0f87c2c2c7ea0788e87c2c2c4ea80e8ac4cac4e0ba9eaaaaaaa1f0b0b1fa889e0acacacac4c4ea87c2c2c7ea63792b2b2b2b1313aa0b070b07030b0b030b0b030703070303a0b82c0c1c1c4c4c4c8c1c1c2c2c2e0b82e0f81e030f83c3e83c3e83c3c2c2c2c2c1cacac1c4c0c0c4c4c4c4c13271303e83c2c2c2c2c1c6c6c1c4c0c0c4c4c4c4d131b1343e83c6c6c6c6c2c2c2c2c2c2c2c2cbcacacbe0ba9e82c2e0f0f8ac3e0f83ea0b070b0b0b230b070b0b030b030b0b0b0f0b0b0b0b0b2f2b2b2f0fa0f0b0b0b02c9c2c0b0b0b0b2f2b2b2f0fa0f0b0b0b42cdc2d0b0b0b0b0b0b0b0b23132313aaaaaa0b0b0b0b232323231313aa0b0b0b0b232323231313aa070707070707070707070707aaa07aaa82c2c2c2c1c1c1c1c1c1c1c1ea82c2c2c2c1c1c1c1c1c1c1c1ea85c5c5c5c2c1c2c1c0c2c2c0c2c2c0c1c0c1c0c0c2c2c2c2c2c0c1c1c4c4c4c8c1c1eaaaaaaaaaaaa0b0b0b0b072b2b0713033303131313131304c9c4caa0b0b0b0b071b1b0713031b03131313131344c6c4daa1b1b1b1ba0ba23aaa070b0b0b0b80eaa0b0b0b0b2f132b13aaaa0ba9e8aeaaa89e2a02c2c2c2cbcacacbc4c4eaa379a90b0b0b0b2f2b2b2f1313aa1f070b07031f0b031313030713032b071382c0c0c0e81c1c4c4c4c8c1c1c3c3c3e0b83e0f81e030f83c3e83c2e82c2c7c2c2c7c1cacac1c4c4c0c0ccc4c4c4c4c13271303e83c6c2c2c6c1c6c6c1c4c4c0c0c6c4c4c4c4d131b1343e83c6c6c6c6c7c2c2c7c7c2c2c7cacacacae82c2e0ba9e0f83e0f83ea0f070f0f0f230f070f0f030f030f0f0b0b0b1f0b0b1f2b2b2b2b0fa0f0f0f0f03c9c3c1f0b0b1f2b2b2b2b0fa0f0f0f0f43cdc3d0707070787ea0ba81e07070707070707070707a81e03aaa81ea7aaaaa85c5c5c5c1c1c1c1ea217807070707aa2b4b4b2b07070707a98de41c1c1c1ea85c5c5c5c1c1c1c1c0c1c0c1c0c1c1c0c1c1c4c7c4c2c4c2c4c4c0c0e81e070307070f83e0f81e0780c1e070fa0707a07072b172b17070707070703030713131304c9c4c0fa0f1b1b1b1b070707070703030713131344c6c4d0fa0f171b1b17 25 33554431 10 1023
def hc_71_23 : Nat → Nat := unpackHintV5 0x19031c334c3000334 0x70707070b07a70b0b07070b0b0b070b071f07031f4b07031f1f074b070723071f0b0b1f1f87c3c7e1f0f07232323074b07072f1f0b0b171f1f1707c9c5c07172317074b0707172f17171f0b0b1f1f1f1f47cdc7d07232323074b07074f2f4f2f174f17070b07a707070707070b07070707070707070707070707030707070307070b0b0b0b070707070781c3c1e0707070707070b0b0b0b0707070707070701c5c1c07070707171717170b0b0b0b0707070707070741cac1d070707072f2f2f2f171717170707070703070b0307070307070307070303070707070703030307070707070307070b0b0b0b0b07070707070303071384c3c4e130f0b0b0b0b070707070703030713131304c9c4c131313130b0b0b0b070707070703030713131344c6c4d13131313171b1b17 22 4194303 10 1023
def nh_71 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_71_23 (Nat.sub p 736)) (hc_71_22 (Nat.sub p 704)) (Nat.blt p 736)) (hc_71_21 (Nat.sub p 672)) (Nat.blt p 704)) (Bool.rec (Bool.rec (hc_71_20 (Nat.sub p 640)) (hc_71_19 (Nat.sub p 608)) (Nat.blt p 640)) (hc_71_18 (Nat.sub p 576)) (Nat.blt p 608)) (Nat.blt p 672)) (Bool.rec (Bool.rec (Bool.rec (hc_71_17 (Nat.sub p 544)) (hc_71_16 (Nat.sub p 512)) (Nat.blt p 544)) (hc_71_15 (Nat.sub p 480)) (Nat.blt p 512)) (Bool.rec (Bool.rec (hc_71_14 (Nat.sub p 448)) (hc_71_13 (Nat.sub p 416)) (Nat.blt p 448)) (hc_71_12 (Nat.sub p 384)) (Nat.blt p 416)) (Nat.blt p 480)) (Nat.blt p 576)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_71_11 (Nat.sub p 352)) (hc_71_10 (Nat.sub p 320)) (Nat.blt p 352)) (hc_71_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (Bool.rec (hc_71_8 (Nat.sub p 256)) (hc_71_7 (Nat.sub p 224)) (Nat.blt p 256)) (hc_71_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (hc_71_5 (Nat.sub p 160)) (hc_71_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_71_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_71_2 (Nat.sub p 64)) (hc_71_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_71_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)) (Nat.blt p 384)
def f_71 : Nat → Nat × Nat := unpackForestF 0x18be00c5bb7db080315ed66916b344b59245ac912d62916b144b58245ac110018a600b5fb49ae5a4d50016b600b57005a9802d3c0169600b47005a1d94d64014bf6424e0052dd891b2c48c1623610052bd84938014a600a4fafd2700292c0148e00a43ae6b7d74df2b9ace00a3f0051d8028deb44b95a25400519d5ed66af47758468abd1b80257ead2895334fa99a5d54572a668f54134a99a1d4c538012b74dc6ca6e30536d86a1af94da3ba72be53a0fe9d0674e470a6d1b80255e9928948b4fa45a5d2c5729168f4a02ba4c9a522d0e9129c00953004a7d1c5128c69f4614e004a580251c012874056fa1dbe50159e854894026ba0d2250098e814894025b0049fcf4dbe7a6d73e57c9e9b3cf4d8c012773c4689b937cec9726e4d738d7c9c81fce40ce718e1372679bd2e4dc98c0126f36134999b5cd40ae6926933363998ae4cc550012673226498237cc49f2608cf3024e00497cbc5925a8df2e17c96a33cb4538012572356f95db848d59e556d12346f93417ca44f24d0572682793c1649c4d24d0472637091a33c94d82468af23c6e91e2b48cd080124f221648b637c831924128916c6b8fcbe45b19e3c0771e0338eca245b18e306bf1902f8c815c6c4f23204f199348cc1246408e314c1183578b51a45d19a2d29c00923871acc388ee298d10e2378709dc4d1a21c26f1226487097c445921c2571036887093c3a8d21d2c90e1230042fc341120369f01b4b85c2e406d1e1506901b4384c2240693e034970805c80d23c1c092034870603480d1fc14092034770404c80d1bc0ad120504901a3380c2700216de08d8f0460781b0bfd5f1e0476fcd7c7e89fbf44cdf98e0f02377debe3c04edf2af8f9a3f7cd19be51c1e026ef7d7c7bd3e3c04bdecaf8f617c78095bd15f1e9496f437078093bc35f1e38d8f223b78d303c28d1e12f8f01230042bbbc111ba69edd34b76c2e374d1dd9256ec0346e9a1bac111ba49edd24b74c2e37491dd127ee80246e921b9c0d1ba47ee60246e91db94131ba46ede3446f51a37a53dc4688e225c6f4a5b84901c1468de9476fca637c951bd286de0246e919b74138010a60084f6dc22362d3db5088d8a4f6cc263628ddb109c0084b6bc9380211c01086ce56f6adbe33959da9488ce26b69d2233898da5488ce25b68ca23385ada1288ce16367ca233856d9d288ce1230041fb18dbd8c6d6cc57c631b3b18d8d8c4dec626b64ebe31899d8c4c6c623f6311db188dd8d688c62330041db151a15b4dec425c56d35b075f18427ec213360e382b699d814b8ada635fe342b65bd7d2b8ad96b5e2be2f28fd79466bc47056cb3aec5715b2c6ba25c56c97ae45715b256b426f5bdbe2d09ad6daf8b42675ad362d2dd1694c8b426359da82b649d5f4beafa5b58a362c45b15f4aeb025457d29abc9015c468ae15c56c918020dd59068a136b55c95aac0d1426c6aa02450935aa44fd51048a126351cb7a9c9f1472d6a657c51cb3a945b1484e8a416451cb1a8c09142466a105c50c91a8415001066a02644c237a7c9f1308ce9824e4ed322605bd392689816b4dabe26c9f1302ce9a1344c0b1a6052d314b89814700417a5c1911e8de9607c47a33a541911e4de9402447935a4b5f1250f88f26748c1223c98d1e4969005c47923a3c1380105678d6f46db81e359d196d078c6f44497a2c8f1112568892744c962248d111246883703c633a1cd80f18ae85c6e42e2b1e2d09096d07896f41ca61e25ad03af88224b40db81e259d01298789633fca61e256cf12ae7894b3cd379f4df0f34d67c57c3cd339ec9b0f46e87a2643cd319e4d40f128e008273bc321451bcec8c87604428a359d41f0a28ce7393b39c999cc110a28c672064289379c4090a24d66fd7c37c3e14499cd729e6e25c35ca59ae51cd92986c25435ca19ac090a24c66a0442892794492cd10b8512473153218c5bccd4f86316b32ebe18c59cc92d863a7431cb218c58cc504851243295af9784bcbc2566003c2f09397a8d0bd0285e1232ed3014ad5ca52be5295b2d63616c8ecb54c0529572c41d964900b106e58014294a994a4eca74be53a5b2aa361541b0a74ae5425429d2994c900a526e5113428e3314413801046501642423793c5f0908ce4e164241b79344d0906d64bd7c25cbe120d9c9526848363241a59245709068e4814e0040f91c1907e8de4607c1fa339141907e6de440341f9b590b5f0850f83f36720c1a0fcd8c7e6964005c1f9a38fc1380103628d6f1ed380a359c794d028c6f1c49f8ec93071276389371cc9e0e49107126638270146338dc980518ae36268145b78d48e0516d63357c19ca58cc9c0516ce32238145b18c48e0516b628b57145a58ac5bc5d4f82b16b16ebe0ac59c592d82ba7415cb20ac58c554a028b4714a370a5158514840081713c320051bc4c8c82604400a358941f0028ce23a3b11d1988c110028c622064009b78840d0026d61fd7c0fc3e004d9c3749e1e35c0dd2586e91c394981c3540dd2186c0d0026c61a044009a7804d2c310b801347095b204c9bc2d6f81326b0aebe04c99c294d813b7409d3204c98c2506801343015af8384bc1c2561003c0709383a8d01d0280e12306cb000ad5c054be02a5b0563602c4ec152c002a570449d8241001126e080240152980a8ec072be0395b02a360141b0072ae0415401ca980c5000546e0112400e33004138010260003f 10 11
def ch_71 : Nat → Bool := dagCheckNodeV5 fullMask g_71 ep_71 6 63 bds_71 738 (dagTraceF fullMask rootStock 11 f_71) cur_71 nh_71
set_option maxHeartbeats 0 in
theorem rc_71 : dagCheckRootsV5 fullMask g_71 ep_71 6 63 738 bds_71 (dagTraceF fullMask rootStock 11 f_71) (cur_71 0) (nh_71 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_0 : treeBlockF 0 32 ch_71 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_1 : treeBlockF 32 64 ch_71 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_2 : treeBlockF 64 96 ch_71 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_3 : treeBlockF 96 128 ch_71 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_4 : treeBlockF 128 160 ch_71 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_5 : treeBlockF 160 192 ch_71 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_6 : treeBlockF 192 224 ch_71 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_7 : treeBlockF 224 256 ch_71 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_8 : treeBlockF 256 288 ch_71 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_9 : treeBlockF 288 320 ch_71 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_10 : treeBlockF 320 352 ch_71 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_11 : treeBlockF 352 384 ch_71 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_12 : treeBlockF 384 416 ch_71 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_13 : treeBlockF 416 448 ch_71 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_14 : treeBlockF 448 480 ch_71 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_15 : treeBlockF 480 512 ch_71 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_16 : treeBlockF 512 544 ch_71 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_17 : treeBlockF 544 576 ch_71 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_18 : treeBlockF 576 608 ch_71 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_19 : treeBlockF 608 640 ch_71 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_20 : treeBlockF 640 672 ch_71 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_21 : treeBlockF 672 704 ch_71 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_22 : treeBlockF 704 736 ch_71 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_71_23 : treeBlockF 736 738 ch_71 = true := by decide +kernel
theorem nj_71_1 : ∀ i, 0 ≤ i → i < 64 → ch_71 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_71_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_71_1 h1 h2)
theorem nj_71_2 : ∀ i, 0 ≤ i → i < 96 → ch_71 i = true := block_join nj_71_1 (fun _ h1 h2 => treeBlockF_at nb_71_2 h1 h2)
theorem nj_71_3 : ∀ i, 0 ≤ i → i < 128 → ch_71 i = true := block_join nj_71_2 (fun _ h1 h2 => treeBlockF_at nb_71_3 h1 h2)
theorem nj_71_4 : ∀ i, 0 ≤ i → i < 160 → ch_71 i = true := block_join nj_71_3 (fun _ h1 h2 => treeBlockF_at nb_71_4 h1 h2)
theorem nj_71_5 : ∀ i, 0 ≤ i → i < 192 → ch_71 i = true := block_join nj_71_4 (fun _ h1 h2 => treeBlockF_at nb_71_5 h1 h2)
theorem nj_71_6 : ∀ i, 0 ≤ i → i < 224 → ch_71 i = true := block_join nj_71_5 (fun _ h1 h2 => treeBlockF_at nb_71_6 h1 h2)
theorem nj_71_7 : ∀ i, 0 ≤ i → i < 256 → ch_71 i = true := block_join nj_71_6 (fun _ h1 h2 => treeBlockF_at nb_71_7 h1 h2)
theorem nj_71_8 : ∀ i, 0 ≤ i → i < 288 → ch_71 i = true := block_join nj_71_7 (fun _ h1 h2 => treeBlockF_at nb_71_8 h1 h2)
theorem nj_71_9 : ∀ i, 0 ≤ i → i < 320 → ch_71 i = true := block_join nj_71_8 (fun _ h1 h2 => treeBlockF_at nb_71_9 h1 h2)
theorem nj_71_10 : ∀ i, 0 ≤ i → i < 352 → ch_71 i = true := block_join nj_71_9 (fun _ h1 h2 => treeBlockF_at nb_71_10 h1 h2)
theorem nj_71_11 : ∀ i, 0 ≤ i → i < 384 → ch_71 i = true := block_join nj_71_10 (fun _ h1 h2 => treeBlockF_at nb_71_11 h1 h2)
theorem nj_71_12 : ∀ i, 0 ≤ i → i < 416 → ch_71 i = true := block_join nj_71_11 (fun _ h1 h2 => treeBlockF_at nb_71_12 h1 h2)
theorem nj_71_13 : ∀ i, 0 ≤ i → i < 448 → ch_71 i = true := block_join nj_71_12 (fun _ h1 h2 => treeBlockF_at nb_71_13 h1 h2)
theorem nj_71_14 : ∀ i, 0 ≤ i → i < 480 → ch_71 i = true := block_join nj_71_13 (fun _ h1 h2 => treeBlockF_at nb_71_14 h1 h2)
theorem nj_71_15 : ∀ i, 0 ≤ i → i < 512 → ch_71 i = true := block_join nj_71_14 (fun _ h1 h2 => treeBlockF_at nb_71_15 h1 h2)
theorem nj_71_16 : ∀ i, 0 ≤ i → i < 544 → ch_71 i = true := block_join nj_71_15 (fun _ h1 h2 => treeBlockF_at nb_71_16 h1 h2)
theorem nj_71_17 : ∀ i, 0 ≤ i → i < 576 → ch_71 i = true := block_join nj_71_16 (fun _ h1 h2 => treeBlockF_at nb_71_17 h1 h2)
theorem nj_71_18 : ∀ i, 0 ≤ i → i < 608 → ch_71 i = true := block_join nj_71_17 (fun _ h1 h2 => treeBlockF_at nb_71_18 h1 h2)
theorem nj_71_19 : ∀ i, 0 ≤ i → i < 640 → ch_71 i = true := block_join nj_71_18 (fun _ h1 h2 => treeBlockF_at nb_71_19 h1 h2)
theorem nj_71_20 : ∀ i, 0 ≤ i → i < 672 → ch_71 i = true := block_join nj_71_19 (fun _ h1 h2 => treeBlockF_at nb_71_20 h1 h2)
theorem nj_71_21 : ∀ i, 0 ≤ i → i < 704 → ch_71 i = true := block_join nj_71_20 (fun _ h1 h2 => treeBlockF_at nb_71_21 h1 h2)
theorem nj_71_22 : ∀ i, 0 ≤ i → i < 736 → ch_71 i = true := block_join nj_71_21 (fun _ h1 h2 => treeBlockF_at nb_71_22 h1 h2)
theorem nj_71_23 : ∀ i, 0 ≤ i → i < 738 → ch_71 i = true := block_join nj_71_22 (fun _ h1 h2 => treeBlockF_at nb_71_23 h1 h2)
theorem nc_71 : ∀ i, 0 ≤ i → i < 738 → ch_71 i = true := nj_71_23
theorem lb_71 : LowerBin fullMask rootStock g_71 12 :=
  lowerDagV5 (kn_cons lb_70 (kn_cons lb_68 (kn_cons lb_66 (kn_cons lb_63 (kn_cons lb_57 (kn_cons lb_64 (kn_cons lb_62 (kn_cons lb_44 (kn_cons lb_27 (kn_cons lb_41 (kn_cons lb_65 (kn_cons lb_61 (kn_cons lb_67 (kn_cons lb_55 (kn_cons lb_35 (kn_cons lb_30 (kn_cons lb_69 (kn_cons lb_56 (kn_cons lb_46 (kn_cons lb_38 (kn_cons lb_43 (kn_cons lb_50 (kn_cons lb_24 (kn_cons lb_23 (kn_cons lb_40 (kn_cons lb_34 (kn_cons lb_31 (kn_cons lb_9 (kn_cons lb_36 (kn_cons lb_53 (kn_cons lb_28 (kn_cons lb_48 (kn_cons lb_51 (kn_cons lb_58 (kn_cons lb_29 (kn_cons lb_54 (kn_cons lb_59 (kn_cons lb_49 (kn_cons lb_19 (kn_cons lb_20 (kn_cons lb_18 (kn_cons lb_47 (kn_cons lb_60 (kn_cons lb_52 (kn_nil))))))))))))))))))))))))))))))))))))))))))))) rc_71 nc_71 (by decide +kernel)

def wg : List Gate := [⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [2, 8]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [7, 11]⟩, ⟨GateOp.and, [0, 12]⟩, ⟨GateOp.and, [1, 12]⟩, ⟨GateOp.or, [0, 14]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [13, 16]⟩, ⟨GateOp.and, [15, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4008372896 * 2 ^ 32 + 3936395392) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4008372896 * 2 ^ 32 + 3936395392)) (13 - 1) := by
  rw [show canon fullMask (4008372896 * 2 ^ 32 + 3936395392) = g_71 by decide]
  exact lb_71

end PEqualNP.Outside.L_meta_47741

theorem PEqualNP.Outside.L_meta_47741 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372896 * 2 ^ 32 + 3936395392) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372896 * 2 ^ 32 + 3936395392) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_47741.table2_from_lowerBin (4008372896 * 2 ^ 32 + 3936395392) 13 PEqualNP.Outside.L_meta_47741.root_lb PEqualNP.Outside.L_meta_47741.wg 18 rfl PEqualNP.Outside.L_meta_47741.wfits PEqualNP.Outside.L_meta_47741.weval
