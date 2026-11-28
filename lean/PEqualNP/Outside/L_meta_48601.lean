import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48601

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

def m_0 : Nat := 0xf000f000000000
def s_0 : List Nat := [0x50005000000000, 0x30003000000000, 0xf000000000]
def g_0 : Nat := 0x10007000000000
def ep_0 : Nat := 0x60000000000000000000000000000000000000000000100020000000000010004000000000
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

def m_1 : Nat := 0xf000f0000000000
def s_1 : List Nat := [0x500050000000000, 0x300030000000000, 0xf0000000000]
def g_1 : Nat := 0x100070000000000
def ep_1 : Nat := 0x600000000000000000000000000000000000000000001000200000000000100040000000000
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

def m_5 : Nat := 0x3030303000000000
def s_5 : List Nat := [0x1010101000000000, 0x30003000000000, 0x303000000000]
def g_5 : Nat := 0x10103000000000
def ep_5 : Nat := 0x1020000000000010002000000000000000000000000000000000000000000010100000000000
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

def m_6 : Nat := 0x4444444400000000
def s_6 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_6 : Nat := 0x4044400000000
def ep_6 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
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

def m_7 : Nat := 0x2222222200000000
def s_7 : List Nat := [0x202020200000000, 0x22002200000000, 0x222200000000]
def g_7 : Nat := 0x2022200000000
def ep_7 : Nat := 0x220000000000002002000000000000202000000000000000000000000000000000000000000
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

def m_8 : Nat := 0xa000a000a000a00
def s_8 : List Nat := [0x200020002000200, 0xa0000000a00, 0xa000a00]
def g_8 : Nat := 0x20002000a00
def ep_8 : Nat := 0x200080000000200000008000000000000000000000000000000000000000200020000000000000000000000
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

def m_9 : Nat := 0xc000c000c000c00
def s_9 : List Nat := [0x400040004000400, 0xc0000000c00, 0xc000c00]
def g_9 : Nat := 0x40004000c00
def ep_9 : Nat := 0x400080000000400000008000000000000000000000000000000000000000000000000000000040004000000
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

def m_10 : Nat := 0x3333000000000000
def s_10 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_10 : Nat := 0x113000000000000
def ep_10 : Nat := 0x12000000000000010200000000000000000000000000000110000000000000
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

def m_12 : Nat := 0xff000000000000
def s_12 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_12 : Nat := 0x17000000000000
def ep_12 : Nat := 0x600000000000000120000000000000014000000000000
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

def m_13 : Nat := 0xc000c000c000c0
def s_13 : List Nat := [0x40004000400040, 0xc0000000c0, 0xc000c0]
def g_13 : Nat := 0x40004000c0
def ep_13 : Nat := 0x40008000000040000000800000000000000000000000000000000000000000000000000000004000400000
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

def m_14 : Nat := 0xf0f000000000000
def s_14 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_14 : Nat := 0x107000000000000
def ep_14 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
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

def m_15 : Nat := 0xf0000000f000000
def s_15 : List Nat := [0x500000005000000, 0x300000003000000, 0xf000000]
def g_15 : Nat := 0x100000007000000
def ep_15 : Nat := 0x600000000000000000000000000000000000000000000000000000001000000020000000100000004000000
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

def m_16 : Nat := 0xf0f000000000
def s_16 : List Nat := [0x505000000000, 0x303000000000, 0xf000000000]
def g_16 : Nat := 0x107000000000
def ep_16 : Nat := 0x6000000000000000000000000000001020000000000000104000000000
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

def m_17 : Nat := 0x30303030
def s_17 : List Nat := [0x10101010, 0x300030, 0x3030]
def g_17 : Nat := 0x101030
def ep_17 : Nat := 0x10200000000000100020000000000000000000000000000000000000000000101000
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

def m_18 : Nat := 0xff0000000000
def s_18 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_18 : Nat := 0x170000000000
def ep_18 : Nat := 0x6000000000000001200000000000000140000000000
def bds_18 : List (Nat × List Nat × Nat × Nat) := []
def cur_18 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_18 : Nat → Nat := fun _ => 0
def f_18 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_18 : Nat → Bool := dagCheckNodeV5 m_18 g_18 ep_18 1 1 bds_18 1 (dagTraceF m_18 s_18 3 f_18) cur_18 nh_18
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsV5 m_18 g_18 ep_18 1 1 1 bds_18 (dagTraceF m_18 s_18 3 f_18) (cur_18 0) (nh_18 0) s_18 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_18 : treeBlockF 0 1 ch_18 = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 1 → ch_18 i = true := fun _ h1 h2 => treeBlockF_at nb_18 h1 h2
theorem lb_18 : LowerBin m_18 s_18 g_18 4 :=
  lowerDagV5 (kn_nil) rc_18 nc_18 (by decide +kernel)

def m_19 : Nat := 0x4444000044440000
def s_19 : List Nat := [0x404000004040000, 0x44000000440000, 0x44440000]
def g_19 : Nat := 0x4000004440000
def ep_19 : Nat := 0x440000000000000000000000004000000400000000400000400000000000000000000000000000000000000
def bds_19 : List (Nat × List Nat × Nat × Nat) := []
def cur_19 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_19 : Nat → Nat := fun _ => 0
def f_19 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_19 : Nat → Bool := dagCheckNodeV5 m_19 g_19 ep_19 1 1 bds_19 1 (dagTraceF m_19 s_19 3 f_19) cur_19 nh_19
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsV5 m_19 g_19 ep_19 1 1 1 bds_19 (dagTraceF m_19 s_19 3 f_19) (cur_19 0) (nh_19 0) s_19 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19 : treeBlockF 0 1 ch_19 = true := by decide +kernel
theorem nc_19 : ∀ i, 0 ≤ i → i < 1 → ch_19 i = true := fun _ h1 h2 => treeBlockF_at nb_19 h1 h2
theorem lb_19 : LowerBin m_19 s_19 g_19 4 :=
  lowerDagV5 (kn_nil) rc_19 nc_19 (by decide +kernel)

def m_20 : Nat := 0x2222888822228888
def s_20 : List Nat := [0x888800008888, 0x202080802020808, 0x22008800220088, 0x22228888]
def g_20 : Nat := 0x2000002020888
def ep_20 : Nat := 0x200088800000000000000000002000000000080000200000202080000000000000000000000000000000000
def bds_20 : List (Nat × List Nat × Nat × Nat) := []
def cur_20 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0x14b99100f 4 15 2 3 9 511 11 2047
def nh_20 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_20 : Nat → Nat × Nat := unpackForestF 0x32ec880f 1 9
def ch_20 : Nat → Bool := dagCheckNodeV5 m_20 g_20 ep_20 1 1 bds_20 3 (dagTraceF m_20 s_20 4 f_20) cur_20 nh_20
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV5 m_20 g_20 ep_20 1 1 3 bds_20 (dagTraceF m_20 s_20 4 f_20) (cur_20 0) (nh_20 0) s_20 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_20 : treeBlockF 0 3 ch_20 = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 3 → ch_20 i = true := fun _ h1 h2 => treeBlockF_at nb_20 h1 h2
theorem lb_20 : LowerBin m_20 s_20 g_20 5 :=
  lowerDagV5 (kn_nil) rc_20 nc_20 (by decide +kernel)

def m_21 : Nat := 0xa0aa0a00a0aa0a0
def s_21 : List Nat := [0x202202002022020, 0xa0a00000a0a0, 0xa00a0000a00a0, 0xa0aa0a0]
def g_21 : Nat := 0x20020020200a0
def ep_21 : Nat := 0x2000080000000000000000000020020000000a0000000000000000000020020020200000000000000000000
def bds_21 : List (Nat × List Nat × Nat × Nat) := []
def cur_21 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0x16588f 4 15 2 3 5 31 7 127
def nh_21 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_21 : Nat → Nat × Nat := unpackForestF 0x39c4f 1 5
def ch_21 : Nat → Bool := dagCheckNodeV5 m_21 g_21 ep_21 1 1 bds_21 3 (dagTraceF m_21 s_21 4 f_21) cur_21 nh_21
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV5 m_21 g_21 ep_21 1 1 3 bds_21 (dagTraceF m_21 s_21 4 f_21) (cur_21 0) (nh_21 0) s_21 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21 : treeBlockF 0 3 ch_21 = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 3 → ch_21 i = true := fun _ h1 h2 => treeBlockF_at nb_21 h1 h2
theorem lb_21 : LowerBin m_21 s_21 g_21 5 :=
  lowerDagV5 (kn_nil) rc_21 nc_21 (by decide +kernel)

def m_22 : Nat := 0xff00ff0000000000
def s_22 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_22 : Nat := 0x100170000000000
def ep_22 : Nat := 0x1600000000000000000000000000010006000000000001001200000000000100140000000000
def bds_22 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1), (m_18, s_18, 4, g_18), (m_2, s_2, 4, g_2), (m_3, s_3, 4, g_3)]
def cc_22_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_22_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_22 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_22_1 (Nat.sub p 32)) (cc_22_0 p) (Nat.blt p 32)
def hc_22_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_22_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_22 : Nat → Nat := fun p => Bool.rec (hc_22_1 (Nat.sub p 32)) (hc_22_0 p) (Nat.blt p 32)
def f_22 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_22 : Nat → Bool := dagCheckNodeV5 m_22 g_22 ep_22 1 1 bds_22 43 (dagTraceF m_22 s_22 6 f_22) cur_22 nh_22
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV5 m_22 g_22 ep_22 1 1 43 bds_22 (dagTraceF m_22 s_22 6 f_22) (cur_22 0) (nh_22 0) s_22 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_22_0 : treeBlockF 0 32 ch_22 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_22_1 : treeBlockF 32 43 ch_22 = true := by decide +kernel
theorem nj_22_1 : ∀ i, 0 ≤ i → i < 43 → ch_22 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_22_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_22_1 h1 h2)
theorem nc_22 : ∀ i, 0 ≤ i → i < 43 → ch_22 i = true := nj_22_1
theorem lb_22 : LowerBin m_22 s_22 g_22 7 :=
  lowerDagV5 (kn_cons lb_1 (kn_cons lb_18 (kn_cons lb_2 (kn_cons lb_3 (kn_nil))))) rc_22 nc_22 (by decide +kernel)

def m_23 : Nat := 0xffff000000000000
def s_23 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_23 : Nat := 0x117000000000000
def ep_23 : Nat := 0x16000000000000010600000000000001120000000000000114000000000000
def bds_23 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14), (m_12, s_12, 4, g_12), (m_11, s_11, 4, g_11), (m_10, s_10, 4, g_10)]
def cc_23_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_23_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_23 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_23_1 (Nat.sub p 32)) (cc_23_0 p) (Nat.blt p 32)
def hc_23_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_23_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_23 : Nat → Nat := fun p => Bool.rec (hc_23_1 (Nat.sub p 32)) (hc_23_0 p) (Nat.blt p 32)
def f_23 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_23 : Nat → Bool := dagCheckNodeV5 m_23 g_23 ep_23 1 1 bds_23 43 (dagTraceF m_23 s_23 6 f_23) cur_23 nh_23
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV5 m_23 g_23 ep_23 1 1 43 bds_23 (dagTraceF m_23 s_23 6 f_23) (cur_23 0) (nh_23 0) s_23 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_23_0 : treeBlockF 0 32 ch_23 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_23_1 : treeBlockF 32 43 ch_23 = true := by decide +kernel
theorem nj_23_1 : ∀ i, 0 ≤ i → i < 43 → ch_23 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_23_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_23_1 h1 h2)
theorem nc_23 : ∀ i, 0 ≤ i → i < 43 → ch_23 i = true := nj_23_1
theorem lb_23 : LowerBin m_23 s_23 g_23 7 :=
  lowerDagV5 (kn_cons lb_14 (kn_cons lb_12 (kn_cons lb_11 (kn_cons lb_10 (kn_nil))))) rc_23 nc_23 (by decide +kernel)

def m_24 : Nat := 0xffff00000000
def s_24 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_24 : Nat := 0x177700000000
def ep_24 : Nat := 0x6000000000000006000000000000001222000000000000144400000000
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16)]
def cur_24 : Nat → List (Nat × Nat) := fun _ => []
def nh_24 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_24 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV5 m_24 g_24 ep_24 1 1 0 bds_24 (dagTraceF m_24 s_24 4 f_24) (cur_24 0) (nh_24 0) s_24 4 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_24 g_24 ep_24 1 1 bds_24 0 (dagTraceF m_24 s_24 4 f_24) cur_24 nh_24 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagV5 (kn_cons lb_16 (kn_nil)) rc_24 nc_24 (by decide +kernel)

def m_25 : Nat := 0xf0f0f0f000000000
def s_25 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_25 : Nat := 0x10107000000000
def ep_25 : Nat := 0x1060000000000010006000000000000000000000000000101020000000000010104000000000
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_16, s_16, 4, g_16), (m_4, s_4, 4, g_4), (m_5, s_5, 4, g_5)]
def cc_25_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_25_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_25 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_25_1 (Nat.sub p 32)) (cc_25_0 p) (Nat.blt p 32)
def hc_25_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_25_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_25 : Nat → Nat := fun p => Bool.rec (hc_25_1 (Nat.sub p 32)) (hc_25_0 p) (Nat.blt p 32)
def f_25 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_25 : Nat → Bool := dagCheckNodeV5 m_25 g_25 ep_25 1 1 bds_25 43 (dagTraceF m_25 s_25 6 f_25) cur_25 nh_25
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV5 m_25 g_25 ep_25 1 1 43 bds_25 (dagTraceF m_25 s_25 6 f_25) (cur_25 0) (nh_25 0) s_25 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_0 : treeBlockF 0 32 ch_25 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_1 : treeBlockF 32 43 ch_25 = true := by decide +kernel
theorem nj_25_1 : ∀ i, 0 ≤ i → i < 43 → ch_25 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_25_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_25_1 h1 h2)
theorem nc_25 : ∀ i, 0 ≤ i → i < 43 → ch_25 i = true := nj_25_1
theorem lb_25 : LowerBin m_25 s_25 g_25 7 :=
  lowerDagV5 (kn_cons lb_0 (kn_cons lb_16 (kn_cons lb_4 (kn_cons lb_5 (kn_nil))))) rc_25 nc_25 (by decide +kernel)

def m_26 : Nat := 0xcccccccc00000000
def s_26 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_26 : Nat := 0x4044400000000
def ep_26 : Nat := 0x440000000000004004000000000000404000000000000000000000000000004044400000000
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cur_26 : Nat → List (Nat × Nat) := fun _ => []
def nh_26 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_26 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV5 m_26 g_26 ep_26 1 1 0 bds_26 (dagTraceF m_26 s_26 4 f_26) (cur_26 0) (nh_26 0) s_26 4 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_26 g_26 ep_26 1 1 bds_26 0 (dagTraceF m_26 s_26 4 f_26) cur_26 nh_26 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_26 : LowerBin m_26 s_26 g_26 5 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_26 nc_26 (by decide +kernel)

def m_27 : Nat := 0x3333333300000000
def s_27 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_27 : Nat := 0x113133300000000
def ep_27 : Nat := 0x1220000000000012002000000000010202000000000000000000000000000110100000000000
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3), (m_10, s_10, 4, g_10), (m_5, s_5, 4, g_5), (m_7, s_7, 4, g_7)]
def cc_27_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_27_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_27 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_27_1 (Nat.sub p 32)) (cc_27_0 p) (Nat.blt p 32)
def hc_27_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e02200586415a60dad5545a0ad39b942665566b5910608437408a0203a61035944 15 32767 6 63
def hc_27_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e7540e571014d8c00562302 13 8191 6 63
def nh_27 : Nat → Nat := fun p => Bool.rec (hc_27_1 (Nat.sub p 32)) (hc_27_0 p) (Nat.blt p 32)
def f_27 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
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
  lowerDagV5 (kn_cons lb_3 (kn_cons lb_10 (kn_cons lb_5 (kn_cons lb_7 (kn_nil))))) rc_27 nc_27 (by decide +kernel)

def m_28 : Nat := 0xaa00aa00aa00aa
def s_28 : List Nat := [0x22002200220022, 0xa000a000a000a, 0xaa000000aa, 0xaa00aa]
def g_28 : Nat := 0x20022000200aa
def ep_28 : Nat := 0x8800000020000000a80000000000000000000200000002000000020022000200000000000000000000
def bds_28 : List (Nat × List Nat × Nat × Nat) := []
def cur_28 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_28 : Nat → Nat := fun _ => 0
def f_28 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_28 : Nat → Bool := dagCheckNodeV5 m_28 g_28 ep_28 1 1 bds_28 1 (dagTraceF m_28 s_28 3 f_28) cur_28 nh_28
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV5 m_28 g_28 ep_28 1 1 1 bds_28 (dagTraceF m_28 s_28 3 f_28) (cur_28 0) (nh_28 0) s_28 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28 : treeBlockF 0 1 ch_28 = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 1 → ch_28 i = true := fun _ h1 h2 => treeBlockF_at nb_28 h1 h2
theorem lb_28 : LowerBin m_28 s_28 g_28 4 :=
  lowerDagV5 (kn_nil) rc_28 nc_28 (by decide +kernel)

def m_29 : Nat := 0xaaaaaaaa00000000
def s_29 : List Nat := [0x2222222200000000, 0xa0a0a0a00000000, 0xaa00aa00000000, 0xaaaa00000000]
def g_29 : Nat := 0x2022200000000
def ep_29 : Nat := 0x220000000000002002000000000000202000000000000020222000000000000000000000000
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7)]
def cur_29 : Nat → List (Nat × Nat) := fun _ => []
def nh_29 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_29 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV5 m_29 g_29 ep_29 1 1 0 bds_29 (dagTraceF m_29 s_29 4 f_29) (cur_29 0) (nh_29 0) s_29 4 = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_29 g_29 ep_29 1 1 bds_29 0 (dagTraceF m_29 s_29 4 f_29) cur_29 nh_29 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_29 : LowerBin m_29 s_29 g_29 5 :=
  lowerDagV5 (kn_cons lb_7 (kn_nil)) rc_29 nc_29 (by decide +kernel)

def m_30 : Nat := 0x5555555500000000
def s_30 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_30 : Nat := 0x115155500000000
def ep_30 : Nat := 0x1440000000000014004000000000010404000000000001101000000000000000000000000000
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2), (m_11, s_11, 4, g_11), (m_4, s_4, 4, g_4), (m_6, s_6, 4, g_6)]
def cc_30_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_30_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_30 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_30_1 (Nat.sub p 32)) (cc_30_0 p) (Nat.blt p 32)
def hc_30_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e02200586415a60dad5545a0ad39b942665566b5910608437408a0203a61035944 15 32767 6 63
def hc_30_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e7540e571014d8c00562302 13 8191 6 63
def nh_30 : Nat → Nat := fun p => Bool.rec (hc_30_1 (Nat.sub p 32)) (hc_30_0 p) (Nat.blt p 32)
def f_30 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_30 : Nat → Bool := dagCheckNodeV5 m_30 g_30 ep_30 1 1 bds_30 43 (dagTraceF m_30 s_30 6 f_30) cur_30 nh_30
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV5 m_30 g_30 ep_30 1 1 43 bds_30 (dagTraceF m_30 s_30 6 f_30) (cur_30 0) (nh_30 0) s_30 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_0 : treeBlockF 0 32 ch_30 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_1 : treeBlockF 32 43 ch_30 = true := by decide +kernel
theorem nj_30_1 : ∀ i, 0 ≤ i → i < 43 → ch_30 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_30_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_30_1 h1 h2)
theorem nc_30 : ∀ i, 0 ≤ i → i < 43 → ch_30 i = true := nj_30_1
theorem lb_30 : LowerBin m_30 s_30 g_30 7 :=
  lowerDagV5 (kn_cons lb_2 (kn_cons lb_11 (kn_cons lb_4 (kn_cons lb_6 (kn_nil))))) rc_30 nc_30 (by decide +kernel)

def m_31 : Nat := 0xc0c0c0c0c0c0c0c0
def s_31 : List Nat := [0x4040404040404040, 0xc000c000c000c0, 0xc0c00000c0c0, 0xc0c0c0c0]
def g_31 : Nat := 0x40004000c0
def ep_31 : Nat := 0x400080000000400000008000000040004000c0000000000000000000000000000000000000004000400000
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
def cur_31 : Nat → List (Nat × Nat) := fun _ => []
def nh_31 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_31 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV5 m_31 g_31 ep_31 1 1 0 bds_31 (dagTraceF m_31 s_31 4 f_31) (cur_31 0) (nh_31 0) s_31 4 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_31 g_31 ep_31 1 1 bds_31 0 (dagTraceF m_31 s_31 4 f_31) cur_31 nh_31 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagV5 (kn_cons lb_13 (kn_nil)) rc_31 nc_31 (by decide +kernel)

def m_32 : Nat := 0x3333000033330000
def s_32 : List Nat := [0x1111000011110000, 0x303000003030000, 0x33000000330000, 0x33330000]
def g_32 : Nat := 0x113000003130000
def ep_32 : Nat := 0x200000000000000000000000012000000100000010200000302000000000000000000000110000000100000
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_32 : Nat → List (Nat × Nat) := fun _ => []
def nh_32 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_32 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV5 m_32 g_32 ep_32 1 1 0 bds_32 (dagTraceF m_32 s_32 4 f_32) (cur_32 0) (nh_32 0) s_32 4 = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_32 g_32 ep_32 1 1 bds_32 0 (dagTraceF m_32 s_32 4 f_32) cur_32 nh_32 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_32 : LowerBin m_32 s_32 g_32 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_32 nc_32 (by decide +kernel)

def m_33 : Nat := 0x5500550055005500
def s_33 : List Nat := [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500]
def g_33 : Nat := 0x100150005001500
def ep_33 : Nat := 0x400000000001400000010000000000000000000010004000500040001001000000010000000000000000000
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cur_33 : Nat → List (Nat × Nat) := fun _ => []
def nh_33 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV5 m_33 g_33 ep_33 1 1 0 bds_33 (dagTraceF m_33 s_33 4 f_33) (cur_33 0) (nh_33 0) s_33 4 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_33 g_33 ep_33 1 1 bds_33 0 (dagTraceF m_33 s_33 4 f_33) cur_33 nh_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_33 nc_33 (by decide +kernel)

def m_34 : Nat := 0xff000000ff00
def s_34 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_34 : Nat := 0x170000001f00
def ep_34 : Nat := 0x800000000000000000000000000000000000000060000000e0000001200000010000000140000001000
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 4, g_18)]
def cur_34 : Nat → List (Nat × Nat) := fun _ => []
def nh_34 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV5 m_34 g_34 ep_34 1 1 0 bds_34 (dagTraceF m_34 s_34 4 f_34) (cur_34 0) (nh_34 0) s_34 4 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_34 g_34 ep_34 1 1 bds_34 0 (dagTraceF m_34 s_34 4 f_34) cur_34 nh_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagV5 (kn_cons lb_18 (kn_nil)) rc_34 nc_34 (by decide +kernel)

def m_35 : Nat := 0xf0f00000f0f0
def s_35 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_35 : Nat := 0x1070000010f0
def ep_35 : Nat := 0x80000000000000000000000060000000e0000000000000000000001020000010000000104000001000
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16)]
def cur_35 : Nat → List (Nat × Nat) := fun _ => []
def nh_35 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_35 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV5 m_35 g_35 ep_35 1 1 0 bds_35 (dagTraceF m_35 s_35 4 f_35) (cur_35 0) (nh_35 0) s_35 4 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_35 g_35 ep_35 1 1 bds_35 0 (dagTraceF m_35 s_35 4 f_35) cur_35 nh_35 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_35 : LowerBin m_35 s_35 g_35 5 :=
  lowerDagV5 (kn_cons lb_16 (kn_nil)) rc_35 nc_35 (by decide +kernel)

def m_36 : Nat := 0xcccc0000cccc0000
def s_36 : List Nat := [0x4444000044440000, 0xc0c00000c0c0000, 0xcc000000cc0000, 0xcccc0000]
def g_36 : Nat := 0x4000004440000
def ep_36 : Nat := 0x440000000000000000000000004000000400000000400000400000000000000000000000004000004440000
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_19, s_19, 4, g_19)]
def cur_36 : Nat → List (Nat × Nat) := fun _ => []
def nh_36 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV5 m_36 g_36 ep_36 1 1 0 bds_36 (dagTraceF m_36 s_36 4 f_36) (cur_36 0) (nh_36 0) s_36 4 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_36 g_36 ep_36 1 1 bds_36 0 (dagTraceF m_36 s_36 4 f_36) cur_36 nh_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagV5 (kn_cons lb_19 (kn_nil)) rc_36 nc_36 (by decide +kernel)

def m_37 : Nat := 0xaa00aa00aa00aa00
def s_37 : List Nat := [0x2200220022002200, 0xa000a000a000a00, 0xaa000000aa00, 0xaa00aa00]
def g_37 : Nat := 0x20002000a00
def ep_37 : Nat := 0x2000800000002000000080000000000000000000000020002000a0000000200020000000000000000000000
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_37 : Nat → List (Nat × Nat) := fun _ => []
def nh_37 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV5 m_37 g_37 ep_37 1 1 0 bds_37 (dagTraceF m_37 s_37 4 f_37) (cur_37 0) (nh_37 0) s_37 4 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_37 g_37 ep_37 1 1 bds_37 0 (dagTraceF m_37 s_37 4 f_37) cur_37 nh_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_37 nc_37 (by decide +kernel)

def m_38 : Nat := 0x3300330033003300
def s_38 : List Nat := [0x1100110011001100, 0x300030003000300, 0x330000003300, 0x33003300]
def g_38 : Nat := 0x100130003001300
def ep_38 : Nat := 0x200000000001200000010000000000000000000010002000300020000000000000000000100100000001000
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def nh_38 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV5 m_38 g_38 ep_38 1 1 0 bds_38 (dagTraceF m_38 s_38 4 f_38) (cur_38 0) (nh_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_38 g_38 ep_38 1 1 bds_38 0 (dagTraceF m_38 s_38 4 f_38) cur_38 nh_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagV5 (kn_cons lb_3 (kn_nil)) rc_38 nc_38 (by decide +kernel)

def m_39 : Nat := 0xcc00cc00cc00cc00
def s_39 : List Nat := [0x4400440044004400, 0xc000c000c000c00, 0xcc000000cc00, 0xcc00cc00]
def g_39 : Nat := 0x40004000c00
def ep_39 : Nat := 0x4000800000004000000080000000000000000000000040004000c0000000000000000000000040004000000
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_39 : Nat → List (Nat × Nat) := fun _ => []
def nh_39 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_39 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV5 m_39 g_39 ep_39 1 1 0 bds_39 (dagTraceF m_39 s_39 4 f_39) (cur_39 0) (nh_39 0) s_39 4 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_39 g_39 ep_39 1 1 bds_39 0 (dagTraceF m_39 s_39 4 f_39) cur_39 nh_39 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_39 : LowerBin m_39 s_39 g_39 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_39 nc_39 (by decide +kernel)

def m_40 : Nat := 0xf000f000f000f00
def s_40 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_40 : Nat := 0x100070007000f00
def ep_40 : Nat := 0x600080000000600000008000000000000000000000000000000000001000200020000000100040004000000
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1), (m_15, s_15, 4, g_15), (m_9, s_9, 4, g_9), (m_8, s_8, 4, g_8)]
def cc_40_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_40_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_40 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_40_1 (Nat.sub p 32)) (cc_40_0 p) (Nat.blt p 32)
def hc_40_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e56655092040a6ad8c0011820539b81622002630805682cb74a008803a6b2b0810 15 32767 6 63
def hc_40_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e754ae0732b4dad55068b56 13 8191 6 63
def nh_40 : Nat → Nat := fun p => Bool.rec (hc_40_1 (Nat.sub p 32)) (hc_40_0 p) (Nat.blt p 32)
def f_40 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_40 : Nat → Bool := dagCheckNodeV5 m_40 g_40 ep_40 1 1 bds_40 43 (dagTraceF m_40 s_40 6 f_40) cur_40 nh_40
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV5 m_40 g_40 ep_40 1 1 43 bds_40 (dagTraceF m_40 s_40 6 f_40) (cur_40 0) (nh_40 0) s_40 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_0 : treeBlockF 0 32 ch_40 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_40_1 : treeBlockF 32 43 ch_40 = true := by decide +kernel
theorem nj_40_1 : ∀ i, 0 ≤ i → i < 43 → ch_40 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_40_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_40_1 h1 h2)
theorem nc_40 : ∀ i, 0 ≤ i → i < 43 → ch_40 i = true := nj_40_1
theorem lb_40 : LowerBin m_40 s_40 g_40 7 :=
  lowerDagV5 (kn_cons lb_1 (kn_cons lb_15 (kn_cons lb_9 (kn_cons lb_8 (kn_nil))))) rc_40 nc_40 (by decide +kernel)

def m_41 : Nat := 0xcc00cc00cc00cc
def s_41 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_41 : Nat := 0x40044004400cc
def ep_41 : Nat := 0x40008800000040000000880000000000000000000400000000000000000000000000000004004400440000
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def nh_41 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV5 m_41 g_41 ep_41 1 1 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) (nh_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_41 g_41 ep_41 1 1 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 nh_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV5 (kn_cons lb_13 (kn_nil)) rc_41 nc_41 (by decide +kernel)

def m_42 : Nat := 0xffff0000
def s_42 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_42 : Nat := 0x7570000
def ep_42 : Nat := 0x500000000000000702000000000000020200000000000004540000
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

def m_43 : Nat := 0xff00ff00
def s_43 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_43 : Nat := 0x7001f00
def ep_43 : Nat := 0x180000000000000000000000000007000e0000000000020010000000000004001000
def bds_43 : List (Nat × List Nat × Nat × Nat) := []
def cc_43_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682b1560ac148a80d009c3382704a2941282314418810861042084108210420748e81d03a0740c901c001 0x7a3876346c3c68345c305d44564c5244484c4444382039342a48264022381e30144c10440c3c0834f63fea3be637de33d93fd53bc137ad33a92fa52b91277d23703f643b603758334c2f402b3c273423301f2c1b18170413000f 11 2047 5 31 10 1023 16 65535
def cc_43_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0a2a0a092898881808080808080646060606044404040404040242020202004 0xfc38f834f028ec24e230e344d24cce40c84cc440bd3cb934b418b014a3489f40983c94308d4c894484188014 8 255 3 7 10 1023 16 65535
def cur_43 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_43_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_43_0 p) (Nat.blt p 32)
def hc_43_0 : Nat → Nat := unpackHintV5 0xa142548910a03a70e1c3260c15284480d12204081014204081008000 0x0 7 127 2 3
def hc_43_1 : Nat → Nat := unpackHintV5 0xb14a850952214074c983060c152850a1422344881020405081020402 0x0 7 127 2 3
def nh_43 : Nat → Nat := fun p => Bool.rec (Bool.rec (0) (hc_43_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_43_0 p) (Nat.blt p 32)
def f_43 : Nat → Nat × Nat := unpackForestF 0xf838f834063fec28ec24063b0637e3440633053f053bc64cc640c44cc4400537b13cb134b018b0140533052f052b97489740943c94300527814c814480188014052376387634043f683c6834043b04375d440433524c5244042f444c4444042b042739340423041f041b1e481e401e381e300417084c0844083c08340413000f 6 10
def ch_43 : Nat → Bool := dagCheckNodeV5 m_43 g_43 ep_43 1 1 bds_43 64 (dagTraceF m_43 s_43 5 f_43) cur_43 nh_43
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV5 m_43 g_43 ep_43 1 1 64 bds_43 (dagTraceF m_43 s_43 5 f_43) (cur_43 0) (nh_43 0) s_43 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_0 : treeBlockF 0 32 ch_43 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_1 : treeBlockF 32 64 ch_43 = true := by decide +kernel
theorem nj_43_1 : ∀ i, 0 ≤ i → i < 64 → ch_43 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_43_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_43_1 h1 h2)
theorem nc_43 : ∀ i, 0 ≤ i → i < 64 → ch_43 i = true := nj_43_1
theorem lb_43 : LowerBin m_43 s_43 g_43 6 :=
  lowerDagV5 (kn_nil) rc_43 nc_43 (by decide +kernel)

def m_44 : Nat := 0xaaaaaaaa
def s_44 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_44 : Nat := 0x2020aaa
def ep_44 : Nat := 0x8a800000000000000a00000000002020a0000000000020200000000000000000000
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

def m_45 : Nat := 0xff000000ff000000
def s_45 : List Nat := [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000]
def g_45 : Nat := 0x100000007000000
def ep_45 : Nat := 0x600000000000000000000000000000000000000010000000700000001000000020000000100000004000000
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
def cur_45 : Nat → List (Nat × Nat) := fun _ => []
def nh_45 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV5 m_45 g_45 ep_45 1 1 0 bds_45 (dagTraceF m_45 s_45 4 f_45) (cur_45 0) (nh_45 0) s_45 4 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_45 g_45 ep_45 1 1 bds_45 0 (dagTraceF m_45 s_45 4 f_45) cur_45 nh_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin m_45 s_45 g_45 5 :=
  lowerDagV5 (kn_cons lb_15 (kn_nil)) rc_45 nc_45 (by decide +kernel)

def m_46 : Nat := 0xff000000ff0000
def s_46 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_46 : Nat := 0x17000000570000
def ep_46 : Nat := 0x40000000000000000000000000000000000000000600000002000000120000000200000014000000540000
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cur_46 : Nat → List (Nat × Nat) := fun _ => []
def nh_46 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_46 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV5 m_46 g_46 ep_46 1 1 0 bds_46 (dagTraceF m_46 s_46 4 f_46) (cur_46 0) (nh_46 0) s_46 4 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_46 g_46 ep_46 1 1 bds_46 0 (dagTraceF m_46 s_46 4 f_46) cur_46 nh_46 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_46 : LowerBin m_46 s_46 g_46 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_46 nc_46 (by decide +kernel)

def m_47 : Nat := 0x4444444444444444
def s_47 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_47 : Nat := 0x4044404440444
def ep_47 : Nat := 0x440000000000440000000000004004000400040000404000400040000000000000000000000000000000000
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cur_47 : Nat → List (Nat × Nat) := fun _ => []
def nh_47 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_47 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV5 m_47 g_47 ep_47 1 1 0 bds_47 (dagTraceF m_47 s_47 4 f_47) (cur_47 0) (nh_47 0) s_47 4 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_47 g_47 ep_47 1 1 bds_47 0 (dagTraceF m_47 s_47 4 f_47) cur_47 nh_47 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_47 : LowerBin m_47 s_47 g_47 5 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_47 nc_47 (by decide +kernel)

def m_48 : Nat := 0xa0a0a0a0a0a0a0a
def s_48 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_48 : Nat := 0x2020202020a0a
def ep_48 : Nat := 0x200080800000200000008080002000000000000000000000000000000020202020200000000000000000000
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_48 : Nat → List (Nat × Nat) := fun _ => []
def nh_48 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_48 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV5 m_48 g_48 ep_48 1 1 0 bds_48 (dagTraceF m_48 s_48 4 f_48) (cur_48 0) (nh_48 0) s_48 4 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_48 g_48 ep_48 1 1 bds_48 0 (dagTraceF m_48 s_48 4 f_48) cur_48 nh_48 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_48 : LowerBin m_48 s_48 g_48 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_48 nc_48 (by decide +kernel)

def m_49 : Nat := 0xc0c0c0c0c0c0c0c
def s_49 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_49 : Nat := 0x4040404040c0c
def ep_49 : Nat := 0x400080800000400000008080004000000000000000000000000000000000000000000000004040404040000
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_49 : Nat → List (Nat × Nat) := fun _ => []
def nh_49 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_49 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV5 m_49 g_49 ep_49 1 1 0 bds_49 (dagTraceF m_49 s_49 4 f_49) (cur_49 0) (nh_49 0) s_49 4 = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_49 g_49 ep_49 1 1 bds_49 0 (dagTraceF m_49 s_49 4 f_49) cur_49 nh_49 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_49 : LowerBin m_49 s_49 g_49 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_49 nc_49 (by decide +kernel)

def m_50 : Nat := 0xaaaaaaaaaaaaaaaa
def s_50 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_50 : Nat := 0x2022202020aaa
def ep_50 : Nat := 0x200088800000220000008a800020020000000a00002020002020a0000020222020200000000000000000000
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_29, s_29, 5, g_29), (m_44, s_44, 4, g_44), (m_37, s_37, 5, g_37), (m_7, s_7, 4, g_7), (m_28, s_28, 4, g_28), (m_48, s_48, 5, g_48), (m_21, s_21, 5, g_21), (m_8, s_8, 4, g_8), (m_20, s_20, 5, g_20)]
def cc_50_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x8ca3084a01802007c5c3701c068991641906055354141501314c13044910440f23c0e1380d107001 0x101497ca2bad255682c81465a0b7145a29cc01459af2ad4912688b424e29245790268715e31a9144e4926a393d18988853824850b437927b853d7286a13f3c999a4acb24e403f14138607c102e001f 10 1023 4 15 11 2047 17 131071
def cc_50_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x28a05000 0x37514e82acf639cc535 6 63 3 7 9 511 15 32767
def cur_50 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_50_1 (Nat.sub p 32)) (cc_50_0 p) (Nat.blt p 32)
def hc_50_0 : Nat → Nat := unpackHintV5 0x82b4e07077676dd20f74801cf857184d92e764211908058d6d5b8f56e015905538591ae746a00ed5b3ac10c4cd31200bd8e27af8978e25e00724b1c80050c31341c2fbb0017c0000 0xa3cd67ad8e1d1ce73c8811c775acf1e18f63b8c631a206f6bd8ee311dc631ec775adf1cf0c608c2e8231adf359e3cb5ed6f5ae9137b1ed6f5c75bd6b5ee8637adf3e39df2d68878f56cf0c6799d678f51d104e319d679c73d51eb68879d8d1a0c75443688886dda346ad9c7053c2881b41a355b274110436891d1a356a7601440dac63874e5c31ad743060b200 18 262143 7 127
def hc_50_1 : Nat → Nat := unpackHintV5 0x4d807c3e1db8380000e 0x2c67b7b458c63d8d631d4d678f0d6f18c1107b4 15 32767 7 127
def nh_50 : Nat → Nat := fun p => Bool.rec (hc_50_1 (Nat.sub p 32)) (hc_50_0 p) (Nat.blt p 32)
def f_50 : Nat → Nat × Nat := unpackForestF 0x889cc44d41686f9497ca28293dd692094f6228b05399682c01404a1aad7956a4093f4229205791684813404999c578125663520493924e4926a083f189e8c4c4104e214e040f84908102e001f 6 11
def ch_50 : Nat → Bool := dagCheckNodeV5 m_50 g_50 ep_50 3 7 bds_50 36 (dagTraceF m_50 s_50 7 f_50) cur_50 nh_50
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV5 m_50 g_50 ep_50 3 7 36 bds_50 (dagTraceF m_50 s_50 7 f_50) (cur_50 0) (nh_50 0) s_50 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_0 : treeBlockF 0 32 ch_50 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50_1 : treeBlockF 32 36 ch_50 = true := by decide +kernel
theorem nj_50_1 : ∀ i, 0 ≤ i → i < 36 → ch_50 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_50_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_50_1 h1 h2)
theorem nc_50 : ∀ i, 0 ≤ i → i < 36 → ch_50 i = true := nj_50_1
theorem lb_50 : LowerBin m_50 s_50 g_50 8 :=
  lowerDagV5 (kn_cons lb_29 (kn_cons lb_44 (kn_cons lb_37 (kn_cons lb_7 (kn_cons lb_28 (kn_cons lb_48 (kn_cons lb_21 (kn_cons lb_8 (kn_cons lb_20 (kn_nil)))))))))) rc_50 nc_50 (by decide +kernel)

def m_51 : Nat := 0x5555555555555555
def s_51 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_51 : Nat := 0x115155505551555
def ep_51 : Nat := 0x440000000001440000010000014004000500040010404000500040001101000000010000000000000000000
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_30, s_30, 7, g_30)]
def cur_51 : Nat → List (Nat × Nat) := fun _ => []
def nh_51 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_51 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV5 m_51 g_51 ep_51 1 1 0 bds_51 (dagTraceF m_51 s_51 7 f_51) (cur_51 0) (nh_51 0) s_51 7 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_51 g_51 ep_51 1 1 bds_51 0 (dagTraceF m_51 s_51 7 f_51) cur_51 nh_51 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_51 : LowerBin m_51 s_51 g_51 8 :=
  lowerDagV5 (kn_cons lb_30 (kn_nil)) rc_51 nc_51 (by decide +kernel)

def m_52 : Nat := 0xff00ff00ff00ff00
def s_52 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_52 : Nat := 0x100170007001f00
def ep_52 : Nat := 0x6000800000016000000180000000000000000000100060007000e0001001200020010000100140004001000
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_22, s_22, 7, g_22), (m_40, s_40, 7, g_40), (m_39, s_39, 5, g_39), (m_33, s_33, 5, g_33), (m_38, s_38, 5, g_38), (m_37, s_37, 5, g_37), (m_45, s_45, 5, g_45), (m_34, s_34, 5, g_34), (m_43, s_43, 6, g_43)]
def cur_52 : Nat → List (Nat × Nat) := unpackCursorV5 0x13098486411188442030078bc1e0e1703443801 0x18d0322a394074a844c09227b4fe697ad1eda1d14f9297051d8a1a93f427664dc499801f 9 511 4 15 11 2047 15 32767
def nh_52 : Nat → Nat := unpackHintV5 0xacedba17b7945d28d76e816c1726f0636f054fe74cc833cffd318b723ddb16bd20fd6e03cc10003c00000 0x1543b631d0c6355555555558c6b39cef3cce78e795400000000400021dbaa8754aaaaaaaaa318c75553e9d2a800000000800054319c63a872aaaaaaa8e6318c6378c631c73caa00000000200010edaaaaa8c631d52a80004080005543a3d52aaaaaaaaaac635d554fa74aa000000045c0400016b5ac635aceb9675caaaaaaaa31bf631ad6318e6f9bd55400000000400006318d55554637ec6318def7bd546318e18c671caaaa358c00004000000006318ce38631c318c6aaaaaaaa31ac6318c637cdf37aa80000000080000c631aaaaa8c6bdad6b5aa8000080002c58c6b555555ac6318def7bdeaaab5ad72ceb3ae555518c60000200000002cb8554ba87552aaaaaaacdf37d3f7554755500000000100003c7955555ef7be9fb39e954eb38ce339ce73aaaad40000200000000739c6719d678f1ce7555555559be6faa8e7a7aa80000000080001ce73aaaaad547b6aa000020001154aaaaaf7bdf554f5559750eaa55558f0000080000001170555555000010000 20 1048575 8 255
def f_52 : Nat → Nat × Nat := unpackForestF 0x169e2d2c5a3e4541686253c4a5894774a8250c49f893b126e4910499801f 4 11
def ch_52 : Nat → Bool := dagCheckNodeV5 m_52 g_52 ep_52 3 7 bds_52 16 (dagTraceF m_52 s_52 8 f_52) cur_52 nh_52
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV5 m_52 g_52 ep_52 3 7 16 bds_52 (dagTraceF m_52 s_52 8 f_52) (cur_52 0) (nh_52 0) s_52 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_52 : treeBlockF 0 16 ch_52 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 16 → ch_52 i = true := fun _ h1 h2 => treeBlockF_at nb_52 h1 h2
theorem lb_52 : LowerBin m_52 s_52 g_52 9 :=
  lowerDagV5 (kn_cons lb_22 (kn_cons lb_40 (kn_cons lb_39 (kn_cons lb_33 (kn_cons lb_38 (kn_cons lb_37 (kn_cons lb_45 (kn_cons lb_34 (kn_cons lb_43 (kn_nil)))))))))) rc_52 nc_52 (by decide +kernel)

def m_53 : Nat := 0xf0f0f0f0f0f0f0f0
def s_53 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_53 : Nat := 0x101070005010f0
def ep_53 : Nat := 0x40008000001060000010a000100060005000e0000000000000000000101020000010000010104000501000
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_25, s_25, 7, g_25)]
def cur_53 : Nat → List (Nat × Nat) := fun _ => []
def nh_53 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_53 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV5 m_53 g_53 ep_53 1 1 0 bds_53 (dagTraceF m_53 s_53 7 f_53) (cur_53 0) (nh_53 0) s_53 7 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_53 g_53 ep_53 1 1 bds_53 0 (dagTraceF m_53 s_53 7 f_53) cur_53 nh_53 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_53 : LowerBin m_53 s_53 g_53 8 :=
  lowerDagV5 (kn_cons lb_25 (kn_nil)) rc_53 nc_53 (by decide +kernel)

def m_54 : Nat := 0x3333333333333333
def s_54 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_54 : Nat := 0x113133303131333
def ep_54 : Nat := 0x200000000001220000010200012002000100020010202000302020000000000000000000110100000101000
def bds_54 : List (Nat × List Nat × Nat × Nat) := [(m_27, s_27, 7, g_27)]
def cur_54 : Nat → List (Nat × Nat) := fun _ => []
def nh_54 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_54 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV5 m_54 g_54 ep_54 1 1 0 bds_54 (dagTraceF m_54 s_54 7 f_54) (cur_54 0) (nh_54 0) s_54 7 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_54 g_54 ep_54 1 1 bds_54 0 (dagTraceF m_54 s_54 7 f_54) cur_54 nh_54 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_54 : LowerBin m_54 s_54 g_54 8 :=
  lowerDagV5 (kn_cons lb_27 (kn_nil)) rc_54 nc_54 (by decide +kernel)

def m_55 : Nat := 0xcccccccccccccccc
def s_55 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_55 : Nat := 0x4044404440ccc
def ep_55 : Nat := 0x4400888000004400000088800040040004000c00004040004000c0000000000000000000004044404440000
def bds_55 : List (Nat × List Nat × Nat × Nat) := [(m_36, s_36, 5, g_36), (m_26, s_26, 5, g_26), (m_47, s_47, 5, g_47), (m_39, s_39, 5, g_39), (m_41, s_41, 5, g_41), (m_31, s_31, 5, g_31), (m_49, s_49, 5, g_49), (m_6, s_6, 4, g_6), (m_19, s_19, 4, g_19)]
def cur_55 : Nat → List (Nat × Nat) := unpackCursorV5 0x119 0xddf 3 7 1 1 5 31 6 63
def nh_55 : Nat → Nat := unpackHintV5 0x845000840000 0x9d4d6f7ac6738c9180407d2cf4338ce3b90b1e0c393656bd1a744 16 65535 8 255
def f_55 : Nat → Nat × Nat := unpackForestF 0xddf 1 5
def ch_55 : Nat → Bool := dagCheckNodeV5 m_55 g_55 ep_55 3 7 bds_55 2 (dagTraceF m_55 s_55 7 f_55) cur_55 nh_55
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV5 m_55 g_55 ep_55 3 7 2 bds_55 (dagTraceF m_55 s_55 7 f_55) (cur_55 0) (nh_55 0) s_55 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55 : treeBlockF 0 2 ch_55 = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 2 → ch_55 i = true := fun _ h1 h2 => treeBlockF_at nb_55 h1 h2
theorem lb_55 : LowerBin m_55 s_55 g_55 8 :=
  lowerDagV5 (kn_cons lb_36 (kn_cons lb_26 (kn_cons lb_47 (kn_cons lb_39 (kn_cons lb_41 (kn_cons lb_31 (kn_cons lb_49 (kn_cons lb_6 (kn_cons lb_19 (kn_nil)))))))))) rc_55 nc_55 (by decide +kernel)

def m_56 : Nat := 0xf0f0f0f0f0f0f0f
def s_56 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_56 : Nat := 0x107070707070f0f
def ep_56 : Nat := 0x600080800000600000008080006000000000000000000000000000001020202020200000104040404040000
def bds_56 : List (Nat × List Nat × Nat × Nat) := [(m_40, s_40, 7, g_40)]
def cur_56 : Nat → List (Nat × Nat) := fun _ => []
def nh_56 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_56 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV5 m_56 g_56 ep_56 1 1 0 bds_56 (dagTraceF m_56 s_56 7 f_56) (cur_56 0) (nh_56 0) s_56 7 = true := by decide +kernel
theorem nc_56 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_56 g_56 ep_56 1 1 bds_56 0 (dagTraceF m_56 s_56 7 f_56) cur_56 nh_56 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_56 : LowerBin m_56 s_56 g_56 8 :=
  lowerDagV5 (kn_cons lb_40 (kn_nil)) rc_56 nc_56 (by decide +kernel)

def m_57 : Nat := 0xffffffff
def s_57 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_57 : Nat := 0x7571fff
def ep_57 : Nat := 0x18a800000000005000e00000000007020e0000000000020210000000000004541000
def bds_57 : List (Nat × List Nat × Nat × Nat) := [(m_43, s_43, 6, g_43)]
def cur_57 : Nat → List (Nat × Nat) := fun _ => []
def nh_57 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_57 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV5 m_57 g_57 ep_57 1 1 0 bds_57 (dagTraceF m_57 s_57 6 f_57) (cur_57 0) (nh_57 0) s_57 6 = true := by decide +kernel
theorem nc_57 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_57 g_57 ep_57 1 1 bds_57 0 (dagTraceF m_57 s_57 6 f_57) cur_57 nh_57 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_57 : LowerBin m_57 s_57 g_57 7 :=
  lowerDagV5 (kn_cons lb_43 (kn_nil)) rc_57 nc_57 (by decide +kernel)

def g_58 : Nat := 0x117177707571fff
def ep_58 : Nat := 0x640088800001660000018a800160060005000e00106060007020e0001121222020210000114144404541000
def bds_58 : List (Nat × List Nat × Nat × Nat) := [(m_23, s_23, 7, g_23), (m_56, s_56, 8, g_56), (m_54, s_54, 8, g_54), (m_22, s_22, 7, g_22), (m_51, s_51, 8, g_51), (m_53, s_53, 8, g_53), (m_55, s_55, 8, g_55), (m_41, s_41, 5, g_41), (m_50, s_50, 8, g_50), (m_40, s_40, 7, g_40), (m_19, s_19, 4, g_19), (m_25, s_25, 7, g_25), (m_57, s_57, 7, g_57), (m_24, s_24, 5, g_24), (m_27, s_27, 7, g_27), (m_13, s_13, 4, g_13), (m_30, s_30, 7, g_30), (m_43, s_43, 6, g_43), (m_18, s_18, 4, g_18), (m_46, s_46, 5, g_46), (m_52, s_52, 9, g_52), (m_12, s_12, 4, g_12), (m_35, s_35, 5, g_35), (m_7, s_7, 4, g_7), (m_45, s_45, 5, g_45), (m_17, s_17, 4, g_17), (m_14, s_14, 4, g_14), (m_32, s_32, 5, g_32), (m_15, s_15, 4, g_15), (m_42, s_42, 4, g_42), (m_6, s_6, 4, g_6), (m_39, s_39, 5, g_39), (m_38, s_38, 5, g_38), (m_10, s_10, 4, g_10), (m_3, s_3, 4, g_3), (m_49, s_49, 5, g_49), (m_33, s_33, 5, g_33)]
def cc_58_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xa80d4029834c0a40d2028054009e0cc0e6012c1883c4021830818404202101080820bf09f80f817c03e01e82f01664b3000e4001 0xf954074b203655019ad00b95c05eb18319cc162b80a1340512304558c208de0f45f071b7834d7c1568e09936029a38081580bad0056730211a01091805ad00236f042b181f1bc0e8be06b6f031af812d1c0746c0306600c2b5f717ef68b778c57b8a29dbcd7ed96b76bb57b3da9d8ad3ec06975f347ae5a1d5c97ea64af4e24fa4d23d1a8fe5346f1c95f890adc0655de12a6e394f6cca5b3651d7b286ae93f5489da7e4dd132667e92b2b89394217ca00b643857218298f613c7a0962b0471542186e0fc36076188370bc1985c0ac2404e0901f0440d80405c010260003f 13 8191 6 63 11 2047 21 2097151
def cc_58_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x9c2709c2348c23084989601805c5705c143501314c13040cf1348d0304c02c4920d8300481000400 0x1fb487cd11ea4478511d06f720969d63a29be7a5f9c8d6516f9057e01357649dc0566a555a563665bd915f600d1596f1049540564e1595a464c159386f4e4d941364c1bd6d6358919516f5257c39354a158c347465510964 10 1023 4 15 11 2047 18 262143
def cc_58_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xb02c0b0284a0280a025367190641725c152541233ccf03c0f02d0b0284a024490240902409002400 0xbedcef36cbad82e246b41b6c84db009fbb6fe89bf925dde8df496fc65770937b649eb866700f928260605aa3548c4d69364864d68354985fe1135965bdf1457a4966b649897e5a357415a4b548f16235638b18e2453869be125f82935f24578499c856 10 1023 4 15 11 2047 18 262143
def cc_58_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0d82c136984a6510c84421d8e869b41a0a64ca6130984515ca05028140a01f0c0281001 0x3fa37846df049be011bbf16f7d26ef849c140b3cd68782cad0574100b3b568734b8ea5959caeb9a6e6c2debc535c6303517f652dae05357092940246b46ed79e09c12375686d4cad8975a91bb215c3a07c4c099a1b7b3a6f5e49acc915951bb216e590ccc5181603b3027c 9 511 3 7 11 2047 19 524287
def cc_58_4 : Nat → List (Nat × Nat) := unpackCursorV5 0x9c652942508ca308c1e5781e065581601805c5704d130449104411038c4a100400c4300842000800 0x9f8f93693a2caece47c9b4f9331c254bec815f9829b124962d2ecb2559546f1e539682348a3791b19271f24922c82378f2f91b1c1602b45b7c8a6e11291a79a7cea6d9a49f2e8de50b6c714f8c26f1049d5c2303016852cb06595fcbfc094d 10 1023 4 15 11 2047 19 524287
def cc_58_5 : Nat → List (Nat × Nat) := unpackCursorV5 0xdc1dc0d81d80d41d40d01d00d00c82c80c80c80c02c00bc13a1380380341340283280280202200200200182006000000 0xbf4c97a9f2ed2a5ca6cb74a96c912ceb1d9246b06e5f55bfdeb5fa567eeac7d51af9631f0c5bdc8a7b4dbf61b5eb367d36c7a0d7f39ade5357c66a78ad3f11a1e0246be2df7859ee8afdc157b529f441be2033be05f5b0ae7613ed01fd883daf06e0e0d6b0a2d395faa29b46496a122d3a37a46a74691ab5a7d5a4fa946f4c53e949bd1127 12 4095 6 63 11 2047 19 524287
def cc_58_6 : Nat → List (Nat × Nat) := unpackCursorV5 0xb42d0a529098e518ca3080e007c5b4685a059151505404c5303d0f0384e02cca1244902409002400 0x70348df689bc91374a26cb78bf4c9b659355326cc7ccc8cda8d82f53e6b97cd54d9a91d34a372f867b008b9a95349b967b68bb4a9a2553252a67c6ccd4d998deb21a85ca6ccb2d99297322325207fc70496c91305aa61d6fc2acf828c6dc9ed186f890ceb815ec81684025 10 1023 4 15 11 2047 19 524287
def cc_58_7 : Nat → List (Nat × Nat) := unpackCursorV5 0x809886018054d50541324c13040d004010040100298a0280a01cc701c0701c0340c0300c00300000 0x802447f94488d6f87d6b86567845638346b81c6380c5b7f4537e3687db6461a467cb587c3547b37c7ab706124679b587935478a5478154778545983d76b487634475a4474b487434473a44731447234871b4471244 10 1023 4 15 11 2047 20 1048575
def cc_58_8 : Nat → List (Nat × Nat) := unpackCursorV5 0x902408c6308c2308c22188211570ba2c0a128091240901c8701c07010c400c4300c0120400100000 0x8e96c8c15c8b0249245f91c5b91457904538fa5f8f25b8e2578da538d24f8ca4b8ba478aa439ed6f9dd6b9cd679b5639a36f98b6797b5f96357929368a13489164881548737c8697c85a5485154848548394482a448214481144 10 1023 4 15 11 2047 20 1048575
def cc_58_9 : Nat → List (Nat × Nat) := unpackCursorV5 0x843cde0e27032d90c155aa13491481ecf06a3098096482412082401c8381008040200200 0x9f16495936921349e154919349d17c9513691134908249c154901349b8549a964949348e92499a7c9917c9413498154939348c1249726c9696c931348e96c8c15c95d6f9556794a6e9426693a5e9325690844 9 511 3 7 11 2047 20 1048575
def cc_58_10 : Nat → List (Nat × Nat) := unpackCursorV5 0xc021f84201801f17c1e1781e0781b35d1705856054550505405014050131394e0380e0380e03440d 0xbcd6fbbd6bbad67b9563b826fb6a67b5a5fb4257b2a45b1235b096fb0167af95faf1575a927ae164ad154ac17cab254aa954aa054add6facd6babd67a9d63a8c68a7c58a6c70a404fa5c58a5154a4855a3854a084da0d63a856fa756ba6567a3563a296fa2167a195fa11575286f460673e85f30857a004d 10 1023 4 15 11 2047 20 1048575
def cc_58_11 : Nat → List (Nat × Nat) := unpackCursorV5 0xa02808215b5412348111440e3380e0308c02c4b02c092240812008018860180330c03000c0000000 0xc235fc1b5bc1357c0b53c025fbfa57bf23fbea37ccc6fcbc6bcac67c9c63c8b6fc7b67c734fc4b47c3136c2818be014bd364b3a45b2235bc354bb37cb3245b1a35ba354b9854b8b64b7b7cb717cb6354b536cb496cb3d6fb35675b925b256fb1d675b125 10 1023 4 15 11 2047 20 1048575
def cc_58_12 : Nat → List (Nat × Nat) := unpackCursorV5 0x90a409016e581425012248102400e2380c23009320480200801c4250802000800000000000000000 0xd0460cf84cd8b6fd736bd6367d4363d326fd2267d125dd0a3fcf237ce96fce167af13fa11375c127cd164c2014cc144c1814cb17cc1014ca144c0814c9164c0014c817cc4134bf814bf014c5844c6a5cc615cc3934c505cbe814c4266c3a46 10 1023 4 15 11 2047 20 1048575
def cc_58_13 : Nat → List (Nat × Nat) := unpackCursorV5 0xd96c343a0c8e432190b1d82a2c9602c560b049241028040200a650190c04220010000000 0xe0244df944de964dd97cdc15cda934db85cdaa46e2c6fe1c6be0c67df463de36fdd367dcb4fdb347da136d9568d836cd7a35d6d70d5b6cd5235d4934d3d68d1a5cd2d70d1a6e5c925 9 511 4 15 11 2047 20 1048575
def cc_58_14 : Nat → List (Nat × Nat) := unpackCursorV5 0x9c738260cc094328240c8090110a20421786f01e03c0780f0183300600c01708740c01042002104000400000 0xf0464ef865e4845eeb54edc7cecb54ebc64eb065ea47c5d9255406f49067e8458e794c5387f48077e704de684ce4b6fef36fee36bed367ec363eaa6fe9a67e9245e8a3fe6237e596fe5167af93fa19375d1275306f47067e40452403f1903714827e3164e2144e117c 11 2047 5 31 11 2047 20 1048575
def cc_58_15 : Nat → List (Nat × Nat) := unpackCursorV5 0x9c252942328c212841f27c1c36c5b06c1b068555541504c9304c1304c1304c1304c1302e00b00000 0xff144f4814fe16cf4014fd144f3814fc154f3014fb16cf7134f2814f2014f8844f9a5cf915cf6934f805cf1814f7256f6a46f534ff4b4bf4347f3b43f324ff2a47f223ff1a37ffc5ffec5bfdc57fcc53fbb5ffab57fa34ff7b47f6136f5818f1014 10 1023 4 15 11 2047 20 1048575
def cc_58_16 : Nat → List (Nat × Nat) := unpackCursorV5 0xacab0a86a0a82a09ce439024088a2084610805f1785d1741b26c1a168182511404884e100400c403 0x11037c87d1ac3b5c21b6f90d2358649a42a93a1147c5e92585a3e42a9f213ae108a7c839b4414d520e8d904b5083036414d72098c90403483dafc1ad6e0b6af03b5381a3840a1322169f0f34b871a3c30d0e174db0a24f84923c208fe0446ee514f670a3ac04fd4426e5e12780426404552000a8f5014 10 1023 4 15 11 2047 21 2097151
def cc_58_17 : Nat → List (Nat × Nat) := unpackCursorV5 0xc8190320567ac0bd1702e0544a8140a804c298130222440805001e13c0780f01833005842484008000800000 0x23f8d11f14c1fc2f8d415e3d09b1e04c0ac12c9ed3e4c6972534791da1c8c9564349f20a479011fc768ddcb29ece9475849fa8a4dcbe24f1d0551f8278d211c4a07e198370a813c70552370a91a9448ccb646291230289171548b0b6452572262691405c8992346d17e348b7194578be29c5ad7e2b6af1534f89da3c4a4da238f911044 11 2047 5 31 11 2047 21 2097151
def cc_58_18 : Nat → List (Nat × Nat) := unpackCursorV5 0x8007e17e07e07a27627607607224f24e01d91c01c01c01631601601221201011001000c2082080080023020001000000 0x9782a4b85525b0a92ed6b96ab1cb15ae57ac73545f9a22dccd15e638a73135f985abcc0d3e5f68f1e05f8a02dc0a15df00a6e684f6dc25b3e11d8a0872c83b9581bd155be87ad73e5679dab1c765be272d7021677bcb1b9857db62b6cf157624a9ce05356527a601252a43792e19c800be378579b026caa13254080160250540f81205e528c9288459402249cd924d46b25d68925b24908d4bf24a36847916324881144c07f21568 12 4095 5 31 11 2047 21 2097151
def cc_58_19 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc321ade92a4281a0262765d0741d0741c1430f13c0e1290a02449018c6014450104040000000000 0x4ce1327f8e13f27c9f4bece65356627a611259982603207c0b02f3204c9e1a04e40f67b8b13d2549e4aace2536770a93784d98c2603007c0a02f390549d6b7ce95ae73acf38d638f8b73e6589cf2bcc69522a83793019c810be380579b8a2cdd58e6fac71e96f738afcda5166b0ab348459741dcb00de670db2e03a995a24c81165a0772b837 10 1023 4 15 11 2047 21 2097151
def cc_58_20 : Nat → List (Nat × Nat) := unpackCursorV5 0x8810899fb30660c4988310620b8d612394608c1182304425b0b01511ec3c0708a4122204388610c014420804 0x910b7d3c536a36d75036390cb7c5a5ae142cefb963a7ca2ad64fd2f2665586f26833d3a1144f07e0d01f0300bd36db29a26b4c36ca5d1a52c4d56927c97132a65b5d2ad8e412df1596b848b3bea58e942bab413f4b099d1e15292adf48d6ba42b3d1d58e402df1516b840b3be858dd12bedc95b684abb1c54e6b09946468a2cb2cea5356727a619259a8264d2132898b1441559d0a6cd01328529141134a15265024c28227940a44a189fd084ee8326f40133 11 2047 4 15 11 2047 21 2097151
def cc_58_21 : Nat → List (Nat × Nat) := unpackCursorV5 0x86b0c1eb3d06ceb29602c0580a4d482904e49492823229e500a0122240480810e20b2140280320600c009001 0x9296f8c96b871677ed63afd5daa6669216f86967af53d37d3537925ace6faee3d37e358c56a865664012a37526aca6faa267af23591d6f8bd6b861677e563ae9353f92b37127ae364ade34ad935ad364acd3520c4f1d447ac15d7594fad74bacb43ac5557554f6f14b69947645435c13f4d133abc552084f1d0471443f0701f03417ab77cab135aab7caa6345b93e4cd32aaf4baa343a9d6d74d4f6e94b6914763d435b53f4c533a9754a9234a8b54a85352b06f 11 2047 4 15 10 1023 20 1048575
def cc_58_22 : Nat → List (Nat × Nat) := unpackCursorV5 0xb756c2b2d60a6726a48445880fd5f83f07c2f81a52aa540a8150282500a0140280410530a00e61c029005000 0xb85557794f7154b6c54766543b7c552104f1dc470801f03c17a925e6bd57b753d3b1353ad25a6a57b6e3d3b235a8e5fa6657b72357715f70d5b6b95765d53b69354192b3a927b616d7694f7054b6b14765543a5e566a957b593d3a13539d25b4c34b535bb4b53a865fa5a57b463d3a2357015a6a5564152a39926a825fa5657b56357615f6f95b6a15764d53b413540d2b395279456fb314db2b5bb27539405f8dc5b8885780053b203fb1c3393d6f8d96b885677fd63b39452b46f27867b3448b2c45b18440781f03817ade6e9356f87d67b113d38d3538925ada6fab267b0a3d38e35ad66faae67b0e359316f8d16b879677f563b05354052b38527 11 2047 4 15 10 1023 20 1048575
def cc_58_23 : Nat → List (Nat × Nat) := unpackCursorV5 0xc02c00ba3a6aa60a22a209c388a8808048007a366a6605e45e04e84e04e04a24a04a04a04624414402cc092042040002 0xbfd5d3ed55bf65d3ee55a2e37bfa55a4a3fa2a37bf1555e53f56d3b541374f5334452b3e927be94d3e145be24d3e245a2237be645a463fa1e37bdd455dd3f5653b539374ed3343d2b3dd279fa363d96dbd565439293da6dbce659f637bd26da423f9f237bc96d5d53f55d3b531374e5334312b3d1279ea36bc14d3c9453c525bba4d3ca459e6375593a5293642d2a3c1260d437bad4d52537ba124b9c2552027ba63fb9a33a3d2f9dd27b943fb90335cc2f5502b51c274dc234241b3bc17bbe45a3a3f9da37bb5455c93f54d3b519374d9334212b3b927bb048ba845b8c4414c3f0d0370b4270881f040172144f1e047b815d77d4f 12 4095 5 31 10 1023 20 1048575
def cur_58 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec ([]) (cc_58_23 (Nat.sub p 736)) (Nat.blt p 768)) (Bool.rec (cc_58_22 (Nat.sub p 704)) (cc_58_21 (Nat.sub p 672)) (Nat.blt p 704)) (Nat.blt p 736)) (Bool.rec (Bool.rec (cc_58_20 (Nat.sub p 640)) (cc_58_19 (Nat.sub p 608)) (Nat.blt p 640)) (cc_58_18 (Nat.sub p 576)) (Nat.blt p 608)) (Nat.blt p 672)) (Bool.rec (Bool.rec (Bool.rec (cc_58_17 (Nat.sub p 544)) (cc_58_16 (Nat.sub p 512)) (Nat.blt p 544)) (cc_58_15 (Nat.sub p 480)) (Nat.blt p 512)) (Bool.rec (Bool.rec (cc_58_14 (Nat.sub p 448)) (cc_58_13 (Nat.sub p 416)) (Nat.blt p 448)) (cc_58_12 (Nat.sub p 384)) (Nat.blt p 416)) (Nat.blt p 480)) (Nat.blt p 576)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_58_11 (Nat.sub p 352)) (cc_58_10 (Nat.sub p 320)) (Nat.blt p 352)) (cc_58_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (Bool.rec (cc_58_8 (Nat.sub p 256)) (cc_58_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_58_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (cc_58_5 (Nat.sub p 160)) (cc_58_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_58_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_58_2 (Nat.sub p 64)) (cc_58_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_58_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)) (Nat.blt p 384)
def hc_58_0 : Nat → Nat := unpackHintV5 0xad01c4a5e9c69bb28e9529a28bca588ac8408848a087104e80e18c78f9fa74412e6ca9e667714e61099a57227a4f61f047f9da3d02be32fa823260262fe89e27ca082329281ba9e014a9c01458141160be0ca130075952014186000050000000 0x83e0f45d507542d55662d5551b031b030fa03540d1b55500000000000005c007003c0804400400101000c013000000000042700000022c0000303000170707172b87c3cae1f0f170707171b48c2c6d230b1b231b1f00c0c0c000c0c00c0c0c0c0c0c0c0c0000000000000000000000000000c0c0c5c1c1c5c5e170f1785c3c5c1c1c5c5d170b1745c2c6c8c6c7c0c0c0e2c0c1c0c0c0c1c0c0c0c0c0c0c0c0c0c00000000000017001c01305c00170000f02002c04003000c00000000000000022c00083e0f1f171f071f071f1703030001b1f1b1f0fa0f1b47c2c6d1f0b03030303280c02800c0c0c0c0000000000000000000000000020f83c3c5c3c1c3c1c3c3c0c0c0c6c7c6c7c3e83c3d0f0b0f43c2c0c0c0c0e80e2e80c0ea0303030300000000000005c007003c0800f03c000f0000b01000c00300000000000000008b00002d2b04c03132722e2c1c5e0f50f0b40d0e2c3c3f040b40c4c272722e2c3cad0c3c2d034309c2f372f2b172b072b072b172b0f2b8ae2b0f55555000030303030303030303030005100000000000000000ac0000000000002f372f541d51756543d555550303030303030303503555038b0000000000000005c007003c0804001100102c04400300c0030000000109c00000000008b00004c4c4c4d555555555131313131313131350001545138b00000000000000000122c0000000002f132f131b231b2313231b131317370713073b17130f1384e130f130b1b44d230b03030303030303030303030303000000000000000000000000000000bcdcbc8cdc8c8cbc8c0cdc0c0cbc0c8c0c0c0000000017001c00f02002c04003000000000000022c0002f2f2f2f2323232323232323030303030303030303030303000000000037000bc0000022c0017001c00f02002c04003000c000281c1e07a2ea070707170707170fa0f0f43c2c3d0f0b170307030fa030f0f03030f4b030323030305c007003c0800f03c000f09c000b01000c013000000000000000001c00800003c2700000000008b42d17070717543d950762d5555517030703540d1b51b031b035505c00701100109c000f020101000c01b000000000000000001c000109c0000000000008b83e0f45d507542d55662d5551b031b030fa03540d1b55505c007003c080440042700101000c013000000000000000007c008000109c00000000022c0c0c0c5c1c1c5c5e170f1785c3c5c1c1c5c5d170b1745c2c6c8c6c8c0c0c0e2c0c1c0c0c0c1c0c0c0c0c0c0c0c0c0c17001c01305c001709c000f02002c04003000c00000000000000000700001709c000ec0000000008b83e0f0f170f070f070f0f0303031b1f1b230fa0f0f43c2c3d0f0b03030303a038ba0303a80c0c0c0c17001c00f02003c0f0003c270002c04003000c00000000000000001f00200000f09c00000000022c9c1309c8b8b071783d43c2d03438b0f09c27100c4c272722cbcdcbd507545d5950f5555540c0c0c0c0c0c0c0d40d5540e2c17001c00f020109c00440040400300c00300000000000000000003b000ec109c000000000000022c4c4c4c4d555555555131313131313131350001545130b00000000000c00001304000013000bc4cbc4c6c8c6c8c4c8c6c4c4c5c9c1c4c1c9c5c4c3c4e1384c3c4c2c6d1348c2c0c0c0c0c0c0c0c0c0c0c0c0c0c000000000c00000027000270000000781c1e070707070707070707070707071f232f1f07030703070307031f032f0323033b0301c00001c0022c0200000070008b0000000002800002d0796696900762d559031b40700427200808b406c02000a07aaa80233723aaaa3b033703aaaa23033b0300070800020008b02c00009c002000000000002f372f233723232f23033703032f0323030305c007003c0800b01000c000000000000000000000000022cbcbcbcbc8c8c8c8c8c8c8c8c0c0c0c0c0c0c0c0c0c0c0c0c00000000000000000008b05c007003c0800b01000c003000047474747474747474747 24 16777215 10 1023
def hc_58_1 : Nat → Nat := unpackHintV5 0xded9b2d811b2cf4a32c1fb54bd6126b8394ab21988aa1a00a53938a158f8974a848ea22a865a128089747ca8f876a182706190611bd25b297c5838bc4b034e3e133c39692a38d8243401362d09be23a25a1ce9ae135a640d49840611ce000184 0x131313131313130713071317130f1384e130f42d0b42d0b5000030303030303030303130303403000004c0000000013013100000000004c4c4c4c4c4c4c4c4c4c4c4d0b42d0b42d4004c4c4c4c4c4c4c4c2c2c0000b0b40b0b000004c0022c0003000004c04c00001322c00002f332f332b2b2b2b2b2b2b2b42d0b42d0b002b2b2b2b2b2b2b2b0b0b030303030303030b0b50b0b0303030303030303032b0303030303038b035503000000cc00000ac8b00000bcccbccd0b42d0b42c2c5c2c1c2c1c2c2c2c3c2e0b82c2c02b1733072b0733172b0f2f8ae330f0b0b550b0b0b0b0b0b0b0b330b0b130b0b0b0b0303030303030303035503030303030303030b030303000000000000b00030030022c0000cc022c4040cc27000000c00002aa1783ea810b42e62d81c1c2c2c2c2c5c2c7c2e5682e2e805c0ccc0e030b3b08b0701c80aaaa00acdc1cac1daea6aaa90b42d9998000cc0ccc0eaaa8cc4c0cac4c0c2d40c0000000b00b0000332aaa8042d0b662e5a660b0b070b070ba596a82e2eaa00cc0ccc0eaa03aa0b5030b0b030b3b030dc88880b102c2c0b00c330bcdcbd0b42d0b42c2c5c2c1c2c1c2c2c2c3c2e0b82c2c0033703032f030b5030b0b03030b03030dc0bc0b102c2c02c00c08c2308c2323048b50540c6c0306c00bcbcbcbd55540c0c0c0c0c0c0c0d5400000000000048b00000005c007003c080400c0030000002001c041d17643d52348d51f47d5406c0c6c0c4d40c5c0f03c00106c011022e81c1e07a2ea070707541d51756543d550f48d550f43d555555540170307030fa030f0f03030f1b030344d5503551701c0f203c3c03c123050440306c1701c0f203c3c0f00f0f2327050b50122c0c030000170707171785c3c5e170f541d5175545d235545d1756543d5555555401703070317170303171b03031b031b0346d550355022c07001c000000000000000000104008b000083e0f0f170f070f070f0f01507545d5950f5543d235543d0f55555555006c0c6c0c3e80c3c3c0c0c3c6c0c0d135540d540008b20200000000000000000410022c0000bcdcbd507545d5950f5555006c0c6c0c6c0c6c0d1b5540d543702f123050440306c2308c2308c50b50122c0c03000bcbcbcbd0b42d0b42c0c0c0c0c0c0c0c0c0d40c000000000000bc0000c0000bcbcbcbd0b42d0b42c0c0c0c0c0c0c0c0c0d40c000000000000bc00122c03000005c007003c0800b00311c00300000002f2f2f2f1b231b231b231b230303030303030303030303030000000000002f0000322c000017001c00f02002c04003000000a070781e8ba81c1c1c5c1c1c5c3e83c3d0f0b0f43c2c0c4c0c0c0c1c0c0c0c3ea80c0c0c3c0c3c0c0c0c0c0c3c0c9c0c0c0c0c0c2c0d0340c0c0c0c0c0c0e80c0c0c0c0c0c0c0c0c0c0c0c0c4c0c01701c0f203c3c03cfc08c1b00c0c00c4c00c0300c0300ca8030300c00c3c0c9c00c0300c0c0c0c0c00322c00bc4cbc4d55555555503030303030303035054155503030dc130bc4448c500c0c0300c0300c0303141122d100c0c0c0020f83d555540c0c0c0d00540c0c22c1c07100000408b0300170707171785c3c5e170f170707171745c2c5d170b1b231b23031703030307030303170317030303030317032703030303030f0380e0303030b0340d03030303030303030303030303030303030303030303030008b01c00700000000000000000000000c00c008b0083e0f0f170f070f070f0f006c8c6c8c3e83c3d0f0b0f43c2c0c4c0c0c0c1c0c0c0c3ea80c0c0c3c0c3c0c0c0c0c0c3c0c9c0c0c0c0c0c2c0d0340c0c0c0c0c0c0e80c0c0c0c0c0c0c0c0c0c0c0c0c4c0c000022c808000000000000800003c2700000c00c008b00aaaa015555662d55555555503030303aa80eaa035054155503030dc88884448c500c0c031303e8b00e2c2aa1783ea810b42c0c1c0c0c0c0c5c0c4c0ea0303a80e2c2c0c0c0c0c0ea038b03008b0701c80aaaa006c8c6c8eaaa80c0c0c0c1c0eaaa0303aaa80e2c0c2c0c0c0c0c0c0c0c0eaaa038baa03030303030037222208c1b00c0c032700c030bcdcbc6c8c6c8c6c8c6c8c0c5c0c0c0c1c0c0c0c3c0e0380c0c0c2c0d0340c0c0c0c0c0c0c0c0c0c0c0c0c0c0c00dc0bc2306c030300300300c0300c0300c0c0300c0303030303000c8b0081e280001c1c0005c1c1c5c3e83c7d1f0b1f47c2c5c0c1c0c3e80c7c4c0c0c7c4c0c0c8c0cfc0c00000000000000000001f00000000281c1e07a2ea070707170707170fa0f0f43c2c3d0f0b170307030fa030f0f03030f43030323030300000000000005c007003c0800f03c000f0000b01000c01300000000000f09c0000008b00002c2c0005c1c1c5cae1f0f2b87c3c540141545c0c1c0c6c4c0c0c6c4c0c0c6c0c6c0d540000000000000000000000000010b45c1c1c5d50f6541d8b5555545c0c1c0d50346d46c0c6c0d5400000000000017001c0440040003c080404003006c00000000000000022c00083e0f1f171f071f071f170b0b000551500501b031b030fa031b1303031b13030355000000000000000000007c00000000 24 16777215 10 1023
def hc_58_2 : Nat → Nat := unpackHintV5 0xe20178db899ed870c6cf3250c9b160c2d1b8bef8f6b839b0b2896cad0162a4921c96ab7a8d6a507e33ce7651f8688b725ee26a5829ae5620825061704443083e2986321b043048742a517e25394620812e19f1a41429720d09c806919e0001a4 0xaa1317130713071313a0001b231b23aa1344c2c4d130b030303032a03130303030303000004c000000000000000000aa1b231b23aa03030303a8030303035717370737075717a000230b1b46d230ba00000000000000000000cc00000c0003b03c00020785c1555544e84d00544e2c01022c00c0ee2022d1004c130a81ea17aa006c8c6c8e6a60baa13173707130717a13aaaaa57aaaa130b1b44d230b0303030380eaa03aa0303030303000000000000030030022c00ec208008b0cc000001309c0000c000000aaaaaaaaaa001c1c1c1c7c7c2c7c7c2eaaa81c0c1c0c7c4c0c7c4c0eaaa88c0cec0c001c01c200200000002aaa81c1c1c1c1c1c1c1c1c1c1c1c0001c1c1c1c1c1c1c1ea8ac8d3c8c1c0c1c0c1c0c1c0ea8ac0cec0c8c0cec0c070001c00020800000a0783e81e8ba07a2c10741d0754d0741d999990f501b071b5031b4011022c0aaa0783eaa81e8baaa07a2ea8007070707070b07070707aaaa073b0307070307030703aaaa23033b030701c1c0701c8a2208c00c3b2a07a85ea802337239a982ea80cdc0eaa80ea88c0c0c3720a088230030270bc9ca0fa0222c8c230bc0c2f0300bc20f83c8c8c8c8c3e83c0c0c0c0c0e80c0c0c0c0c00000000000088b00000005c007003c02c04003000c00000081e0ba070707070b81c1ea82c1d0742d90b5050b05c0c1c0c3e80ccc4c0c0ccc4c0c0c2d40c5c0703c8332b0332b00b100c3305c0703ca80f40f05402c54031b00c1b00a070781e8ba81c1c1d0742d90b50b0b50b0b0b17070707070b0b0b0faa0b0b0b0f0b0f0b0b0b0b0b0f0b0b0b0b0b005c0c1c0c3e80c3c3c0c0c3ccc0c0c2d40c2c2c0c0c2c4c0c0c5c0703c80f0f00f4f00b102c2c02c00c3305c0703ca80f0f03c03c3c8c9c048b50540c6c0306c001c1c0c0c0c0c0c0cbe330f2f8cc3c5c1c1c5d4140c41d0b42d0b0303030303030303030303030303030303503332b0332b01701c330bc0b100c0300d0500300c0300c0ccc03100c030000c0c0c5c1c1c5c5e170f1785c3d0742d42c2d42c2d0b42c2c5c1c1c1c1c2c2c2c4c2c5c2c2c2c2c2c5c2c2c2c2c2c2c3c2e0b82c2c00303038b03070303030703030303030350303030303030303031701c17170174f0330bc0b102c2c02c00c0300c0300c0c0300317032700300c0ccc122d415030300c0300331733073307331783e0fa0303a030342d0b50503190b030303030380c0e80c0c0e80c0d40d7c370ccac0ccac03c80b100c0300c0300d05003200c40300c0083e0f0f170f070f070f0f03030342d0b642d42c2d42c2c2c5c2c1c2c1c2c2c2c3ea82c2c2c3c2c3c2c2c2c2c2c3c2c2c2c2c2c003030303a038ba0303a80d40c0c0c0c0c0c0c0c0c3703c80f0f00f4f00b102c2c02c00c0300c0300ca8030300c00c3c0c9c048b50540c0c0300c00bc4cbc4c4c5cdc1c4c1cec5c4c3c4e1384c3d0b42d0b42d4140c0303030303030303030b03030b503030dc130bc3b3b01300b100c0c0300c0300c03033b00c6d4140300c40303038b00c0c030007070001f87c3c7e1f0f17070717500041c0b42d0b1f1303031f130303170307031f031f030b503000000000000000000001f00000005c3dfc3c5c2c7c2c3c2d7c2e2e2c278b083e0f17070717171313173b1f1713131717170fa0f42d0b40030303030b030b0308b0701c000000ec6c4000c8b0005c1c1c5c5e170f1785c3d0742d42c2d42c2d0b42c2c5c1c1c1c1c2c2c2c5c2c5c2c2c2c2c2c5c2c2c2c2c2c2c3c2e0b82c2c0170307031717030317330303032f030b5030b0b03030b0303022c07001c000000000000000000008b10101b0000331733073307331783e0fa00042d0b5000602ccc0ccc0ccc4c0c0ccc4c0c0c3e80c2d40c000000000000000000000000020f83c3c5c3c1c3c1c3c3c042d0b642d42c2d42c2c2c5c2c1c2c1c2c2c2c3ea82c2c2c3c2c3c2c2c2c2c2c3c2c2c2c2c2c0330333030fa030f0f03030f3303030b5030b0b03030b13030300022c808000000000000800003c270022c40406c0002070781e81c2c013031303000cc8020707a2e81c1c5c1c1c5c3e83c3c3c3c3dac3cacac3c3c3d0b42c003c0ccc0c4c0c4c0c003c2b02c0b0332000f09c00017171707072b2b2b2f2b6b0017170fa0f0707070b00fc0cac0c5c0ccc0c02c0b0002b1ac00005c2700ac7c7dac3c3c3e8acac005c1c1c3c3c3ea0b004c0c4c0c3c0ccc0c02c0b0002b200000f09c0030383e0f17070717131713173f87172b2b1317130fa0f42d0b0003038b070307033303130303030303000b02c00c005c270330001707070f0303170707170fa0f0f0f0f0f3f770f2b2b0f0f0f42d0b0080e2e03a03030303000b02c00c8003c2700004c4c4c4d0b42d0b42c4c5c4c1c4c1c4c4c4c3c4e1384c3c0c0c0000c4c0c0c0c0c0c0c0c0c5503031303000000000000000001300000000000bcdcbcac5cdc1cac1c5cac3cbe2b83d0b42d0b42c00000cdc0c0cbc0cfc0c0cac0c0c2d40c00000b00b000000000000000000002f332f3342d0b42d0b0303030303030303031033317330733073317330f2f8be330f0050030300000000000000000000000000000 24 16777215 10 1023
def hc_58_3 : Nat → Nat := unpackHintV5 0xbbcb26b3222aa693249eb1f899495a9329888f090886c2127ec9fe7a611a6e8af66719dc5f61ee57f1dc5361244aca2645097040a11a3be1303b2030394078301a4a2c010626516c2051801bd1201481d40e897e0939540209cc01b01600006c 0x20783e83c3c3c3e17a0f0f0f17070707070f0f0f170f170f0f0f0f0f170f2f0f0f0f0f005c1c1c5c5d170b1745c2c3e83c3d0f0b0f43c2c5c0c1c0c5c4c0c0c5c4c0c0c3e80c3c3c0c0c3cbc0c0c8c0c0c08b01c0070000000000000000008b20200000020f83c3c5c3c1c3c1c3c3c0541d517566543d0f5543d2f5543d0f55555555006c0c6c0c3e80c3c3c0c0c3c6c0c0d135540d1b5500000000104008b0000022c808000000000083e0f0f170f070f070f0f006c7c6c8c3e83c3d0f0b0f43c2c4c4c4c1c4c1c4c5c3c3ea83c3c3c3c3c3c3c3c4cbc3c3c4cbc3c3c3c3c4c2c4d1344c2c0c0c0c0c0e80c0c0c0c0c0c0c0c0c0c0c0c0c4c0c0000000000000c00c008b00022c808000000000083e0f0f170f070f070f0f008cdc8c3e83c3d0f0b0f43c2c0cdc0c3e80c3c3c0c0c3cbc0c0c8c0c0c3703c80f0f00f2f02300302709c222e82a2308c0300c00aa23232323aa03030303aa03030303000000000037088b0008c00000c00005c0070200b01000c0030000002aaaa82c2d4115555555545c0c1c0ea86c4c0c0c6c4c0c0d545c072214cac14cac1100c1b05c072103c3c141100c03008c02c081e17a8ae2ba8ae5faa00455130313031ba03171000407002b09c8808b406c10b6a07a85d5565a55aa5665010762d5555555642d545c0c1c0d50346d61baa80ea9545c071410828221100c1b05c070707144148c9c283e8088b5110306c0c6c0230aaaaa0303a08a17070717aa1b48c2c6d230b80c0c0ea80c0eaa80c0c0c0c5c072214cac14cac08c1b00c0300c032200c0c00c0c00ccc0300c0c030303000c3b00c081e17a8ae2ba8ae43aa042d0b642c00c03a031704c0000c07002b09c8808b330030030303a81ea17aa85eaa84e17aaaaaa005c1c1c5c4d170b1744c2e6a60baa0303038b03070303030703a03aaa0303aa030303031701c131701708282208c1b00c0300c03030700c0c030031703270a03a0222c0ccc0300c0c030303000c3b00c0c0eaaaa84c4c1c1c1c1c4e2ea0707aaa285c1c1c5c4c4c4c4ea84c4c4c4c5c0704c132204c1308c1b00c0300c0c030313038b2200c0300c03002a8ec5c4c1cdc1c4c5e82286c8c6c8ea84d230b1b44c2c0c0c0c0c0eaaaa030303030dc881303b3b02306c0300c0300c8803030030300300c030300c0c00aa55556f17370737076f175045555503030303aa550303aaa6f0dc88446f2b06f2b00300c0300c0ceca12511030f030510030300c0c0c0e2c0030ec81e170170707178ad0eaaa2b2baa554003a030300ac82b002104030ee2022cac270010030a81ea17aa01507545d5599559565655555555540c0c0c0e03aa80ea940d5540e2c3720a08841412314030300c0300c0ceca03a0222d40c9c14414440c0c03030303000c3b228028280005c1c1c5ea87d1f0b1f47c2c5c0c1c0ea87c4c0c0c7c4c0c0c8c0c0c0000000000000000000000000000c0a84e13a84e3f81e17aa042d0b642c4c0c4c0c0e80c00000004c130078808b3300300aa17070717171717171313173b1f1713138042d0b42d0b170303030303aa08b0701c000000054d1f8b2b09ca170f91f45d96f8b8b3f0ac09e2c9c02a07a85eaa17aaa1785eaaa1783eaa80170707171745c2c5d170b9a982ea85c0c1c0c5c5c0c0c5c0c0eaa80ea88c0c0c08b01c007080000000000000700001709c0820022c000000002d6917070717552b2b53d8d5000762d5555031b46c0c6c0c5c002801c0109c0000303aa17070717131713172b2b173f631317130042d0b42d0b03038b070307030303030317000a007001709c0001313130713071317aaa0001b231b231344c2c4d130baa03030303031303a203030303000000000000000000000000000170707170041d176654fd6354ad2b5550303030340d5038b3f0a10ac00000ec0109c000002aaa17aa2e1717070707072b8ba81c1eaa001707071717171717aa2b232b231703070317031703aa2b032b0323033f0300070001722c00000000aa63172b0737072b170000233723aa2b48c2d3d230b033703aa2b03033f0303230303000020800000000000000000002a95551bc5cdc1cdc1dbc5d400140006c0c6c0ea9546c4c0c0c6c4c0c0c000000000000000000000000002a07a85ea80541d51755665565599590f55555555006c0c6c0e1baa80ea91b5540d1b5500000000104008b00000820022c4270000100001b0002a078b0717131313a57a17078b8b04c27 24 16777215 10 1023
def hc_58_4 : Nat → Nat := unpackHintV5 0xeb8aa0e13296d7f250cf0a3abf83e2b6ea26b11176a5cad29e59dc99c1269269d68be9a086b94c85f83083f8807bea046f5b2469298c6062325951c45239c64f18c841f34a390a3a32f1862e412c24b2641fb93e114b9c0c494001fa9400007e 0xa0707a070f81e0741d5541d075541d507542d555541d0b55662d5550713030307070303070307030fa03540d1b555071f0070700701c0f21411f0440306c0707170707001c8b0f2a144148c9c1100c03007c1f00c0c00c0303070707071384c3c4e130f070707071348c2c6d130b13231b130303030307030307030303030303030303030701c1303b3b0130bc2306c0300c0300c03030030300300c0cec0300c030300c0c00070700300c0e0781e80c0e80c0c1c1c1c1c6d1f0b1b47c2c3e83c0c0c0c0e80c0c0e030303a03030303030701c1f1f01f1f00f207c1b00c0300c0300c0c00c0c00c80300c0300c00307c0300c0e0781e83c3e13a2c1c1c1c1c1c1c1e81c1c1c1e81c0c0c0c1c1c1c1c4c4c4c4c3e83c3c3c3c3c1c0704c1303c80f03c1f06c0300c0300c032a00c0c03030f038b00c030000a0707a070f81e0707070f070707070707070707070f0f07070707070707070303030741c1c1d070b070707070fa0f0f43c2c3d0f0b030703030303030303030303030303a038ba0303a80c0c0c0c1c7c01c1c01c0703c80f0f00f1f01f06c0300c0307030307000c8b032a00c0c030030f032700300c0300c00307c0707070755555045530f2f8be530f555503030303030303035503030303030303030701c530bc44532b0532b00300c0307100c0c03033b1100c5c0c14400c0c0303000c3b020783c1cad0c1c1c1c1c1c1c1cacac1c1c1c1c3e83d55000c0c0c0c0c0070ac00070ac4100c1c07022c3b2b09c000001e07070781c3c1c1c1c1d550741d55075507541d5950f55555555540c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0d40d5540e2c1c01c1c01c0702f105048c500c0c0300c1c0c0c1c00322c0c03033b140c9c1441100c0c0303000c3b00c0c0004e130f1384c3c1c1c1c1c4d130b1344c2c1c1c1c1c4c4c4c4c0c4c0c0c1c0c03030303030303030303000000000000000000000130000000020f83d0741d51f47d52b4ad90f5550303030340d5038b01c1c3f10ac0000000ed09c00000000070707071f87c3c7e1f0f070707072b47c2c7d230b1f232f1f070307032b03031f03031f032f032303030007007000000000000000000000001c1c0000781c02801c1c1c1c7d1f0b1f47c2c3e83c1c0c1c0c7c4c0c0c7c4c0c0c3e80c8c0c0c00000000000000000000000000001c4c4c1c1c1c1c1c1c1cfcfc1c1c1c1e0783e010742d0b42c0c0c0c0c3c0c3c0c000001c07022c00811f54e2cac2701c1c3d0754d7b43e2cfc8b2b22c27270020781e83c3e1fa2c1c1c1c1c1c1c1e81c1c1c1e81c0070707071f1f1f1f0fa0f0f0f0f0f070307031f031f030fa030f030f0323033f0300000080003c8b000000a0707a070f81e0707070f070707070707070707070f0f0707070707070707001d07070741c2c1c1c1c1c3e83c3d0f0b0f43c2c1c4c0c0c1c1c0c0c1c0c1c0c3e80c3c3c0c0c3c0c0c8c0c0c07000000008b20200000070070022c0200000f09c000000001c1c1c1d515540007c3cbe2f87c3d40001c0c1c0c6c0c6c0d546c4c0c0c6c4c0c0c0000000000000700005300000000000000781c1c1e070f070707075541d075541d541d50756543d555555540071b030307070303070307031b031b0346d550346d5400000000410022c00070070022c00000000000000707000070707071384c3c4e130f070707071344c2c4d130b1313131300c0c0c0c4c0c0c0c0c0c0c0c0c0c00130000000000000004c00000007070707070707071b231b1f03030300c0c0c0c0c0c0c0c1c1c0007c3cbe2f87c3c8c2c6d1b48c2c0c0c00000000000000000000000000000020783d555544c1c1d2d00548e2c01022c00c0701c08b0ed00000781c1c1e070f070707070741c1c1d070b070707071b231b1f070713070707070707070707075707070707070707071f0f2f8ae1f0f230b1b46d230b030303030303030303030303030303030303030303000000000000030030022c070070022c00ec00000000000001e07070781c3c1c1c1c1c1d07070741c2c1c1c1c1c8cbc8c1c0c0c1c1c0c0c1c0c1c0c0cbc0c8c0c0c1c01c1c01c0702f08c00c01c1c5c1c1c00722c9c372708c2300c0300dc05c1c1c5c5c1c1c5c8c8c8c8c0c0c0c0c0c0c0c0c0c0c0c0c00000000000722c000000001700f02002c04003000c0000000b020f83c5c1c1c3cac3cbc3c3c3cac3cac3c3c3c011544c0c4c0c3c0c6c0c5c40010008b8842d81e0f543d943c5c1c1c1c1c3c3d5543c3d43cbd54041d8b55555555545c0c1c0d50344d43e80c3c3c0c0c3c6c0c0d545c0714100f203c3c03cbc1100c1b05c07141230222e82a440300c0003020f83c5c1c1c3cac3cbc3c3c3cac3cac3c3c3c10b42d0b42c00c030303031704c0000c0022e200c0c0e0783e83c3e83c3c3c5c1c1c1c1c3c3c3c4c3c5c3c3c3c3c3c4c3cbc3c3c3c3c0170707171344c2c4d130b0fa0f0f43c2c3d0f0b0303038b0307030303070303a030303030303030303030303031701c131301300f203c3c03cbc08c1b00c0300c0300c0c00c0c088ba0a80c0300c030005c1c1c3c05c1c1c5c3e83c3c3c3c3cacac3cacbc3c3c3d55000c0c0c0c0c02b03c004100c22e20020f83c3c5c3c1c3c1c3c3c0541d51756543d550f4bd550f43d5555555550303030303a030303030303030303503555038b0dc0f203c3c03cbc105048c500c0c031300c03088ba0a940c9c1441100c0c03030003e170f2f0f47d174bd0f8b8b2b22c9c 24 16777215 10 1023
def hc_58_5 : Nat → Nat := unpackHintV5 0x7bf1c63c107a1c36748db31a0673599322c5b97e24d0b9696a596cd22980cd933762493f17247dc8721fa7d107821477e2f8390cb91a06a00c572b0544b9c27a4a01110b087e62883d607418a9820a129084d30d823b0ba0b51a2036e8e80ed3280001da 0x5c1c1c5c5e170f1785c3c5c1c1c5c5d170b1745c2c6d3c6c7c5c5c1c1cac1c1c1c5c5c5c5c5c5c4c5c5c1c0c0c1c1c1c1c0c0c0c0c7c3cae2b87c3cac2c6d1b4ac2c5c0c1c0c5c4c0c5c0c0c5c5c4c0c0c7c0cfc0c6c0cfc6d3c0c0022c07001c000000c00c008b00000000000000000003001c1c1c1c4c4c4c4c1c1c1c1c4d131344c4c4c4c4c0707078b070707130001c1c04c3c4c4c4c3c4c2c4c4c4c2c00022c130000000c0000000000000001e07070781c3c1c1c1c1c1d07070741c2c1c1c1c1c6d3c6c7c1c1c4c5c0c0c0c0c1c1c1c1c1c1c0c0c1c1c1c1c1c1c1c1c1c1cac5c7c3cae2b87c3cac2c6d1b4ac2c1c1c4c0c0c1c1c0c1c0c0c1c0c1c0c7c0cfc0c6c0cfc6d3c0c001c01c008b002b0006c00c00c008b00000000000000000001313131383e0f801b1f1b331344c4d130fa0f131313130f0f00003c3e1303c3c3e2c4c4c4c4c00130008b000000c00000000000083e0f0f170f070f070f0f006c7c6ccc3e83c3d0f0b0f43c2c4c4c4c1c4c1c4c5c3c3e84ea0f0f0f0f0f0f0f0f0f80eaa03030303130b1344d130b130313030fa030f0f030f03030f0f130303130333131303000008b202000030030022c000000000000000002a84c4c4c4e006c7c6c7ea84d131344c4c4c4c4c4c5caa2ea13002804c4c4c4c0000022c1300000c000000000000a81ea17aa006c7c6cce6a60baa13171f0713072b17a0f0faaaaa0303aaaaa2b0f130b1b44d2b0b13031303a13aaa0303aa13033f134f030000ac208008b001b0030030000000000000000000003313331355550b0b0b0b0b0b0b0b50b132b132b1313131350001540303038b000010008b10030000040000000004c4c4c4c4c4c4c4c4c4c4c4d0b42d0b42d4004c4c4c4c4c4c4c4c2c2c0000b0b44c0b0b0b8b000004c0022c000300000000000000cccccccd0b42d0b42c2c5c2c1c2c1c2c2c2c3c2e0b82c2c02b172b072b072b172b0f2b8ae2b0f0b0b51b542c2c2c2c2c2c2c2c2d035540c0c0c0c6c0c6c0c6c0c6c0c2c2d546c0c2c2c0c2c0c0c2c2c4c0c0c00000022c40400c00c008b0000000000000000002f132f131b231b2313231b13132b2b37132b2b57132b132f132b135713231b1b131b23232b1727072b072717130f278ae130f230b1b46d230b000303030303030303030303034b030000000000000300000030022c000033000004c27004c000300020707a2e81c1d0b42c5c1c1c5c3e83c3c3c3c3c9c9c3c9cac3c3c3c2d42c0c0c0c0c0c4c000000003c2709c1300302f132f1355555555549c9c9c9c4c9c9c4d4015140000000000000000400400130000bcdcbc6c8c6c8c6c8c6c8c9c5c9c1c9c1c9c5c9c3c9e2789c3c8c2c6d1b48c2c0c0c0c0c0c0c0c0c0c0c0c0c0c00000000000000000000270009c000300008c5c4c1c1c0fa0f0b50b03030313013130fa0f0b50b131737030000c00004c4c00131313131b231b23131313131313130713071317130f1384e130f130b1344d130b1313133713131313131313131313131313131b1313132300030303030303030303030303130300000000000300c030030022c00004c0004c04c2700000001b1b1b1b170707170fa0f0b1b46d0b47034703470347031b03471b0300001b00c0c0c0c0c00322c001b0000c03000081e0fa0f0fa0f0f45d507545d175545d375542d555555662d5551703070317130303171303030fa03540d1b5551701c17170173700f21415b0440306c01c8b070700707070f2144148c9c1100c0300020f83c5c1c1c5c5c5c5c5c7c7c5c7cac5c5c5c0c042d0b42d0b0303030308000f03c00c22c1c0707c1f000081e0fa0f0fa0f0f0f17070707070f0f0f170f170f0f0f0f0f170f370f0f0f0f030303170707171745c2c5d170b0fa0f0f43c2c3d0f0b030303030303030303030303a038ba0303a80c0c0c0c5c0705c5c05cdc03c80f0f00f02306c0300c00c8b0307003070303200c0c00c0c00c0300c0300020f83c5c1c1c5c5c5c5c5cacac5cacdc5c5c5c3e83d55000c0c0c0c0c017000ac4100c22c1c070000170707171785c3c5e170f541d5175545d375545d1756543d55555555503030303030303030303030303030303503555038b1701c17170173700bc41412314030300c00c8b030700307030300c50327051044030300c0c0001707071717131317373717131317171783e0f8042d0b42d0b030303030f030f030000008b0701c00170f370f4dd175ed0f8b8b2b22c9c020783e83c3e83c3c3c5c1c1c1c1c3c3c3c5c3c5c3c3c3c3c3c5c3cdc3c3c3c3c0170707171745c2c5d170b0fa0f0f43c2c3d0f0b1703070317130303171303030fa030f0f03030f0303230303000000022c8080000022c07001c000000000000005c1c1c5c5e170f1785c3d507545d55174dd551745d5950f55555555005c0c1c0c5c5c0c0c5c6c0c0c6c0c6c0d1b5540d1b5500000000104008b00022c07001c00109c00000000004cdc4c5c3cac5c3cdc3e8b8b09c20f83d555544cdc4c5d00548e2c01022c00c08b0701c40005c1c1c5c5e170f1785c3c5c1c1c5c5d170b1745c2c6c8c6c8c5c5c1c1c1c1c5c5c5c5c4c5c5c5cdcdc5c5c4cdc5c5c5c5cac3cbe2b83c8c2c6d1b48c2c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0000000000000c00c008b022c07001c000000000000005c1c1c5c5e170f1785c3c5c1c1c5c5d170b1745c2c8cbc8c5c0c1c0c5c5c0c0c5cdc0c0c0cbc0c8c0c0c5c0705c5c05cdc02f08c00c00722c1c1c01c1c1c9c2708c2300c030001c1c1c1c1c1c1c1c8c8c8c8c0c0c0c0c0c0c0c0c0c0c0c0c000000000722c0000bc000000001c03c0800b01000c003000000141160781e81c1e82c2d555555541c0c1c0c6c4c0c0c6c4c0c0c3e80d541c0707c7c07c7c03c8440306c0707101c5c5c5c14403ca8440300c01f07c 25 33554431 10 1023
def hc_58_6 : Nat → Nat := unpackHintV5 0x90910f45e898212a728ff2a8a7871c939f2919b097c0cde29a5fcdc92e4668160048ca0c3d04de0a024ae9090bc66c7e79da39d15b1c362c8d9e1f46529f22d9d3e154c6089bd3a4441a741ae9c90a32d083587041798ca09fc7403047e80e22800001c4 0x20f83d0b42d90b13131313683e550b1313071307130f0f84e0f0f0f8b0b0b50b0b0b0b00b0b0b01f07c0f202c4131300b04c8b0303032307c0f202c41304c132304c4c0083e0f42d0b642c7c7c7c7d20f842c4c4c1c4c1c4c3c3e1383c3c3c3c2c2d42c2c2c2c0c0c2c2c2c0c0c4c0c4c0c3e80c2d540c4c4c0c0c2c0c6c0e2c02307c0f202c41f08c132304c4c0300c83e0f42d0b5a662c2c5c2c1c2c1c2c2d5a84c4c4c1c4c1c4c5c3c3e84ea0f0f0f0f0b0b550b0b0b0b0b0b0b0b130b0b130b0b0b0b130313030fa030b55030b0b030b03030b0b130303007c1f03c80b102c2c0b00b0b2b00303030303000c8b2307c0f202c40b0b00b23013230131300300c000301c5c4c1c1c4c4c4c4c4c5c1c1c5c6cac6cac4c4c4c4c4c4c1c4c1c4c5c4c5c4c4c0c070013131313131313131303070313130301c08b13031303130333131303005c070ac2b04c130ac1b04c1300c0304c5c4c4c1c1c4c4e130f1384c3c5c1c1c5c4d130b1344c2c4c4c4c4c1c1c4c1c1c4c5c4c5c1c1c1c1c4c4c4c4c4c4c4c4c4c4c4c6c4c4c4ccc4c0c1c0c4c4c4c4c0c4c0c4c0ccc4c4c0c01701c13132b1304c2b06c0303030303000c8b1701c13130132b01304c2b06c132b0131300300c001313131313130b13130b131313131313131303130313038b138b0307130707070707070707070301c0c4c4cac4c130ac1b00e2c8b0722e2e2c0c0704c1304c130ac1b00c0301c070001c1c1c1c1c1c1c1c1ccc4ccc6c4c1c1c4c1c1c1c1c1c1c4c7c4d5c4c4c7c4d9c6c6c4c6ccd5c1c4c0c1c1c0c4c0c4c0c4c0d1c4d9c0c0070707070f0781e0707070b0741d070707170717030300700c0c1cac070704c1f0ac1b00c0c0c0c0c00322c0c0c01c0c01c0704c370cc1b0acdc04cdc00c0301c1c01cdc0000c070713131313070707071b1f1b2b0707070713131313070007070301c1c1c1e2c1c1c1c4c4c4c4c4c4c4c4c4c4ccc1c08b13130301c0c1c0c4c0c4c0c4c0ccc4c4c0c02b07c0701c1304c2b06c1304c0300c0707070781c1c1e070f070707070741c1c1d070b07070707131313130707131707070707070707071313131313131313131313131b131313330707130703070313031303130333131303001c1cac1c0704c130ac1b00c0c0c0c0c00322c1cac01c1c01c0704c130ac1b04cac04c4c00c030004c4c4c4c6ccc6ccc4c4c4c4c1c0c4c0c4c0c4c0c4c0e2c4e2c0c1c1704c130ac1b00e2c8b0722e2e2cac2b04c130ac1b00c030001c1c1c1c1c1c1c1c1c2c4c4c4c4c1c1c4c4c0c4c0c4c0e2c4e2c0c1c1c5c4c4c4c4c5c5c5c5c0c070307072b1304c2b06c030322c1c038b8b0301c0701c1304c2b06c0300c1705c001707071317073307171713331b131317131707070707131313531353135713671b1b131b335713130307130313031303130347136703004c4c4c4c3c5e1784c3c5c2c5d1745c2c1c1c1c1c0c0c04c0303171701cac130ac2b06c0303030303000c8b03030170301701c1303306c2b5701300300c17170173b0001707070f0f0f1f1742d0b13130f13331313130fa0f0f170b50b03003171f0f1f00300c0f0ac170ac83e0f1f1f1f1f0320f1b1f1b330fa0f1b2b1b1f131313130f0f84e0f0f0f0f0f0f0320013131313130313030fa031313032022c4c0ccc4c4c0c02b07c0f207c2b0ac1b04c1300c0320f83c3c5c3c1c3c1c3c3c3c3c3c6c7c6ccc3e83c3d0f0b0f43c2c4c4c4c7c4c4c4e84e83c3c3c3ea84c4c4c6c4c4c4ccc4c0c4c0c3e80c3c3c4c4c0ccc4c4c0c01f07c0f203c3cacac1b00c0c0c0c0c00322cac1f03c80f0f00f2b02b06c132b0131300300c000f0f0f0f1b1f1b330f0f0b0f0f0b130313030f0f1313038b138b03aa83eaa8a1f07c0f0f2b2b06c038b22e22e2e2e20ac1f03c0f0ac1b00c0322002a86ccc6cceaa131313135713131353a13aaa1313131b131313331303130384ea84c0ccc4c4c0c084ea07aaa0b99a83e0f80c228ac2b213282b06c0303030303000c8ba080c0bc2f220bc1b04cbc04c4c00c032821300081eaa81ccd0b42c4c1c4c0c1c0ccc4c7c1c7c0709c2720781e81ccd90b130784ccc4c1c1e07aa0b507030031f0787c0c030ac8070ac2b2b2b2baa8a1b331b331b2b1b2baa1313131380280caa8ba84c4c4c4c4c4ccc4c0c4c0e022c4c4c0caa13033313130300ac2b0ac2b220ac1b04c1300c032a07a85eaaa1b331b339a982ea84c4c4c4c4c4d4e83c3eaaa84c4c4c4c6c4c4c4ccc4c0c4c0e84ea84c0ccc4c4c0c02b0aca2b882b06c0303030303000c8b2b0ac8ac28220ac1b04cac04c4c00c030004c4c4c4c6c7c6ccc4c4c4c4c4c0c4c0e83e13038b138b031f07c80f0ac1b00e2c8b88b8b8b2b07c1304c2b06c0300c00aa1b1f1b33aa82c4c0c4c0e84c4c0e2c4e2c0c3c3c3c3e83c3c3c3c3e287c1f28acac1b00c0c8b8038b8b0320ac1f220ac1b00c0303c0f0f0f0020f83c6c7c6ccc3e83c4c4c4c7c4c4c4d5c3c3ea83c3c4c4c4c6c4c4c4ccc4c0c4c0c3e80c4c0ccc4c4c0c0271f1f3b0f20f271b1b33a01313133b813031f07c0f20ac1b00c0c0c0c0c00322c0c2720f83c6c7c6ccc3e3383c3c4c4c4c7c4c4c4d5c3c3c3c3ea84c4c4c4c6c4c4c4ccc4c0c4c0c3c3e84c0c4c0ccc4c4c0c00f170f070f070f0f0f0f0f0f0b0f43d0f0baaa00f00c0c7c1f03c3c8ac2b06c0303030303000c8b030300f03007c0f20cc1b04d5c04c4c00c0303c3c0f00f0f3b0001313131342d0b42d0b0b170b070b070b0b0b0f0b82e0b0b0b0b0b131313671313136713131313131313135131b50b0b0b0b5513031303130313030b55030b0b1300ac2b04c1302c40b0b1b1b0303030303000c8b2308c1304c0b102c2c02c8c04c8c04c4c00c03000cc4ccc4d0b42d0b42c4ccccd5c4ccccd5c4ccc4ccc4ccc4ccc2c2c2c2d544c6c4c0c4c0c4c0c4c0c2c2d544c0c00b170b070b070b0b0b0f0b82e0b0b0b0b0b555500b02c03032b0ac130ac0b0b11b00c0c0c0c0c00322c0c0c02c0c08c2304c2302c423230132300300c0b0b00b230000f81e8baa55555584c4e4415138b82b1122ccd030382f14bc4e07aa07a2d555590b584c4ea13674415138b2b21122ccd03032f214bc4c4c4c4c4d55544e2c4d5c4c4c4e2c4c4c4e2c4e2c4c4d48b62d42c2c2c2c2c2c2c2d42d52b0ac1304c5110303030303142308c1304c511138b0138b00b02c00131355555555544d9c4d9c4c4c4c4d415055562d3c4f04c4f141122d140303030130511444b04c0003004c4c4c4c4c1c1c4c4d131344c5c1c1c5c4c4c4c4c4c4c0001313071304c5c4e2c4c4c4c4c4c4c4c4c130008b00000000c000000000000 25 33554431 10 1023
def hc_58_7 : Nat → Nat := unpackHintV5 0x91851a477c51a2d13b50f11de82554d3eea901e68434e4b3a46e74f9354c7b9959534c18a505c71152c128994cf4e89c7a80468dec2106900f6d45872025a3161e81670900a2245847da4e1ecd480b84f884ed3542081ba0cc4df03dca180f23f00001e4 0x20f83d0b42d6998b0b170b070b070b0b56a130313030fa030b5030b0b03030b13030300000000002c000c8b0005c007003c0800b01002c0b0002c0004c000000000000000000006c6c6c6d1c0d1c0d1c0d1c0c6c0c6c0c0000000322c0017001c00f02002c040470000000000000000aa17070717aa13030703aa13031303170f070707070f0faaaa1f0b1b46d1f0ba08a1701c881f06c03200c0c2805c07220bc1b00c0307c7c07c9c0003c3c1c1c1c1c4c3eaaaaa85c1c1c5c4d130b1344c2ea84c0c1c0c4c4c4ea84c0c4c0c5c0704c4c7e207c1b00c81701c1327013130882b06c0300c0083e81e8baaa85c1c1c5e60b9aaa1317070707071717aaa57a13aaaaaa130b1b44d330b13030703a80e13aaa1303471303005c072822b0883306c0303030303000c8b1701ca08bc220bc1b0bcbc04cbc00c030020781c1c1c1c1c3e83c1c0c1c0c3e80c4c0c4c0c1c1e81e07070f0faa0f0f130b1344d130b030300700c0c1c0703c83306c0301c03030070300701c0f20cc1b00c0304c9c04c4c0020781c1c1c1ea07070f0faa0f0f070707070fa0f1344c2c4d130b070307030fa03131313130313030701c0f204c4cacac1b00c0701c0703c813270131302b06c0300c0081e8ba0707a81c3c1c1c1c1c1c3e83c1d070b0741c1c1c1c1c1c1c1c1c1c3c3ea83c3c1c1c1c1c1c1c4c1c1c4c1c1c1c1c4c2c4d1344c2c1c0c1c0c3e80c1c1c0c0c1c4c0c0c4c0ccc4c4c0c00701c0f201c1c01cac0cc1b00c0c0c0c0c00322c1c0703c807070073703306c13370131300300c000707070707070707aaaaaa1344c2c4d130b07070707aa13131307030703aa13033313130313132b0701c882b06c030804c4c04c9c01c07220ac1b00c03002a81c1c1c1ea81c0c1c0ea84c0d1c4d9c0c1c1c1c1c1c1c1c1eaaa8cc2c6d1b4cc2e82281c07220cc1b00c2003030a00701c882f06c0300c2f2702f27000a07aaaa07a2e6a60b07070707aaa13aaaaa570707070707070707aaaa130b1b44d330b84eaa0307030703aa1303471303022b0a00701c883306c0303030303000c8b8bc2801c07220bc1b0bcbc04cbc00c030020783c5c1c1c5c3e83c4c0c1c0c3e80c4c0ccc4c4c0c4e07070707a0f07aa0707130b1344d130b030300f00c0c5c0703c83306c0303c030300f0301701c0f20cc1b00c0304c9c04c4c0020783e81c1c1c1c4e0707aa0f07170707170fa0f1344c2c4d130b130307030fa031313131303331313031701c0f204c4cacac1b00c0f05c0703c813270131302b06c0300c0081e0f80c1c4c1e83c5c1c1c5c3e83c4d131344c4c4c1c1c4c5c3c3e83c3c3c3c03c3c3c04c4d1344c5c0703c8131300f04c8b3306c0303031701c0f204c130cc1b04c130020783e01c5c1c83c5c1c1c5c3e83c6cac6c7c4c4c1c1c4c5c3c3e83c3c3c3c0c0c3c3c3c0c0c4c4d1344c4c0c1c0c3e80c4c4c0c0c3c0c7c0e2c4c0ccc4c4c0c01701c0f207c2b0ac1b04c1300c0320783e01c5c1c83c5c1c1c5c3e83c6c9c6ccc4c4c1c1c1c1c4c5c3c3ea83c3c4c4c4c9c4c4c4cec4c2c4d1344c2c4c0c1c0c3e80c4c0c4c0c4c0ccc4c4c0c01701c0f20ec270cc1b00c0c0c0c0c00322e81c1e07a2ea070707170707170fa0f0f43c2c3d0f0b13130707070713170f0faa0f0f0f0f0f0f0f0f130f0f130f0f0f0f130b1344d130b130307030fa030f0f030f03030f0f130303130333131303005c0703c80f0f03c03c3cac0cc1b00c0c0c0c0c00322c5c0703c80f0f03c03c3cec0cc1b04c04c4c00c030001c1c1c1d0741d0b42c1c0c1c0c6c0c6c0c2d40c1c1d41d07071f0f338ce1f0f0b0b550b0b030300700c0c1c0707c1f02c40301c03030070300701c1f08c0b100c0308c8c08c8c0001c1c1c1d0741d0b42c1c1c1d07541c1c4c4c3c4e1384c3c2c2d542c2c1c0c1c0c4c0c4c0c2d40c4c4c4c1c0704c1302c413132b0301c0701c1304c0b104c8c04c4c00c030001c1c1c1d0741d0b42c1c1d03131313130b550b070707078b07070713130f1313130f0b0b50b0b0707007070700701c1304c0b104c4c01c1322c0c0c0c1c0704c1302c41304c132304c4c000707070741d8b5070742d0b541c3c1e0781c1c1c2c1c1c1c1c1c1c1c1c1c1c1ccc5c7c3cce3387c3c2c2d542c2c1c1c1c1c1c1ccc1c1c4c1c1c1c1c1c0c1c0c6c0c6c0c2d540c1c1c0c1c0c0c1c1c4c0c0c00701c1f07c0b101c1c01cac00c0c0c0c0c00322c1c0707c2302c4070700723023230232300300c001707071741d0b42d0b170307031b031b030b5031741c1c1c1d4cc3cce338cc3c2c1d541c1c0c0c02c03031701c330cc0b100c0b00c0c02c0c05c0708c2302c40300c2323023230001307071341d0b42d0b507071307071344d130f1384e130f0707550b0713030703130313030b5031313131701c1304c0b104c4cac0c0b05c0704c1302c413230131300300c001307071341d0b42d0b40c1c4c4c4c4c4c1d542c4c4c1c4c1c4c5c4e2c4c4e1384c2c2d42c2c2c2c02c2c2c05c0704c1302c4131300b04c8b0303031701c1304c0b104c1304c8c13130005c1c1c5d0742d0b42d01c5cacacacac1c42c5c5c1cac1c5c5c5c5cacae2b8ac2c2d42c2c2c2c0c0c2c2c2c0c0c5c0c1c0c6c0c6c0c2d540c6cac0c0c2c0c6c0e2c01701c2308c0b108c2308c8c232300c0305c1c1c5d41c1d0762d0b42d50b0f0b82e0b0b070707171707073307070717171717330f338ce330f0b0b550b0b0b0b0b0b0b0b330b0b130b0b0b0b170307031b031b030b55030b0b030b03030b0b130303005c070cc3302c40b0b02c02c2cac00c0c0c0c0c00322c5c0708c2302c40b0b00b23023230232300300c00aa42d0b6613031303aa0b5033317330733073317a59a0b0b550b0ba08a4f13c880b100c803030a02308c880b100c0308c8c08c8c002a90b42d984c4c4c1c4c1c4c5ea65684c2c2d542c2c4c0c4c0ea82d40c4c4c4cac2b2202c413132b03208c232202c413230131300300c00aa42d0b6613131313a60b550b131313131317aa8ba84c2c2d42c2e82a04310c880b104c4c204c8b0303032308c880b104c1304c8c1313002a90b42d98b5a85ea07a560b84c5ccc1c4c1ccc5eaaaa8cc3c2c2d542c2eaa8ce84ea84c0c4c0ea82d540ea80c0e84e804f13c880b12822b00303030303000c8b2308c880b128223023230132300300c0083e0f42d0b642c4c0c4c0c3e80c2d40c4c4c4c1c4c1c4c5c3daa50b95680c0c02c03031f07c0f202c40302c030300b0302307c0f202c40300c13230131300083e0f42d0b642c4c4c4c1c4c1c4c5d684e83d0f69542e130313030fa030b5031313131f07c0f202c413132b0302c2307c0f202c413230131300300c00 25 33554431 10 1023
def hc_58_8 : Nat → Nat := unpackHintV5 0xbd29b4b8f10eb1f1c0ab21b4a51184a081249d50cc98a92a94f0ee8eb1908c908887f92682895c7b51ce74d99e6b7a5866e92461795c5a11da5441744db9a247419e3d827036f9a22d9a5827b9782131a217a2641251540b79b606115a000184 0x1c1c1c1d0741d0b42c1c1c4e2c1c1c1c1c4c4c4c4c2d42c1c1c1c1c3c1e0781c1c1c2d541c1c1c5c1c0000000000000000000000000001c0131313130707070741d0b41d0742d0b13001c1c07131313130b50b00000000000707070781c1c1e070f07070707507075070b41d0742d0b070713070707070707138b131313130b50b01c0000000000000000000000000001707071341d0b42d0b131307070707138b131313130b50b131313130f1785e130f0b0b550b0b07070700000000000000000000000000083e0f0f170f070f070f0f0f0f0f42d0b642d42c2d42c2c4c4c4c4e84e2e83c3ea0b50b000000000000000000000000000aa42d0b6613131313a138baa0b50b84ea07aaa0b55a83e000000000000000000000000000431f1f2baa8042d0b642d984c4c4c4c3c0a20b50b0000000000a81ea17aaa90b42d6960b6613131313a0faaa138b0b50b002000000000000000000000000020f83d0b42d90b131313130fa02d42c7c7c7c7c3c00b50b800000000000083e0f42d0b642c4c4c4c4c3c3ea84e2c2d42c3c5c3c1c3c1c3c3c3c3c3c2c2d542c2ea00000000000000000000000003c00042d0b42d0b0b50b000000000000000000042d0b42d0b1b1b1b1b0b50b000000122c0017001c00f02002c00c4700000000000000000003c3c000a802805c1c1c5c6d1f0b1b47c2ea84c0c1c0ea84c4eaa84c0c4c0c000000000000000000000000020fa07a2eaaa17070717982e6aa84c0c1c0ea0384eaa84c0c4c0c00000000000322c0017001c08800800202002c0404700000000000000000000881c02803c3c0001c1c1c1c3e83c4d130b1344c2c1c0c1c0c3e80c1c1c0c0c4c4c0c0c4c0c4c0c0000000000000000000000000207a2e81c1ea070f07070707070fa0f0741c2c1d0707070307030fa03070703030713030313031303000000000000c8b0001c007003c0800701c00070000b01004c000000000000000000001c0c1c1eaa884c4c4c4c1c1c1c1ea8001322c00000000220001c0080040000000000000001c1c0028002886d1f0b1b47c2c1c1c1c1ea84c4eaa81c0c1c0ea84c0c4c0c0000000000000000000000000281eaaa81e8b9a982c1c1c1c1eaa84eaa80c0c1c0c1c0ea84c0c4c0c00000000000322c00800220001c0070202002c040470000000000000000000081e2001c0170707170fa0f1b1f1b1f130307030fa030f03031303031303130305c000f0007c00404c00000000000081e280001c1c0005c1c1c5c3e83c4d130b1344c2c4c0c1c0c3e80c3c3c0c0c4c4c0c0c4c0c4c0c0000000000000000000000000020788007005c1c1c5c3e83c6c9c6ccc4c0c1c0c3e80c4c0c4c0c4c0c4c0c000000000322c0017001c00f0200ec027002c0401300a070781e8ba81c1c1c5c1c1c5c3e83c3d0f0b0f43c2c4c0c1c0c3e80c3c3c0c0c3c4c0c0c4c0c4c0c00000000f00000322c0017001c00f02003c0f0003c0002c0401300000000003c0000000000007070707441d0b42c01407c3c7e1f87c3c2c2c0001c0c1c0c6c0c6c0c2d40c1c1c0c0c6c4c0c0c0000000000000000000000000001c1c1c1d0762d41c1d0b42d5070f0781e0707070b07070307031b031b030b5030707030307130303000000000000c8b0001c007003c0800b01001c070001c0006c000000000000000000005c1c1c5d07442d0b401f332b1f07005c0c1c0c6c0c6c0c2d40c2c0c0c6c0c0c170000802c003f01b000000000000005c1c1c5d07442d0b50001f0f338ce1f0f0707000170307031b031b030b5030b0b03031b130303000000000000000000000000000170707175070741d8b42d0b542c3c2e0b82c2c1c1c1c5c0c1c0c6c0c6c0c2d40c2c2c0c0c2c4c0c0c0000000000b000322c0017001c00f02002c0400b02c000b0001b00000000000000000000aa42d0b4633171f071f07331700500b0b00013031303aa0b503aa1313a000000000000000000000000000aa42d0b662d6a17a81e9582e13031303aa0b503a80e13a000000000000c8b0005c0070202002c040880080006c000000000000000000020f83d0b42d907c7c7c7d02004c0c4c0c3e80c2d40c2c0c0c4c0c0c001c03c000b0007c04c000000000000083e0f42d0b6413171307130713135000a000130313030fa030b5030b0b030313130303000000000000000000000000000 24 16777215 10 1023
def hc_58_9 : Nat → Nat := unpackHintV5 0xcae15ac3a9cebdc978b4aa48af6950a7c1eaa141a09b4180922a468b71ae81ca6a7c41627589ae6bb27665b97e5cd23a58691a52e9604bc9c846c1424181503a69c63309d82cb19627a9422031de1ba12415918410c9320d10ee06d1900001b4 0x3c3c00081ea00a041d0b50b0b5a66170707171f131b031f131b03aa0b50b0000000000000000000000000083e81e8baaa90742d60b5a6617070717a80e1faaa0b50b0000000000122c001705c00701c08800800202002c00c47000000000000000000000028a0700a00f0f00041d07642d42c2d41c1c1c1c1c1c3e83c7c4c6c0c7c4c6c0c2d42c0000000000000000000000000207a2e81c1ea070f0741d07642d41c2d41c1c1c1c1c1c3e83c1c1c1c0c1ccc1c0c2d42c000000000048b0001c007003c0f022001c070001c0002c00c47004c0000000000000000000001c1c0028002896942c2d0741d987c4c6c0c7c4c6c0c1c1c1c1ea82d42c0000000000000000000000000281eaaa81e8b65a5a0b0b41d07668ceaa0307070707aa0b50b0000000000122c00800220001c17001c070203c08800b00311c0000000000000000000000a070781e8b280001c1c0010742d90b50b0b50b0b170707170fa0f1f131b031f131b030b50b0000000000122c000000000000000081e2001c041d0b642d0b42c5c1c1c5c3e83ccc6c9c6c2d42c0000000048b0005c007003c08053009c00b0030ec013000a070781e8ba81c1c1d0742d90b50b0b50b0b170707170fa0f0f0f0f030f330f030b50b0000000000122c0017001c00f02003c0f0003c0002c00c47004c00000000000f0000000000000c0c0005c1c1c5cce1f0f3387c3d0742d42c2d42c2d0b42c030707070300007070701b031b030b50300000000000000000000000000030303170707171785c3c5e170f41d0b50b0b50b0b42d0b0307038b070703030707071b031b030b5030000000000122c0017001c01305c00170000f02002c00c03004c0000000000000000000000c01f1f1f1f0707070750750b41d0742d0b17001c0c031b031b030b50307c00070000b00013000000000000003030001f87c3c7e1f0f070707075070750b0b41d0742d0b171713000007070300c1c6c0c6c0c2d40c000000000000000000000000000c0c0c1e07070781c3c1c1c1c1d41c1d41c2d0741d0b42c1c1c5c1c1c0c0c0c1c0e2c6c0c6c0c2d40c070000000000048b0001c0001c070001c007003c0800b00300c01300000000000000000000083e0f1f171f071f071f17030300042d0b642d42c2d42c2c6c0c6c0caa03000a802d40c000000000000000000000000020f83c3c5c3c1c3c1c3c3c0c0c0d0b42d90b50b0b50b0b1b031b03a038ba0303a82d40c000000000048b0005c007003c0800f03c000f0000b00300c013000000000000000000000431f1f2baa8042d0b5942d986c0c6c0c3c0a20b5030010c00802c0004c0000000000000cc5c7c1c7c1ccc5eaa80010b42d6942c2d986c0c6c0c3c3c3c0002a282d40c00000000000000000000000002a07a85eaaa42d0b5a582d986c0c6c0e83eaa80e2c2d40c00800000000122c0017001c08002200202002c00c03004c0000000000000000000003e07a2ea90b613070717aa131f84c4eaaa0b50b13070717aa030384c4eaaa0b50b0000000000000081ea81e8b9660b0b84c4eaaa135707070707aa0b50b84c4eaaa030307070707aa0b50b00000000000000030303130707131384c3c4e130f41d0b50b0b50b0b42d0b01c1c4e2c1c1c4c4c0001c1c1c04c4c4c4c2d42c0000000000000000000000000000c0c0c1e07070781c3c1c1c1c1d41c1d41c2d0741d0b42c1c1c4c00001c1c1c1c0707138b131313130b50b01c00022c000000000000000000000020f83c3c5c3c1c3c1c3c3c0c0c0d0b42d90b50b0b50b0b13131313284e2e83c3c002a00b50b000000000000000000000000000a81ea17aaa90b42d6960b6613131313a0f0000aa284e2c2d42c00800022c0000000000000000000004c4d0b42d0b42c4c5d5c1c4c1d5c5c4c3c4e1384c3c2c2d542c2c4c0c6c4c0c6c4c0c6c4c0c6c2c2d540c2c0000000000000000000000000000000083e81e8baaa90742d60b5a6613070717a87e13aaa0b50b00000000000000000000000000081e8ba0707a81c3c1d0741d90b5070b50707070707070fa0f07070713071307070b50b000000000000000000000000000a07aaaa07a2d969682c2d0741d9a13aa95c1c1c1c1ea82d42c0000000000000000000000000020788007010742d90b42d0b130707130fa0f131313130b50b00000000000a070781e8ba81c1c1d0742d90b50b0b50b0b130707130fa0f0f0f0f130f130f0f0b50b0000000000000000000003c0000000131713130707131384c3c4e130f41d0b50b0b50b0b42d0b0707138b07071313070707131313130b50b000000000000000000000000000 24 16777215 10 1023
def hc_58_10 : Nat → Nat := unpackHintV5 0xca0238c301c0be512cb80992b3113eab49f2a6992ca019a09bc91496c14291b144898a0a8529187f29807761f27079ba66aa7460499858b9e451e9b44bc18a46994a4590423f39963492aa2b225c215274188a321129d80b996404b9b800012e 0xa81ea17aa010b42d969682c2d982c5c2c1c2c1c2c2e96a95682c2e82c3eaaa80331b1f1b8ceaa03aa0b0b53f0b0b0b0b030b3f0b0300208008b022c4040000000000000000000042d0b42d0b0b170b070b070b0b0b0f0b82e0b0b006c6c6c6c2c2d42c2c2c2c0c2c2c0c0048b50546c08c2308c2302c40b0b00b2301b08c000f0f0002a00a055555555170707171b131b031b131b03aa550000000000000000000000000083e81e8baaa9555555545c1c1c5ea0386eaa9540000000048b000005c0070220020008080400c01b00000000000000000000220700a00f0f00055555555070707070fa0f1b131b031b131b03550000000000000000000000000081e8ba0707a81c3c1d555555541c1c1c1c3e83c1c1c1c0c1c6c1c0d540000000048b000001c007003c0800701c0007000400c0130000000000000000000001c1c002800289555555546c4c6c0c6c4c6c0c1c1c1c1ea9540000000000000000000000000281eaaa81e8b5555642d55561baa80c1c1c1c1ea9540000000048b00002000880007001c08080400c01b00000000000000000000207880070155555545c1c1c5c3e83c6c6c6c6d54170003c001f0400130000000000002078a000070700055555555170707170fa0f1b131b031b131b035500000000000000000000000000081e2001c0555555170707170fa0f1b1b1b1b55000000122c000017001c00f02014c02701003004c00a070781e8ba81c1c1d555555545c1c1c5c3e83c3c3c3c0c3c6c3c0d5400000000f0048b000005c007003c0800f03c000f000400c01300000000000f00000000000155546c6c6c6c6c6c6c6d54000048b000005c007003c080400c01b00000000000000001a955555543c3d695541145c1c1c5ea9546c4c6c0c6c4c6c0c5c07221102c2c2806c1b05c07221107c7c07c9c06c1b0020fa07a2eaaa541d51755655599599590f55555555005c1c1c5ea0386eaa91b5540d1b551701ca08ac22142d4048b1b06c1701ca08bc2212f050441b06c0081d81c1d555569555543c3d41141c1c1c1c3e83d546c4c6c0c6c4c6c0c1c0703c8440b0b0070701b06c0701c0f2110dc9c0dc9c06c1b00207a2e81c1ea070f07541d50756543d55075550741d555555540070707070fa0f07070703071b070344d550346d541c0703c807070072b050b50122c6c1b01c0703c807070073704dc141106c1b002a607555550707555a55504507070707aa46d546c4c6c0c6c4c6c0c1c072210402c2c2806c1b01c0722110bc9c0bc9c06c1b00281eaaa81e8b55665565507541d595955555554086eaa0307070707aa46d550346d562b0a00701c8850b50122c6c1b22f0a00701c884bc141106c1b0020795555555a55507075045170707170fa0f46d546c4c6c0c6c4c6c0c5c0703c8440b0b00f0b01b06c1701c0f21120c9c20c9c06c1b002079807170720f5545d5543d0f5550f42d55555547d8b005c1c1c5c3e83c6c6c6c6d135546d545c0703c81f0ac44441b06c8007010745d990f43d52749d52754d5406c0c6c0c4d40c6d004408b1701c0f203c42701101106c1b0020f275342d0b0b62c81e601c5c1c83d507545d59950f43d527554d5555540170707170fa0f1b1b1b1b44d550346d545c0703c809c50b50122c6c1b281c1e07a2ea070707541d517566543d0f5543d5543d0f5555543d0b555005c1c1c5c3e83c3c3c3c0c3c6c3c0d135540d1b551701c0f203c3c0f00f0f2b050b50122c6c1b05c0703c80f0f03c03c3c1050441b06c00005c1c1c5c5e170f1785c3d50741d51745d550741d550b42d5950f55545d0b55555005c1c1c5c5c5c5c0c5c6c5c0c6c6c6c6d1b5540d1b55022c07001c00104008b00000000000000000000001e07070781c3c1c1c1c1d550741d550742d50741d50745d5950f555541d0b5555001c6c1c0c1c1c1c0c1c1c1c1c6c6c6c6d1b5540d1b5501c01c008b002b0410022c006c000000000000000000083e0f0f170f070f070f0f01507545d59950f43d5599550b42d555550f42d55401b1b1b1b0fa0f0f0f0f030f1b0f0344d550346d540008b2020410022c00000000000000000002a07a85ea80541d517556655642d599590f555555642d5401b1b1b1b86eaa03aa46d550346d5400ac208008b104008b001b000000000000000000020707a2e81c1c5c1c1c5c3e83c3c3c3c3c9c9c3c9cac3c3c3d54003c0c6c0c4c0c4c0c00005c2000f09c411b00bcdcbc9c5c9c1c9c1c9c5c9c3c9e2789c3d555400006c0c6c0c6c0c6c0c6c6c0c0c6c6c0c0d54000000000000270000270400406c00001507545d5950f5555006c6c6c6c6c6c6c6d1b5540d1b550050b50122c6c1b001050441b06c00 24 16777215 10 1023
def hc_58_11 : Nat → Nat := unpackHintV5 0x87a4c242984ea0fa14903591e7e40db3cbc991d623f0dd83646b2ce53332991893418bba23e56b1c829089412ae7588c325041692c1cf6ef8d774105e2b642b88e3140e6d88ca4f442e0dc1f70800dee72866823c2e793212dd18062ad1017b6680002f6 0x20f83d0b42d90b0b170b070b070b0b0b0faa0b0b030303130313030fa035038b50303540000000000000000000000000020f83d507545d5950f5555544c0c4c0c3e80d42d5540e2c0000000000000000004270000000000083e0f0fa0f3b3b0fa0f3b3b00000000000000000083e0f0fa0f47470fa0f47470000222c000017001c00f00b01000c00000000000000000003c3c1c1c1c1c2c2eaaaaa90742d4161985c1c1c5c7c4c6c0c7c4c6c0ea82d42c5c072414222106c1f05c0707c8c07c7c2202c41b08c0083e81e8baaa90742d60b5a660b17070707070b0baaa0b0ba0baaaaaa005c1c1c5ea038ceaa82c2d42c2c2c2c0c2c2c0c5c072822b088122d4151b0cc1701ca088c2202c40b0b00b2301b08c0081e07070707a81c1c3c3ea82c2d0741d90b5050701c1c1c1c3e83ccc4c6c0ccc4c6c0c2d42c1c0703c80741401c41b0cc0701c0f208c8c08c8c02c41b08c0081e8ba0707a81c3c1d0741d90b5070b5070707070707070707070b0faa0b0b0707070707070b0b07070b07070707001c1c1c1c3e83c1c1c1c0c1ccc1c0c2c2d4cc2c2c2c2c0c2c4c2c0c1c0703c807070072b0122d4151b0cc0701c0f201c1c01c8c02c40b0b00b2301b08c000707070707070707aaaaaa585041d076633131b0333131b0307070707aa0b0b55f0b50900701c888101b0cc23230232300701c880b106c2300281eaaa81e8b5a582d0741d9a82eaaaa82c2c1c1c1c1c1c1c1c1eaaa808ceaa0307070707aa0b0b50b0b0b0b030b0b038ac2801c0722048b50546c332230a00701c880b102c2c02c8c06c230020782e81c1c1c1c2e0707aa0b0741d0b642d4142c170707170fa0f33131b0333131b030b0b5330b1701c0f203d0500b1506c3305c0703c823230232300b106c230020782e01c5c1c83d0742d90b42d0b0b17070707070b0b0b0faa0b0b0b530b0b0b270b0b005c1c1c5c3e83ccc6c9c6c2c2d4cc2c2c2c2c0c2c4c2c0c5c0703c85b09c122d4151b0cca070781e8ba81c1c1d0742d90b50b0b0b0b43d42c2c2c5c1c1c1c1c2c2c2c3ea82c2c2c3c2c3c2c2c2c2c2c3c2c2c2c2c2c0170707170fa0f0f0f0f030f330f030b0b5330b0b0b0b030b130b031701c0f203c3c03cac048b50546c3305c0703c80f0f03c03c3c8c02c40b0b00b2301b08c000707030307070b03338cc3cce330f170707175050b10742d0b42c2c1c0c0c1c1c0c0c2c0c1c0c6c0c6c0c2c2d46c0c5d0501701c330cc0b100c1b08c8c08c8c05c0708c2302c40300c00030303170707171785c3c5e170f41d0b50b0b50b0b42d0b0b17070707070b0b0b130b170b0b0b0b0b170b0b0b0b0b0b0f0b82e0b0b000c1c0e2c1c1c0c0c1c1c1c6c0c6c0c2c2d46c0c2c2c0c0c2c4c0c0c5c0705c5c05cac0cc33048b50540c1b05c0705c5c05c8c08c2302c40b0b00b2300300c000707030307030707070707073387c3cce1f0f41d075071410b42c1c0c1c0c5c4c0c0c2c2c0c0c6c0c6c0c2c2d46c0c1c071401d01f07c07100c1b01c0708c8c08c8c07c2302c40300c000301c1c7c7c7c7c1c1c1c1d42c2d1b62c1d0741d0b42d41c1c1c1d41c1c1c1c1c1c1c2c2c2c2c01706c0c1c0c1c0c6c0c6c0c2c2d46c0c2c2c0c2c4c0c8c1f01c0707c2302c40b02c0300c0303030781c1c1e070f07070707507075070b41d0742d0b07070b070707070707070707070b0b07070707070707070b0f0b82e0b0b001c1c5c1c1c0c0c0c1c0e2c6c0c6c0c2c2d46c0c2c2c0c0c2c4c0c0c1c1cac01c1c0700701c1f07c122d4150306c07230070700701c1f08c0b102c2c02c8c00c03000cc5c7c1c7c1ccc5e0f83e80c0e82c0d0b42d4142c642c6c0c6c0c2e0303a03030ba030b0b51b031f07c0f41403c80b100c1b08c1f08c8c08c8c03c80b100c030020f83c3c5c3c1c3c1c3c3c0c0c0d0b42d90b50b0b50b0b0b170b070b070b0b0b0faa0b0b0b0f0b0f0b0b0b0b0b0f0b0b0b0b0b006c0c6c0e80e2e80c0ea0b0b51b030b0b03030b1303031f07c0f203c3c03cac048b50540c1b08c1f03c80f0f00f2300b102c2c02c8c00c03002a8cc5ccc1ccc1ccc5eaaa90b42d9961406c0c6c0ea83c3c0c0c2c2c0c0c2c2d46c0cfc3f2214242100c1b08c232208c8c08c8c02c40300c002b2b2b2baa8a42d0b50b0b46d8b9982c2c2c2d6a96aaa006c0c6c0c3c1b03aa0b0b51b030b0b030b13032308c2308c880b102c0b00c032a07a85eaaa42d0b5a582d982c5c2c1c2c1c2c2e82eaaaa82c2eaaa801b031b03a0faaa038b0b0b51b030b0b03030b1303033f0fca2b0a2088122d4150306c2308c88c282202c40b0b00b2300300c000f81e8baa55582c2e42e031390b0b030b038b82b0146cce08c51b2381ea81e8b5582d7ea0b0b42e1333a80c0d0b0b030b038b2b20146ccc8c851b23333355550b0b0b0b0b0b0b0b50b1b031b031b031b0350b0b0b03030b030b038b3f0fc330fc410540c6c1b08c2308c2314442c0b00c6c03230003e07a2ea84c1c1c5ea84c7e1313aaa90b64480c4e0b0b0b0b82b1106c4e08c2304c1b1381ea81e8b84c4eaaa133f07070707aa642d121313a80c0c2c2c2c2cac8441b1323208c1306c4c4c4c4c5cfc1c4c1cfc5c4c3c4e1384c3d0b42d0b42d4142c13031303130313030b0b0b0b0b5030b3f0fc130fc1b41402c4031b04c2308c1308c23230132300b100c6c03230000170707171785c3c5e170f41d0b50b0b0b0b45d42c2d0b42c2c5c2c5c1c1c1c1c2c1c2c2d541c1c1c1c2c1d42c2c2c2c2c3c2e0b82c2c01707071717171703173317031f1b3f1b0b0b53f0b0b0b0b030b3f0b03022c07001c00022c40406c0000000000000000000000781c1c1e070f0707070741d41c1d41c1c2c2d0741d0b42c1c1d41c1c1c1d541c1c2c2c1c1c2c5c1c1c1c1c1c1c1c1c2c3c2e0b82c2c00733070307070703070707071f1b3f1b0b0b53f0b0b0b0b030b3f0b0301c01c0000008b1010000000000000000000020f83c3c5c3c1c3c1c3c3c042d0b642d42c2c2c2d0f50b0b0b170b070b070b0b0b0f0b0faa0b82c2d56a82e50b0b0b0b00cc6c7c6c3e83c3c3c3c0c3ccc3c0c2c2d4cc2c2c2c2c0c2c4c2c0c0008b202008b10101b00000000000000000000 25 33554431 10 1023
def hc_58_12 : Nat → Nat := unpackHintV5 0xcd7a0ac43252baca5ab6591cb0f15aa999d6a3b9789a9a489559508d91f28711a07e2a3a77a1a26daa7e6761925d3a8a53ea544ef93c4969644620d24099623892023231982d71302649ca22b8e41e392018398013812e0d818006c1b00001b0 0xa81ea17aa01507545d5599559565655555555544c0c4c0e13aa80ea942d5540e2cfc3f283e8088b4ac1413f14031b04d3c2f0bc8bc282214bc1441100c6c032f0000a81e07a85e17aa81e07aa83e0faaa85e0faaa005c1c1c5c5d170b1745c2e6a60baa1707071717171703171f170387eaa03aa3f3f3f3f022c07001c208008b000000000000000000000002aa0781eaa0783ea0781ea0785eaaaa0783ea800741c1c1d070b070707079a982ea81cfc1c0c1c1c1c0c1c1c1c1e1faa80ea8fcfcfcfc0700700020800000ac002b0000000000000000002a07a85ea809a982ea91d1eaa80ea91d1c283e8088b04702f0bc8bc28220bc2f0bc2f0002c2c0020783d43c3d5441d5005055170707171b131b031b131b030fa0f550000000000000000000000000042d81e0f543d950762d5555517070717540d1350fa0f5500000000222c00001705c00701c0440040003c101000c01b0000000000000000000230020781d4507642c01403c3ea81c1c2c2c0001c1c1c1c3e83c2d42c7c4c6c0c7c4c6c0c000000000000000000000000020781d0762d41c1d90b541c3ea81c1c1c2c1c1c1c1c1c3e83c2d42c1c1c1c0c1c4c1c0c000088b0000000001c007003c02c0b011001c070001c0000c0330000000000000000000230001c1c0015543c3e0781d400145546c4c6c0c6c4c6c0c1c1c1c1c3e83d540000000000000000000000000141d695543c3e0781d55541d8b5544d5503070707070fa0f5500000000222c0000400110001c17001c07003c102c044003006c00000000000000000008c0081e0f5070741d8b190b50000f0faa0b0b0707000170707170fa0f0b50b33131b0333131b030000222c000000000000000000000081e0f5070741d8b642d50b0faa0b0b070707170707170fa0f0b50b0b0b0b030b130b030000222c0000000017001c00f00b01002c0b0002c0000c0330000000000000000000230000c0c0020783e83c3e83c3c5c1c1c5c4d130b1344c2c3e83c030707070300070700fa03130313030000000000000000000000000003030381e0fa0f0fa0f0f170707171344c2c4d130b0fa0f0307038b070703030707070fa031303130300000000222c00001705c00701c01305c00130000f00b01000c0130000000000000000000030000c0c00281c1e83c3e0781c4d130b1344c2c1c1c1c1c3e83c4c4c0001c0c030fa031303130300000000000000000000000000030303a0707a070f81e070741c1c1d070b070707070fa0f070713070703030307038b0fa031303130300000000222c0000070000701c000705c00701c00f00b01000c03004c0000000000000000000030020f83d0b42d90b0b170b070b070b0b0b0faa0b0b030303130313030fa035038b5030354000088b00000000005c007003c02c0b011002c0b0002c1b0000c0130000000000000000000030020f83d0cad0cada2b8ba0f0f555540130313030fa030b0144170003c10c0040013000000000000020f83c4c4c4c1c4c1c4c5d5543c3d555540004c0c4c0c3e80c2c2c0014400000000000000001309c00000000020f83d2d2d2d2c3e83d5555004c0c4c0c3e80c4c051000000000083e0f4b274b270fa0f555540130313030fa030b0144000088b00000005c007003c09c27012c0101000c0130020f83d507545d59950f43d55555130313030fa0350b555038b0000222c4000000000005c007003c1000440040b011000c03004c00000004000000000000000c0003030381c1e070f81e070741c1d07070707070fa0f070700001c1c1c1c0707138b0fa0f131313130000000000000000000000083e0f507555543d8b5555544c4c4c4c3e83d400055144e2c000040000000000000100000000083e0f1b331b330fa0f13175707130757170f0faa0f0f130b1b44d330b13034713030f0fa030f1303471303000000000000000000000000000020f83c8c8c8c8c3e83c0c0c0c0c0e80c0c0c0c0c0000000000000000010b60783d50f6541d8b5555545c1c1c5d50344d43e83d54000000000000000000000000020781d0762d41c1d90b541c3ea81c1c1c2c1c1c1c1c1c3e83c2d42c1c1c1c0c1c4c1c0c0000000000000000000000000141d695543c3e0781d55541d8b5544d5503070707070fa0f550000000000000000000000000081e0f5070741d8b642d50b0faa0b0b070707170707170fa0f0b50b0b0b0b030b130b030000000000000000000000000003030381e0fa0f0fa0f0f170707171344c2c4d130b0fa0f0307038b070703030707070fa031303130300000000000000000000000000030303a0707a070f81e070741c1c1d070b070707070fa0f070713070703030307038b0fa031303130300000000000000000000000000 24 16777215 10 1023
def hc_58_13 : Nat → Nat := unpackHintV5 0xd849fed2f156ca821cc52956bcba1cb48a0cafc930ab192ca3e9cc9fe10299f97a9638f09039808899e881b1ba7c695272e2626ca98e6541da5e99aa59814653598a49029641c9ce371aac2fa1de2522a01e11c41639f60c32820589aa000162 0xaa5070741d8b6656aaa81c1c1c5c1c1c5ea82d42c2c2c2c0c2d0c2c0c0088b000000002c00005c0070200b01002c0b0002c0000c0330000000000000000000000c0c002aaaaa85c1c1c5c6d330b1b4cc2ea80307030007070aa1303130300000000000000000000000000030303aaaaaa170707171345c2c5d130baa0307038b07070303070707aa13031303000000222c00000017001c01305c0017000802c04003004c000000000000000000000303000aaaaaa1b47c2c6d1f0b07070707aa1313000070300ea84c0c4c0c000000000000000000000000000c0c0eaaaaa81d07070741c2c1c1c1c1ea81c1c5c1c1c0c0c0c1c0e2ea84c0c4c0c00000088b00000001c0001c070001c0070200b01000c013000000000000000000002a90b42d982c5c2c1c2c1c2c2eaaa80c0c0c4c0c4c0ea940e2d40c0d500222c0000000000017001c0802c0b011002c0b0002c1b0000c013000000000000000000002a90c5d0c1d0c1d0c5d6955555540004c0c4c0ea82c2c00144008000000000000000000000002a92c9d2c9ea95555004c0c4c0ea82c05100222c0000000017001c0809c04b0101000c013002a9507545d599590f5555544c0c4c0ea942d5540e2c0088b00000000000005c0070204001100102c04400300c013000000010000000000000002a955662d555555513131313aa50001545138b000000000000000001000000000aa1b331b33aa1317570713075717aaaa130b1b44d330b13031303aaa130347130300000000000000000000000000002aaa91d1ea91d1c0088b00000005c0070200b01000c000000000000000002aaaa82c2d4115555555545c1c1c5ea86c4c6c0c6c4c6c0d545c072103c3c141106c1b05c072207c7c07c9c1106c1b0010b6a07a85d5565a55aa5665010762d5555555642d545c1c1c5d50346d61baa80ea9545c071412b0a0fa0222d106c1b05c071412f08bc28221106c1b002aa966a82290790707665a50b0b07070707aa1f131b031f131b030b50b0701c880f0f0070700b106c1f01c072207c7c07c8c02c41b08c0081e070642c0d40e1313aaa84c7ea82d42c1c1e1313a80c0e82c2c1c1e0f888b1f04c1b131f208c1306c4ea07a81ea8041d8b507075a582d995a07aaaaa0707aaaa070b070707070787eaa03aa0b50b070707030707030701ca0fa0222c2c407070071f01b07c0701c87c282202c407070072301b08c00aaa0707aa50455541d5555541c1c1c1ea86c4c6c0c6c4c6c0d541c0720403c3c141106c1b01c072207c7c07c9c1106c1b00141d6955556a81ea076556aa0155541d8b55555546d55030707070786eaa03aa5547c1401c07283e8088b441b06c4bc1401c0721f0a088441b06c00aa9aa5a08a41d9996941c1c5c1c1c5ea87c4c6c0c7c4c6c0c2d42c5c072203c3c02c2c02c41b07c1701c881f1f01f2300b106c230020785c190b40c0d84c4eaaa131faa07507131713aaa03a0b0b0b0b83e222cac1306c4c8c82304c1b13aa85ea8041d9a9a0b8b6640717aaa82c2eaaa2b8b0710b170707178ceaaa82d42cac6cac6c5c0722328880b108c2306c232a07a85ea805070741d8b65a5a0b0b665682eaaaa82c2e82c3eaaa81c1c1c5c1c1c5e33aa80ea82d42c2c2c2c0c2c2c0c5c07283e8088b0b102c2c0b00b0b2b01b0cc1701c88c282202c40b0b00b2301b08c00aaaaa0303a08a17070717aa1b47c2c6d1f0b80c1c0ea81c1eaa84c0c4c0c5c072203c3c05c3c07c1b00c1305c072207c7c07c9c0bc1b00c030000c0c0ea07a85eaa17aaa1385eaaaaa80170707171345c2c5d130b9a982ea80c1c0e2c1c1c0c0c1c1c1e84eaa80c0ea84c0c4c0c5c0704c5c05cac283e8088b3306c0304c1701c13170172f08bc28220bc1b00c03002aa80c0eaa82281c1c1c1ea86d1f0b1b47c2c1c1c0e0307aa1313aaa130313030701c880f0f0070701f06c0304c0701c881f1f01f2702f06c0300c00030303aa81e07aa81ea81ea07aaaaaa001d07070741c2c1c1c1c1e6a60baa070717070703030307038b84eaa03aa13031303071f0070700701ca0fa0222c7c1b00c1301cbc01c1c01c0721f0a0882f06c0300c00030303aaaaa131307070707138ba81c1eaa8a1707071713131313aa131313131701c131304c7c880f04c1f06c1701c1304c881304c2f06c00aa1f1713071f071317a08a1b1f1b33aa134cc2c6d130b1303130347aaaa84c0c4c0c7c1f2203c3c07c3c0cc1b00d1c130bc1f2204c9c0bc9c0bc1b00c03002a07a85ea8042d0b5a582d982c5c2c1c2c1c2c2e82c6eaaaa82c2eaaa80c0c0c4c0c4c0e13aa80ea940e2d40c0d53f0fca0fa0222c2c2c46c0b0b00b1b00304c2308c88c282202c40b0b00b1b00300c00aa55551f171f071f071f175045555513031303aa550b0baaa1f07ca0488b47c503c3c1400c6c131f07c1f221107c7c07c9c00c03002a07a85ea804b274b2792eaa27aa55555555451303130384eaa03aa0b04c0d54fc3f283e8088b270fc440304c 24 16777215 10 1023
def hc_58_14 : Nat → Nat := unpackHintV5 0x81e92a3efc7e1dd46a8e7b9ba6f1532358e7f19106dcbf82405cf8b22ae8e5145448094339c45d9101f80db0ed63a86fd9b634d4c6187e7b0afe5044b3b2e1f41970e8447064e3d02c518813d096085664838c27c1499f207f496025a6800a1230000142 0x42d81e0f543d943c5c1c1c1c1c3c3d5543c3d43d54041d8b55555555545c1c1c5d50344d43e83c3c3c3c0c3c6c3c0d545c071412b0222e82a441b06c1701c50403c80f0f00f0441b06c00070707541c1e0781e8281c41d0750b0b50b0b642c1c1c1c1c7c4c6c0c7c4c6c0c3e83c2d42c1c0701e0a007202c41b07c0701c1f1f01f2300f202c41b08c0081e070707070707070707010762d41c1d90b50b0b50b0b541c3ea81c1c1c3c1c3c1c1c1c1c1c3c1c1c1c1c1c1c2c1c1c1c1c1c3e83c3c3c3c0c3ccc3c0c2d42c1c1c1c0c1c4c1c0c1c07088ba0a82c407070071f01b07c0701c0f203c3c03c8c02c407070072301b08c00070707070707070781e07545055555555070707071b131b031b131b030fa0f550701ca050420441b06c0701c1f2701f1f00f21106c1b00141d9550f81e0750f555550f0f07070707070707070155541d8b55555544d5503070707070fa0f0f0f0f030f1b0f035547c1401c07088ba0a9106c1b1370500701c0f203c3c03cdc1106c1b00141c1c1c1c3d81e0fa0a0b10742d41c1d42c1d90b1707071733131b0333131b030fa0f0b50b1701c0b82802ca80b106c3305c0708c8c08c8c03c80b106c230020783c3c5c1c1c1c1c3c3c05070741d8b642d42c2d42c2d50b0f0b0faa0b82c2c2c3c2c3c2c2c2c2c2c3c2c2c2c2c2c1c1c1c5c1c1c5c3e83c3c3c3c0c3ccc3c0c2d42c2c2c2c0c2c4c2c0c5c07088ba0a82c40b0b00b2b01b0cc1701c0f203c3c03c8c02c40b0b00b2301b08c000707030307070f03a0a0f20783c4d130b1344c2c5c1c1c5c3e83c3c1c0c0c1c1c0c0c3c0c1c0c3e80c4c0c4c0c4e0a01701c0f20cc1b00c1304c4c04c9c05c0703c83306c0300c0003020f83c5c1c1c3c9c3d2c3c3c3c9c3c9c3c3c3c10b42d0b42c00c030303030008b881704c2000f09c27003003030381e0fa0f0fa0f0f0f17070707070f0f0f130f170f0f0f0f0f130f0f0f0f0f005c1c1c5c4d130b1344c2c3e83c3d0f0b0f43c2c0c1c0e2c1c1c0c0c1c1c1c3e80c3c3c0c0c3c4c0c0c4c0c4c0c5c0704c4c04cac088ba0a8cc1b00c1305c0704c4c04c03c80f0f00f3b03306c0300c00070703030703070781e07a072801c1c1c1c4d130b1344c2c3e83c1c0c1c0c4c4c0c0c3c3c0c0c3e80c4c0c4c0c1c072801e007207c1b00c1301c0704c9c04c4c03c83306c0300c00030303a0707a070f81e0707070f070707070707070707070f0f0707070707070707001d07070741c2c1c1c1c1c3e83c3d0f0b0f43c2c1c1c4c1c1c0c0c0c1c0e2c3e80c3c3c0c0c3c4c0c0c4c0c4c0c1c7c01c1c01c07088ba0a87c1b00c1301cdc01c1c01c0703c80f0f00f3703306c0300c0013173f0713073f1783e0fa0a0f06ccc6ccc6d130b134cc2c3e83c4c0c4c0c3c3c3c3c3e80c3c4c0c4c0cfc3f0fe0a00f20cc1b00d1c1300fc9c04c9c03c83306c0300c0083e0f0f170f070f070f0f010b42d90b50b0b50b0b0b170b070b070b0b0b0faa0b0b0b0f0b0f0b0b0b0b0b0f0b1b0b0b0b0b030303130313030fa030f0f03030f1303035038b5030354fc3f088ba0a82c2c46c0b0b00b1b00304c2308c0f203c3c03c8c02c40b0b00b1b00300c0083e0f5555131313071307131745505555130313030fa03550b0b03030f0b03033f0fc4204cc5281400c6c13131ec7b03c84413270131300300c0083e0f0f170f0f0f0f00acacacac3c3ea8ae2d5a5555555555144c0c4c0c3e80c3c3c0c3c4c0c2c1303552b0ac0f203c0f0ac2b1100c0305c1c1c3c05c1c1c5c3e83c3c3c3c3c9c9c3c9d2c3c3c3d55000c0c0c0c0c008b88002709c0f203c0f003c27011100c030020f83c3c5c3c1c3c1c3c3c04b274b270fa0f0f0f0f270f4b0f0f5555555545130313030fa030f0f03030f1303030b04c0d54fc3f088ba0a89c3f1100c1320f83c3c5c3c1c3c1c3c3c0541d51756543d550f5550f43d555555555130313030fa030f0f03030f13030350b555038b3f0fc222e82a52b05104cc500c6c1313003c80f0f00f3b05051044031b00c4c00020783e83c3c3c3e17a0f0f0f170f17070707070f070f0faa070707070f07a0f0f0f0f005c1c1c5c5d170b1745c2c3e83c3d0f0b0f43c2c5c1c1c5c5c4c5c0c5c4c5c0c3e83c3c3c3c0c3cfc3c0cfcfcfcfc08b01c007008b202000000000000000000000000081e81c1e81c1c3c3e0781c1c1e81c1c1c1ea81c1c3c3c1c1c3c5c1c1c1c1c1c1c1c1c00741c1c1d070b070707070fa0f0f43c2c3d0f0b0713070307070703070707070fa0f0f0f0f030f3f0f033f3f3f3f01c01c008b022c808000000000000000000000000b50f91707071755272b49c9d5000762d5555031346c0c6c0c0000070042703c0f101b083e0f271727072707271700002337230fa0f2748c2c9d230b3b0337030fa03273b03032727030323033b03000000000000002700f0003c09c00009c00083e0f0f170f070f070f0f003e83c3d0f0b0f43c2d1d1c3e83c3c3c3c0c3c3c0d1d1c088ba0a811c003c80f0f00f00470000b0b000aa55a515005055170707171b131b031b131b03aa550000000000000000000000000042daa566541d8b5555545c1c1c5d50346d6a95400000088b00000005c0070110010008101000c01b000000000000000000002a9107660050aaaa0b0b00007070707aa0b50b1f131b031f131b0300000000000000000000000000aa41d8b507076656aaa81c2c1c1c1c1c1ea82d42c1c1c1c0c1d0c1c0c0088b000000000001c0070200b01001c070001c0000c0330000000000000000000001c1c0029556a9400145546c4c6c0c6c4c6c0c1c1c1c1ea9540000000000000000000000000141d695560faa55550762d551b5540c1c1c1c1ea95400000088b0000001000440007001c08101000c01b000000000000000000002a90746640aaa07005c1c1c5ea82d42ccc6cac6c1700200b000cc003300000000000002a9074665000aaaa070700017070717aa0b50b33131b0333131b03000000000000000000000000000 25 33554431 10 1023
def hc_58_15 : Nat → Nat := unpackHintV5 0xbc4954b509d0b0592ca971baa2d9a69a0a349381a289ba7284495c7c79f472827e6cd16c6711706338f65d218654a2205021204b01484319fa3ef9083a412e35c12031b9022bd17a2529aa2049381991ae1449521128c80c21420549b6000152 0x2a90742d4585c5eaa801402c2c0005c1c1c5ea82d42d4c4c6c0d4c4c6c0c00000000000000000000000002a90742d98b5a85ea07a560b85c1c1c5ea82d42ea0390e8000722c000000000017080800b02c0440880080000c0330000000000000000000230015545c5eaa8001554001445c1c1c5c6c4c6c0c6c4c6c0ea95400000000000000000000000001507545ea9655555598b1707071746d5503aa550001c8b000000000005c1000440080f0220102c044003006c00000000000000000008c0081e0f41d0b5a662c1717070707070b0b5000a000170707170fa0f0b50b1f131b031f131b030001c8b00000000000000000000000020783d0742d6998b0b17070707070b0b56a170707170fa0f0b50b0b0b0b030b430b030001c8b000000000005c03c0800b01002c0b0002c0000c0130000000000000000000230020783c5c5c1c1c1c1c3c3c0c0c0005c1c1c5c3e83c6d1f0b1b47c2c5c0c1c0caa0300a01b031b030000000000000000000000000081e0f0f17070707070f0f030303170707170fa0f0f43c2c3d0f0b17030703a038ba0303a86c0c6c0c000722c00000000001700f03c08800f03c000f0000b01000c013000000000000000000003002aa85c5eaa80005c1c1c5c6d430b1b50c2ea85c0c1c0c3c3c002886c0c6c0c00000000000000000000000002a07a85eaaa170707179a982ea85c0c1c0e83eaa80e2c6c0c6c0c000722c00000000001708002200203c08800b01000c03004c0000000000000000000030005c1c1c5d0742d0b42c2c5c1c1c1c1c2c2c2c3c2e0b82c2c0c0c0c5c0c1c0c6c0c6c0d40e2d40c0d50001c8b0000000000005c03c0800b02c04400b02c000b06c0003004c00000000000000000000c001707071741c1cae2c1c1c5c5d0cad0cad5555005c0c1c0c6c0c6c0c2c05105c03c00430010004c0000000000000170707175551717430f4390e430f55555000170307031b031b030b0b00051000000000000000010c27000000000017070717170707174b4b4b4b555540170307031b031b031b014400000000005c1c1c5c5c1c1c5d2c9d2c9d5555005c0c1c0c6c0c6c0c2c0510001c8b0000000005c03c0802709c04b00404003004c0017070717541d07545d1756543d55555170307031b031b0350b555038b0001c8b001000000000001700f0201000440040b011000c03004c00000004000000000000000c00aa85eaaa170707179a6aa13030713a0002a8a138b1313131300000000000000000000000130707135551762d65555555130307131313131350001545138b000010008b00000000001000000000170707131707071713331b131317030307031717130f1384e130f130b1b44d330b13170307031713034713031303471303000000000000000000000000000005c1c1c5c5c1c1c5c8c8c8c8c0c0c0c0c0c0c0c0c0c0c0c0c0000000000000000020783d17541d50b55598b55545c1c1c5c3e83d50346d55400000000000000000004270000000aa41d0b662d6a17a81e9582e17070717aa0b50ba80e43a00000000000000000000000000541d517aa5955555662c5c1c1c5d1b5540ea954000000000000000000000000020783d0742d6998b0b17070707070b0b56a170707170fa0f0b50b0b0b0b030b430b030000000000000000000000000081e0f0f17070707070f0f030303170707170fa0f0f43c2c3d0f0b17030703a038ba0303a86c0c6c0c00000000000000000000000002a07a85eaaa170707179a982ea85c0c1c0e83eaa80e2c6c0c6c0c000000000000000000000000005c1c1c5d0742d0b42c2c5c1c1c1c1c2c2c2c3c2e0b82c2c0c0c0c5c0c1c0c6c0c6c0d40e2d40c0d500000000000000000000000000017070717541d51756543d55555170307031b031b0350b555038b000000000000000000109c000000000005c1c1c5c5c1c1c5c5c1c1c5cecececec0000000000000000005c1c1c5c5c1c1c5c5c1c1c5d1d1d1d1c000722c0000001700f02002c04003000000000000000000007070b0b07070f0b505481e0f555555551b131b031b131b03170707170fa0f5550a01701c48441b06c63270632701701c0f21106c1b0002c083e0f1707070f270f530f0f0f270f270f0f0f00455130313030f031b030008b8817108003c27046c0 24 16777215 10 1023
def hc_58_16 : Nat → Nat := unpackHintV5 0xc93276c3397eba9a28b2b9f8aba9c4a1da749313b2889a9e7f9a4076a23e67d3b46059de55f29a4cba4e3d8bcc3d40123d20083cd8123cb8083bb0423b90083b50103af01839e84231da04293a281e12ca1629fa1089680d10de07596e0001d6 0xaaaa81e0faa507075070b41d07662d6a07aaa0781eaa07a81e9582e073307030707070307070707aa0b50ba80ea0707170707001c8b880b12822b01b13c07230070700701c880b12822301b08c00aa5045aaaa5555598b555507070707aa1b131b031b131b03550712205c5c141106c1b01c07220bc9c0bc9c1106c1b00005541d075541d541d507aaaaaa59555555555662c1c6c1c0c1c1c1c0c1c1c1c1d1b5540ea9541c1c5c1c1c00722d2b05088441b06c072f0070700701c4bc14221106c1b0001c1c01c070781e07a076950741d41e5a641c1c1c1c1c7c4c6c0c7c4c6c0c3e83c2d42c1c0705c5c02c2c03c80b106c1f01c0707c8c07c7c03c80b106c2300020783d0742c1c4c4c1c1c1c1c1c1c1d0dcc1c1c1c1da6584c1c0c0c1c1c1c0c1c1c3c3c2c2c2c2c1c5c1c0722c7c1f06c7c8c0708c2306c8c081c1c1e07070f8b81e0741c1c1d07070b8b41d07641c1c1c1c1c1c1c1c2c2c1c1c1c1c1c1c1c7e2d20f842c1c4c1c1c1c1c1c1c1c1c3e83c2d42c7c6c7c6c1c8c070701c0703c80b107c1f06c230081e81c1e81c1c3c3e0781d0750707507070b0b41d075a662c1c1c2c1c1c1c1c1c1c1c1c1c1c2c2c1c1c2c5c1c1c1c1c1c1c1c1d5a81c4c1c0c1c1c1c0c1c1c1c1c3e83c2d42c2c2c2c0c2c2c0c1c1c5c1c1c00722c3c80b102c2c0b00b0b1f01b07c07230070700701c0f202c40b0b00b2301b08c00030300701c0c1c1c1c1c4e130f1384c3c1c1c1c1c4d330b1b44c2c4ccc6c4c1c0c1c1c1c0c1c1c1c4c0c4c0d1c4c0c4c0d1c1c0704c5c0fc5c04c3f0cc1b00d1c1301c0704c9c0dc9c04c370cc1b00cdc03370001c1c01c070781e07a0703a0303070707071b47c2c6d1f0b0fa0f07030703a03030780c0c1e80c6c0c6c0c1c0705c5c03c3c03c81f06c0307c0701c1f2701f1f00f20dc1b00c030000c070781e07a0f0f84e8b07070707070707a07070707a0703030307070707131313130fa0f0f0f0b0f0f0b0701c1304c0f203c3c0f1f07c1b01c0704c1303c80f0f03cdc3306c000281c1e81c3e0781c1c1c3c1c1c1c1c1c1c1c1c1c1c3c3c1c1c1c1c1c1c1c1c0c0c0c1d07070741c2c1c1c1c1c3e83c3d0f0b0f43c2c1c1c4c0c0c1c1c0c1c0c0c1c0c1c0e80e2e80c0ea1b031b030707170707001c8b0f203c3c03c7c07c1b00c1f01cdc01c1c01c0703c80f0f00f3703706c0300c00aaa08aaaaa07070707aa1b5cc2c6d730b07030703aaa0f0f0303070703031b031b030722205c5c280fc1b00c3f01c07220bc9c0bc9c0bc1b00c030000aa81e07aa81ea81ea07aaaaaaa81d07070741c2c1c1c1c1e6a60baa071303030707030307030703a0faaa038b1b031b030707170707001c8b8ac28220fc1b00c3f01cbc01c1c01c0722f0a0882f06c0300c000301c1c1c1c1c1c4c4c4c4d0741d42c2d1362c1d0b42c1c1c1c1c1c1d41c1c1c1d41c2c3c2c2c2c2c0c0c0c1c0704c1304c1302c2c46c0b0b02c6c0701c1304c1304c0b102c2c0b1b00000781c1c1e070f07070707507075070b41d0742d0b07070b1b070707070707070707070b0b07070707070707070b0f0b82e0b0b0303030707130303070703070303070307031b031b035038b50303541c1c5c1c1c00722cfc3f02c2c46c0b0b00b1b00306c07230070700701c2308c0b102c2c02c6c00c030003e8b8b83e2e2c1d41c3e43038b3f08b8b5b0f5b8b0f1702d80c2e2c1701c1c1c1d555541143e83d55541c0c1c0c6c0c6c0d5542c2c0c0c1c1c0c0c1c1c101c8b3f0fc4fc505c5c1400c6c1b4f01c070dc37110dc9c0dc9c00c6c033700000781c1c1e070f07070707074b070707070727070707074b274b2755555555450713030307070303070307031b031b030b06c0d541c1c5c1c1c00722cfc3f09c3f1100c1b000781c1c1e070f070707075541d075541d541d50756543d5555555550713030307070303070307031b031b0350b555038b0707170707001c8b3f0fc4ac1413f14031b06d3c07370070700701c370dc537051044031b00cdc00001e07070781c3c1c1c1c1c1d07070741c2c1c1c1c1c1c1c0c1c1c1c0c1c1c1c1d1d1d1d1c1c1c5c1c1c00722c011c01cdc01c1c01c070dc370dc370dc370020783c5c5d5542c2c0015465401405c1c1c5c3e83c6c4c6c0c6c4c6c0d5400000000000000000001f09c00000020783c5c1c1c5c3c0551504170707170fa0f1b1b1b1b55000000000081e0f170707170b015454105c1c1c5c3e83c6c6c6c6d54000722c000000001700f02017c009c270101000c0130020783d17541d50b55598b55545c1c1c5c3e83d50346d554000722c00000000001700f03c08804400400101000c0130000000000400000000008c00 24 16777215 10 1023
def hc_58_17 : Nat → Nat := unpackHintV5 0xd761f8d11992c87a28bdbab0b5e9f4aec1caa98150a3f9629d09bc97c95090f1b68c412c85f99280915a7a818471b2346b399e61da585c695c5531ce4b6a7245d1663fe97a37b20e32d1382b09f226113e1f59ae1779f80d6a8406b1ae0001ac 0x5c1c1c5c5c5c3c5c5c3c5c5c1c1c1c1cae2d50707554acacacad5555555145c0c1c0c5c4c0c5c4c0c6c0c6c0c2c1b03551701c1705c2b0ac2b0ac440300c083e0f1707071717171717271f17271f1717170fa0f554003030303030022c1c070005c0705c17005c27009c2711100c030000170707171785c3c5e170f1707071717171727174b17174b274b2755555555451703070317130303171303031b031b030b06c0d540722c1c1c01c1c1cfc3f09c3f1100c1b00170707171785c3c5e170f541d5175545d5545d1756543d5555555551703070317130303171303031b031b0350b555038b01c8b070700707073f0fc52b05104fc500c6c1b4f05c0705c5c05cec0141441100c6c0300000005c1c1c5c7e1f0f1f87c3c5c1c1c5c9d1f0b1f48c2c7c8cbc7c5c0c1c0c9cec0c0c7c9c0c0c7c0cbc0c8c0cec0c000000000000170005c0027000000000170707171785c3c5e170f170707171745c2c5d170b17070717171717031717034747474701c8b07070070707004701701c17170170004700081e0755070750b0b00055150050070707070fa0f1b131b031b131b03550000000000000000000000000081e07070707070b015454101c1c1c1c3e83c6c6c6c6d540722c00000000000700f02017c0270101000c0130020781d07541d50b55598b55541c1c1c1c3e83d50346d5540722c0000000000000700f02011001000404003004c0000000001000000000002a90741d1aa81c1e801402c2c0001c1c1c1ea82d42d8c4c6c0d8c4c6c0c00000000000000000000000002a90741d98b5a81ea07a560b81c1c1c1ea82d42ea0390e80722c00000000000007080800b010220020000300cc000000000000000000005070755aaa00055500051070707071b131b031b131b03aa5500000000000000000000000000541d507aa5955555662c1c1c1c1d1b5540ea9540722c00000000000007040011002020101000c01b0000000000000000000020781d0741d901c1c1c1c1c1d02001c1c1c1c3e83c2d42c7c6c7c6c0700f0002c001f0004c000000000000081e0741d076407070707070707075000a000070707070fa0f0b50b1f131b031f131b0300000000000000000000000000081e0741d075a662c1c1c1c1c1c1c1c1d5a81c1c1c1c3e83c2d42c2c2c2c0c2d0c2c0c0722c0000000000b00000700f02002c0400b02c000b00003004c0000000000000000000081e0707070707070707070303000070707070fa0f1b47c2c6d1f0b07030703280c02806c0c6c0c000000000000000000000000020781c1c1c1c1c1c1c1c1c0c0c0c1c1c1c1c3e83c3d0f0b0f43c2c1c0c1c0e80e2e80c0ea1b031b0301c8b00000000000001c03c0800f03c000f0000b01000c01300000000000000000000281c1eaaaa80001c1c1c1c6d430b1b50c2ea81c0c1c0c3c3c002886c0c6c0c00000000000000000000000002a07a81eaaa070707079a982ea81c0c1c0e83eaa80e2c6c0c6c0c0722c0000000000000708002200202002c04003004c000000000000000000000707070741d0742d0b07070707070707070b0f0b82e0b0b030303070307031b031b035038b50303540722c00000000000000700f02002c0b011002c0b0002c1b0000c0130000000000000000000001c1c1c1d41c1d550c3d0e4390c3d555540001c0c1c0c6c0c6c0c2c2c00144070000000000000000000000000007070707070707074b274b27555540070307031b031b030b01440722c00000000000700f02009c04b0101000c0130001c1c1c1d50741d50745d5950f5555541c0c1c0c6c0c6c0d42d5540e2c0722c000000000000000700f0201000440040b011000c03004c000000040000000000000000707070750762d555555555070707031313131350001545138b000000000000000001000000000070707070707070713331b130703070707070303130f1384e130f130b1b44d330b070307070703130313031303471303000000000000000000000000000001c1c1c1c1c1c1c1c1c1c1c1d1d1d1d1c0722c000000000700f02002c04003000000000000000000504581e07a0707a0b0b555555555070707071b131b031b131b030fa0f5507105c5c1403c8441b06c0701c1f2701f1f00f21106c1b0000a0707a070f81e07072707070707075f070707070b20f55555555540713070307070703070707070fa0f1b1b1b1b550707170707001c8b0f207c1f1106c1b00a0707a070f81e0741d5541d075541d507542d555541d0b55662d5550713070307070703070707070fa0f540d1b5550707170707001c8b0f21411f0441b06c07370070700701c0f214414dc1106c1b002822aa96a690741d41c1d42c2da681c1c1c1d3c4c6c0d3c4c6c0ea82d42c1c817170a0880b106c4f01c0708c8c08c8c2202c41b08c000aa41d0b07131307070707070707437707070707960b50b07131303070703030707a0b0ba07170701c8b2b0ac1b432301c2308c1b23 24 16777215 10 1023
def hc_58_18 : Nat → Nat := unpackHintV5 0xce9800cde82ccdc808cda808cc8848c6e16ac5b84ac4904abbe22cb880d8b570c4afe962a941aaa2e1989b01f89162688ab9aa8409ac7a826274c96e6c2a28640a085cf9c44f4b6c4572763c724036b17028838c2119da16b29a07e3b40001f8 0x22e2c5c1c1c22c3e2c9d2c8b17070f83c16d6c9c9c9c9c9c9c9c9d5555006c0c6c0c6c0c6c0c2c051000009c8b00000005c007003c080270404003004c008b83c1dacfc1c9d2e2e2c3dacfc3c9d2c3f8b5b5b3f174b073f074b173f0f4b8fe4b0f272727274b27272727274b270155554155146c0c6c0c6c0c6c0c6c4c06c4c0c0c2c1b03553f0fc3f0fc2727272727009c8b440306c272727275555551b031b031b031b030b031b0355272755031b1b032f2f2f2f55550303030303030303550000000000000000000541d51756543d555551b031b031b031b0350b555038b515155031b1b1b030303030354551540c6c0c0c0c0c0d415282c2e83c2e0783d555555546c4c6c0c6c4c6c0c5c1c1c5c3e83d55401c1c101c0f21106c1b07c9c07c7c05c0703c8441b06c00083e0f17070717171717171f1f171f1f1717170b0154104c0c4c0c6c0c6c0c22c1c070005c0705c17005c1f003c84441b06c00020783e83c3e83c3c5c1c1c5c5c5c5c7c5c7c5c5c2c83d55555555505c1c1c5c5c4c5c0c5c4c5c0c3e83c6c6c6c6d540722c1c1c01c1c1c3c81f07c441b06c020783e83c3e83c3d17541d51745d55175550b555555598b55545c1c1c5c5c4c5c0c5c4c5c0c3e83d50346d5540722c1c1c01c1c1c3c85047c1106c1b05c0705c5c05c7c03c851050441b06c00a0a89a5aaa50b0b50b0b41d0b661f131b031f131b0317070717aa0b50ba0070708072202c41b07c1f2301f1f01701c880b106c230002a90b42c5c1c1c5c5c4c4c5d0c7c5c4c4c5c5c5e582d42c5c5c5c4c4c0c4c5c0c0e82c2e81c8b0701c1cac2b06d0c5c2308c2306c8c0aaaaaa41d0b50b0b50b0b662d6a17a81ea1785eaa17aa9582e170707171717170317331703aa0b50ba80ea01c8b07070070707880b12822b01b13c1701c1717017230880b12822301b08c00aa4550aaaa5555555517070717aa1b131b031b131b03554072201c1c141106c1b05c072207c7c07c9c1106c1b0000541d5175545d5545d17aaaaaa59555555555662c5c1c1c5c5c5c5c0c5c6c5c0d1b5540ea9540722c1c1c01c1c1d2b05088441b06c1701c17170172f04bc14221106c1b0001c1c01c1c2ca5a0f60783d6942e41d0b642c7c4c6c0c7c4c6c0c5c1c1c5c3e83c2d42c2c1c01c1c02c07070703c80b106c1f07c8c07c7c05c0703c80b106c2300020f83d0b42c5c1c1c5c5c4c4c5c7c7c5c4c4c5c5c5da6581c1c4c5c0c0c5c4c4c0c3c3c2c2c2c2c1c8b0701c1c7c1f06c7c5c1f08c2306c8c081e0fa0f0fa0f0f41d0b50b0b50b0b5a662c2c5c2c5c1c1c1c1c2c1c2c2c2c5c2c5c2c2c2c2c2c5c2c2c2c2c2d5a85c1c1c5c5c4c5c0c5c4c5c0c3e83c2d42c2c2c2c0c2c2c0c0722c1c1c01c1c1c3c80b102c2c02c7c06c1f05c0705c5c05c7c03c80b102c2c02c8c06c230000c0c01c0c5c1384c3c4e130f170707131b44c2c4d330b1707071713331b1313171713170307031713031303130313031f070070701701c1307c3306c034704c3f270132701701c1303306c0300c000707007070f280c0e83c0e0783c6d1f0b1b47c2c5c1c1c5c3e83c5e0303a0303170307030fa031b031b030f070070700f01c0f207c1b00c1f07c9c07c7c05c0703c87f06c0300c00083e0f17070717171717171f1f171f1f17171703010b42d0b42c0c0c0c0c2022c1c0700007001707c0f03c270030020783e83c3e83c3c3c5c1c1c1c1c3c3c3c5c3c5c3c3c3c3c3c5c3c3c3c3c3c0c0c0c5c1c1c5c5d170b1745c2c3e83c3d0f0b0f43c2c5c0c1c0c5c4c0c0c5c4c0c0e80e2e80c0ea1b031b0301c8b070700707070f203c3c03c7c07c1b00c1f05c0705c5c05c7c03c80f0f00f006c0300c00aa8aa0aaaa17070717aa1b47c2c6d1f0b17030703aa0f0f0303170f03031b031b038072201c1c2807c1b00c1f05c072207c7c07c9c0bc1b00c030000a81ea17aa85eaa85e17aaaaaaa85c1c1c5c5d170b1745c2e6a60baa170307031713030317130303a0faaa038b1b031b0301c8b070700707078ac28220fc1b00c3f05c0705c5c05cbc22f0a0882f06c0300c00005c1c1c5c5e170f1785c3d0742d42c2d42c2d0b42c2c5c1c1c1c1c2c2c2c5c2c5c2c2c2c2c2c5c2c6c2c2c2c2c2c3c2e0b82c2c0c0c0c5c0c1c0c5c4c0c0c5c4c0c0c6c0c6c0d40e2d40c0d501c8b070700707073f0fc0b0b11b02c2c02c6c00c1b05c0705c5c05c8c08c2302c40b0b00b1b00300c0017070717555545501f0f1f87e1f0f5555170307031b031b03550b0b0303170b0303401c07c1f11f140707050031b06c7c1701c1f07c441f1f01f2700300c00 24 16777215 10 1023
def hc_58_19 : Nat → Nat := unpackHintV5 0xc7f9a2c2017eb8ba52afd23aa829eaa199a49c91429501e487db4a83611e7d099678911e75b0b86e41dc6751bc5f91f05e784658019e4ec2504c908c4681844430943bda1639a88c3399842ee92c2c28b023722e19ca6a0fa28a0702280001c0 0x7030707aaa65995541d559551362d555555513131313431307070707aa5144cd544c4c0c4c9c0c1c0c1c0ea95150bd54bc0cbc0c1c0722151f47d52b4ad0741d99552b42d4ac4c4c0c4c6c0c0d0b540e2e81c1e92b2b140ad1b2b2709c4bc501b2f0303a07aaaa07a2d5599559541d50756565555642d55555a13aaa030307030703aa50b555038ba2a01c1c1c1ea94545540c6c4c4c0e2f8a807030703aa52f4550bd540c6c0c0cbc0cbc0cbc0e0795555555a55507075555130307030fa03550b0b03030f0b0303170707170fa0f4cd544cac4c13131300c6c4c4c4c0c5c0c1c0c3e80d544c4c9c9c0c13130313003030303030381e603071307a0f5551745d5543d8b5550f42d55555544d8b545c1c1c5c3e83c4d0c4c4c4c4d43554cd545c0c1c0c3e80c4c9c0c4c4c0d555550c0d0c0e081c01d0745d90f54ad2b547d1f4ad0b555131b03031313130342d5038b17170f0f0f0f2b4150ad546c4c4c4c4c9c2713f1406c4e0795555170307170fa0f55130307030fa03550b031b131303170707170fa0f55535353530313130381e603071707a0f541d51756543d52749d53b55555555130307030fa0313031b13130350b555038b170707170fa0f3b27273b51513355031b13131303a070781e8ba81c1c1d50741d51745d59950f43d550f5550f43d555550f42d5555130307030fa030f0f030f03030f0f13030350b555038b170707170fa0f0f0f0f03c3c51513355031b13131303170307030fa030f0f030f00c3c3cec0c54550bd540c6c0c0c4c0c0c0c3e07a2ea85c1c1c5ea8ac7e431faaa95512031382c0b05c5e822b2b29544c4e0bc2709c07a2e07a0f07070707070fa0f070707072b2b0743430707075544070313030b02c07070f0f07070072b2b1544c4c1c3709c27207aa07a2e4343aaa8acac1c1c1c1ea955104e80c2c0b22b2b2801c1e9544c4cbc82709c170707170fa0f3b27273b440b02c17170f0f3b3b55131381c1e8ba0707170707170fa0f0f0f0f0f2b2b0f43430f0f0f43d0b55440f0f03030f1343030b02c17170f0f0f0f0f0ac3c1544c4c3c3c03cec2709c43172b0743072b17430f2b90e2b0f555550541b031b031b031b030b0b01b0b03154ac2b0ac2b154540306c6c6c002b2702b270440300c0081c1e8ba0707170707170fa0f0f0f0f0f27270f274b0f0f0f5544030303030300c0f0fc270170307030fa030f030f0300f032703055503030303270327038b0f6b2b0f0ac2762cbcdcbcac5cac1cac1cac5cac3cae2b8ac3d555540000c0c0c0c0c0c0c0c0c0c0014400002700000009c00270440000000022c002f372f2717270727072717270f2789e270f555550540303030303030303030300303031543702f09c9c09c1100c0300c9c03032700c0c9c03032700d55151030300c0c0c0309c0309c030f00f884b273f2755130313031717aa272783e81e8baaa85c1c1c5ea2792eaa955555555544c0c1c0ea0384eaa82c0c4c0d545c1c1c5ea28aa275b5b275503131303280f00f4b273f27551303130307070f0f070781e8ba0707a81c3c1c1c1c1c1c3e83c1c1c1c9c1d2c1c1d55555555541c0c1c0c3e80c1c1c0c0c1c4c0c0c2c0c4c0d541c1c1c1c3e83c1c1c1c070709c9d540c4c4c0c1c07220fc9d2c9d544c0c4c0e81c1e96cfe81eaaa81e8b92eaa2707070707aa555555555584eaa0307030703aa0b03130355a2a01c1c1c1ea89d6d6c9d540c4c4c0e07981c1c5c1e83d5555544c0c1c0c3e80c4c0c4c0d545c1c1c5c3e83d2d2d2d2d540c4c4c0e081c01d2c9cfc9d544c0c4c0c5c5c3c3c3c3cfd44c4e81c1e07a2ea070707170707170fa0f0f0f0f0f27270f0f4b0f0f5555555555130307030fa030f0f03030f1303030b03130355170707170fa0f0f0f0f03c3c27275503131303171717170707171785c3c5e170f0707278b07071717070707272727275555545555170307031713030317130306c0c6c0c2c0c6c0d545c1c1c5c5c5c5c174b1712d2d2d2c9c9c9c9d540c6c6c0c1c1c1c1e07070781c3c1c1c1c1c1c1c5c1c1c1c1c1c1c9e2c9c9c9c9d2c9d51555555541c4c0c07070303070307031b031b030b031b0355074b0701c1c1c070707074b4b4b4b272727274b2755031b1b0383e0f0f170f070f070f0f0f0f0f27272727a278ba0f0fa955555551544c0c4c0c3e80c3c3c0c0c3c4c0c0b031303554b4b4b4b0fa0f0f0f0f03d2c3c272727275503131303a81ea17aaa89c9c9c9d2c9e83eaa89e2d555155555544c0c4c0e138a80ea82c2c0c4c4c0d552d2d2d2e4b8a8aa272727274b275503131303 24 16777215 10 1023
def hc_58_20 : Nat → Nat := unpackHintV5 0xe010da6b289c335a4758a021ac0988d5a88b8ab2e42d4ba1baa0b8a34a40c3a3243f90c01a47a497735210097945f8a87286436a1a1cf0988cac3985b114a2471230dec89859e2b014731009f00904e802026202411203e08700404280201be0ac0001be 0x83e0f2b171f071f072b170f0f0001b1f1b230fa0f1b48c2c6d230b03030303280c000c0c00c0c0c0c00002700000007c000000000000083e0f271727072707271703030803031b231b230fa0f1b48c2c6d230b0303030303a030380ca0030303030dc0f209c09c9c08c1b00c0300c03032700c3c803030f03032700c030300c0c0c00309c83e0f0f170f070f070f0f0303031b1b0fa0f0f43c2c3d0f0b47034703a038ba0303a86c0c6c0c3e83c3c3c3c0f0f06c6c0d1d1c0c0c0c3e80c3c3c0c0f0300c6c0c0c0c0c0c0c0eaa966aaaa9907665a50b0b07030703aaa0f0f0303070703030b50307070707aa332b1f0ccac7c0b50b031b1b0307030703aa23230308c8c0c0b503030303031f03230381e07a642c521f2baaa87c7ea82c02e0fa80e2c4c0c4c0c1c1c7c80b0b070723207c232a0781ea0785eaaa41d8b507075a582d995a07aaaaa0707aaaa070b0707030703a0faaa038b0b50307070303071303030707070793e2a2a82d42c1c1c1c070700c6c6c0c1c0c1c0e238a8aa0b50307070301c8c0c030303031f032303aa9aa5aaaa41d9996941c1c5c0c1c0ea83c3c0c0c2c2c0c0c2d40c5c1c1c5ea8ccaccc332b3302d42c0c6c6c0c5c0c1c0ea88c8c0c23230302d40c0c0c0c0c8c0c8c0eaa85e8baaa90766982d99030713aaa82c2eaaa138b0750b1707071790eaaa82d42c4c4c4c4c5c0c1c0e23aaaa0b503130313032303230381e17a642d062b2baaa8fdcea81c01e0fa80e2c4c0c4c0c5c5cae0a8a0b0b0b0b1b1b23208c2308c8ea0781ea1785eaaa5070741d8b5a582d995a0baaaaa0b0ba0b0faaaa07070717030703a0faaa038b0b5030b0b030b03030b0b1303031707071793e2a2a82d42c2c2c2c0b0b00c6c6c0c5c0c1c0e238a8aa0b5030b0b0302c8c0c030303032303230343172b0743072b17aaa0a81b4f1b4f1b50c2c6d2b0baa430343030f0f03f0f032a86c0c6c0cac2b2a8a82b06c0311cad1c2f0bc2b2702b270882f06c0300c00a81ea17aaa86c6e6a60baa47034703a0faaa038b1b031b03a2a2a86c6c0d1d1c0cbc0cbc0e2f8a8aa2f031b03030303032f032f0383e81e8baaa90742d60b5a660b17070707070b0baaa0b0ba0b1baaaaaa03030313030703a80e13aaa5038b50303545c1c1c5ea24f8aa0b0b51b0b0b0b0b02c6c2c0313130317030703a888e2a82d40c2c2c0c0b1b0300c0c0c0c8c0c8c0e07a2e81c1ea070f0741d07642d41c2d41c1c1c1c1c1c1c1c1c1c2c3ea82c2c1c1c1c1c1c1c2c2c1c1c2c6c1c1c1c1c0c0c0c1c0c1c0c3e80c1c1c0c0c1c4c0c0d40e2d40c0d5070707070fa0f07070701d3c1c0b0b51b0b0b0b0b02c6c2c03131303070307030fa0307070301c8c0c0b5030b0b0302c6c0c0303030323032303a07aaaa07a2d969682c2d0741d9a82c6eaaaa82c2c1c1c1c1c1c1c1c1eaaa80c0c0e13aa80c1c0c1c0ea940e2d40c0d593e2a01c1c1c1ea82c2d46c2c2c2c2c0b1b0b00c4c4c0e238a807030703aa0b5030b0b0302c6c0c030303032303230381e0b80c1c5c1e83d0742d90b42d0b0b17070707070b0b0b0faa0b0b0b1b0b0b0b1b0b0b030303130307030fa03130313035038b50303545c1c1c5c3e83cec9c9cec2c2d46c2c2c2c2c0b1b0b00c4c4c0e81c1e07a2ea07070741d0b642d42c2c2c2d0f50b0b0b17070707070b0b0b0faa0b0b0b0f0b0f0b0b0b0b0b0f0b1b0b0b0b0b030303130307030fa030f0f03030f1303035038b50303545c1c1c5c3e83c3c3c3c0f4f0f02c2d46c2c2c2c2c0b1b0b00c4c4c0c5c0c1c0c3e80c3c3c0c3c030f0f230302d40c2c2c0c0b1b0300c0c0c0c8c0c8c0d0b42d0b42c2c5c2c1c2c1c2c2c2c3c2e0b82c2c0c0c0c6c0c6c0c6c0c6c0d40e2d40c0d50b0b51b0b0b0b0b02c6c2c031b1b0323032303230323030b5030b0b0302c6c0c03030303230323036aa55555550f0f5a55555513030703aa550b0baaa17070717aa551f1f1f07c7c7c0313130317030703aa551f1f0307c9c0c030303031f031f030f00f8841d17547d1f54fd63665551303130342d5038b1717aa4acac502b46cac9c2712f1406cbcbcbe0fa07a2eaaa541d51755655599599590f55555555544c0c1c0ea0384eaa942d5540e2c5c1c1c5ea28aa515155031b13130317030703a88be2a94bd1542f55031b03032f032f032f0381d81c1d555569555543c3d55541c0c1c0c3e80d542c2c0c0c1c1c0c0c1c1c1c1c3e83d544cac4c13131300c4c4c0c1c0c1c0c3e80d544c9c0c13130300c0c0c0cdc0cdc0ca03c03d0741d90f54ad2b547d1f5551303130342d5038b07070f0f07074acac502b46c4c9c271371406c4e07a2e81c1ea070f07541d07541d1756543d55075550741d555555555070307030fa03070703030713030350b555038b070707070fa0f07070701c1c51513355031b13131303070307030fa0307070301cdc0c5374550bd540c6c0c0c4c0cdc0cdc0e2c2b8b8b0ae2c1d9604e2b5b038b8b8b05c1c3e0b4ac0c2c0d6ea981e8b555550707555a55555507030703aa550b0baaa07070707aa552b0ac0313130307030703aa552f27030bc9c0c030303032f032f03 25 33554431 11 2047
def hc_58_21 : Nat → Nat := unpackHintV5 0x9c3457a5ff21c93089ea3af2268a9884a19921a8250829f842207b285d1d5a2e07044a49b161f664550097d727c5bc473159b2ac515ca2134a21a4a405d111c2e83f6ca08e862aa31a10f0b2228c2718ae08852821d14a005444021004a183221be0490ff0000248 0x541d517aa5955555662c6c6c6c6d1b5540ea955454aa551b1b1b1b2f232f234bd152a9546c6c6c6cbc8cbc8e0f83d0b42d90b2b171f071f072b170f0faa0f0f0b0b550b0b130313030fa030b5030b0b00b0b0307c1f03c80b104c4c4c0c13131308c1f03c80b108c8c08c8c00c030020f83d0b42d90b13177307130773175aa0f69542e13031b13030f0fa030f0b0b5030b0b0b0b43430fa0f0b50b431304d0c031b131303230323030fa030b50323230304c8c0c031b030323032303230383e0f42d0b642c4c5c4c1c4c1c4c4c3c3c203c3c2c2c102c2c4c4c0c4c0c6c3e80c2d40c4c4c4c7c1f03c80b102c2c02c2c00c6c131307c1f03c80b104c4c04c8c00c030020f83d0b42d90b1f171f071f071f175080f68102e1b1f1b0fa0f0b50b1f1b032b1b031f07c0f0f203c2c2c40b0b0b0b1b0ac2307c0f202c41f230232301b08c08c08c83e0f42d0b5a662c2c5c2c1c2c1c2c2d5a86c6c3e83c2d42c2c2c2c0c2c2c0c3e83c2d42c2c2c2c0b0b06c6c8c8c8c8c3e83c2d42c2c2c2c0b230b06c8c8c6c8c8c8c8e80c0eaa696aa942c2d42c2d0742d9aa81c1ea030703aa0b503332b330ccaccc17070717aa0b50b0313130323230308c8c0c17030703aa0b5030303030323032303030303aaaaa41d0b42c2d0b0b6681c1c4e2c1c1c4c4eaa0707aa60b50b17070717131313134313aa0b50b1313131317030703131303132303aa0b50313031303230323030303aa42d0b17070717131713173f63172b2b131713140b00b07038b0703070713031303170aca0b0ba1708c2308c030303aaaaaa41d0b50b0b50b0b662d6a17a81ea1385eaa17aa9582e0307038b07070303070707aa0b503aa0303a13a1707071713171705d3c4caa0b50ba8a00c4c4c0c5c0c1c0c4c5c0c1723032a82d40ea223803030303230323030707030307070b03a5a0f60783d6942e41d0b642c2c1c0c0c1c1c0c0c2c0c1c1c1c0c3e80c2d40c4c4c4c132b1305c1c1c5c3e83c2d42c0c4c4c0c4c4c0c13230305c0c1c0c3e80c2d40c0c0c0c0c7c0c8c0c0c0e0f83d0b42c5c1c1c5c4c4c4c4c7c7c4c7cac4c4c4d06081c0e2c1c0c1c1c4c4c4c0c4c6c0c0c1c1c4c4c04c7cac0f0f0b0b0b0b13131308c1f08c1f2303030381e0fa0f0fa0f0f41d0b50b0b50b0b5a662c2c5c2c5c1c1c1c1c2c1c2c2c2c4c2c5c2c2c2c2c2c4c2c2c2c2c2d5a80c1c0e2c1c1c0c0c1c1c1c3e80c2d40c2c2c0c0c2c4c0c0c5c1c1c5c4c4c4c134f1303e83c2d42c2c2c2c0b0b00c4c4c0c5c0c1c0c4c4c0c13230303e80c2d40c2c2c0c0b230300c0c0c0c7c0c8c0c0c0c01c170317070717438ac3cae430f170707171b4ac2c6d430b1b4f1b4f170307033f070301c1c10c0d0c0c6c0c6c0c5c5c0705c5c5c5cac2b0ac1b00c472b4705c070ac9c0ac9c013c1b00c030005c5c0005c1c1c5cae2b0f2b8ac3c5c1c1c5c6d230b1b48c2c6c8c6c8c030303000303003030303030303030009c0000000000000027000000000c0c00c0303170707172789c3c9e270f170707171b48c2c6d230b1b231b230303030303030300c0c00c0c0c0c0c0c0c0c5c0709c09c9c02f08c1b00c0300c5c0300c0c5c0c0c03032700c9c0300c0c030303000c2700c0c0c5c1c1c5c5e170f1785c3c5c1c1c5c5d170b1745c2c6c6c0c1c0e2c1c1c0c0c1c1c1d1c0d1c0c6c0c6c0c5c1c1c5c5c5c5c171706c6c0d1d1c0c5c0c1c0c5c5c0c170300c0c0c6c0c0c0c0c0c0c0e80c0eaaa96a690741d41c1d42c2d981c1c0e03071313aaaaa0b50307070707332b1f0ccac7caa0b50b031313030703070323230308c8c0caa0b503030303031f0323030303aa41d0b072b2b070707070707073f6307070707140b00b0717070307038b130313031f01ca0b0ba2301c2308c030303aaaa81e0faa507075070b41d07662d6a07aaa0781eaa07a81e9582e070717070703030307038baa0b503a80e13a074f0701c1c1c07070707aa0b50ba8a00c4c4c0c1c8c0c07070301c0c1c0ea82d40ea2238030303031f032303070703030703070781e07a076950741d41e5a641c1c0c1c0c4c4c0c0c2c2c0c0c3e80c2d40c1c1c1c1c4c7c4c13131303e83c2d42c0c4c4c0c1c0c1c0c4c8c0c13130303e80c2d40c0c0c0c0c7c0c7c0c0c0c0e07070781c1c3e2e0781d070741c2d0741d907070707070707070b0b07070707070707138b683e50b071f07070707070707070fa0f0b50b13131313072303070703070307030fa030b503130313031f031f0303030381e81c1e81c1c3c3e0781d41c1d41c2d0741d6998b07070b070707070707070707070b0b07070b17070707070707070756a070713070703030307038b0fa030b5030b0b030b03030b0b130303071f0701c1c1c070707070fa0f0b50b0b0b0b02c7c2c0313130307230301c1c0c070307030fa030b5030b0b0302c8c0c030303031f031f030303007030707e1f0f1f87c3c1c1c1c1c6d1f0b1b4ac2c1c1c1c1c6d3c6c7c5c5c07c5c0c070307031f0343031b031b030707070701c1c1c1f07c2b06c0311cad1c2b2701f2700701c1f0dc3706c0300c000303030781c1c1e070f070707070741c1c1d070b070707071b1b070717070703030307038b470347031b031b03070701c1c1c070707071b1b0347470307370301c1c0c070307033703370337031b030303030337033703070707541c1e0781e80c0e81c0d0741d42c2d42c2d90b070307030780c0e80c0c1e80c2d40c1c1c1c1c7c7c7c1f1f1f03e83c2d42c0c6c6c0c1c0c1c0c7c7c0c1f230303e80c2d40c0c0c0c0c7c0c7c0e0781c1c1c1c1c1c1c0c0c0d0741d90b42c2d0b0b070740c1e84e2e83c3c1c1e07a81c1c2d42c1c1c1c1c3e83c3c3c3c3c7c3c2d42c4c4c4c4c1c0c1c0c3e80c3c3c0c3c8c0c2d40c4c0c4c0c7c0c7c0e0781c1c1c1c1c1c1c1c1c0c0c0d0762d41c1d90b50b0b50b0b541c3ea81c1c1c3c1c3c1c1c1c1c1c3c1c1c1c1c1c1c2c1c1c0c1c0e80e2e80c0ea0b5030707030703030707130303070707070fa0f0f0f0f03c7c3c0b50b07070701c7c1c031b1b03070307030fa030f0f0303c8c0c0b50307070301c8c0c030303031f031f035070707070f60783e80c0e82c0d0742d41c1d42c1d90b170307030b80c0e80c0c2ea80c2d40c5c1c1c5cccac7c332b1f03e83c2d42c0c6c6c0c5c0c1c0c8c8c0c23230303e80c2d40c0c0c0c0c7c0c8c0c5c1c1c3c0c0d0b42d043e83c3c3c3c3cfddc3cacac3c3c3c1c01e038b80e84c0c4c0c5c5e83c3c03c7cac0b0b0b0b1b1b0f08c2308c1f2381e0f0f17070707070f0f0303035070741d8b642d42c2d42c2d50b0f0b0faa0b82c2c2c3c2c3c2c2c2c2c2c3c2c2c2c2c2c1c1c1c5c0c1c0e80e2e80c0ea0b5030b0b03030b130303170707170fa0f0f0f0f03d3c3c0b50b0b0b0b02c2c031b1b03170307030fa030f0f0303c8c0c0b5030b0b0302c8c0c030303031f03230383e0f1f171f071f071f170303080f031b1f1b4f0fa0f1b4ac2c6d1f0b43031f030fa031f80ca01b031b031f07c0f0f203c3c3c3cac1b00c472b4701f03c81f2702b2704f06c0300c00 26 67108863 11 2047
def hc_58_22 : Nat → Nat := unpackHintV5 0xea619ce0da62d582d6cc5a4ac37a38b9f262b1c20caab1c4a16a529612d69111408e18be8799a07eb23a75f2306c6a6264f1de6250a85c0194532a364a0a48413a34390a0c3381622fa0f829e17022f9ba1a32321341bc0c49be06996c0001a6 0x42d17070717543d950762d5555517070717540d1b51b1b1b1b55170707175451546c6c6c6c5c1c1c5d5142323551b1b1b1b23230707070741d0742d0b0703070707070303130f2b8ae130f0b0b550b0b07030703130313030b5030707007070301c1c0701c4c1f02c41313130304c4c4c0701c1308c0b108c8c08c8c00c030001c1c1c1d0741d0b42c1c0c1d50303130f1384e130f0b0b550b0b070307070703130313031b0b0b5030b070707070707071343130b50b431304d0c031b13130307030703130323030b50323230304c8c0c031b03032303230323030707070741d0742d0b0701c1c1c1c04c3c4e1384c3c2c2c102c2c1c1c0c1c0c1c4c0c4c0c2d40c4c4c4c1c0704c1302c40707007070031b04c4c0701c1304c0b104c4c04c8c00c030001c1c1c1d0741d0b42c1c075407c3c7e1f87c3c2c2c102c2c1c1c1c1c7c6c6c2d42c7c6c0cac6c0c1c07070707c1f02c2c40b0707071b0ac0701c1f08c0b107c8c08c8c06c230001c1c1c1d0762d41c1d0b42d5070f0781e0707070b07070707071b1b0b50b07070703070703070707070b50b07070701c1c1b1b07070707232323230b50b07070701c8c1c1b23231b232323230707007070707e1f0f1f87c3c1c1c1c1d415155546c6c6c0c6c6c6c0c1c1c1c1c6c6c6c6d5550701c1c1c1f07c4541b1b06c1b2b2701f2700701c1f0dc441b06c0050765543c1c1c1c1d55541d8b5546d5503070707071b1b1b1b5551501c1c1c1d546c6c6c6d374540707070737233723551b1b1b1b372337231707071341d0b42d0b1717030307031717130f2b8ae130f0b0b550b0b13030703130313030b5030b0b00b0b0305c0704c2b02c41313130304c4c4c1701c1308c0b108c8c08c8c00c030005c1c1c4d0742d0b42d40c0c1c0c5d130f1384e130f0707550b0713170307031713031b13030b0b5030b0b0b0b170707171343130b50b431304d0c031b13130317030703130323030b50323230304c8c0c031b0303230323032303407178acaea81c42c5c2a0b083e0f331b2b1b80cce17172baa0b0b0b0ba80b80ccac8c23208c2323407170fa0b0710b82323131b131b1717a0b0b0b0b88c7cad01c5c3c3c3e8acac1c42c5c03c3c3c2c02ea131b131b0f03330317170fa1f2b0b0b0b0b0b802c2c2c1f2b2308c0f0f00f2307c8c4c1c1c4d0742d0b42c4c5c01c1313130f1384e130f0b0b040b0b13030703130313030b5031313131701c1304c0b102c2c02c2c00c6c131305c0704c1302c413130132300300c001707071741d0b42d0b500705d2b0f8ae0f0707040b07170707171b1b0b50b3f1b032b1b03171701c172b0ac0b0b102c2c2c2c6c2b05c0708c2302c423230232301b08c08c08c170707175070741d8b42d0b542c3c2e0b82c2c1c1c1c5c1c1c5c6c6c2d42c2c2c2c0c2c2c0c5c1c1c5c2d42c2c2c2c0b0b06c6c5c1c1c5c8c8c8c8c2d42c2c2c2c0b230b06c8c8c6c8c8c8c8e0f83c7c5c7c1c7c1c7c5c2c2c203c2d555551406c6c6c6c3e83c6c6c6c0c6c6c6c0d547c1f03c3c80f551506c1b16c1f03c81f2702b270441b06c0083e0f55550303030303a035500000000000000000083e0f2b171f071f072b170f0f000551500501b031b030fa031b1303031b13030355000009c0000001f0020001100000022c0083e0f27172707270727170b0b080f0b555554501b031b030fa031b1b03031b1b0303550dc0f209c09c9c1100c1b08c9c23232708c3c3ca80f5545440c6c1b031b06c2708c2708e0781c1c1c9e2c1c1c1c1c2ea83c1c1c1c1c3e281c1c1c5c1d55555555501c1c1c1c3e83c6c6c6c6c1c1c1c0c1c4c1c0d541c1c1c1c3e83c7c7c7c7c7c7c1c1c1c071f071546c6c6c6e0783c5c5c1c1c1c1c9e2c2e83c5c5c5c3c3e283c3c1c1c1d55555555505c1c1c5c3e83c6c6c6c6c5c4c5c0c5c4c5c0d545c1c1c5c3e83c9c7c9c7c5c5c5c175f171546c6c6c6e0f83c9c7c7c7c7c9c2c283d7c5c7c1c7c1d3c5c3c3c283c3c055555455501b1b1b1b0fa0f1b1b1b1b1b131b031b131b03551f07c0f202722c9c9c09c9c9d106c1b20f83c7c7c7c7c2c05515041b1b1b1b0fa0f1b1b1b1b5500000009c27000005c007003c080270404003004c0083e0f27270ba0f5555551b1b1b1b0fa0f1b1b1b1b550fa0f2727551b1b1b1b83e0f45d507542d55662d5551b1b1b1b0fa0f540d1b5550fa0f5451546c6c6c6c8c8c3e83d5454551b1b1b1b2323aa42d0b662b172b072b072b17aaaa0b0b550b0b13031303aa0b503a0a82b0aca220b104c4c4e04c4c4c2308c880b108c8c08c8c00c03002a90b42d984c5ddc1c4c1ddc5ea5682c2d542c2c4c0c4c0c6eaa82c2d40c2ea4343aa0b50b431304d0c031b13130323032303aa0b50323230304c8c0c031b0303230323032303aa42d0b6613171307130713138aa00b0b040b0b13031303aa0b5031313132b0ac880b1282800c6c131308c232202c413130132300300c00aa42d0b662b1763072b07631789500b0b040b0b1b1baa0b50b3f1b032b1b032b0ac8a80b0b102ea1b0ac2308c880b108c8c08c8c06c23002a90b42d98b5a85ea07a560b86c6ea82d42ea03aaa82d42ea281b1b23232323aa0b50ba888e06c8c8c6c8c8c8c8d7c5cac1d7c1cac5eaa82a1554151546c6c6c6c6c6c6c0c6c6c6c0ea954ac2b158a84541b1b06c1b2f0bc2b2702b27088441b06c00 24 16777215 10 1023
def hc_58_23 : Nat → Nat := unpackHintV5 0x7bf92f3c1e779d153e8e2399c6c7929337eaf989a494bbf2385935312a9282140a4fc98e9da488cfa22aa67101c4e475aace36611d19008c0c0e1c85919d627255a11dc6d88332ec3eb8b81a354a0ab09a848933c1f513e0b252103a67b010e31400021c 0x3c3c0c0c1c0c5c3eaaaaa85c1c1c5c6d130b134cc2ea84c5c0c1c0c5eaaaa13031303170707171f1304c7caa331b1b1f03131303170307032f270304c9c0caa2f031b03030303031f032f03131700704c4eaaa2805c1c1c5c4d130b1344c2ea84c0c1c0c4c4c4eaa84c0c4c0c5c072828220ac1b00cac131305c0704c4c04c9c220bc1b00c030003c3c01c170faaa8a0170707174f47c2c7d4f0baa170707173f1f031f3f03aa4f3f3f171701c17aa2a0ac2b0ac2b05c070ac9c07c9c220bc2f0bc2f02f02f20fa07a2eaaa17070717982e6aa85c1c1c5ea03aaa91d1c5c1c1c5ea28aa474717070717a88be2a8bcbcbcbcbcbcbcbcbcbcbcbe0781c1c0c1c1c1c1c0c0c3c3ea83c3c1c1c1c1c3e83c6d2b0b1b4ac2c1c0c1c0c3e80c1c1c01c1c0c130313030701c0f204c4c4cac1b00c13131301c0703c82b2702b2702b06c0300c0081e07070307a80c0c3c3ea83c3c1c1c1c1c3e83c6d130b134cc2c1c0c1c1c1c0c3c3e80c3c1c1c1c4c0c4c0c1c1c1c1c3e83d0c4c13430cc6c6ccc0c4c4c0c1c0c1c0c3e80cdc9c0c1327030cc0c6c0c0c0c0c0cdc0cdc0e0781c1c0707070700f0f080f0f070707070fa0f1344c2c4d130b0707030703070fa03131313130313030701c0f201c1c01c1c07c1b00c7c131301c0703c813130132703306c0300c0081e070701ea00f0f080f0f070707070fa0f1f4ac2cad1f0b070707070fa0f1f2b032b1f034f3f3f0701c1c1c0f0f203c1c1c1cac2b0ac2b01c0703c81f2702b270370dc370dc0081e8ba0707a81c3c1c1c1c1c1c3e83c1d070b0741c1c1c1c1c1c3e83c1c1c1c0c1c1c0d1d1c1c1c1c1c3e83c1c1c1c070711d1c1c1c1c1c3e83c1c1c1c0737070dcbcdcbcdcbcdcbcdcbcdcbc1c1c0c0c1c1c1c0eaaaaa86d2b0b1b4ac2c1c1c1c1eaaaa28007030703aa13033f1343031313130701c882b06c81322c4c4c0ac9c0ac9c01c07220ac1b00c030001c1c0c0c1c1c1c0eaaaaa84d330b1b44c2c1c1c1c1eaaa070307070703aaa1303471303134310c4c07070707aa331b1b3303131303471327030bc9c0c07030703aa2f031b0303032f03032f2f032f0307070070707282a2a84d130b1344c2c1c1c1c1ea84c4c4c1c0c1c0ea84c0c4c0e82801c072207c1b00c7c131304c9c04c4c01c07220bc1b00c030001c1c01c1c1ca0a8aa2b47c2c7d2b0b07070707aa2b1f031f2b0307070707aa4f3f3fa81c07070722a0ac2b0ac2b0ac9c07c9c01c07220bc2f0bc2f00bc0be81eaaa81e8b9a982c1c1c1c1eaaaa80c1c1c1c1ea91d1e8a807070707aa47478be2a01c1c1c1ea8bcbcbcbcbcbcbcbcbcbcbcbe0783c5c5c0c0c1c0c5c5c3c3ea83c3c5c1c1c5c3e83c6d2b0b1b4ac2c4c0c1c0c3e80c3c3c03c3c0c13033f1343031701c0f204c4c4cacac1b0cc0c13131305c0703c82b2702b2702b06c0300c0081e0fa030307031781c1ea83c1c5c1c1c5c3e83c6d130b134cc2c4c5c0c1c0c5c3c3e80c3c3c3c3c4c0d1c4c0c5c1c1c5c3e83d0c4c13430cc6c6ccc0d1c4c4c0c5c0c1c0c3e80d2c9c0c1327030cc0c6c0c0c0c0c0d0c0d2c0e0783c4c5c01c13130f0f080f0f170707170fa0f1344c2c4d130b130307030fa03131313130313031701c0f203c3c03c3c07c1b00c7c131305c0703c813130132703306c0300c0081e0fa00705e0707080f07170707170fa0f1f4ac2cad1f0b170707170fa0f1f2b032b1f034f3f3f171701c170f0f203c3c3c3cac2b0ac2b05c0703c81f2702b2704f03f0fc0081e0f170707170fa0f0303030303a030303030300000000000000000081e05c5c0003c3c0005c1c1c5c3e83cad230b2b48c2c5c0c1c0c3e80cac4c0c0cac4c0c0c8c0cec0c00002700000001c0080000f03c0000008b0020783e801c1781c1c203c1c5c1c1c5c3e83c9d230b2748c2c5c0c1c0c3e80c9cec0c0c9c9c0c0c8c0cec0c5c0703c827027270230030ec171701c1c1c170f0f2a03c3c3c3c8c9c2f23270bc0c9c2f03270bc270bc270be07981c1c5c1e83d17441d50f46542d555549d8b55545c1c1c5c3e83c6c6c6c6d50344d5545c1c1c5c3e83c9c9c9c9d515b4551b1b1b1b81e0b81c1c5c1ea83d0742d90b42d0b130707130fa0f44c4c4c4c4c2d42c5c1c1c5c3e83c9c9c9c9c2d42c4c4c4c4c85c05c3c03d07c9c2c02c4c0c4c0c1c1e89c9c2c2c2c2e0782e07071707aa0f41d0b642d42c2d2762c2c5c1c07070b0b0b0f8a0b0b542c2c2c5c1c1c5c3e83c9c6c6c9c6c6c2d42c2c2c2c2c0cec2c2c4c2c0c5c1c1c5c3e83c9c9c9c9c2d42c2c2c2c0b0b06ccccc6e0783e0070717070a0f17170070717170f0f0a0f0f005c1c1c5c3e83c9c9c9c9d4d530b5354c2c5c1c1c5c3e83c9c9c9c9cec4cec0cec4cec0cecececec5c0703c809c8b272702727275b03b0ec81e2001c0170707170fa0f27272727170707170fa0f272727273b3b3b3b00000009c8b000005c007003c0802700b01000c0130020783e07071707a0f170707170fa0f2727170707170fa0f3b27273b3b3b170707170fa0f27273b3ba070781e8ba81c1c1c5c1c1c5c3e83c3d0f0b0f43c2c5c1c1c5c3e83c3c3c3c0c3c3c0d1d1c5c1c1c5c3e83c3c3c3c0f0f11d1c5c1c1c5c3e83c3c3c3c3c0f0f0f0bcbd1cbcbcbcbc2c2c01c170b170707175f8ac3cae5f0f55545055170707171b1b1b031b1b1b031b1b1b1b55171701c1754ac2b11506c1b05c070ac9c0ac9c01106c1b0005c5c0005c1c1c5cae2b0f2b8ac3c540141545c0c1c0c6c4c0c0c6c4c0c0c6c0c6c0d5400270000000000000009c00000000b0b00705c2c5c1c1c5c9e270f2789c3d555141545c0c1c0c6c6c0c0c6c6c0c0c6c0c6c0d545c0709c09c9c02f1100c1b05c5c0705d52308c8c9c454031b00c1b02309c 25 33554431 10 1023
def hc_58_24 : Nat → Nat := unpackHintV5 0x1e6 0x5c5c0c0c1c0c5c5eaaaaa85c1c1c5c6d1f0b1b47c2ea84c0c1c0e82a2a84c0c4c0c5c0704c4c4e207c1b204c4c4c1701c1f2701f1f0882b06c0300c00 18 262143 9 511
def nh_58 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_58_24 (Nat.sub p 768)) (hc_58_23 (Nat.sub p 736)) (Nat.blt p 768)) (Bool.rec (hc_58_22 (Nat.sub p 704)) (hc_58_21 (Nat.sub p 672)) (Nat.blt p 704)) (Nat.blt p 736)) (Bool.rec (Bool.rec (hc_58_20 (Nat.sub p 640)) (hc_58_19 (Nat.sub p 608)) (Nat.blt p 640)) (hc_58_18 (Nat.sub p 576)) (Nat.blt p 608)) (Nat.blt p 672)) (Bool.rec (Bool.rec (Bool.rec (hc_58_17 (Nat.sub p 544)) (hc_58_16 (Nat.sub p 512)) (Nat.blt p 544)) (hc_58_15 (Nat.sub p 480)) (Nat.blt p 512)) (Bool.rec (Bool.rec (hc_58_14 (Nat.sub p 448)) (hc_58_13 (Nat.sub p 416)) (Nat.blt p 448)) (hc_58_12 (Nat.sub p 384)) (Nat.blt p 416)) (Nat.blt p 480)) (Nat.blt p 576)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_58_11 (Nat.sub p 352)) (hc_58_10 (Nat.sub p 320)) (Nat.blt p 352)) (hc_58_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (Bool.rec (hc_58_8 (Nat.sub p 256)) (hc_58_7 (Nat.sub p 224)) (Nat.blt p 256)) (hc_58_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (hc_58_5 (Nat.sub p 160)) (hc_58_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_58_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_58_2 (Nat.sub p 64)) (hc_58_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_58_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)) (Nat.blt p 384)
def f_58 : Nat → Nat × Nat := unpackForestF 0xbfcaedf8956fd4bb7e1550062fdf4536f748b7c24dbdca280316ef52cb7926dbcd32de45b4018af7814db8d22ddc936e328b71848baca6dc6116e447f73924b9c12dc88cee407f72033b8c2200314edf2ab7015db7c2a802d7edd27b6d235b6d1edb44d4016b76c16d005abdac4f6d046b68b5bb4c1a5a2d4ed147b68135005a9d8c516c60916614db1822d8ed6ec76a76383fb1c19d8c1100169f6213db051ad848f6c126a00b4bafcae802d1ebd27b5d235aed1ed744d4016875b364ad91a56c4d6af69759b64acc9ad5ed0eaf2ab5815dabc2a80297eac6f956135a9da5d52df2a946953b43a9cb680295ea46a952234a75b5d42d52a126b4eb63a74a2d3c5369d08a00a4fa69b65344d6946d74b36ca591a52c4d6946c74a15d00523d1d5be8ead747567a3c2a51d58c0147f45c68a2cb2ca95be888b144155952b5d004fe854994013ba009bd044f281489401339f6384fa9f27d2fb2a5679de2c4ee952772ab3c3409dc2a4a958e71adf38d6b9c6b3ce415271ac72a14d9b6b1cdd58e6d28b2a04d9ac2acad17e6908b2b45b99c36cad15e646893204595a29cacd7e566af2b34f959a3cbc1525aad72d95496c2a4b558e560772bd6b95eb1cac0de540992a0400051bca11925008b280448e9a7c9ad924d46b1d34b92eb4474d1e486c9242358e9a1c74956448c9220458e927c855a23a48f1d23f8f2344785323c09b1e04c8e91bc74154012bf1b9548dc2a44b17e3528912c5b8ccb644b15e304891814489629c5c552256bf1616c895abc4ad3e282b91405c895a3c4c91a2526c0095b88a3e4441120469f0fb7c87d1ac08d2e1dae102347865be4328d6192690234381136c2b1f2154f90224f84eb840891e114f90223f81dafc1d1b2076b70606c81dabc14d72088c90403481da9c0b1c20509902237004abc00552010990005478a2fbfc511e28b6fe16c78a2bbf4511e28a6fc154789afbec5b1e26aef134f7c12e3e0571f1088f805c789a3bda959ed48cf11367880c3c6d3de3696f1b4778da1bc693de348ef1a3f78d1bbc4050012a6efc6477c32b90dbddd6a8e436b76e3e390d9dd96a8e436375a323ac195c84deea47c72133b90915c847ee6c58734a639a135cd098e4237720b7b9059dc96dee4045004a7b8c591b48dee21446d235b845f1b48cedfa446fca236918dbd2c8da36f6ecbe368d9db469edb95c6dc2e368d1db548cda136004a5b655a19c6ded7b6c6bd1ab38dadadae0ce3676a5b63528d5a9268ce36369eb43389bda5ae0ce26768d373389759c47ecfc6067c263388dd9c2dece167004a3b345917c8decc1445f235b2c5f17c8ceca1445f231b245917c6dec817c5f1b3af8d3d8a4b8c515c62c223141717c68ec3a6661d232f84d97c030beb5f5f5adafad5d7d6a6bea5f5f52bafa8fd7d46ebe014004a1af4d915eadebc35457ab5aecdf15eaceb9b545cc2a2bd58d716c8af26f5b9be2dc5f15e4ceb63545792fad2db1692d8af25759ab7acd59d5e48ab1d6f58eb3abc8d55e2deaf167578afabc55c0127eae16454eb7ab455153ad6ac17c54eb3aa8951542a8aa05454eb18024ed518d0a056f53e2c2815ad4d8e0a056751e2c28e551470aaa404f51c2a28158d402dea0167500afa8055d41ac6a004d0049ba7c59114ade9e154452b5a745f114ace9b9544dc2a22958d352c88a36f4c93e2645f1146ce98154451afa5a9b12d2d88a35749ab7a4d59d264dc932664992f24c9591426c8ac5f4562da2b15d210888ac534552fa2a96d1d2d88aa5745529a2a93d154968c15c45523a2c091154868a13400499a24590feade881543fab5a1adf10d2f87f5674252a212551090a87f56341ca21fd1ad04488821443fa31a04510fe8b67fa443fca21fd14c012567db683edb215f5bcf86b07c3542beb59eadf0f56e057d673bdac1ded50ef4a8779543bc2a15f58ceb69075b443ad2215f1ace669073344399221cc510af8c671348389a21c4910af8b66eb48375a21ba910dd28857c5336cb215edbcd98f857b6b35cbe15ed9cd54d86a4742bdb19a2dc8d12a857b5f33e3615ed6ccd4d865b7a32cb615ed5cc94b863c6431c1215ed4caf69e57b43306b798359cc146257a462fd3215e5bcbd4f8579672ed2a15e57cb94d8579572d92a16c910af29e5783f2cab1964918af07a583722bc1b80249ca269e5614528927954534a246e53a4529d1b94453ca226e51b5328d2314449c010be0085b27e3e110d3c884da4dc7c26d3e11093c988e04c14d2211b92a9549546e4416d23e3e11e91491b1847a3723cbe11053c8d8e044137225be112dc08948c441270042b80214c852ca3e36f20cb28f89bc8129a3e2371fd1b8f85bc7c26e3e1270042780212c78ad03c16515db78eb5a0752ca2ba6f1cd370ae974708c03814d15d1b8d55a06a4ca3525d1af3c0d48dc572de3236f191378c89146446e3216e15cae8c51805726e3027c171b98b8db05c6c02e24615c938b01b45809a2c02715c3300211c010862a3540e2b18a4d90384de283540e12f8708d44b6c825a5f12d1a8705bc496a81c15f11e2c08358c418c620c531053788297c4149a1c1350f1a4078d103c4881e1440e0938721bc3904a1c0560041f8020ec352aa195630c8b786457c0106e18034004198020ac25ac612a460ad2304a5bc252be1313609c9b04c1bc250ac0082708caa02758c212c809c6f07caa02717c1d2c809b6f06caa026d7c19ad00b67305eb182c5701368e0a24604c9b00207c0103601d6300e3780717c036de01b5f02eb40159cc0368e0424600d1b00619805ad00236f00c2b00205c010260003f 10 11
def ch_58 : Nat → Bool := dagCheckNodeV5 fullMask g_58 ep_58 6 63 bds_58 768 (dagTraceF fullMask rootStock 11 f_58) cur_58 nh_58
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV5 fullMask g_58 ep_58 6 63 768 bds_58 (dagTraceF fullMask rootStock 11 f_58) (cur_58 0) (nh_58 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_0 : treeBlockF 0 32 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_1 : treeBlockF 32 64 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_2 : treeBlockF 64 96 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_3 : treeBlockF 96 128 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_4 : treeBlockF 128 160 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_5 : treeBlockF 160 192 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_6 : treeBlockF 192 224 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_7 : treeBlockF 224 256 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_8 : treeBlockF 256 288 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_9 : treeBlockF 288 320 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_10 : treeBlockF 320 352 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_11 : treeBlockF 352 384 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_12 : treeBlockF 384 416 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_13 : treeBlockF 416 448 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_14 : treeBlockF 448 480 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_15 : treeBlockF 480 512 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_16 : treeBlockF 512 544 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_17 : treeBlockF 544 576 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_18 : treeBlockF 576 608 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_19 : treeBlockF 608 640 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_20 : treeBlockF 640 672 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_21 : treeBlockF 672 704 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_22 : treeBlockF 704 736 ch_58 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58_23 : treeBlockF 736 768 ch_58 = true := by decide +kernel
theorem nj_58_1 : ∀ i, 0 ≤ i → i < 64 → ch_58 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_58_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_58_1 h1 h2)
theorem nj_58_2 : ∀ i, 0 ≤ i → i < 96 → ch_58 i = true := block_join nj_58_1 (fun _ h1 h2 => treeBlockF_at nb_58_2 h1 h2)
theorem nj_58_3 : ∀ i, 0 ≤ i → i < 128 → ch_58 i = true := block_join nj_58_2 (fun _ h1 h2 => treeBlockF_at nb_58_3 h1 h2)
theorem nj_58_4 : ∀ i, 0 ≤ i → i < 160 → ch_58 i = true := block_join nj_58_3 (fun _ h1 h2 => treeBlockF_at nb_58_4 h1 h2)
theorem nj_58_5 : ∀ i, 0 ≤ i → i < 192 → ch_58 i = true := block_join nj_58_4 (fun _ h1 h2 => treeBlockF_at nb_58_5 h1 h2)
theorem nj_58_6 : ∀ i, 0 ≤ i → i < 224 → ch_58 i = true := block_join nj_58_5 (fun _ h1 h2 => treeBlockF_at nb_58_6 h1 h2)
theorem nj_58_7 : ∀ i, 0 ≤ i → i < 256 → ch_58 i = true := block_join nj_58_6 (fun _ h1 h2 => treeBlockF_at nb_58_7 h1 h2)
theorem nj_58_8 : ∀ i, 0 ≤ i → i < 288 → ch_58 i = true := block_join nj_58_7 (fun _ h1 h2 => treeBlockF_at nb_58_8 h1 h2)
theorem nj_58_9 : ∀ i, 0 ≤ i → i < 320 → ch_58 i = true := block_join nj_58_8 (fun _ h1 h2 => treeBlockF_at nb_58_9 h1 h2)
theorem nj_58_10 : ∀ i, 0 ≤ i → i < 352 → ch_58 i = true := block_join nj_58_9 (fun _ h1 h2 => treeBlockF_at nb_58_10 h1 h2)
theorem nj_58_11 : ∀ i, 0 ≤ i → i < 384 → ch_58 i = true := block_join nj_58_10 (fun _ h1 h2 => treeBlockF_at nb_58_11 h1 h2)
theorem nj_58_12 : ∀ i, 0 ≤ i → i < 416 → ch_58 i = true := block_join nj_58_11 (fun _ h1 h2 => treeBlockF_at nb_58_12 h1 h2)
theorem nj_58_13 : ∀ i, 0 ≤ i → i < 448 → ch_58 i = true := block_join nj_58_12 (fun _ h1 h2 => treeBlockF_at nb_58_13 h1 h2)
theorem nj_58_14 : ∀ i, 0 ≤ i → i < 480 → ch_58 i = true := block_join nj_58_13 (fun _ h1 h2 => treeBlockF_at nb_58_14 h1 h2)
theorem nj_58_15 : ∀ i, 0 ≤ i → i < 512 → ch_58 i = true := block_join nj_58_14 (fun _ h1 h2 => treeBlockF_at nb_58_15 h1 h2)
theorem nj_58_16 : ∀ i, 0 ≤ i → i < 544 → ch_58 i = true := block_join nj_58_15 (fun _ h1 h2 => treeBlockF_at nb_58_16 h1 h2)
theorem nj_58_17 : ∀ i, 0 ≤ i → i < 576 → ch_58 i = true := block_join nj_58_16 (fun _ h1 h2 => treeBlockF_at nb_58_17 h1 h2)
theorem nj_58_18 : ∀ i, 0 ≤ i → i < 608 → ch_58 i = true := block_join nj_58_17 (fun _ h1 h2 => treeBlockF_at nb_58_18 h1 h2)
theorem nj_58_19 : ∀ i, 0 ≤ i → i < 640 → ch_58 i = true := block_join nj_58_18 (fun _ h1 h2 => treeBlockF_at nb_58_19 h1 h2)
theorem nj_58_20 : ∀ i, 0 ≤ i → i < 672 → ch_58 i = true := block_join nj_58_19 (fun _ h1 h2 => treeBlockF_at nb_58_20 h1 h2)
theorem nj_58_21 : ∀ i, 0 ≤ i → i < 704 → ch_58 i = true := block_join nj_58_20 (fun _ h1 h2 => treeBlockF_at nb_58_21 h1 h2)
theorem nj_58_22 : ∀ i, 0 ≤ i → i < 736 → ch_58 i = true := block_join nj_58_21 (fun _ h1 h2 => treeBlockF_at nb_58_22 h1 h2)
theorem nj_58_23 : ∀ i, 0 ≤ i → i < 768 → ch_58 i = true := block_join nj_58_22 (fun _ h1 h2 => treeBlockF_at nb_58_23 h1 h2)
theorem nc_58 : ∀ i, 0 ≤ i → i < 768 → ch_58 i = true := nj_58_23
theorem lb_58 : LowerBin fullMask rootStock g_58 12 :=
  lowerDagV5 (kn_cons lb_23 (kn_cons lb_56 (kn_cons lb_54 (kn_cons lb_22 (kn_cons lb_51 (kn_cons lb_53 (kn_cons lb_55 (kn_cons lb_41 (kn_cons lb_50 (kn_cons lb_40 (kn_cons lb_19 (kn_cons lb_25 (kn_cons lb_57 (kn_cons lb_24 (kn_cons lb_27 (kn_cons lb_13 (kn_cons lb_30 (kn_cons lb_43 (kn_cons lb_18 (kn_cons lb_46 (kn_cons lb_52 (kn_cons lb_12 (kn_cons lb_35 (kn_cons lb_7 (kn_cons lb_45 (kn_cons lb_17 (kn_cons lb_14 (kn_cons lb_32 (kn_cons lb_15 (kn_cons lb_42 (kn_cons lb_6 (kn_cons lb_39 (kn_cons lb_38 (kn_cons lb_10 (kn_cons lb_3 (kn_cons lb_49 (kn_cons lb_33 (kn_nil)))))))))))))))))))))))))))))))))))))) rc_58 nc_58 (by decide +kernel)

def wg : List Gate := [⟨GateOp.and, [0, 4]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.or, [2, 12]⟩, ⟨GateOp.or, [6, 8]⟩, ⟨GateOp.and, [7, 13]⟩, ⟨GateOp.or, [9, 14]⟩, ⟨GateOp.or, [11, 15]⟩, ⟨GateOp.and, [16, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276676744 * 2 ^ 32 + 4171816960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276676744 * 2 ^ 32 + 4171816960)) (13 - 1) := by
  rw [show canon fullMask (4276676744 * 2 ^ 32 + 4171816960) = g_58 by decide]
  exact lb_58

end PEqualNP.Outside.L_meta_48601

theorem PEqualNP.Outside.L_meta_48601 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676744 * 2 ^ 32 + 4171816960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676744 * 2 ^ 32 + 4171816960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_48601.table2_from_lowerBin (4276676744 * 2 ^ 32 + 4171816960) 13 PEqualNP.Outside.L_meta_48601.root_lb PEqualNP.Outside.L_meta_48601.wg 18 rfl PEqualNP.Outside.L_meta_48601.wfits PEqualNP.Outside.L_meta_48601.weval
