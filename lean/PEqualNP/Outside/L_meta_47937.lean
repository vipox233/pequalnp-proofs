import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_47937

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

def m_0 : Nat := 0xff000000000000
def s_0 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_0 : Nat := 0x17000000000000
def ep_0 : Nat := 0x600000000000000120000000000000014000000000000
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

def m_1 : Nat := 0xff0000000000
def s_1 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_1 : Nat := 0x170000000000
def ep_1 : Nat := 0x6000000000000001200000000000000140000000000
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

def m_2 : Nat := 0xc000c000c000c0
def s_2 : List Nat := [0x40004000400040, 0xc0000000c0, 0xc000c0]
def g_2 : Nat := 0x40004000c0
def ep_2 : Nat := 0x40008000000040000000800000000000000000000000000000000000000000000000000000004000400000
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

def m_3 : Nat := 0xf0f0000
def s_3 : List Nat := [0x5050000, 0x3030000, 0xf0000]
def g_3 : Nat := 0x1070000
def ep_3 : Nat := 0x60000000000000000000000000000010200000000000001040000
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

def m_4 : Nat := 0x33330000
def s_4 : List Nat := [0x11110000, 0x3030000, 0x330000]
def g_4 : Nat := 0x1130000
def ep_4 : Nat := 0x120000000000000102000000000000000000000000000001100000
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

def m_8 : Nat := 0x4444444400000000
def s_8 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_8 : Nat := 0x4044400000000
def ep_8 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
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

def m_10 : Nat := 0x5050505000000000
def s_10 : List Nat := [0x1010101000000000, 0x50005000000000, 0x505000000000]
def g_10 : Nat := 0x10105000000000
def ep_10 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000000000000000000
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

def m_11 : Nat := 0xa0a0a0a
def s_11 : List Nat := [0x2020202, 0xa000a, 0xa0a]
def g_11 : Nat := 0x2020a
def ep_11 : Nat := 0x2080000000000020008000000000000000000000000000202000000000000000000
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

def m_12 : Nat := 0xc0c0c0c
def s_12 : List Nat := [0x4040404, 0xc000c, 0xc0c]
def g_12 : Nat := 0x4040c
def ep_12 : Nat := 0x4080000000000040008000000000000000000000000000000000000000000040400
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

def m_13 : Nat := 0x30303030
def s_13 : List Nat := [0x10101010, 0x300030, 0x3030]
def g_13 : Nat := 0x101030
def ep_13 : Nat := 0x10200000000000100020000000000000000000000000000000000000000000101000
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

def m_14 : Nat := 0xc0c0c0c0
def s_14 : List Nat := [0x40404040, 0xc000c0, 0xc0c0]
def g_14 : Nat := 0x4040c0
def ep_14 : Nat := 0x40800000000000400080000000000000000000000000000000000000000000404000
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

def m_15 : Nat := 0xc0c00000c0c0
def s_15 : List Nat := [0x404000004040, 0xc0000000c0, 0xc0c0]
def g_15 : Nat := 0x40000040c0
def ep_15 : Nat := 0x408000000000000000000000004000000080000000000000000000000000000000000000004000004000
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

def m_16 : Nat := 0x22222222
def s_16 : List Nat := [0x2020202, 0x220022, 0x2222]
def g_16 : Nat := 0x20222
def ep_16 : Nat := 0x2200000000000020020000000000002020000000000000000000000000000000000
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

def m_17 : Nat := 0xf000f00
def s_17 : List Nat := [0x5000500, 0x3000300, 0xf00]
def g_17 : Nat := 0x1000700
def ep_17 : Nat := 0x6000000000000000000000000000000000000000000010002000000000001000400
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

def m_18 : Nat := 0x5555000000000000
def s_18 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_18 : Nat := 0x115000000000000
def ep_18 : Nat := 0x14000000000000010400000000000001100000000000000000000000000000
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

def m_19 : Nat := 0xf0f000000000000
def s_19 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_19 : Nat := 0x107000000000000
def ep_19 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
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

def m_20 : Nat := 0x3333000000000000
def s_20 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_20 : Nat := 0x113000000000000
def ep_20 : Nat := 0x12000000000000010200000000000000000000000000000110000000000000
def bds_20 : List (Nat × List Nat × Nat × Nat) := []
def cur_20 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_20 : Nat → Nat := fun _ => 0
def f_20 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_20 : Nat → Bool := dagCheckNodeV5 m_20 g_20 ep_20 1 1 bds_20 1 (dagTraceF m_20 s_20 3 f_20) cur_20 nh_20
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV5 m_20 g_20 ep_20 1 1 1 bds_20 (dagTraceF m_20 s_20 3 f_20) (cur_20 0) (nh_20 0) s_20 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_20 : treeBlockF 0 1 ch_20 = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 1 → ch_20 i = true := fun _ h1 h2 => treeBlockF_at nb_20 h1 h2
theorem lb_20 : LowerBin m_20 s_20 g_20 4 :=
  lowerDagV5 (kn_nil) rc_20 nc_20 (by decide +kernel)

def m_21 : Nat := 0x33003300
def s_21 : List Nat := [0x11001100, 0x3000300, 0x3300]
def g_21 : Nat := 0x1001300
def ep_21 : Nat := 0x12000000000000000000000000000100020000000000000000000000000001001000
def bds_21 : List (Nat × List Nat × Nat × Nat) := []
def cur_21 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_21 : Nat → Nat := fun _ => 0
def f_21 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_21 : Nat → Bool := dagCheckNodeV5 m_21 g_21 ep_21 1 1 bds_21 1 (dagTraceF m_21 s_21 3 f_21) cur_21 nh_21
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV5 m_21 g_21 ep_21 1 1 1 bds_21 (dagTraceF m_21 s_21 3 f_21) (cur_21 0) (nh_21 0) s_21 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21 : treeBlockF 0 1 ch_21 = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 1 → ch_21 i = true := fun _ h1 h2 => treeBlockF_at nb_21 h1 h2
theorem lb_21 : LowerBin m_21 s_21 g_21 4 :=
  lowerDagV5 (kn_nil) rc_21 nc_21 (by decide +kernel)

def m_22 : Nat := 0xa0a0a0aa0a0a0a0
def s_22 : List Nat := [0x202020220202020, 0xa0a0a0a0, 0xa000a00a000a0, 0xa0a0000a0a0]
def g_22 : Nat := 0x20202000000a0
def ep_22 : Nat := 0x200000000a000020000000000a0000000000000000000020202000000000000000000000000
def bds_22 : List (Nat × List Nat × Nat × Nat) := []
def cc_22_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xc8390320621b87702e05c0b81512a0540a8150271cc198130250c4388110220440788f01e03c0780d8c1d001 0x1c0f0e03079283a921b130c89860442e16160909a98484c22220d0f068583d3c1c9a0c13050982444101e070d022980c4c04224d8fe64771e378d19c54fe2276fd377c99bd4bde256dd276691b20fd887abc3b541ba10d4f866682f2a159409c80462c1f0c0d8505c0826000f 11 2047 5 31 10 1023 17 131071
def cc_22_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c2613094c8640fd7c3e1d4e16cab950a1502653091369a0b4582c12890481d0381001 0xd930d410ef48eb40d120e43ce030da30d42cd23488448836c0356c2e4c22301e1012c044903c8c3cba4cb640b14cad40883c9930903c9a308c3c91308c30a63ea2329d3e9532883e803d804c 9 511 3 7 10 1023 16 65535
def cc_22_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x102040810202440810204081004 0x96a64a5024899204087264290208990040 7 127 3 7 10 1023 17 131071
def cur_22 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_22_2 (Nat.sub p 64)) (cc_22_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_22_0 p) (Nat.blt p 32)
def hc_22_0 : Nat → Nat := unpackHintV5 0xb815822c015c2a6451127892c89224429f94f827823a11b10d426243101804b0854228112108843a51828b845442620f200b8002 0x0 13 8191 5 31
def hc_22_1 : Nat → Nat := unpackHintV5 0xd095d5a92d4049464622208f1070436118189944631e28e846863021708a8850222310088003c21e00f007803c01a20448184006 0x0 13 8191 5 31
def hc_22_2 : Nat → Nat := unpackHintV5 0x3a4999cc445c32d0958898a3a9144869c2c4103070828800a 0x0 13 8191 5 31
def nh_22 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_22_2 (Nat.sub p 64)) (hc_22_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_22_0 p) (Nat.blt p 32)
def f_22 : Nat → Nat × Nat := unpackForestF 0xc7e063b90a64850240992040031b818cc0a7e053b81264090200990040029b814cc0a5e052b71a438d01c078e0300293b58c1a858d2340291810fc087ac044021dab9315c80ad4c56a0010dd147c8a32449f268c112648d304618220f8086a804c02199b4a0da4870183626010bcb09858442c16160900856042722a61113088880423189e0c4d06858304c020f8713038881c3c0e1a0106c082e094c0426021100826000f 7 10
def ch_22 : Nat → Bool := dagCheckNodeV5 m_22 g_22 ep_22 1 1 bds_22 78 (dagTraceF m_22 s_22 5 f_22) cur_22 nh_22
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV5 m_22 g_22 ep_22 1 1 78 bds_22 (dagTraceF m_22 s_22 5 f_22) (cur_22 0) (nh_22 0) s_22 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_22_0 : treeBlockF 0 32 ch_22 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_22_1 : treeBlockF 32 64 ch_22 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_22_2 : treeBlockF 64 78 ch_22 = true := by decide +kernel
theorem nj_22_1 : ∀ i, 0 ≤ i → i < 64 → ch_22 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_22_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_22_1 h1 h2)
theorem nj_22_2 : ∀ i, 0 ≤ i → i < 78 → ch_22 i = true := block_join nj_22_1 (fun _ h1 h2 => treeBlockF_at nb_22_2 h1 h2)
theorem nc_22 : ∀ i, 0 ≤ i → i < 78 → ch_22 i = true := nj_22_2
theorem lb_22 : LowerBin m_22 s_22 g_22 6 :=
  lowerDagV5 (kn_nil) rc_22 nc_22 (by decide +kernel)

def m_23 : Nat := 0xff00ff0000000000
def s_23 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_23 : Nat := 0x100170000000000
def ep_23 : Nat := 0x1600000000000000000000000000010006000000000001001200000000000100140000000000
def bds_23 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7), (m_1, s_1, 4, g_1), (m_5, s_5, 4, g_5), (m_6, s_6, 4, g_6)]
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
  lowerDagV5 (kn_cons lb_7 (kn_cons lb_1 (kn_cons lb_5 (kn_cons lb_6 (kn_nil))))) rc_23 nc_23 (by decide +kernel)

def m_24 : Nat := 0xffff000000000000
def s_24 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_24 : Nat := 0x117000000000000
def ep_24 : Nat := 0x16000000000000010600000000000001120000000000000114000000000000
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_19, s_19, 4, g_19), (m_0, s_0, 4, g_0), (m_18, s_18, 4, g_18), (m_20, s_20, 4, g_20)]
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
  lowerDagV5 (kn_cons lb_19 (kn_cons lb_0 (kn_cons lb_18 (kn_cons lb_20 (kn_nil))))) rc_24 nc_24 (by decide +kernel)

def m_25 : Nat := 0xffff00000000
def s_25 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_25 : Nat := 0x175700000000
def ep_25 : Nat := 0x4000000000000006020000000000001202000000000000145400000000
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_25 : Nat → List (Nat × Nat) := fun _ => []
def nh_25 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_25 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV5 m_25 g_25 ep_25 1 1 0 bds_25 (dagTraceF m_25 s_25 4 f_25) (cur_25 0) (nh_25 0) s_25 4 = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_25 g_25 ep_25 1 1 bds_25 0 (dagTraceF m_25 s_25 4 f_25) cur_25 nh_25 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_25 : LowerBin m_25 s_25 g_25 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_25 nc_25 (by decide +kernel)

def m_26 : Nat := 0xf0f0f0f000000000
def s_26 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_26 : Nat := 0x10105000000000
def ep_26 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000010105000000000
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_26 : Nat → List (Nat × Nat) := fun _ => []
def nh_26 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_26 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV5 m_26 g_26 ep_26 1 1 0 bds_26 (dagTraceF m_26 s_26 4 f_26) (cur_26 0) (nh_26 0) s_26 4 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_26 g_26 ep_26 1 1 bds_26 0 (dagTraceF m_26 s_26 4 f_26) cur_26 nh_26 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_26 : LowerBin m_26 s_26 g_26 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_26 nc_26 (by decide +kernel)

def m_27 : Nat := 0xcccccccc00000000
def s_27 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_27 : Nat := 0x4044400000000
def ep_27 : Nat := 0x440000000000004004000000000000404000000000000000000000000000004044400000000
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_27 : Nat → List (Nat × Nat) := fun _ => []
def nh_27 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_27 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV5 m_27 g_27 ep_27 1 1 0 bds_27 (dagTraceF m_27 s_27 4 f_27) (cur_27 0) (nh_27 0) s_27 4 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_27 g_27 ep_27 1 1 bds_27 0 (dagTraceF m_27 s_27 4 f_27) cur_27 nh_27 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_27 nc_27 (by decide +kernel)

def m_28 : Nat := 0x5050505050505050
def s_28 : List Nat := [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050]
def g_28 : Nat := 0x10105000505050
def ep_28 : Nat := 0x40400000001040000050000010004000500000000000000000000000101000000000000000000000000000
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_28 : Nat → List (Nat × Nat) := fun _ => []
def nh_28 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_28 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV5 m_28 g_28 ep_28 1 1 0 bds_28 (dagTraceF m_28 s_28 4 f_28) (cur_28 0) (nh_28 0) s_28 4 = true := by decide +kernel
theorem nc_28 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_28 g_28 ep_28 1 1 bds_28 0 (dagTraceF m_28 s_28 4 f_28) cur_28 nh_28 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_28 : LowerBin m_28 s_28 g_28 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_28 nc_28 (by decide +kernel)

def m_29 : Nat := 0x5555555500000000
def s_29 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_29 : Nat := 0x115155500000000
def ep_29 : Nat := 0x1440000000000014004000000000010404000000000001101000000000000000000000000000
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5), (m_18, s_18, 4, g_18), (m_10, s_10, 4, g_10), (m_8, s_8, 4, g_8)]
def cc_29_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_29_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_29 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_29_1 (Nat.sub p 32)) (cc_29_0 p) (Nat.blt p 32)
def hc_29_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e02200586415a60dad5545a0ad39b942665566b5910608437408a0203a61035944 15 32767 6 63
def hc_29_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e7540e571014d8c00562302 13 8191 6 63
def nh_29 : Nat → Nat := fun p => Bool.rec (hc_29_1 (Nat.sub p 32)) (hc_29_0 p) (Nat.blt p 32)
def f_29 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_29 : Nat → Bool := dagCheckNodeV5 m_29 g_29 ep_29 1 1 bds_29 43 (dagTraceF m_29 s_29 6 f_29) cur_29 nh_29
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV5 m_29 g_29 ep_29 1 1 43 bds_29 (dagTraceF m_29 s_29 6 f_29) (cur_29 0) (nh_29 0) s_29 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_0 : treeBlockF 0 32 ch_29 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_1 : treeBlockF 32 43 ch_29 = true := by decide +kernel
theorem nj_29_1 : ∀ i, 0 ≤ i → i < 43 → ch_29 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_29_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_29_1 h1 h2)
theorem nc_29 : ∀ i, 0 ≤ i → i < 43 → ch_29 i = true := nj_29_1
theorem lb_29 : LowerBin m_29 s_29 g_29 7 :=
  lowerDagV5 (kn_cons lb_5 (kn_cons lb_18 (kn_cons lb_10 (kn_cons lb_8 (kn_nil))))) rc_29 nc_29 (by decide +kernel)

def m_30 : Nat := 0x666600006666
def s_30 : List Nat := [0x222200002222, 0x60600000606, 0x6600000066, 0x6666]
def g_30 : Nat := 0x64600004666
def ep_30 : Nat := 0x402000000000000000000000004000000020000006020000020000000000000000000000000000000000
def bds_30 : List (Nat × List Nat × Nat × Nat) := []
def cur_30 : Nat → List (Nat × Nat) := unpackCursorV5 0x16ac58b12a44890e8701 0x1924309193c2050d3c205263d88d5d2a549902a109800f 7 127 3 7 10 1023 14 16383
def nh_30 : Nat → Nat := unpackHintV5 0x340d0340d0302c0300c02c215002 0x0 10 1023 5 31
def f_30 : Nat → Nat × Nat := unpackForestF 0xc7a63529564f0a4c42a49e205084c00f 3 10
def ch_30 : Nat → Bool := dagCheckNodeV5 m_30 g_30 ep_30 1 1 bds_30 10 (dagTraceF m_30 s_30 4 f_30) cur_30 nh_30
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV5 m_30 g_30 ep_30 1 1 10 bds_30 (dagTraceF m_30 s_30 4 f_30) (cur_30 0) (nh_30 0) s_30 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30 : treeBlockF 0 10 ch_30 = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 10 → ch_30 i = true := fun _ h1 h2 => treeBlockF_at nb_30 h1 h2
theorem lb_30 : LowerBin m_30 s_30 g_30 5 :=
  lowerDagV5 (kn_nil) rc_30 nc_30 (by decide +kernel)

def m_31 : Nat := 0x66006600660066
def s_31 : List Nat := [0x22002200220022, 0x6000600060006, 0x6600000066, 0x660066]
def g_31 : Nat := 0x6004600460066
def ep_31 : Nat := 0x40002000000040000000200000000000000000000600020002000000000000000000000000000000000000
def bds_31 : List (Nat × List Nat × Nat × Nat) := []
def cur_31 : Nat → List (Nat × Nat) := unpackCursorV5 0x16ac58b12a44890e8701 0x1924309193c2050d3c205263d88d5d2a549902a109800f 7 127 3 7 10 1023 14 16383
def nh_31 : Nat → Nat := unpackHintV5 0x340d0340d0302c0300c02c215002 0x0 10 1023 5 31
def f_31 : Nat → Nat × Nat := unpackForestF 0xc7a63529564f0a4c42a49e205084c00f 3 10
def ch_31 : Nat → Bool := dagCheckNodeV5 m_31 g_31 ep_31 1 1 bds_31 10 (dagTraceF m_31 s_31 4 f_31) cur_31 nh_31
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV5 m_31 g_31 ep_31 1 1 10 bds_31 (dagTraceF m_31 s_31 4 f_31) (cur_31 0) (nh_31 0) s_31 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31 : treeBlockF 0 10 ch_31 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 10 → ch_31 i = true := fun _ h1 h2 => treeBlockF_at nb_31 h1 h2
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagV5 (kn_nil) rc_31 nc_31 (by decide +kernel)

def m_32 : Nat := 0x3030303030303030
def s_32 : List Nat := [0x1010101010101010, 0x30003000300030, 0x303000003030, 0x30303030]
def g_32 : Nat := 0x10101000101030
def ep_32 : Nat := 0x2000001000000010200010000000100020000000000000000000000000000000000010101000101000
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
def cur_32 : Nat → List (Nat × Nat) := fun _ => []
def nh_32 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_32 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV5 m_32 g_32 ep_32 1 1 0 bds_32 (dagTraceF m_32 s_32 4 f_32) (cur_32 0) (nh_32 0) s_32 4 = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_32 g_32 ep_32 1 1 bds_32 0 (dagTraceF m_32 s_32 4 f_32) cur_32 nh_32 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_32 : LowerBin m_32 s_32 g_32 5 :=
  lowerDagV5 (kn_cons lb_13 (kn_nil)) rc_32 nc_32 (by decide +kernel)

def m_33 : Nat := 0xc0c0c0c0c0c0c0c0
def s_33 : List Nat := [0x4040404040404040, 0xc000c000c000c0, 0xc0c00000c0c0, 0xc0c0c0c0]
def g_33 : Nat := 0x40004040c0
def ep_33 : Nat := 0x40408000000040000040800000004000400080000000000000000000000000000000000000004000404000
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15), (m_14, s_14, 4, g_14), (m_9, s_9, 4, g_9), (m_2, s_2, 4, g_2)]
def cc_33_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_33_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_33 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_33_1 (Nat.sub p 32)) (cc_33_0 p) (Nat.blt p 32)
def hc_33_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_33_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_33 : Nat → Nat := fun p => Bool.rec (hc_33_1 (Nat.sub p 32)) (hc_33_0 p) (Nat.blt p 32)
def f_33 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_33 : Nat → Bool := dagCheckNodeV5 m_33 g_33 ep_33 1 1 bds_33 43 (dagTraceF m_33 s_33 6 f_33) cur_33 nh_33
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV5 m_33 g_33 ep_33 1 1 43 bds_33 (dagTraceF m_33 s_33 6 f_33) (cur_33 0) (nh_33 0) s_33 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_0 : treeBlockF 0 32 ch_33 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_1 : treeBlockF 32 43 ch_33 = true := by decide +kernel
theorem nj_33_1 : ∀ i, 0 ≤ i → i < 43 → ch_33 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_33_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_33_1 h1 h2)
theorem nc_33 : ∀ i, 0 ≤ i → i < 43 → ch_33 i = true := nj_33_1
theorem lb_33 : LowerBin m_33 s_33 g_33 7 :=
  lowerDagV5 (kn_cons lb_15 (kn_cons lb_14 (kn_cons lb_9 (kn_cons lb_2 (kn_nil))))) rc_33 nc_33 (by decide +kernel)

def m_34 : Nat := 0x5555000055550000
def s_34 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_34 : Nat := 0x115000001550000
def ep_34 : Nat := 0x40000000000000000000000014000000540000010400000100000001100000010000000000000000000000
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 4, g_18)]
def cur_34 : Nat → List (Nat × Nat) := fun _ => []
def nh_34 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV5 m_34 g_34 ep_34 1 1 0 bds_34 (dagTraceF m_34 s_34 4 f_34) (cur_34 0) (nh_34 0) s_34 4 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_34 g_34 ep_34 1 1 bds_34 0 (dagTraceF m_34 s_34 4 f_34) cur_34 nh_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagV5 (kn_cons lb_18 (kn_nil)) rc_34 nc_34 (by decide +kernel)

def m_35 : Nat := 0x5500550055005500
def s_35 : List Nat := [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500]
def g_35 : Nat := 0x100150001005500
def ep_35 : Nat := 0x400000001400000054000000000000000000010004000100000001001000010000000000000000000000
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
def cur_35 : Nat → List (Nat × Nat) := fun _ => []
def nh_35 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_35 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV5 m_35 g_35 ep_35 1 1 0 bds_35 (dagTraceF m_35 s_35 4 f_35) (cur_35 0) (nh_35 0) s_35 4 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_35 g_35 ep_35 1 1 bds_35 0 (dagTraceF m_35 s_35 4 f_35) cur_35 nh_35 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_35 : LowerBin m_35 s_35 g_35 5 :=
  lowerDagV5 (kn_cons lb_5 (kn_nil)) rc_35 nc_35 (by decide +kernel)

def m_36 : Nat := 0xff000000ff00
def s_36 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_36 : Nat := 0x170000005700
def ep_36 : Nat := 0x400000000000000000000000000000000000000006000000020000001200000002000000140000005400
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_36 : Nat → List (Nat × Nat) := fun _ => []
def nh_36 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV5 m_36 g_36 ep_36 1 1 0 bds_36 (dagTraceF m_36 s_36 4 f_36) (cur_36 0) (nh_36 0) s_36 4 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_36 g_36 ep_36 1 1 bds_36 0 (dagTraceF m_36 s_36 4 f_36) cur_36 nh_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_36 nc_36 (by decide +kernel)

def m_37 : Nat := 0xf0f00000f0f0
def s_37 : List Nat := [0x505000005050, 0x303000003030, 0xf0000000f0, 0xf0f0]
def g_37 : Nat := 0x1050000050f0
def ep_37 : Nat := 0x40a0000000000000000000000040000000a0000000000000000000001000000000000000105000005000
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
def cur_37 : Nat → List (Nat × Nat) := fun _ => []
def nh_37 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV5 m_37 g_37 ep_37 1 1 0 bds_37 (dagTraceF m_37 s_37 4 f_37) (cur_37 0) (nh_37 0) s_37 4 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_37 g_37 ep_37 1 1 bds_37 0 (dagTraceF m_37 s_37 4 f_37) cur_37 nh_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 5 :=
  lowerDagV5 (kn_cons lb_15 (kn_nil)) rc_37 nc_37 (by decide +kernel)

def m_38 : Nat := 0x33333333
def s_38 : List Nat := [0x11111111, 0x3030303, 0x330033, 0x3333]
def g_38 : Nat := 0x1131333
def ep_38 : Nat := 0x12200000000000120020000000000102020000000000000000000000000001101000
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4), (m_21, s_21, 4, g_21), (m_13, s_13, 4, g_13), (m_16, s_16, 4, g_16)]
def cc_38_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_38_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_38 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_38_1 (Nat.sub p 32)) (cc_38_0 p) (Nat.blt p 32)
def hc_38_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e56655092040a6ad8c0011820539b81622002630805682cb74a008803a6b2b0810 15 32767 6 63
def hc_38_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e754ae0732b4dad55068b56 13 8191 6 63
def nh_38 : Nat → Nat := fun p => Bool.rec (hc_38_1 (Nat.sub p 32)) (hc_38_0 p) (Nat.blt p 32)
def f_38 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_38 : Nat → Bool := dagCheckNodeV5 m_38 g_38 ep_38 1 1 bds_38 43 (dagTraceF m_38 s_38 6 f_38) cur_38 nh_38
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV5 m_38 g_38 ep_38 1 1 43 bds_38 (dagTraceF m_38 s_38 6 f_38) (cur_38 0) (nh_38 0) s_38 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_0 : treeBlockF 0 32 ch_38 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_1 : treeBlockF 32 43 ch_38 = true := by decide +kernel
theorem nj_38_1 : ∀ i, 0 ≤ i → i < 43 → ch_38 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_38_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_38_1 h1 h2)
theorem nc_38 : ∀ i, 0 ≤ i → i < 43 → ch_38 i = true := nj_38_1
theorem lb_38 : LowerBin m_38 s_38 g_38 7 :=
  lowerDagV5 (kn_cons lb_4 (kn_cons lb_21 (kn_cons lb_13 (kn_cons lb_16 (kn_nil))))) rc_38 nc_38 (by decide +kernel)

def m_39 : Nat := 0xcc00cc00cc00cc
def s_39 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_39 : Nat := 0x40044004400cc
def ep_39 : Nat := 0x40008800000040000000880000000000000000000400000000000000000000000000000004004400440000
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cur_39 : Nat → List (Nat × Nat) := fun _ => []
def nh_39 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_39 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV5 m_39 g_39 ep_39 1 1 0 bds_39 (dagTraceF m_39 s_39 4 f_39) (cur_39 0) (nh_39 0) s_39 4 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_39 g_39 ep_39 1 1 bds_39 0 (dagTraceF m_39 s_39 4 f_39) cur_39 nh_39 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_39 : LowerBin m_39 s_39 g_39 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_39 nc_39 (by decide +kernel)

def m_40 : Nat := 0xf0f0f0f
def s_40 : List Nat := [0x5050505, 0x3030303, 0xf000f, 0xf0f]
def g_40 : Nat := 0x107070f
def ep_40 : Nat := 0x6080000000000060008000000000000000000000000010202000000000001040400
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3), (m_17, s_17, 4, g_17), (m_12, s_12, 4, g_12), (m_11, s_11, 4, g_11)]
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
  lowerDagV5 (kn_cons lb_3 (kn_cons lb_17 (kn_cons lb_12 (kn_cons lb_11 (kn_nil))))) rc_40 nc_40 (by decide +kernel)

def m_41 : Nat := 0xaaaaaaaa
def s_41 : List Nat := [0x22222222, 0xa0a0a0a, 0xaa00aa, 0xaaaa]
def g_41 : Nat := 0x202aa
def ep_41 : Nat := 0x2a800000000000200a8000000000002020000000000000202000000000000000000
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def nh_41 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV5 m_41 g_41 ep_41 1 1 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) (nh_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_41 g_41 ep_41 1 1 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 nh_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_41 nc_41 (by decide +kernel)

def m_42 : Nat := 0xff000000ff0000
def s_42 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_42 : Nat := 0x17000000570000
def ep_42 : Nat := 0x40000000000000000000000000000000000000000600000002000000120000000200000014000000540000
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_42 : Nat → List (Nat × Nat) := fun _ => []
def nh_42 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_42 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV5 m_42 g_42 ep_42 1 1 0 bds_42 (dagTraceF m_42 s_42 4 f_42) (cur_42 0) (nh_42 0) s_42 4 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_42 g_42 ep_42 1 1 bds_42 0 (dagTraceF m_42 s_42 4 f_42) cur_42 nh_42 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_42 nc_42 (by decide +kernel)

def m_43 : Nat := 0xf000f000f000f0
def s_43 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_43 : Nat := 0x100050005000f0
def ep_43 : Nat := 0x4000a000000040000000a00000000000000000000000000000000000100000000000000010005000500000
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cur_43 : Nat → List (Nat × Nat) := fun _ => []
def nh_43 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_43 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV5 m_43 g_43 ep_43 1 1 0 bds_43 (dagTraceF m_43 s_43 4 f_43) (cur_43 0) (nh_43 0) s_43 4 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_43 g_43 ep_43 1 1 bds_43 0 (dagTraceF m_43 s_43 4 f_43) cur_43 nh_43 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_43 : LowerBin m_43 s_43 g_43 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_43 nc_43 (by decide +kernel)

def m_44 : Nat := 0x5500aa005500aa
def s_44 : List Nat := [0xaa000000aa, 0x11002200110022, 0x5000a0005000a, 0x5500aa]
def g_44 : Nat := 0x150002005500aa
def ep_44 : Nat := 0x4000a800000000000000000000000000000000000400020000000000100002000000000000000000000000
def bds_44 : List (Nat × List Nat × Nat × Nat) := []
def cur_44 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58b12a44874e0701 0x1a4471b4371343927d8d5ed5949d1540f 7 127 3 7 6 63 10 1023
def nh_44 : Nat → Nat := unpackHintV5 0x340c0b00c02c2b02c0b02c015002 0x0 10 1023 5 31
def f_44 : Nat → Nat × Nat := unpackForestF 0xfa7536ed0caf472174aa0f 3 6
def ch_44 : Nat → Bool := dagCheckNodeV5 m_44 g_44 ep_44 1 1 bds_44 10 (dagTraceF m_44 s_44 4 f_44) cur_44 nh_44
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV5 m_44 g_44 ep_44 1 1 10 bds_44 (dagTraceF m_44 s_44 4 f_44) (cur_44 0) (nh_44 0) s_44 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_44 : treeBlockF 0 10 ch_44 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 10 → ch_44 i = true := fun _ h1 h2 => treeBlockF_at nb_44 h1 h2
theorem lb_44 : LowerBin m_44 s_44 g_44 5 :=
  lowerDagV5 (kn_nil) rc_44 nc_44 (by decide +kernel)

def m_45 : Nat := 0x4444444444444444
def s_45 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_45 : Nat := 0x4044400444444
def ep_45 : Nat := 0x40400000000440000044000004004000440000000404000000000000000000000000000000000000000000
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8)]
def cur_45 : Nat → List (Nat × Nat) := fun _ => []
def nh_45 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV5 m_45 g_45 ep_45 1 1 0 bds_45 (dagTraceF m_45 s_45 4 f_45) (cur_45 0) (nh_45 0) s_45 4 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_45 g_45 ep_45 1 1 bds_45 0 (dagTraceF m_45 s_45 4 f_45) cur_45 nh_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin m_45 s_45 g_45 5 :=
  lowerDagV5 (kn_cons lb_8 (kn_nil)) rc_45 nc_45 (by decide +kernel)

def m_46 : Nat := 0x55550000aaaa
def s_46 : List Nat := [0xaaaa, 0x111100002222, 0x50500000a0a, 0x55000000aa]
def g_46 : Nat := 0x1555000002aa
def ep_46 : Nat := 0x40000000a8000004000000020000001000000002000000000000000000
def bds_46 : List (Nat × List Nat × Nat × Nat) := []
def cur_46 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58b12a44874e0701 0xd2440c34d0c309343924cf626af2d592906842c00f 7 127 3 7 9 511 13 8191
def nh_46 : Nat → Nat := unpackHintV5 0x340c0b00c02c2b02c0b02c015002 0x0 10 1023 5 31
def f_46 : Nat → Nat × Nat := unpackForestF 0x33d33532dd3432573472421a21600f 3 9
def ch_46 : Nat → Bool := dagCheckNodeV5 m_46 g_46 ep_46 1 1 bds_46 10 (dagTraceF m_46 s_46 4 f_46) cur_46 nh_46
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV5 m_46 g_46 ep_46 1 1 10 bds_46 (dagTraceF m_46 s_46 4 f_46) (cur_46 0) (nh_46 0) s_46 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_46 : treeBlockF 0 10 ch_46 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 10 → ch_46 i = true := fun _ h1 h2 => treeBlockF_at nb_46 h1 h2
theorem lb_46 : LowerBin m_46 s_46 g_46 5 :=
  lowerDagV5 (kn_nil) rc_46 nc_46 (by decide +kernel)

def m_47 : Nat := 0x55005500aa00aa
def s_47 : List Nat := [0xaa00aa, 0x11001100220022, 0x50005000a000a, 0x55000000aa]
def g_47 : Nat := 0x150055000200aa
def ep_47 : Nat := 0x40000000a80000000000000000000400000002000000100000000200000000000000000000
def bds_47 : List (Nat × List Nat × Nat × Nat) := []
def cur_47 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58b12a44874e0701 0xd2440c34d0c309343924cf626af2d592906842c00f 7 127 3 7 9 511 13 8191
def nh_47 : Nat → Nat := unpackHintV5 0x340c0b00c02c2b02c0b02c015002 0x0 10 1023 5 31
def f_47 : Nat → Nat × Nat := unpackForestF 0x33d33532dd3432573472421a21600f 3 9
def ch_47 : Nat → Bool := dagCheckNodeV5 m_47 g_47 ep_47 1 1 bds_47 10 (dagTraceF m_47 s_47 4 f_47) cur_47 nh_47
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV5 m_47 g_47 ep_47 1 1 10 bds_47 (dagTraceF m_47 s_47 4 f_47) (cur_47 0) (nh_47 0) s_47 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_47 : treeBlockF 0 10 ch_47 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 10 → ch_47 i = true := fun _ h1 h2 => treeBlockF_at nb_47 h1 h2
theorem lb_47 : LowerBin m_47 s_47 g_47 5 :=
  lowerDagV5 (kn_nil) rc_47 nc_47 (by decide +kernel)

def m_48 : Nat := 0x2222222222222222
def s_48 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_48 : Nat := 0x2020200020222
def ep_48 : Nat := 0x2000000200000002200002000000020020000202020002020000000000000000000000000000000000
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16)]
def cur_48 : Nat → List (Nat × Nat) := fun _ => []
def nh_48 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_48 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV5 m_48 g_48 ep_48 1 1 0 bds_48 (dagTraceF m_48 s_48 4 f_48) (cur_48 0) (nh_48 0) s_48 4 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_48 g_48 ep_48 1 1 bds_48 0 (dagTraceF m_48 s_48 4 f_48) cur_48 nh_48 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_48 : LowerBin m_48 s_48 g_48 5 :=
  lowerDagV5 (kn_cons lb_16 (kn_nil)) rc_48 nc_48 (by decide +kernel)

def m_49 : Nat := 0xa0a0a0a0a0a0a0a
def s_49 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_49 : Nat := 0x202020002020a
def ep_49 : Nat := 0x800000200000002080002000000020008000000000000000000020202000202000000000000000000
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_49 : Nat → List (Nat × Nat) := fun _ => []
def nh_49 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_49 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV5 m_49 g_49 ep_49 1 1 0 bds_49 (dagTraceF m_49 s_49 4 f_49) (cur_49 0) (nh_49 0) s_49 4 = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_49 g_49 ep_49 1 1 bds_49 0 (dagTraceF m_49 s_49 4 f_49) cur_49 nh_49 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_49 : LowerBin m_49 s_49 g_49 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_49 nc_49 (by decide +kernel)

def m_50 : Nat := 0x5a5a00005a5a
def s_50 : List Nat := [0xa0a00000a0a, 0x121200001212, 0x5a0000005a, 0x5a5a]
def g_50 : Nat := 0x12520000525a
def ep_50 : Nat := 0x400800000000000000000000004000000008000000000000000000001202000002000000000000000000
def bds_50 : List (Nat × List Nat × Nat × Nat) := []
def cur_50 : Nat → List (Nat × Nat) := unpackCursorV5 0x16ac58b12a44890e8701 0x193430d19282090d28209263a88d9d3a54d903a10d800f 7 127 3 7 10 1023 14 16383
def nh_50 : Nat → Nat := unpackHintV5 0x340d0340d0302c0300c02c215002 0x0 10 1023 5 31
def f_50 : Nat → Nat × Nat := unpackForestF 0xc7463629d64a0a6c43a494209086c00f 3 10
def ch_50 : Nat → Bool := dagCheckNodeV5 m_50 g_50 ep_50 1 1 bds_50 10 (dagTraceF m_50 s_50 4 f_50) cur_50 nh_50
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV5 m_50 g_50 ep_50 1 1 10 bds_50 (dagTraceF m_50 s_50 4 f_50) (cur_50 0) (nh_50 0) s_50 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50 : treeBlockF 0 10 ch_50 = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 10 → ch_50 i = true := fun _ h1 h2 => treeBlockF_at nb_50 h1 h2
theorem lb_50 : LowerBin m_50 s_50 g_50 5 :=
  lowerDagV5 (kn_nil) rc_50 nc_50 (by decide +kernel)

def m_51 : Nat := 0x5a005a005a005a
def s_51 : List Nat := [0xa000a000a000a, 0x12001200120012, 0x5a0000005a, 0x5a005a]
def g_51 : Nat := 0x1200520052005a
def ep_51 : Nat := 0x40000800000040000000080000000000000000000000000000000000120002000200000000000000000000
def bds_51 : List (Nat × List Nat × Nat × Nat) := []
def cur_51 : Nat → List (Nat × Nat) := unpackCursorV5 0x16ac58b12a44890e8701 0x193430d19282090d28209263a88d9d3a54d903a10d800f 7 127 3 7 10 1023 14 16383
def nh_51 : Nat → Nat := unpackHintV5 0x340d0340d0302c0300c02c215002 0x0 10 1023 5 31
def f_51 : Nat → Nat × Nat := unpackForestF 0xc7463629d64a0a6c43a494209086c00f 3 10
def ch_51 : Nat → Bool := dagCheckNodeV5 m_51 g_51 ep_51 1 1 bds_51 10 (dagTraceF m_51 s_51 4 f_51) cur_51 nh_51
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV5 m_51 g_51 ep_51 1 1 10 bds_51 (dagTraceF m_51 s_51 4 f_51) (cur_51 0) (nh_51 0) s_51 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51 : treeBlockF 0 10 ch_51 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 10 → ch_51 i = true := fun _ h1 h2 => treeBlockF_at nb_51 h1 h2
theorem lb_51 : LowerBin m_51 s_51 g_51 5 :=
  lowerDagV5 (kn_nil) rc_51 nc_51 (by decide +kernel)

def m_52 : Nat := 0xc0c0c0c0c0c0c0c
def s_52 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_52 : Nat := 0x404040004040c
def ep_52 : Nat := 0x800000400000004080004000000040008000000000000000000000000000000000004040400040400
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cur_52 : Nat → List (Nat × Nat) := fun _ => []
def nh_52 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_52 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV5 m_52 g_52 ep_52 1 1 0 bds_52 (dagTraceF m_52 s_52 4 f_52) (cur_52 0) (nh_52 0) s_52 4 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_52 g_52 ep_52 1 1 bds_52 0 (dagTraceF m_52 s_52 4 f_52) cur_52 nh_52 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_52 : LowerBin m_52 s_52 g_52 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_52 nc_52 (by decide +kernel)

def m_53 : Nat := 0x55aa000055aa
def s_53 : List Nat := [0xaa000000aa, 0x112200001122, 0x50a0000050a, 0x55aa]
def g_53 : Nat := 0x1502000055aa
def ep_53 : Nat := 0x40a800000000000000000000000000000000000004020000000000001002000000000000000000000000
def bds_53 : List (Nat × List Nat × Nat × Nat) := []
def cur_53 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58b12a44874e0701 0x1a4471b4371343927d8d5ed5949d1540f 7 127 3 7 6 63 10 1023
def nh_53 : Nat → Nat := unpackHintV5 0x340c0b00c02c2b02c0b02c015002 0x0 10 1023 5 31
def f_53 : Nat → Nat × Nat := unpackForestF 0xfa7536ed0caf472174aa0f 3 6
def ch_53 : Nat → Bool := dagCheckNodeV5 m_53 g_53 ep_53 1 1 bds_53 10 (dagTraceF m_53 s_53 4 f_53) cur_53 nh_53
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV5 m_53 g_53 ep_53 1 1 10 bds_53 (dagTraceF m_53 s_53 4 f_53) (cur_53 0) (nh_53 0) s_53 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53 : treeBlockF 0 10 ch_53 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 10 → ch_53 i = true := fun _ h1 h2 => treeBlockF_at nb_53 h1 h2
theorem lb_53 : LowerBin m_53 s_53 g_53 5 :=
  lowerDagV5 (kn_nil) rc_53 nc_53 (by decide +kernel)

def m_54 : Nat := 0xaaaaaaaaaaaaaaaa
def s_54 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_54 : Nat := 0x20202000202aa
def ep_54 : Nat := 0xa800000200000002a800020000000200a8000202020002020000020202000202000000000000000000
def bds_54 : List (Nat × List Nat × Nat × Nat) := [(m_22, s_22, 6, g_22)]
def cur_54 : Nat → List (Nat × Nat) := fun _ => []
def nh_54 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_54 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV5 m_54 g_54 ep_54 1 1 0 bds_54 (dagTraceF m_54 s_54 5 f_54) (cur_54 0) (nh_54 0) s_54 5 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_54 g_54 ep_54 1 1 bds_54 0 (dagTraceF m_54 s_54 5 f_54) cur_54 nh_54 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_54 : LowerBin m_54 s_54 g_54 6 :=
  lowerDagV5 (kn_cons lb_22 (kn_nil)) rc_54 nc_54 (by decide +kernel)

def m_55 : Nat := 0x5555555555555555
def s_55 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_55 : Nat := 0x115155501555555
def ep_55 : Nat := 0x40400000001440000054000014004000540000010404000100000001101000010000000000000000000000
def bds_55 : List (Nat × List Nat × Nat × Nat) := [(m_29, s_29, 7, g_29)]
def cur_55 : Nat → List (Nat × Nat) := fun _ => []
def nh_55 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_55 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV5 m_55 g_55 ep_55 1 1 0 bds_55 (dagTraceF m_55 s_55 7 f_55) (cur_55 0) (nh_55 0) s_55 7 = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_55 g_55 ep_55 1 1 bds_55 0 (dagTraceF m_55 s_55 7 f_55) cur_55 nh_55 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_55 : LowerBin m_55 s_55 g_55 8 :=
  lowerDagV5 (kn_cons lb_29 (kn_nil)) rc_55 nc_55 (by decide +kernel)

def m_56 : Nat := 0xff00ff00ff00ff00
def s_56 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_56 : Nat := 0x100170001005700
def ep_56 : Nat := 0x400000001600000056000000000000000000010006000100020001001200010002000100140001005400
def bds_56 : List (Nat × List Nat × Nat × Nat) := [(m_23, s_23, 7, g_23)]
def cur_56 : Nat → List (Nat × Nat) := fun _ => []
def nh_56 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_56 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV5 m_56 g_56 ep_56 1 1 0 bds_56 (dagTraceF m_56 s_56 7 f_56) (cur_56 0) (nh_56 0) s_56 7 = true := by decide +kernel
theorem nc_56 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_56 g_56 ep_56 1 1 bds_56 0 (dagTraceF m_56 s_56 7 f_56) cur_56 nh_56 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_56 : LowerBin m_56 s_56 g_56 8 :=
  lowerDagV5 (kn_cons lb_23 (kn_nil)) rc_56 nc_56 (by decide +kernel)

def m_57 : Nat := 0xf0f0f0f0f0f0f0f0
def s_57 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_57 : Nat := 0x101050005050f0
def ep_57 : Nat := 0x4040a000001040000050a000100040005000a0000000000000000000101000000000000010105000505000
def bds_57 : List (Nat × List Nat × Nat × Nat) := [(m_33, s_33, 7, g_33)]
def cur_57 : Nat → List (Nat × Nat) := fun _ => []
def nh_57 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_57 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV5 m_57 g_57 ep_57 1 1 0 bds_57 (dagTraceF m_57 s_57 7 f_57) (cur_57 0) (nh_57 0) s_57 7 = true := by decide +kernel
theorem nc_57 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_57 g_57 ep_57 1 1 bds_57 0 (dagTraceF m_57 s_57 7 f_57) cur_57 nh_57 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_57 : LowerBin m_57 s_57 g_57 8 :=
  lowerDagV5 (kn_cons lb_33 (kn_nil)) rc_57 nc_57 (by decide +kernel)

def m_58 : Nat := 0x3333333333333333
def s_58 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_58 : Nat := 0x113131301131333
def ep_58 : Nat := 0x2000001200000012200012000000120020010202020102020000000000000000000110101001101000
def bds_58 : List (Nat × List Nat × Nat × Nat) := [(m_38, s_38, 7, g_38)]
def cur_58 : Nat → List (Nat × Nat) := fun _ => []
def nh_58 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_58 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV5 m_58 g_58 ep_58 1 1 0 bds_58 (dagTraceF m_58 s_58 7 f_58) (cur_58 0) (nh_58 0) s_58 7 = true := by decide +kernel
theorem nc_58 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_58 g_58 ep_58 1 1 bds_58 0 (dagTraceF m_58 s_58 7 f_58) cur_58 nh_58 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_58 : LowerBin m_58 s_58 g_58 8 :=
  lowerDagV5 (kn_cons lb_38 (kn_nil)) rc_58 nc_58 (by decide +kernel)

def m_59 : Nat := 0xcccccccccccccccc
def s_59 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_59 : Nat := 0x40444004444cc
def ep_59 : Nat := 0x40408800000440000044880004004000440088000404000000000000000000000000000004044400444400
def bds_59 : List (Nat × List Nat × Nat × Nat) := [(m_33, s_33, 7, g_33)]
def cur_59 : Nat → List (Nat × Nat) := fun _ => []
def nh_59 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_59 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_59 : dagCheckRootsV5 m_59 g_59 ep_59 1 1 0 bds_59 (dagTraceF m_59 s_59 7 f_59) (cur_59 0) (nh_59 0) s_59 7 = true := by decide +kernel
theorem nc_59 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_59 g_59 ep_59 1 1 bds_59 0 (dagTraceF m_59 s_59 7 f_59) cur_59 nh_59 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_59 : LowerBin m_59 s_59 g_59 8 :=
  lowerDagV5 (kn_cons lb_33 (kn_nil)) rc_59 nc_59 (by decide +kernel)

def m_60 : Nat := 0xff00ff00ff00ff
def s_60 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_60 : Nat := 0x170057005700ff
def ep_60 : Nat := 0x4000a800000040000000a80000000000000000000600020002000000120002000200000014005400540000
def bds_60 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_2, s_2, 4, g_2), (m_47, s_47, 5, g_47), (m_44, s_44, 5, g_44), (m_51, s_51, 5, g_51), (m_31, s_31, 5, g_31)]
def cc_60_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb42b2ac2b099660946509060480200801b56c1b06c1b06499064145501405014048920480d507001 0xfa443c0910b5e40d68eb5238958d95632970bb5c20d34c34510934b24528d749a5d2457050360409872341a4d0845e1f168645216d5850560c910292410d783b5a08d481a560415a034f78d1dba4f6691d714f5451d11373449ca84f2211c48370209c001f 10 1023 4 15 11 2047 18 262143
def cc_60_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x88441dae870b81b2bc5c2e1709548225108132180c0601e8e070381c0a85028028000000 0x3f4b9f15d909afa174b06bd84ce4a642537a28a404de022ecd7352bae125d02e8609724b9835ca5a6e2d16149b7a45b5aed8976326cd926ac2e4e8d260694c5ea22d4b14a46ad1956 9 511 3 7 11 2047 17 131071
def cc_60_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xc29a21100 0x884c854c534d8745204d8245 6 63 3 7 9 511 16 65535
def cur_60 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_60_2 (Nat.sub p 64)) (cc_60_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_60_0 p) (Nat.blt p 32)
def hc_60_0 : Nat → Nat := unpackHintV5 0xed09ca437c66c8cbb797602e815d00b90546b28c05180a3010cea180430084090411e883a0c6e18a2e944028804f089a111481f8c391838e801c0000 0x3fd3d13fdff0d555005103c000141540003e20019660000880f00fff13d3df7fc905550001103c43ffd0f53fdff2555400001440f055550410041000 15 32767 6 63
def hc_60_1 : Nat → Nat := unpackHintV5 0xd000d000af42af00ae02ae00ad029530950095009500744274007302730072025a305a005a005a00384438003800360434042c10260c200c023c020002000004 0x5b6d5fb555550c484155557dd754015d5555d757d4312150550f30c000004d4d30c0f0300000fff1f43df7fc341554440f10000f 16 65535 7 127
def hc_60_2 : Nat → Nat := unpackHintV5 0xd00c82c80c02030000 0x55fb6d555500 12 4095 6 63
def nh_60 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_60_2 (Nat.sub p 64)) (hc_60_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_60_0 p) (Nat.blt p 32)
def f_60 : Nat → Nat × Nat := unpackForestF 0x2204c82516114c821140b4f7a971e95d7a1740b4776131c14572531c0450293da35c68575a05d0291d925c5ed15835c5e914094f56d755a5d561700947471791c5a4c8d13034471491b5646558093736d78db5a3c910f02436d48da5636558092732970b3452ed70b2450213c935d24974915c0211c545e151686a341a4d0545214d585056020dc135e04d682a440a49013520495810560209c001f 7 11
def ch_60 : Nat → Bool := dagCheckNodeV5 m_60 g_60 ep_60 2 3 bds_60 69 (dagTraceF m_60 s_60 7 f_60) cur_60 nh_60
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsV5 m_60 g_60 ep_60 2 3 69 bds_60 (dagTraceF m_60 s_60 7 f_60) (cur_60 0) (nh_60 0) s_60 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_0 : treeBlockF 0 32 ch_60 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_1 : treeBlockF 32 64 ch_60 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_60_2 : treeBlockF 64 69 ch_60 = true := by decide +kernel
theorem nj_60_1 : ∀ i, 0 ≤ i → i < 64 → ch_60 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_60_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_60_1 h1 h2)
theorem nj_60_2 : ∀ i, 0 ≤ i → i < 69 → ch_60 i = true := block_join nj_60_1 (fun _ h1 h2 => treeBlockF_at nb_60_2 h1 h2)
theorem nc_60 : ∀ i, 0 ≤ i → i < 69 → ch_60 i = true := nj_60_2
theorem lb_60 : LowerBin m_60 s_60 g_60 8 :=
  lowerDagV5 (kn_cons lb_0 (kn_cons lb_2 (kn_cons lb_47 (kn_cons lb_44 (kn_cons lb_51 (kn_cons lb_31 (kn_nil))))))) rc_60 nc_60 (by decide +kernel)

def m_61 : Nat := 0xf0f0f0f0f0f0f0f
def s_61 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_61 : Nat := 0x10707070107070f
def ep_61 : Nat := 0x800000600000006080006000000060008000000000000000001020202010202000104040401040400
def bds_61 : List (Nat × List Nat × Nat × Nat) := [(m_40, s_40, 7, g_40)]
def cur_61 : Nat → List (Nat × Nat) := fun _ => []
def nh_61 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_61 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_61 : dagCheckRootsV5 m_61 g_61 ep_61 1 1 0 bds_61 (dagTraceF m_61 s_61 7 f_61) (cur_61 0) (nh_61 0) s_61 7 = true := by decide +kernel
theorem nc_61 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_61 g_61 ep_61 1 1 bds_61 0 (dagTraceF m_61 s_61 7 f_61) cur_61 nh_61 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_61 : LowerBin m_61 s_61 g_61 8 :=
  lowerDagV5 (kn_cons lb_40 (kn_nil)) rc_61 nc_61 (by decide +kernel)

def m_62 : Nat := 0xffff0000ffff0000
def s_62 : List Nat := [0x5555000055550000, 0x3333000033330000, 0xf0f00000f0f0000, 0xff000000ff0000, 0xffff0000]
def g_62 : Nat := 0x117000001570000
def ep_62 : Nat := 0x40000000000000000000000016000000560000010600000102000001120000010200000114000001540000
def bds_62 : List (Nat × List Nat × Nat × Nat) := [(m_24, s_24, 7, g_24)]
def cur_62 : Nat → List (Nat × Nat) := fun _ => []
def nh_62 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_62 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_62 : dagCheckRootsV5 m_62 g_62 ep_62 1 1 0 bds_62 (dagTraceF m_62 s_62 7 f_62) (cur_62 0) (nh_62 0) s_62 7 = true := by decide +kernel
theorem nc_62 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_62 g_62 ep_62 1 1 bds_62 0 (dagTraceF m_62 s_62 7 f_62) cur_62 nh_62 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_62 : LowerBin m_62 s_62 g_62 8 :=
  lowerDagV5 (kn_cons lb_24 (kn_nil)) rc_62 nc_62 (by decide +kernel)

def m_63 : Nat := 0xffff0000ffff
def s_63 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_63 : Nat := 0x1757000057ff
def ep_63 : Nat := 0x40a8000000000000000000000040000000a8000006020000020000001202000002000000145400005400
def bds_63 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1), (m_15, s_15, 4, g_15), (m_46, s_46, 5, g_46), (m_50, s_50, 5, g_50), (m_30, s_30, 5, g_30), (m_53, s_53, 5, g_53)]
def cc_63_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb42b2ac2b099660946509060480200801b56c1b06c1b06499064145501405014048920480d507001 0xfa443c0910b5e40d68eb5238958d95632970bb5c20d34c34510934b24528d749a5d2457050360409872341a4d0845e1f168645216d5850560c910292410d783b5a08d481a560415a034f78d1dba4f6691d714f5451d11373449ca84f2211c48370209c001f 10 1023 4 15 11 2047 18 262143
def cc_63_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x88441dae870b81b2bc5c2e1709548225108132180c0601e8e070381c0a85028028000000 0x3f4b9f15d909afa174b06bd84ce4a642537a28a404de022ecd7352bae125d02e8609724b9835ca5a6e2d16149b7a45b5aed8976326cd926ac2e4e8d260694c5ea22d4b14a46ad1956 9 511 3 7 11 2047 17 131071
def cc_63_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xc29a21100 0x884c854c534d8745204d8245 6 63 3 7 9 511 16 65535
def cur_63 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_63_2 (Nat.sub p 64)) (cc_63_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_63_0 p) (Nat.blt p 32)
def hc_63_0 : Nat → Nat := unpackHintV5 0xed09ca437c66c8cbb797602e815d00b90546b28c05180a3010cea180430084090411e883a0c6e18a2e944028804f089a111481f8c391838e801c0000 0x3fd3d13fdff0d555005103c000141540003e20019660000880f00fff13d3df7fc905550001103c43ffd0f53fdff2555400001440f055550410041000 15 32767 6 63
def hc_63_1 : Nat → Nat := unpackHintV5 0xd000d000af42af00ae02ae00ad029530950095009500744274007302730072025a305a005a005a00384438003800360434042c10260c200c023c020002000004 0x575d5f7555551c484155557cd354014d5554d357d4312150550fb2c000005d4db2c0f0b00000fff1f43df7fc741554440f10000f 16 65535 7 127
def hc_63_2 : Nat → Nat := unpackHintV5 0xd00c82c80c02030000 0x55f75d555500 12 4095 6 63
def nh_63 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_63_2 (Nat.sub p 64)) (hc_63_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_63_0 p) (Nat.blt p 32)
def f_63 : Nat → Nat × Nat := unpackForestF 0x2204c82516114c821140b4f7a971e95d7a1740b4776131c14572531c0450293da35c68575a05d0291d925c5ed15835c5e914094f56d755a5d561700947471791c5a4c8d13034471491b5646558093736d78db5a3c910f02436d48da5636558092732970b3452ed70b2450213c935d24974915c0211c545e151686a341a4d0545214d585056020dc135e04d682a440a49013520495810560209c001f 7 11
def ch_63 : Nat → Bool := dagCheckNodeV5 m_63 g_63 ep_63 2 3 bds_63 69 (dagTraceF m_63 s_63 7 f_63) cur_63 nh_63
set_option maxHeartbeats 0 in
theorem rc_63 : dagCheckRootsV5 m_63 g_63 ep_63 2 3 69 bds_63 (dagTraceF m_63 s_63 7 f_63) (cur_63 0) (nh_63 0) s_63 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_0 : treeBlockF 0 32 ch_63 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_1 : treeBlockF 32 64 ch_63 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63_2 : treeBlockF 64 69 ch_63 = true := by decide +kernel
theorem nj_63_1 : ∀ i, 0 ≤ i → i < 64 → ch_63 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_63_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_63_1 h1 h2)
theorem nj_63_2 : ∀ i, 0 ≤ i → i < 69 → ch_63 i = true := block_join nj_63_1 (fun _ h1 h2 => treeBlockF_at nb_63_2 h1 h2)
theorem nc_63 : ∀ i, 0 ≤ i → i < 69 → ch_63 i = true := nj_63_2
theorem lb_63 : LowerBin m_63 s_63 g_63 8 :=
  lowerDagV5 (kn_cons lb_1 (kn_cons lb_15 (kn_cons lb_46 (kn_cons lb_50 (kn_cons lb_30 (kn_cons lb_53 (kn_nil))))))) rc_63 nc_63 (by decide +kernel)

def g_64 : Nat := 0x1171757015757ff
def ep_64 : Nat := 0x4040a800001640000056a800160040005600a8010606020102020001121202010202000114145401545400
def bds_64 : List (Nat × List Nat × Nat × Nat) := [(m_62, s_62, 8, g_62), (m_60, s_60, 8, g_60), (m_29, s_29, 7, g_29), (m_61, s_61, 8, g_61), (m_63, s_63, 8, g_63), (m_58, s_58, 8, g_58), (m_38, s_38, 7, g_38), (m_57, s_57, 8, g_57), (m_56, s_56, 8, g_56), (m_59, s_59, 8, g_59), (m_33, s_33, 7, g_33), (m_54, s_54, 6, g_54), (m_23, s_23, 7, g_23), (m_40, s_40, 7, g_40), (m_49, s_49, 5, g_49), (m_48, s_48, 5, g_48), (m_24, s_24, 7, g_24), (m_28, s_28, 5, g_28), (m_34, s_34, 5, g_34), (m_45, s_45, 5, g_45), (m_35, s_35, 5, g_35), (m_43, s_43, 5, g_43), (m_42, s_42, 5, g_42), (m_39, s_39, 5, g_39), (m_26, s_26, 5, g_26), (m_41, s_41, 5, g_41), (m_51, s_51, 5, g_51), (m_30, s_30, 5, g_30), (m_52, s_52, 5, g_52), (m_32, s_32, 5, g_32), (m_27, s_27, 5, g_27), (m_36, s_36, 5, g_36), (m_50, s_50, 5, g_50), (m_31, s_31, 5, g_31), (m_53, s_53, 5, g_53), (m_44, s_44, 5, g_44)]
def cc_64_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xa23d102881440a00ce0a701341980cc025832c0940ca025011c38e046063011028804306103080820c1020030008003d0c0f8001 0xa63104e9bc252de1012707c35020088020240da64071370345bc180880bc53054b7826110128a608956040a301c5900d6de0616e0282201314c076de02844012298065580228d8d45fc662de2d15f138a788b5fc41ade1ad5f0a6a78434fc19a5e0ad1efd6877625fb892dd9c95eb24a75724faa125d3c91e9c4874c23fa491dd108de864673095f904adc2e55de52a6ea14f708a5b4251d97286c313f5d09daa64dd492669012f3dc9597249c602462f05f16c2d8b015c550a62604f1242587411c390861803f0b41d83c0dc1d0660c82f0581582809c0f0460581f0200d80c05c010260003f 13 8191 6 63 11 2047 21 2097151
def cc_64_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x7d3e1d4e85bac152a850a8132984c228d86834168a250248cc6029140844020090400400 0x2035a7ed61f6727ad822d62869be096f7849dd86a2208818126649dbb646ad919c7e64d21c36e6c9bda16f6249d785c5c1515935568d56237544dd1127511a1346848d291b48455c90b50 9 511 3 7 11 2047 18 262143
def cc_64_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xd1d0c9b3b0a9a1a09991898881807978786a4c48483a31302913100908010000 0x2f927ba112e45376558f946b4dc2c927ae112b4539e49e9c64a31927d7e9cd62a46ea49be816f9a49e584c9411239458e91642478c51df127895a21568 8 255 3 7 11 2047 18 262143
def cc_64_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xc8320c8311b8ee0b82c2b02b1ac2a1a4681a02719c2709c2709c26198251852106d8fc3c0e103800 0x1f125bf46c7d8c0f6981e49a3c034768dce8db9b9a03846e708dcd4581a0943625f6b4b6d295d9d29b8d6e6f8dcdd151b5b733134650691717e2a2dc2c57828a700d7dfdadbd357776a6ead3dcda5b934764686c4d0edeb7dad6bb1acf5d58eae37d4c6ba58cf4518e7e2fce45b9b8af1914d8d1a3096e 10 1023 4 15 11 2047 19 524287
def cc_64_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xbc6f0b0ea2a0a7194a418c612805e2709c06c592515312e092240902409020453140500c82100800 0x744693d1f9cd1a4e944978a0e48d266bf38a3470469335f9bd1a372346d46928de1b09248b64948f8d649241b034924916d9211d19c924ab6f936d724d9e3db1b312465249359fa62bf4bd64968fcc88d188bf471448d08902dbdc5a0c3a3b896d910d8219304214483088e0d020637b7b42 10 1023 4 15 11 2047 19 524287
def cc_64_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x8818808808427c45165004844804424214014003843613412e32a22a02242201e21c11a11a01241010e1083061060003 0x5eb40bd8a9780d301a7dfb4bbe68f76d0fd6b7f9d6beeacfd558f9e37f2c6be08cfb918f662feb45bd58af9314f09b1319205f0deb219d342f9e0573109e4011f041e5d030ad8ff351462d1a5c1648a4696c552251a44234b48f9671c2151a5917c8424906492091a58154af0a933142051a56d7f988a5008d2b0b23fa34aa288fc8d1f51a5457ca7ae0f48d298be3c92478248ee8d290a25184476469435f9d51a50154 12 4095 5 31 11 2047 19 524287
def cc_64_6 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc312b52c1b02849c6708d20374db260d625454150131449103c8691806018060180510140000000 0x1bc8c1e00862b70df690ee48374223b120dbafdb4d61d4906003074241b11fb5da439920bf061a3141c8905f030d3afd9ed21c4906734870241a75fb35a4379206e2417a0c1b4906746ece8dd9f5bb363765a3065021a99fb4abf68d64d08fd86dcb31a432120ca089760c3112264569c7ac38d1a71630e1c53 10 1023 4 15 11 2047 19 524287
def cc_64_7 : Nat → List (Nat × Nat) := unpackCursorV5 0xf43d0f43d0d9f60d468da024490213805f1785c2611806016249102400c430093204711844201000 0x80e7e7fd7e7f5647ec7e7c97e7e1447d8447cb438f56f8e56b8c5678ad638946f8846b8646784c638345f81c5b814577d4537c16e74c7f6a4517b36845920643707a358451204492044120439407824b431307947c78c7077b7042920762404181063b7076b58411207585469c504092074d7f69452743684012063370733483f9203f1203e9203e1407125b3d9307257c71d7070b703d120 10 1023 4 15 11 2047 20 1048575
def cc_64_8 : Nat → List (Nat × Nat) := unpackCursorV5 0xbf72cd8b1627cc991a0c06ed18b060c13a44878e1c2c50a0e1214201 0x8a47f80c518f9648e9548dc7c8d4708c97c8b9548b054804508a57f7fc52899648894487d7c875708697c85944850448457e8395482c7e821447f4508057e8057e 7 127 2 3 11 2047 20 1048575
def cc_64_9 : Nat → List (Nat × Nat) := unpackCursorV5 0x98a51942238821184210841e3781e0709c0701a2681a060971585605455054150540e7380d103400 0xa02549f85494c509ed7f944529e2649d2449c57c9bd709b27c9a2449984498d7e982549747e96a4493c5094d7e94d7e9567e9457e93d649347e9127e92a449204491343a3d6fa2d6ba0d679f5639dc6f9cc6b9ac679946397c5f9645b95c5791c5390a6e 10 1023 4 15 11 2047 20 1048575
def cc_64_10 : Nat → List (Nat × Nat) := unpackCursorV5 0x942418c62184601801f1785a464509400f13c0e1380d1340c1300751c043100310c0300c00300000 0xaf25cadb78ac364adc7cabb60ac36cabc74ae36fad36bacb67ab363aac60b956fb7567b5c62b4a6fb2a6bb1267afa63aea5baa257a9164a8134a717ca6134a8b6fa7b6ba6b67a5b63a516e9ec7f95451a4264a3254a247ca1c70a127c 10 1023 4 15 11 2047 20 1048575
def cc_64_11 : Nat → List (Nat × Nat) := unpackCursorV5 0xe8f4383c0d8ec343a0c8e42130078bc1e0d260b018084401c4e061301088031108804002 0xbf934be97cbd934bc934bb96cc256fc1567c036fbf36bbe367bd363bc35bbb357ba96eb9c68b8a3fb8233b7c70b3a69b0a61b6a3bb6237b5468b4246b3d70b325cb235bb1c70b0d70b025c 9 511 4 15 11 2047 20 1048575
def cc_64_12 : Nat → List (Nat × Nat) := unpackCursorV5 0xf8f1f0e9e8e1e0bdb8b8aaa89a988a887a787878787170541f18111009080100 0x19e4d338be66934cfedf9ddaf37b3e6763cc2dd95d93181a64e44c588991df3121a63e44c40898a98318afe2d5bc4aaf8854f2db76526fc94d79099f1d31e3438c38698559306be60564 8 255 3 7 10 1023 19 524287
def cc_64_13 : Nat → List (Nat × Nat) := unpackCursorV5 0x88211842107c9e1781d1741c1701a2681916058060162581515053148511441013c4b42841904001 0xdf568de24fdda43dd570dc568db256dae70da26cd934fd8d70d7e70d726cd626cd4b78d3364d4c7cd2b60d336cd2c74d536fd436bd3b67d2363d1c60dfd62deb6fdcb67dba6fd9a6bd8267d6a63d5a3bd1237d0164 10 1023 4 15 11 2047 20 1048575
def cc_64_14 : Nat → List (Nat × Nat) := unpackCursorV5 0x8ca3084a108421084201801c455d50505404c5304852044510405003c4f0384e0344d01244010004 0xefc7ceb844eea54eb054ec360ed15fec95beb957eb153f246ef126ff026bef267ee263ed848ea844e9964e897ce7964e6934e597ce4934e3934e295ce946fe8467e736fe636be5367e4363e334be2347e196edaa69d7a61e0a4be0247 10 1023 4 15 11 2047 20 1048575
def cc_64_15 : Nat → List (Nat × Nat) := unpackCursorV5 0x94b28221c4088110220402800f85f03e0744e81c0b80700d09a0321640c81712e05822484008008410001000 0x20a8a90423f8151dc068ddff46705d647f8a23fa111f92a8fc0547d89a3e99c1f32d8f89347bca23dc111ec268f55707a4ae3ce4d216adf0a56384e37c2318e0f8bf06c5b8322bbf914dfb6defd3637ddafbead6df26aef83537b5a7bd6d2de868ef334378e323b4111e14a8ec854 11 2047 5 31 11 2047 21 2097151
def cc_64_16 : Nat → List (Nat × Nat) := unpackCursorV5 0xa4290a0680a02628914e501404c5304c12148111441013c4e1290a0208801c452140320c03008402 0x10db4086e2a4340d21e69f0eb4b871a3c32d0e3f69f1eb4b8f1a3c6cd0e3249f1824b8b523c5690e2747f12a3b8891bc408ce1f0d90c0608542a424112102a90714482e284145120947f03a3b8111bc048ce09ac9032488051a40f5920669902564801184028f202ac900344 10 1023 4 15 11 2047 21 2097151
def cc_64_17 : Nat → List (Nat × Nat) := unpackCursorV5 0xc8baaaa1a0a0a099757070695a58515049414039383831222019181109080100 0x11f37c87438476d021c0e10d8608e1304771523a6f91cb6c8643846e0d2346c11ac7c8cc224629f22f69f175708b13e4529822a6f9140348993e448d6e238e110a7c 8 255 3 7 11 2047 21 2097151
def cc_64_18 : Nat → List (Nat × Nat) := unpackCursorV5 0x842017c5f07c1f070dc0701a268191641816016258151541504c93048520445103c8f03842c08002 0x12f14496e284b75925a2892c84495caa4ac1525426929156947384a05b24e2692614492c224924d24728d23570914ae4864d25f8bf2ec5b9722bcb114e556bf29b5b93dabc9ad4e4a69f2434b911a3c84d0e408f90f070 10 1023 4 15 11 2047 21 2097151
def cc_64_19 : Nat → List (Nat × Nat) := unpackCursorV5 0xa4348280ce19c1382704e08c9182304608c108a10401800f85f03c1780f01c13806c2d81a0b406420e010001 0x27f8c93eb649e9a04f5152796f93c3649dc1a4e719272089382649bab44d89926a6c93483499d324cb1a2634c942c6fa0e31d04dbe806c73f34f9f1a5cf6d1e766873aa6f9d131ce293e6f49736a479ad21cd08fe6647732237989198a013c4108e1a03f0941b8340bc1504f30154 11 2047 5 31 11 2047 21 2097151
def cc_64_20 : Nat → List (Nat × Nat) := unpackCursorV5 0xce730b96e0b82a48de308862084610625805c5705c15250540501041e47009420080110401000400 0xa96b1546dbe9f6cf3696f93cb5c5a59df22c6bb13b5509bd3a9ba6b2df2696b8acb3be058e690bf2585b8a02bbdc14e9b6dd3416f928b5c4e59ded2c74d038a641a52e992954f94b56fa52b3d269ba662df2416b894b3bd658dc62b6d5957a463451e4fe8e26746c70918b4bd45868b27745137a42b7d1959e898c53216f910b5c4459de82c6e215b688abd0e9ba622df2116b880b3bcc58e8408940834 10 1023 4 15 11 2047 21 2097151
def cc_64_21 : Nat → List (Nat × Nat) := unpackCursorV5 0x8007e17a27a07627607607417026656606033d23c03c0344267260241240221220109100100084080061060060022001 0xae09a57d592bd4995dd64adc985704f2b9ac95ba44b062a57e4febc2775d137ad899d85592b54895a044b36b7d9758eca8df64463b1a2fd8916ec38af59c539d0b7bf458ddc2bee415b6b4abb3254d8e29ebd14b57ca3a9650e720bf2b05b8cc2bbf014eb18dd3896f954b5c6459df72c758048abc2255a992ab4f95646faaa33d529ba6f2df2996b8c0b3bea58d78296ae947944b4be8586a729753147a92b454453ea128750570 12 4095 5 31 11 2047 21 2097151
def cc_64_22 : Nat → List (Nat × Nat) := unpackCursorV5 0xa8a829c6709c27098615842108420180200789a4338c0300b12c0b0284a024490204711842408002 0xb7dbe5a81c2dc68169870b48305b2982dc8a96db7cb69b65a01c2d806969340b4a2a5a20d2d569f6a34bb4da3da0d0ee069f6f34bb75a3daed0dde29ee514b6c0a3b3650d9027ebe13b5889ba9a4ced60d967860b302a592112c74a962a44b0a28582912c027f5f13baec9bd724cec0ac95e948 10 1023 4 15 11 2047 21 2097151
def cc_64_23 : Nat → List (Nat × Nat) := unpackCursorV5 0x9ac6b86a06a06816806806616606416406216016006006006005842982802612602412212202202201c304c040002000 0x17715fb90addb055eb42a73b85f9642dc6e15dfd0a69201f3ec0d99405c8d0278256ec0a37603153006dd76a6fb8d35dae99eb34c73b16f960b5c6c59dfc2c69192f3e89599249c8c2462e06b15831dfe0e2fe0680b82b0481181206c040277d844be01a5ed192f46c978b40bc62a5e0df2ef6c977034bf237df518ef96df7bb63bd5a7de6d2ef268f76b439d4b7bf658de229ee714b6dca3b3e50d9427ec013b5a49baa24cc5209e218470d81f84e0dc0d03e03817bad2a5d2912e68a173564b95225c8112ea8bf7445bb9e2bdc714de02bee615b6ccabb3a54d9229ebf14b594a3a9e50ee18f96a870 12 4095 5 31 11 2047 21 2097151
def cc_64_24 : Nat → List (Nat × Nat) := unpackCursorV5 0xb4eb04ac4a849ea9e09688ca87579e7547146d463a6305b851a4d440d3c42fd22d1d519414508c008000 0x3126df82341bf137d9a98e9647748237a14b7c2c58d84276b913751c97a3c4acf524e5b92351497a384acf324e5a92351097a364acf224e5a12350c97a344acf124e59923c61b662ed8294477462376089dadc4dd4125e8c12b3b89396248efb2bf66153a102fc2a14d3f03e8b01b3ac0b95e04efa4df65a63a0cb7c2858d3e25e8a92b3a89395c48f150918a044c0da027a4bd14256749272b491e251bf026857ca6fb2931d5892ea348f4116f84cb1ba452dbd28e9d92f448959ce49cab2469c92f440959ca49ca92469c12f43c959c849ca82469b92f438959c649ca724787c6cc3a3055492e9f48ee814b6e4a3a6a4bd0c2567012729491df057ec92a74085f84829a6607d0a0366e81728c09dee9bec84c74016f844b1a644bd092566e12728891e180e30b0689892f420959b649ca124784c6ebd537dd49aee04cf632639f8b7cbe5ae3f2cf079634bc97a0c4acd924e4f9234b897a0a4acd824e4f123c1db75e69bee84d76f267b1131cf85be5d2d71e967834b1a584bd032566b12727091e02d02f24df73a6bb7533d8698e7b2df2e16b8f0b3c1858d2b25e8112b3549393648f038dc9512f404959a849c9a2469492f400959a649c9924781c6e4a0979fe4acd224e4c123bc52fdcc96edc4af612539e8afcb656e3b2af0595349c979fc4acd124e4b923bc136db4996792db1c965498979fa4acd024e4b123 12 4095 4 15 11 2047 21 2097151
def cur_64 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_64_24 (Nat.sub p 768)) (cc_64_23 (Nat.sub p 736)) (Nat.blt p 768)) (Bool.rec (cc_64_22 (Nat.sub p 704)) (cc_64_21 (Nat.sub p 672)) (Nat.blt p 704)) (Nat.blt p 736)) (Bool.rec (Bool.rec (cc_64_20 (Nat.sub p 640)) (cc_64_19 (Nat.sub p 608)) (Nat.blt p 640)) (cc_64_18 (Nat.sub p 576)) (Nat.blt p 608)) (Nat.blt p 672)) (Bool.rec (Bool.rec (Bool.rec (cc_64_17 (Nat.sub p 544)) (cc_64_16 (Nat.sub p 512)) (Nat.blt p 544)) (cc_64_15 (Nat.sub p 480)) (Nat.blt p 512)) (Bool.rec (Bool.rec (cc_64_14 (Nat.sub p 448)) (cc_64_13 (Nat.sub p 416)) (Nat.blt p 448)) (cc_64_12 (Nat.sub p 384)) (Nat.blt p 416)) (Nat.blt p 480)) (Nat.blt p 576)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_64_11 (Nat.sub p 352)) (cc_64_10 (Nat.sub p 320)) (Nat.blt p 352)) (cc_64_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (Bool.rec (cc_64_8 (Nat.sub p 256)) (cc_64_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_64_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (cc_64_5 (Nat.sub p 160)) (cc_64_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_64_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_64_2 (Nat.sub p 64)) (cc_64_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_64_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)) (Nat.blt p 384)
def hc_64_0 : Nat → Nat := unpackHintV5 0xd50a82cef186c781dcc1099eb45b2caafa58a5496c9baa6896e9308ea2128891848169ca75fadc6f819e69099e63596c5db9685691ca4fe1ac48f1bc4251a837aaaa32415a29fa12217a201b418e10da9a0af17a05097a000142000000000000 0xfa0f0303aa030303030b0303030f03a0303030303030faa89c3c3c3c3c0d03030340c5c0c0c0c0e8dc3c3c3c3c0c1c0c03030300c0c0c0c9cdc9ea0f83e0f0f0f80c0c3c0c0ea03a1c3c3e0f83c3e0faaaa80c3c0c4ea87c3c3c7c4c0c0c4ea87c3c3c7c4c0c0c4c9c9c9c9eaaaaaa03a1eaaaaaaaa1ba82ea0fa1799a8a81e2aa0faa0f0b0f0f0f0b0f0faa23032b132b0323130f0f0f0f6985d69690f43d1745ea88c1cdc47072303c3c3c3cacacacac5d45eaa96a6aaaaa5a0faaa0a80f0b0f0f0f0b0f0faa2b032b132b032b13aa0f0f0f0f5a5a6643d0f45d17a0a0880701c0701c0712696aaaaa83eaa0fa58a00aa0707070f070b0707aa07030713070307070f0f0f0f66507175070743d0f45d17aaaa0707070707070f0f07070f070707070f0f0f0b0f0b0f0f0f130f030f030f0fa8887a0a81c0701c0701c4070703c01c1c1c1c2aaaaaa0783eaa83eaa0f96875a542803e83cae8ac3c3c3c3d91743d0f45d170faa0f0f0f0f0f0b0f0b0f0f0f130f030f030f0faa8dc3c3c3c3cacacacac5d45c3c1c3c0f070f20fa89c3e0f0f0f83e270f0f96875a543c3e0f89eaaa80c2c0daaaa03035550b0b5555555555555aa0f0b0b0f130303133707370dc1cdc55aaaaaaaaa0f83e9556aaaaaaa80c0c2c2c0c2c0c3eaaa80c0c0c2c2c2d5555555556a83c2c2c3c4c0c0c4c4c1c4c130713156aaaaaaaaaaa0f83e968755aa656543d1b542d0b544d13540d03544d135544d55551507466aaa8ac3c3d555556a8dc3c3cdcdcacacdd56aaaaa968755aa656546d50b544d50355515074640aa0707070f070b0707aa07030713070307070f0f0f0f56565541d275541d07542d50f540d513555555555554887a0a81c0701c0710705044aaaaaaaaaa5955687280fa0f2ba2b0f0f0f0f56549d50b543d503544d5555555a370f0f0f0f2b2b2b2b41d15156a83e0f83e0f943d556870f83eaaaa030b03aaaa80c0eaa82c2eaa9990b43d0344d43c3d43c3ea83c2c2c3c4c0c0c4cdc1cdc37073705d45eaaaa82eaa03a9583e0f995683eaaaaaaa80c0c2c2c0c2c0c3eaaa80c0c0c2c2c2d990b43d0344d44c5d44c4ea83c2c2c3c4c0c0c4c4c1c4c13071305d45eaaaaa0b8aeaa80e0faaaa0f83ea9568783eaaaaaa0f86ea0b82ea1384ea0380ea1384eaa13aaa0fa2a07856aaaaaaaa0b030b0b030b0b0b0b0b0b2b6650b50b42d0b45d17aa0b0b02c2c0b0b0b0b1f2b2b1f17517aaa82e82eaaa80e83e8a8aaaaa03030b030303aa03030303030fa9990f43d40d40d0340ea83c3c3c3c0c0c030300c0c0c0c5d45eaaaa82e80e80eaa0fa2a2aaa8ac3c3d990f45d1745ea8dc3c3cdcdcacacdc5d45eaaaaaaaa956878deaaaaaa1ba82ea13a80ea0fa2a078568002a83c2c3c3c3c2c3c3ea8ac0cac4cac0cac4c3c3c3c3c5401415554000000000002aa95696a83eaa0f954019aa543d0b5aa544d0350f0f0f0f661d55555550000000000002020110010000f002c013000c0417011002aa956960f5aa0faa83e5550a1c00202a83c2c3c3c3c2c3c3ea88c0cac4cac0c8c4c3c3c3c3ea88d27173f48c5c3c3c3c3cac9cac9c0000000000002aaaaaaaaaaa0faa000fa0f2ba2b0f0f0f0fa270f0f0f0f2b272b270000000000800f002c013000c017010020fa8dc3e0f0f0f83e2b0f0f83c3e0f8dc28700007aaaa030b03aaaa80c0eaa82c2eaaaa83c2c2c3c4c0c0c4c9d27172749c5e201c0701c0301c1c01c1c01c072aaaaaa8083e0f8aa0a0aaaaaa03030b0b030b030faaaa0303030b0b0baa0f0b0b0f130303131344c5c4d1313880701c0700c07070070700701caaaaaaaaaaa83e0faaa0a1e82aaaa0f86ea0b82ea1384ea0380ea1384eaa13aaa1799a81e02aaa8ac3c3ea89c3c3c9c9c9c9c9e201c0701c0701c072aaaaaaa8287a0aaaa86ea0ba84ea03a85e66a078066a950f42d6a951340d43c3c3c3d98755555556aaa95541cdd41c1d541c1c1c2c1c1c1c3c1c1c1c0c1c0c1c4d555621410700701c0701c44aaa95996aaa95400a0a1c3e83cae8ac3c3c3c3e89c3c3c3c3cac9cac9c1c1ea81cdc1c1c1c2c1c1c1c3c1c1c1c0c1c0c1c4c1c1c1d0741c5c1c80701c0701c0701caaa83e0f83e0f83e0f800a0a1eaaa80c2c0caaaa03030000b0b000aa0f0b0b0f130303132749c5c9d2717000000000000aaaaa0baa80eaaa0f83ea0faa000aaaaaa03030b0b030b030faaaa0303030b0b0baa0f0b0b0f130303131344c5c4d1313000000000000aaaaa82e2baaa0383eaaa83e0fa83ea800287202003c1b002c0b004c13000c03004c130004c0005c040022aaaaaaaa0b030b0b030b0b0b0b0b0b2baa0b0b0b0b0b170b0b0b0b1f27271f0000000000000802c02c00000c05c000aaaaa03030b030303aa03030303030faaa83c3c3c3c0c0c0c0c0c5c0c0c0c0c00000000000020002c00c00c00170002aaa8ac3c3ea89c3c3c9c9c9c9c9c00000002aaaaaaaa27aa000a1c80801b002c013000c017010008 24 16777215 10 1023
def hc_64_1 : Nat → Nat := unpackHintV5 0xdbf95ad401fec962a8c249c6b84282b22986aa61f2a4697e9ba23294e9ae887b1c8459087d01d6724aae68e25a6489166009205959ac54b92853e0364e81584632144011883652702f71b821db662138281f188819b15a11b9fe071aa80001c6 0xba0baa0b2b0313031366648d0b42d5552348d0344d2745d5401cdc01c1c1c41d109eaa1ea0f83e60f569402e82cae87c2c2c2c2c2cad555555bc8ea9bc8d69547c4cac0cac0c7c4d41141c80701c0701c440707007070a2783e0b0b982c3e270f0f95543c3c3d555420700b0baa0b0ba0ba8ae87c2c0c2c2c2c0c2c4c2c2c2c2c2cad595335542d0b5542d542d50b540d5135555555555001c807070070700701c0701c50750109e89e0f82c2c3c2c2ea0ba1c3e270f0f943c3d55695542070aaaaaaaa82c0c2c2c0c2c2c2c2c2c2caea82c2c2c2c2c2c2c2c7c9c9c7ea82c2c2c2c2c2c2c2c7cacac7c9c9c9c9ea82e82eaaa80e85eaa2a02c2ea82c2e82ea2ba1f0b030b0b0b030b130b0b0b0b0b2ba270b42c2c2d0b170b0b0b0b1f272b1fa370b070b02c1c2c0b0b0b0b1f2b2b1f273727a83e0b0b0f0b0ba82e870f8ac3c3e0f0f83e0f0f83eaaaa0f0b0b0faa0f0b0b0f1f1f1f1faa0f0b0b0f1f1f1f1f27272727aaaa82e87aaaaaaaaaa83e83ea03a83e66a2a078aa83ea83c2c3c3c3c2c3c3eaa13aaaa030f0f030f0faa2349c5ced23170f0f0f0f13030313aa2307370ec1c8c0f0f0f0f13030313273727aaaaaaaaaaaaaaaaaaa0f0b0f0f0f0b0f0faa5a55aa030f030f555555555547073711c1cdcaa0f0f0f0f130303135555a5aaaa6a03956a99aa543d0b5aa544d035030f0f030f0faaaa5550f0f50f550f0f0f0b0f0b0f0fa9987555555555556a9510740f0f0f0f130303130f070f03c1c3c55aa5665aaaa1e03a80e55aaa0a80f0b0f0f0f0b0f0faa0303aaaaa030f030f3f49c5cfd2717aa0f0f0f0f13030313a0a0880701c0700c0701caaaaaaaaaa03aa8a00aa0707070f070b0707aa0303071303030707030f0f030f0faaaa0707070707070f0f07070f070707070f0f0f0b0f0b0f0faaa81d07170741c1c3c3c3c3c4c0c0c4c3d0f170f43c3c887a0a81c0701c0301c1c01c1c01c072aaaaaaaaa8780ea03aa8a20f0b0f0b0f84ea83c3d9953b4ed52348d0b43d0344d5401c071074427aaa60f5683e83c0e84c0c3c3c0c3c3d5555552c8ea92c8c3c3c3c2c3c2c3c3d556941141c80701c0700c440707007070aa0f83e60303039540c0c0d555481c0fa0f03a13030f0f030f0f0faa0f0f0f0f0f0b0f0b0f0fa95955b542d50f540d5135543d5543d0f555555543d17555001c80701c0700c070703c01c1c1c1c141d40427aa0f83e80e870303a03030350f0f555a5520703e83c0e84c0c3c3c0c3c3c3ea83c3c3c3c3c2c3c2c3c3eaa270f0f0f0f130303130f43c5c3d0f0fa370f0f0f0f130303130f070f03c1c3c273727aa0f83e80e870303a0303030f83e0f83eaaaa03030303aa1b1b1b1b03030303aa1b1b1b1b0303030327272727aaaa1baaaaaaaaaaa80c0c0c0ea82c2c2c2c0c0c0c0ea82c2c2c2c0c0c0c0c9c9c9c9eaaaaaaa0faa83eaaaaa80c0c0c0ea87c3c3c7c0c0c0c0ea87c3c3c7c0c0c0c0c9c9c9c9eaaaa8ae80e87aa89eaa2baaaaaa86ea82ea80e85e66a2a078a80e030f6642d0f40da030f0f0f0faa45c5d95548d2307108cdc8c9daa8760f56aa0f83e50f81c49d1707187a0380c3e281c2c1c3e03a80c3c3c3c3ea8041d17232723a070707070708c233707aa870783eaaa83e0f83e0aa80ea80c0c0c0c0c3e80c3c3c3c2c3c2c3c3eaaaaa83c3c3c3c0c0c0c0c8d271748c5ea83c3c3c3c0c0c0c0c8c1cdc072309cdc9eaaa87aaaaaaa83e0fa83eaa0faaaaaa03030303aaaa0f0f0f0b0f0b0f0f5a555555555555aa0f0f0f0f030303032f072f0bc1cbc55aaaa0fa9a9555560faa66a950f42d6aaa95540d40c0d540c0c0c2c0c0c0c3ea950340d40c0c0c0c0c3ea661d55555555540d1755aa5441d03c3c3c3c0c1c0c03030300c0c0c0d56aa956960f5aa0fa03a03aaa1d5560faaaaaa030303038aa00f0f0f0b0f0b0f0f0303aaaaa0f0f0f0f030303032f49c5cbd2717880701c0300ca0a00701caaaa0faaaaaaa0faa2802a81c1c1c3c1c2c1c1eaaa80c0c0c0c0c1c0c0c0c0c0c0c1c0c1c0c0c0c2c0c0c0c3ea80c0c0c0c0c0c0c0c0c0c0c0c0c3eaaa0741c5c1d07070f0f0f0f0340c0c0d031703030303221e82a0701c030307070030300c00c0301c072aaaaaa0783eaa83e80e80eaa8783ea82810361e0f0f80c3d583c2c2c3e80e410701ca50f83ea800e030f80c3c2c2c3ea99992342d0f40d0355548d2349d17550073700707071074427aa87a83e0f983d5a500fa0f03a0303030303030f5555555723aa57230f0f0f0b0f0b0f0f5a55504507201c0700c031101c1c00c0c289e0f83e0f0f0f80c0e6035550f0f0f5555081c03e83c0c0ea80c0c0c0c2c0c0c0c3c0e80c0c0c0c0c0c3ea5654bd50b543d550340d55035503540d5555555554007201c0700c1c00c0c00c03141d40427a2783e0f83c3c3e03030f0303a80e8750f0f555a555081c2aaaa80c0c2c0c0c0ea80c0c0c0c0c3eaaa0f0f0f0f0303030303030303aa0f0f0f0f030303030303030327272727aaa82e80e80eaa17aa8a8 24 16777215 10 1023
def hc_64_2 : Nat → Nat := unpackHintV5 0xdb0992d359ecc762fec15982baf998b329f4ace192a511f4995aee9311928b49f285517e7c8a3275d1ae69631c6541085de9d65332ae49ca5a45711640f1203a41ac35a12834c8362f6958271a1420f988173a701059b802c366022028000088 0xaaaa0baa83eaa03aa83c3c3c3c3eaa6a60f0f0f0f0f2b272b27aa81e2a03c3c3c3cacacacac9cdc9ea87aaaaaaaa0faa83eaaaaa80c2c0eaaaa0303aaa0b0baaaaa0f0b0b0f130303132749c5c9d2717aa0f0b0b0f130303133707370dc1cdc27272727aaaaa0baa80eaaa0f83eaaaaaaaaaa80c0c2c2c0c2c0c3eaaa80c0c0c2c2c2ea83c2c2c3c4c0c0c4c4d13171344c4ea83c2c2c3c4c0c0c4c4c1c4c13071309c9c9c9ea87aaaa82e2baaa0383eaaa83e0faaaaaaa0f86ea0b82ea1384ea0380ea1384eaa13aaa1799a8a81e2aaaaa2b0f0faa270f0f2727272727aa370f0f37372b2b3727272727aa1eaaaaaaaaaaaa86ea0ba84ea03a85e66a2a078aaaaa83c3c3c3d55555569543c3c3c2c3c2c3c3cac4cac0cac0cac4d4116201c0701c071101c1c282a6aa83eaa0f9560f95554a2a82eaa0faa80eaa13aa0f0f0f0f55665565595950b543d503544d55559175555550281c1c2882201c0701c07141d40427aaaaa87aa0faa83e583d556954a2a82eaa0faa80eaa13aa0f0f0f0f9a985ea83c3c3c3cac9cac9e078a8aa0f0f0f0f2b2b2b2b273727aaaaa87aa0faa83eaaaaaaaaaa030b03aaaa80c0eaa82c2eaaaa83c2c2c3c4c0c0c4c9d27172749c5ea83c2c2c3c4c0c0c4cdc1cdc37073709c9c9c9eaaaaaaaaa83e0fa83eaa0faaaaaaaa03030b0b030b030faaaa0303030b0b0baa0f0b0b0f130303131344c5c4d1313aa0f0b0b0f1303031313071304c1c4c27272727aaaa1eaaaaaaaaa0f83ea0faa83eaaa83e1ba82e0ba84e13a80e03a84e13aa84eaa85e66a2a078aaaaa8ac3c3ea89c3c3c9c9c9c9c9ea8dc3c3cdcdcacacdc9c9c9c9eaaa87aaaa89eaa37aaaa1ba82ea13a80ea1799a8a81e2aa0faa83eaaaaa87c0c7c4c7c0c7c4c3c2c3c2c3c6ea88d27174348c5c3c2c2c3c7c7c7c7ea88c1cdc43072303c2c2c3c7c7c7c7c9cdc9eaaaaaaaaaaaaaaaaaa96956a87c0c7c4c7c0c7c4ea83c2c2c3d55555555551c1cdc4707372a83c2c2c3c7c7c7c7d555696a9a82eaa55aa66a950f42d6aaa95543c3d43d56aaa544d0350f0b0f0b0f1b0f030f130f030f0f661d55555555555aa5441d03c2c2c3c3c1c3c0f070f07c7c7c7d56a95996a8782ea0baa956aa82a01c1eaaaa87c0c7c4c7c0c7c4ea83c2c2c3cfd27173f49c5ea83c2c2c3c7c7c7c7e8282201c0701c0701c072aaaaaaa82eaaaa2802a81c1c1c3c1c2c1c1eaaa81c1c1c1c1c1c3c3c1c1c3c1c1c1c1eaaa07030713070307070f0b0f0b0f1b0f030f130f030f0faa0741c5c1d07070f0b0b0f0f43c5c3d0f0f1f1f1f1f221e82a0701c07070070700701c0701caaaaaaaa1e0ba82eaaaa2883e0faa031303130f1b66550d43548d2342d0f40d135500701c41d109eaa983d5a0ba0f1fa1f0f0b0f0b0f1b5555555323aa5323555a1f131f031f031f13504507201c0701c071101c1c01c1c2a982c2c2e0f83e550b0b0b555520702e83c3ea83c3ea1fa1f0f0b0f0b0f1b0f030f130f030f0f56556d50b543d550f5550f43d503544d555550f45d55554007201c0701c1c0f00707070700701c50750109eaa0ba1c2c2e82c2c2c3e0f943c3d55695481c0ba0f0faa0f0fa87e87c3c2c3c2c3c6c3c0c3c4c3c0c3c3e89c3c2c2c3c3d0f170f43c3c7c7c7c7e8dc3c2c2c3c3c1c3c0f070f07c7c7c7c9cdc9eaa0ba1c2c2e82c2c2c3e0f83e0f83e0faaaa82c2c2c2ea82c2c2c2c4c4c4c4ea82c2c2c2c4c4c4c4c9c9c9c9eaaaaaa83eaaaaaaaa03030303aa0b0b0b0b03030303aa0b0b0b0b0303030327272727aaaaaaa83eaa0faaaaaa0b0b0b0baa0b0b0b0b1f27271faa0b0b0b0b1f2b2b1f27272727aaa82e87aaaa0fa0faa83eaaaaaa0ba13aa03aa1799a8a81e2a0b9990b682ea917170b2b03513231f2b1f65552348c1c4233723276aa1d83d5aa83e0f943e0712745c1c61e82e8a82ea0baa002cac0c1c0c4c8c7cac7d0745c8c9c8e81c1c1c1c1c2308cdc1eaa1c1e0faaaa0f83e0f820baaa0baaaaaa0b0b0b0b0b2b23031f132b031f13aa0b0b0b0b2349c5d23171f272b1faa0b0b0b0b23073701c8c1f2b2b1f273727aaaa1eaaaaa0f83eaaa0faa83eaaaaaaa96956a82c2c2c2cac0c7c4cac0c7c4d5555555556a82c2c2c2ccc1ccc33073307cacac7d56aa9a9556a83e5583ea99aaaa5550b50b0b55aa542d0b5aaa951340d42c0c2c2c2c0c2c4c2c2c2c2c2cad987555555550b45d5556a9510740b070b02c1c2c0b0b0b0b1f2b2b1f55aaa55a583d60ba0baaa1ea83e55583eaaaa2a801c1eaaaa82c2c2c2cac0c7c4cac0c7c4ea82c2c2c2ccd27173349c5c7c9cac7e201c07282801c0701c072aaaaaaaaa83e83ea8a00aaaa0707070707070b07070b0b07070707aa0707070b070b0707aaa81c0c1c4c1c0c1c1c2c0c2c2c2c0c2c4c2c2c2c2c2caea81d07170741c1c2d0b0b0b42c5c2c2c2c2c7c9cac7c887a0a81c1c1c1c01c1c0b00701c0701c0701caaaaaa81e0fa82e82eaa87aa0fa0faa0a042d8783c3e0b2b56a0b84c0c0c4d041c072943e0faa0 24 16777215 10 1023
def hc_64_3 : Nat → Nat := unpackHintV5 0xf19135d7c2dbad80872a0c4dc7235a86423334765f69c0b9b14952c82a9105249fa0a84e3c4fda309f840c3c00c26d62a8d10271a100434000867c010cbe0e997c0032402e5a129ca2e450fe11f1cf8b22834703207983a8a60001d4 0xaaa203030303555555000000121eaaaaa955402aaa280c0c0c0d55555400006c000121eaaa86eaa555008787aaaa280e1c0c0c0c0d947d7c7d0350000000000aaaaaaaa00aa82eaa86eaa80eaa80e1c0c0c0c0d5555955555500000000000121eaaaaaaaaa9554007e87c0ea8031f1303131303007c7c7c7e0155555555556a87e1f84e0389e2795543e83c0e8030f0f030f0f03a0f0f0f0f0fa030f55555555500000000121c7e87c0c0ea80e1c0c7c4c0c4c4c0c0c0c4c6c4c2c4c2c4c4ea55555555555500000000004c0121ea87e1f84e0384c3e1389c4c4c3e9554000c0c6c6e1384c0c0c0e0380c0d55540121c3e0f942c6c2c6c0c0e0380c0c0c4c0c0c0c0c0c0c7c0c2c0e1c0c0c0c0c0c0c0d55555555554000000000004870f270f270f0b0b0f03030380c3c0e030f03030303555000b0b0b0b0380e131384e130b0b5555004870f83e50b0b0b0b0b1f03130313030b038703030b0b0b0b82e0b0b0303030b130b5555555555500000000000121c3c3c3c3c2c3c2c2c2c2c3c0c0c3c2c2c2e0b0f0b9554000c0c0e0380c7c2c2c2c2c0c0c2c0c0c0c0c0c0c0c0c0c0c0c0c2c0d555555555400000000004870f0f0f0f030f0380c0c0e0b0b0b0b03030303555001b0b130b0303030ba0b130b0b5550004d21c2c3c3c3c4c3d40e1e1c4c0c6c0c0c0c2c0e80c4c0c0d5540013487030f1b271313503030303031f1313131303031387555555500000001304870f0f0f0f030f030303030f0f130f0f0f5550013131b1b80e03131382e0b555550004870f83e58787870b03030b8743c9e1c6c131270f0b1b0b1b03130313030b0300c00b01555555555543c9c3c9c3c6c2c2c9c3c3c3c0c0c3c4c3c9c3c9d5542c3c2c3c0c4c0c4c0c2c0c0f0f0f0f030b0b0f0b03030f5555555550000000000121c2c6c2c6c6c0c4c0c4c4c0c0c2c2c0c2c0c4c4e1384c4c0c0c0c2c2c2d5555555555540000000000013004870f270f270f1b0b0b270f0f0f03030f130f0f131389c3c4c3c4e55500555555000000121c9c9c9c9c9c9c9c9c9c9c9c9d5540008c6c8c2c2c6c2c6c6c6c8c4c8c0c0c4c0c4c4c4c0c2c2c0cbc8c4c8e84e132313231313132f133f13131303030b0b171741d0745d13000000f0f0f83e1b270f0f0f13a130f5b8023a23230b331b330b231b23a2323032f132f0323132f332f61745c5d45c1d41c1d1745d1745c000000000000227a2788c3e89c3e89e2789e2785d60045d1745d1745d17000000001002006c00b004c003001c009c9c9c9c9c9c9c9c9c9c9c9c5d45c00080f0aaaa0baa83eaa03aa83c3c3c3c3d595955995590f542d50f540d51355555555550222070a00701c0701c50750109ea87aaaaaaa960f555a5550a0 23 8388607 10 1023
def hc_64_4 : Nat → Nat := unpackHintV5 0x8811227f6a2a736b00681ad463712a62883a5de12a5601f851612851380a51180850f00a4fb84e4f98084f78084e7042462a123eb9dc320b2c2be98827991425309a2258b62218101f08c41aa11a16810812d0ec0bd1c00a7058045188000114 0x2c2c2c2c0e0384c4e1384c2c2d1745c00108c82308c03b0ec00b02c1300c07003e0f883c0b0b0b0b03130313030b00c2c2d9c8d9e6799c8c000c0c04c4c0011745d0b42d0344d41c1d42c1c0000000000003c3c3c3c2c3c2c2c2c2c3c0c0c3c3c3c3e0f0f0f83d43c002c2c2c2c2c7c0c4c0c4c0c2c0e1c0c0c2c2c2c2e0b82c2c0c0c0c2c4c2d1745d0b42d0344d42c5d42c2c00000000000040cc0800b06c00b02c013000c00b02c000b00007000f0f0f0f0b0f0b0b0b0b0f03030f0b0b0b82c3c2e0f50f000203c00c0c0e0380c7c2c2c2c2c0c0c2c0c0c0c0c0c0c0c0c0c0c0c0c2c0d1745d40c0d40c5d0b42d0340c00000000000040bc0800307c000300c000b002c003000c007000f0f0f0f030f0380c0c0e0b0b0b0b030303030f50f000203c06c2c4c2c0c0c0c2e82c4c2c2c108c80b02c0b10c1304c0300c1304c07002c3c3c3c4c3c83c03872380cec2d0c4c0c6c0c0c0c2c0e80c4c0c0c108c80300c030ec1b06c0b02c1304c07000c3c6c9c4c4c83c03030303031f131313130303138745d1740d0344d1300000000102f02000c1f000c03004c013001c003c3c3c3c0c3c0c0c0c0c3c3c4c3c3c3c3d43c00080f013131b1b80e03131382e0b545d17000042308c882308c03b0ec01b02c1300c07003e0f883c23a1e230b03030b239070703c9e1e1c8c6c13217407270f0b1b0b1b03130313030b0308e88c0c0c0002c2c0011745d0b45d0344d41c1d44c1c000000000000403c9c3c9c3c6c2c2c9c3c3c3c0c0c3c4c3c3c9e0f0f2783d45c002c3c2c3c0c4c0c4c0c2c0c0f0f0f0f030b0b0f0b03030f45d1742d0f40d1343d0f0000000000105b02003c1b002c0b004c13000c03003c00f001c002c6c2c6c6c0c4c0c4c4c0c0c2c2c0c2c0c4c4e1384c4c0c0c0c2c2c2d1745d0b45d0344d44c5d44c4c000000000000400801b06c00b02c01304c00300c01304c001300007000f270f270f1b0b0b270f0f0f03030f130f0f131389c3c4c3c4e0f517000203c02c6c2e82e1e82c2eaa1f0b030b130b030b0b0b0b0b0b0b555555555550000000000121ea82c2e82c3e82e0b83e0f95540282e1eaaa86eaa1b0b0b1ba84e03a5555555555500000000000121eaaaaaaaaa955402a80c0c0c0e89555554000000487aaaaaa55500a8aaa0b0b0b0b5555550000000130487aaaaaa0f9554021e1ea8a0b87aa0b0b0b0b6542d47d8c7c0000000002aaaaaaa802aa0baaa0b87a03aaa13aa0b0b0b0b55556555555400000000000487aaaaaaaaaa555000baa02c0801fa1f1b0b1f0b1b1b1f1f1f1f55555555555aa0f82e0f83e0f83e5550ba02e83e82c3c7e87c3c2c3c2c3c6c3c3c3c3d555555554000000004870b0baa0b870b0b0ba87e87c6c2c7c2c6c6c6c0c6c4c6c0c6c4d55555555555400000001b0000487aa0f82e0f0f86e270f1b0fa0f83e55500030b1303871b0b87130387031303a1f0303031b030b0303a0387a0303a80c0c0c0c0d555555555540000000000487aa0303a030fa1f89e0380e55500aaa0387aa03130313aa1ba82ea1395555555555400000000000487aaaaaaaaaa55500 24 16777215 10 1023
def hc_64_5 : Nat → Nat := unpackHintV5 0xc2a948bfc0babcd8bab74964b52888b0a920a949d89fc2629a81509379c28f19188a313a84f1507d69e27651c670198e65f28a63e8825c89d85302624dc15046b9c24259183d713a38315030a9e22991c623598e19328a14a9220c022a000300 0x2aaaaa80c0c2ea80c0c0c0c0c0c0c0c2c0d5555555556200c1c00c0c01c0700c03112aaaaaaaaa914a2aaaa80c0c4e1d555556200c0301c07112aaaaaa84e4528aaaa030b036a80ea0ba955555556201c0701c0301c07112aaaaa80c0c2c2c0c2c0eaaa80c0c0c2c2c2d5555555556201c0701c0301c1c01c1c112aaaaaaaaaaa13a914a2aaa9555556201c0701c07112aaaaa914a1595542d51b540d513555555001c0701c0701c07141d40427272727272750f555954070706c6c000aa0b00a043a1f43031f1343031f130b0b0b0b0b43645d41c1d42c1d0b42d1745c000000000002a83c3c3c3e83c3e27a0b82e0f83e0f58002c6c2e82e1e82c2eaa1f0b030b130b030b0b0b0b0b0b0b645d42c5d42c2d0b42d1745c000000000000408c0800b02c000b0000b002c013000c00700aa0b0ba0b0fa0b82e0f83e0f5800080f08a00a01b1b000aa1b0b0b1b1f031f131f031f136642d17507075a45d17000000000000aaaaaaaaaa9600a0b87aaaa1baa86c2c2c6ea1380e9990b45d6175a45d170000000000001080801b06c00b02c0880080004c003001c02aaaaaaaaaa58000882a80c0c0c0e890340d990b42c00000000400c0030202002c00b001c02aaaaaa58000882a2aa82c2c2c2d990b42d1344c000000004202002c1b002c0b004c013001c02aaaaa83e96000220a0000b0b000a23f031f133f031f13aa0b0b0b0b5a507076642d0b45d17000000000000aaaaaaaaaa9600aa82eaa82e1e80eaa84ea82c2c2c2d969685c5d990b42d1745c807000000000000108002200202002c1b002c0b004c003001c02aaaaaaaaaa580008802ea80b0b000a0001fa1f1b0b1f0b1b1b1f031f131f031f13645d0b45d41c1d45c1d1745c00000000000042a83e0b83c3e83c3e83e0f83d6000ba02e83e82c3c7e87c3c2c3c2c3c6c3c3c3c3d91742d0f43d0f45d170000000000102302003c00b003c00f004c003001c002c2ea82e1c2c2c2ea1fa1f1b0b1f0b1b1b1b031b131b031b13645d0b45d45c5d45c5d1745c000000000000408c0801b002c01b06c001b00013000c00700aa0f82e0f0f86e270f1b0fa0f83e0f5800080f0030b1303871b0b8713032380c3b02c4304c4c000ee87cec2c7c6cec2c7c6caa0300a003030303033b645d41c1d40c0d1745d0340c000000000002a89cac3c3e89c3e27a1f89e0380e1758000c4c0e87c0c0c0c6c0c2c0c0e80e1e80c0ea0303030303645d40c5d40c0d1745d0340c000000000000408c0800300c00030001b002c003000c00700aa0303a030fa1f89e0380e175800080f0aa8a0313031300a01f1b1f0b1f0b1f1b13130006645d1740d13507075a000000000000aaaaaaaaaa9600aaa0387aa03130313aa1ba82ea139991745d0344d6175a0000000000001080801b002c01304c00300c0880080001c02aaaaaaaaaa58000882aa880c0c0c0d990b42d0340c000000004202002c00b000c003001c02aaaaaa58000882aaa280c0c0c0d991745d0340c000000004202006c01b000c13000c03001c02aaa86eaa96000220a0003f0b1f1b3f0b1f1baa0303000a2030303035a507076645d1740d03000000000000aaaaaaaaaa9600aa82eaa86eaa80eaa80e1c0c0c0c0d969685c5d991745d0340c807000000000000108002200202006c00b000c13000c03001c02aaaaaaaaaa580008807e87c0ea8031f1303131303030001f1b1f0b1f0b1f1ba000645d1745d0344d41c1d44c1c00000000000042a87e1f84e0389c3e89c3e85d6000fa0f03a00c3c3c0c3c3c0e83c3c3c3c3e80c3d91743d0f40d1343d0f0000000000102302003c00b004c003003c00f001c007e87c0c0ea80e1c0c7c4c0c4c4c0c0c0c4c6c4c2c4c2c4c4ea645d1745d0344d44c5d44c4c000000000000408c0801b002c013000c01304c00130000700aa1f87e1380e130f84e2713130fa175800080f003031b1b84e1303030380e030345d17000423208c23010c43006c0b00c0301c00f83e20f02c6c2c6dac8dae6b9ac8c4c4c0000c0c0c0c0303030303000303045d1742d17507075030340d030000000000000f270f270f0b0b0f0f0f2783c3c9e030f030303030f517000b1b0b1b030380e030303130303030303031f030b03870303030303030345d1742d17503175030340d03000000000000102f02006c00b000c030000c0000c13000c03001c003c9c3c9c3c2c2c3c0c0c0e030f0380c3c0c0c0c0c3d45c00080f0 24 16777215 10 1023
def hc_64_6 : Nat → Nat := unpackHintV5 0xcfe112c9799abdfae0b8b152b00a2aa3db0c9e915295ea2a89bb0c7e3ae078c15e77a84672315e69ba1e642964632840630808620840593a345471324d71c03fdb663af93832ca0c2de93825ba0c20396016fa500fa1d60ac138056158000158 0x3e83c0e9030f0f030f0f55555557a570f0f0f0f1380c4d141c80701c0700c440701c0fa0f03a40c3c3c0c3c3c0e83c3c3c3c3e80c3d59523542d50f540d513543d0f543d55555555001c80701c0700c0701c50750107e87c0c0ea80e1c0c7c4c0c4c4c0c0c0c4c6c4c2c4c2c4c4ea566548d542d51b540d03544d135544d5544d13555555544d17555001c80701c0700c070704c01c1c1c1c141d404aa1f87e1380e130f84e2713130fa50f2b555a5520700c0c6c6e1384c0c0c0e0380c0d992348d54350d52348d0b46d0340d0344d5401c07107440f83e43c3d5a0b1b0b1b03030303031f40c0c0c0c0d5555554c8d4e5394c8d5544c4d40c0d5541141c0701c0700c031101c1c00c0c03c9c3c9c3c2c2c3c0c0c0c0d543c3c9e0f0f278070702c6c2c6c0c0e0380c0c0c4c0c0c0c0c0c0c7c0c2c0e1c0c0c0c0c0c0c0d5952f542d51b5540d5540d03540d03540d135555555555001c0701c0700c0c00c1c00c03141d4040f270f270f0b0b0f03030380c3c0e030f0303030350f0f555954070702c2c2c2c0e0384c4e1384c2c2d992348d53b4ed52348d0b42d0b46d0344d5401c07107440f83e43c3d5a0b0b0b0b0b1f03130313030b40c2c2d5555552c8d2e4b92c8d40c0d555544c4d41141c0701c0701c031101c1c01c1c03c3c3c3c2c2c2c2c3c0c0c3d543c3c3e0f0f0f8070702c2c2c2c2c7c0c4c0c4c0c2c0e1c0c0c2c2c2c2e0b82c2c0c0c0c2c4c2d59533542d0b542d1b540d5135542d5542d0b5555555555001c0701c0701c0301c1c01c1c141d4040f0f0f0f0b0f0b0b0b0b0f03030f0b0b0b82c3c2e50f0f555954070700c0c0e0380c7c2c2c2c2c0c0c2c0c0c0c0c0c0c0c0c0c0c0c0c2c0d5952f5540d035540d1f542d50b540d5035555555555001c0700c1c00c0c01c0700c03141d4040f0f0f0f030f0380c0c0e0b0b0b0b0303030350f0f555954070706c2c4c2c0c0c0c2e82c4c2c2d92342d4342d0b40d0344d1344d44d1313404c1d07440b0f0f0f130f43c3d5a038753b03430b130f84c0c6c0c0c0c2c0e80c4c0c0d92340d3b40d0342d0b46d1b44d44d1313404c1d0744030f1b2b131343c3d5a03030303031f13131313030313875654bd50340d50347d513544d555544d5001c0700c0301c130707141d4040f0f0f0f030f030303030f0f130f0f0f50f0f555954070704c4c6c6e0380c4c4e0b82d5952354ed3b548d2342d0b46d1b40d0344d13555007070701c41d103e0f90f0f5686c2c4e82d42c3d2e1c4c0c6e80d40cad2c2c6c2c6c6c0c4c0c4c4c0c2c0d5555554b234b92e4b2355503035550b0b50450701c0701c0700c4407070070700f270f270f0b0b0f0f030313550f4b0f0f2783c3c9d2e8070702c3c2c3c0c4c0c4c0c2c0d555555575757570f0b0b0f13030313450701c0701c0700c440701c0b0f0b0f03130313030b0343c3c3c3c0c2c2c3c2c0c0c3d5955b542d50f540d513543d0f543d55555555001c0701c0701c0301c07141d4040b1b0b1b1b031303131303030b0b030b03131384e13130303030b0b0b565550b42d51b46d50340d51344d55135551344d55555551345d55400701c0701c0700c070704c01c1c1c1c141d4040f270f270f1b0b0b2b0f0f0f03030f130f0f131389c3c4c3c4e50f0f555954070721b86c2c2c6e84ea555555542c2c2c2c6e8cc7c7c7c7d141c072881c0701c440722aaaaa956a8a2a1b0b1f0b1b1b1b1b131b1b1355546d55551b1b0b0b0b0b2387542c2d551f1f1f1f450701c070706c1c1c1c1c0701c440701c0f82e0f86c3c6e0f83e550f83e20700c4c0c4e1baa84e55555551f1f1f1f40c0c0c0c4e8bd141c0701c032881c440722aaaaa956a8a00c7c4c0c4c4c4c6c4c4c4c4ea5555544d551f1f1f1f1313030303032387540c0d55450701c0700c070704c1c1c1c1c440701c1f87e1380e1384c4c4e552388e20708c6c6c6c6c8c4c4c4c4c0c2c2c0cbd84d540c2c8c2c0c6c0c2c0c8c0c2c4c2d5541c1c1c0706cac3c3c3e0f88c6c6c6c6c8c4c4c4c4c0c2c2c0cbc8e13a13131303030b0b55551b0b230b0b1b1b1b1303230303131313131313132323132f1313134107070701c0701c1b2b0f0f0f13a130f5b83e0f88e88c8e88cbcccbd55555555331b230b330b231b2f1323032f0323135045070720701c0701c071101c1c01c1c2a96e3396e2f9548c3e96c3e881c0f0f0f0f2b2b2b2b0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f555555150701c0701c0701c0701c44aaaaaa031303aaa030b0387030303030303035555555555880701c03030030700300c44aaaaaaaaaaa4528aaaaa030b038703030b0baaaa0303030b130b5555555555880701c0700c070700707044aaaaaaaaaaa4528 24 16777215 10 1023
def hc_64_7 : Nat → Nat := unpackHintV5 0xbf09c0ba911eb379c6ad6186a21ad29b09c494d18e90591e8931ca7f228479d15472c9c26e312668f94e68782062e1665be1c05491d450491249e19a3e62e03bc8a634a1ca2a92842541541e39c219a12614694e13e8200e51660751c00001d4 0xc0c0c0c0c7c4c4c4c4c0c0c4e1d5555540000004c121c002f02000c003004c01301000f0f0f0f030f030303030f0f130f0f0f55000203c04c4c6c6e0380c4c4e0b82d55400121c08c232208c2300ec3b006c0b04c031003e0f883c0b1b0b1b03130313030b0312c8d2e4b92c8c0c0c0002c2c001555555555400000000000003c9c3c9c3c2c2c3c3c0c0c4c3c3c9e0f0f27954002c3c2c3c0c4c0c4c0c2c0c0f0f0f0f030b0b0f0b03030f5555555500000000121c005b02003c00b004c003003c00f01000b1b0b1b1b031303131303030b0b030b03131384e13130303030b0b0b555555555500000000004c070121c0002006c00b004c003004c130004c001000f270f270f1b0b0b2b0f0f0f03030f130f0f131389c3c4c3c4e55000203c008c6c2c6c2c6c8c4c0c4c0c4c0c2c2c0cbc8c4c8e84e132313231313132f133f13131303030b0b55555000000f83e1b2b0f0f0f13a130f5b8023a23230b331b330b231b23a2323032f132f0323132f332f555555555550000000000000aa230fa370fa378ce378be5500555555000000121c0002006c00b004c003010037273727372737273727372755000203c182e0b0b43a1f0b0b0b0b0b435555555551b1b5a551f13430343031f13504507201c0701c071101c1c01c1c2a82e0b83e0f9543c3e83c3e881c0b1b0ba0b87a0b0baa87c2c0c2c4c2c0c2c2c2c2c2c2c2d595235542d5542d0b542d0b542d1b540d5135555555555001c807070070700701c0701c5075012a82c2e82c3e82e0b83e0f943c3d55695481ca6aaa1b0b0b1b5555555a555551b1b1f131f031f031f135045880701c0701c4407070a0aaaaaa55aaaa28a0b87aaaa1baa86c2c2c6ea1380e959959542d51b55655599503544d55555555540880701ca081c01c07141d404aaaaaaaaaa583d556954a2a80c0c0c0e99503540d595950b542d55555400300c880701c5075012aaaaa960f555a5528a9aaa0b0b0b0b5656542d50b544d5135555513540880701c0704c1c1c5075012aaaaa83e583d556954a21c7c0c4ea9a0b87aa0b0b0b0b5555555a5550b0b551f130363031f135045880701c0701c504407070a0aaaaaa55aaaa28aa82eaa82e1e80eaa84ea82c2c2c2d55995595656542d50b540d513555555555502070a0880701c0701c5075012aaaaaaaaa960f555a55280ba47e87c6c2c7c2c6c6d5555555542c2d55687c4c7c0c7c0c7c4d41141c80701c0701c440707007070aa0f82e0f83e550f530f0fa0f0f94e881c0ba47e87c3c2c3c2c3c6d555555be9bc3e0b0f1f1f1f1f4507201c0701c071101c0702e90ba0fa0b0f1fa1f0f0b0f0b0f1b0f0f0f0f56548d50b543d50f43d50f5503544d55555554007201c0701c0701c07141d4040b0baa0b870b0b0ba87e87c6c2c7c2c6c6c6c0c6c4c6c0c6c4d599523550b42d51b46d551b5551b46d503544d555551b45d55554007201c0701c1c1b00707070700701c5075012a83e0b83c3e1b89c3c6c3e83e0f943c3d55695481c030b1303871b0b87130354ed0350d0b0b1b03130f8ee87d80e030303030303033b55555555513131f1b3b0b3b0b1f1b5a55504507201c0700c031101c1c00c0c2a87e2b80e03954ac3e8ac3e881c031303a1f0303031b030b0303a0387a0303a80c0c0c0c0d595235540d5540d03542d51b540d03540d135555555555001c803030030700701c0300c5075012a80c0e80c3e87e2b80e03943cad55695481caaa6a031303135555555a551f1b1f0b1f0b1f1b55513135045880701c0700c4407070a0aaaaaa55aaaa28aaa0387aa03130313aa1ba82ea13959959542d51b540d5135565559955555555540880701c0700ca081c141d404aaaaaaaaaa58ad556954a2aa980c0c0c0d595950b542d503540d5555540880701c0300c5075012aaaaa960f555a5528aaa9a030303035656546d51b540d5035551b55540880706c1c1c0300c5075012aaa86eaa58ad556954a21c7c2c6eaaa9a0387030303035555555a551f1b0b5f0b1f1b50303555045880701c0300c504407070a0aaaaaa55aaaa28aa82eaa86eaa80eaa80e1c0c0c0c0d55995595656542d51b540d503555555555502070a0880701c0300c5075012aaaaaaaaa962b555a55281fa1f03a40c7c4c0c4c4d5555555540c0c7c6c7c2c7c2c7c6d556941141c80701c0700c440707007070aa1f87e1380e552b4b0f0fa2b0f92e881c 24 16777215 10 1023
def hc_64_8 : Nat → Nat := unpackHintV5 0xb70228b2512cac0992a80102a3991a9ed9309849a49281728ce966835a6481308a7b796e72da286e292c67e19263d9025f711a5ab1305421a44e597248c1663f32643ad11833c9c22932a624d1181dc9c21332a608fa8e04c10e04382200010e 0xb1b0ba0b87a0b0baa87c2c0c2c4c2c0c2c2c2c2c2c2c2d555555555400000000004870008c0800b02c000b0000b002c013000c0402a82c2e82c3e82e0b83e0f95400080f08a00a01b1b000aa1b0b0b1b1f031f131f031f135555555555000000000000aaaaaaaaaa5500a0b87aaaa1baa86c2c2c6ea1380e95555555554000000000048700202006c00b02200200013000c0402aaaaaaaaa954000882a80c0c0c0e895555540000004870000c0030202002c00b0100aaaaaa55000220a8aaa0b0b0b0b55555500000013048700202002c00b004c0130100aaaaaa0f95400088280002c2c00288fc0c7c4cfc0c7c4ea82c2c2c2d55555555540000000000402aaaaaaaaa95402aa0baaa0b87a03aaa13aa0b0b0b0b5555645d5555540000000000487002000880080800b002c013000c0402aaaaaaaaa9540008802e80b0b000a0001fa1f1b0b0b1b1f031f131f031f1355555555550000000000000aa0f82e0f0fa0f0fa0f83e55000ba02e83e82c3c7e87c3c2c3c2c3c6c3c3c3c3d55555554000000004870008c0800f002c00f003c013000c04002c2ea82e1c2c2c2ea1fa1f1b0b1f0b1b1b1b031b131b031b135555555555000000006c07000121c002302006c00b006c1b0006c0004c0030100aa0f82e0f0f86e270f1b0fa0f83e55000203c00c2c4c0e1c6c2e1c4c0e1c8e030ec0b10c13130003ba1f3b0b1f1b3b0b1f1b280c02800c0c0c0d5555555554000000000002a8ac3e8ac3e87e2b80e03954000c4c0e87c0c0c0c6c0c2c0c0e80e1e80c0ea030303030355555555550000000000121c002302000c030000c0006c00b000c0030100aa0303a030fa1f8ae0380e55000203c2aa280c4c0c4c02807c6c7c2c7c2c7c6c4c4c0015555555554000000000002aaaaaaaaa95402aa80e1ea80c4c0c4ea86ea0ba84e55555555550000000000121c0080801b002c013000c08800800100aaaaaaaaaa55000220aaa203030303555555000000121c0080800b002c003000c0402aaaaa954000882aaa280c0c0c0d55555400006c00121c0080801b006c003000c0402aaa86eaa55000220a0003f0b1f1b3f0b1f1baa0303000a20303030355555555550000000000100aaaaaaaaaa5500aa82eaa86eaa80eaa80e1c0c0c0c0d55559175555550000000000121c008002200202006c00b000c0030100aaaaaaaaaa550002201fa1f03a00c4c0c4c0c0c0007c6c7c2c7c2c7c6e800155555555540000000000002a87e1f84e038ac3e8ac3e954003e83c0e8030f0f030f0f03a0f0f0f0f0fa030f5555555500000000121c002302003c00b004c003003c00f01001fa1f0303aa0387031f13031313030303131b130b130b1313a955555555540000000001301c04870008c0801b002c013000c01304c0013000402a87e1f84e0384c3e1389c4c4c3e95400080f003031b1b84e1303030380e03035500487023208c23010c43006c0b00c031003e0f883c0b1b0b1b53235394e532313130000303030300c0c0c000c0c155555555540000000000003c9c3c9c3c2c2c3c3c3c9e0f0f2780c0c0c0d54002c6c2c6c0c0e0380c0c0c4c0c0c0c0c0c0c7c0c2c0e1c0c0c0c0c0c0c0d55555555540000000000487000bc0801b002c00300c000300003000c04003c9c3c9c3c2c2c3c0c0c0e030f0380c3c0c0c0c0d5400080f00b0b0b0b0380e131384e130b0b5500487023208c2300ec3b002c0b04c031003e0f883c0b0b0b0b031303130300c2d2c8d2e4b92c8c000c0c04c4c00155555555540000000000003c3c3c3c2c2c2c2c3c0c0c3c3c3c3e0f0f0f954002c2c2c2c2c7c0c4c0c4c0c2c0e1c0c0c2c2c2c2e0b82c2c0c0c0c2c4c2d55555555540000000000487000cc0800b002c013000c00b02c000b0004003c3c3c3c2c3c2c2c2c2c3c0c0c3c2c2c2e0b0f0b95400080f003030380e031f0b0b0b0b03030b0303030303030303030303030b0355555555550000000000121c002f02000c1f0000c030002c00b000c00301000f0f0f0f030f0380c0c0e0b0b0b0b0303030355000203c06c2c4c2c0c0c0c2e82c4c2c2c13487023202c0b04c0304c131002c3c3c3c4c3c83c0387872384c0c6c0c0c0c2c0e80c4c0c0c13487023200c0306c0b04c131000c3c6cac4c4c83c 24 16777215 10 1023
def hc_64_9 : Nat → Nat := unpackHintV5 0x87b0e5a19b0a2827c7e1ef535478d4601d2122871905e9b981986b586119b923a62ec7f179c23e5744e5950f1844f38a091cd402442c610fca2823725008bd43ea2cc8510b2102229fc51092a2aa2164688716286176c9d83c14340b048001b821202dc80800016e 0x2c2ea82e1c2c2c2ea1fa1f1b0b1f0b1b1b1b031b131b031b13645d0b45d45c5c5c5d1b5171745d170723aa0707071b0707070b0707071b071b07070707071b07070707070713070307030707001c80701c07070070700701c121d415aa0f82e0f0f86e270f1b0fa0f83e0f581c1e81c3e881c030b1303871b0b8713032380c1cec0c2c1d0c1e1c4c4ea81c1cee87cec2c7c6cec2c7c6c0e80c0e0303a030303030303645d4140c45d1740d0307200d0500701c0300c0312a89c3e89c3e87e2780e0385d620700c4c0e87c0c0c0c6c0c2c0c0e80e1e80c0ea0303030303645d40c5d40c0d1745d0340c1c8ea81c1c0c0c0c0c0c0c1c1c0c0c1c0c0c0c0c1c6c1c1c1c2c1c1c0c0c0c0c0c0c0c0c007200c0c00c1c01c0700c0304875056a80c0e80c3e87e2780e0385d60707a070fa2072aaa80c4c0c4eaaa87c6c7c2c7c2c7c6c4c4c0c0c0c0c1c1d991745d0344d4162201c0701c032414212aaaaaaaaaa58a2aa80e1ea80c4c0c4ea86ea0ba84e6645d1740d13585d6aaaa81c6c1c1c1c2c1c1c1c4c0c0c0c0c1c1eaa81c1e81ea80880701c0700ca081c04875056aaaaaaaaaa5aaaa8a2aaa80c0c0c0d990b42d0340eaaa81c2c1c1c1c2c1c1c0c0c0c0c0c0c0c0c0880701c0300c121d415aaaaaa96aaaa28aaaaa030303036645c5d1b1740d03aaaa071b0707071b0707030303030303030302201c0700c0304875056aaa86eaa96aaaa28aaaa470b1f1b470b1f1baa0303030303030303aa0303030358506645d1740d035090880701c0300c810aaaaaaaaaa9628aa82eaa86eaa80eaa80e1c0c0c0c0d696176645d1740d03a07aaaaa0707aaaa071b0707070b070703030303030303030281c1c2882201c0700c0304875056aaaaaaaaaa5aaaa8a07e87c0e81c0c4c0c4c0c0ea81c0c7c6c7c2c7c2c7c6e80c0c0c0c1e645d1745d0344d4144c07201c0701c0301d05007152a87e1f84e0389c3e89c3e85d620703e83c0e81c0c3c3c0c3c3c0e83c3c3c3c3e80c3d91743d0f40d1343d0f0723aa0707070f0707070b07070713030303030707070f0707070f0707001c80701c0700c0701c121d4151fa1f0303aa0387031f13031313030303131b130b130b1313a991745d1740d1351313171744d44c4c1c8ea81c1c1c6c1c1c1c2c1c1c1c4c0c0c0c0c1c1c1c4c1c4c1c1c1c1c1c4c1c1c1c1c1c007201c0701c0301c1c01c1c04875056a87e1f84e0384c3e1389c4c4c3e85d60707a070fa20700c0c6c6e1384c0c0c0e0380c0d1745c8e81c8c1c8c1c1c1d0c1d0c1c1c1c6c1c2c1c0c0c0c0c01c07121d143e0f81e0f82c6c2c6d3c8d3e4f93c8c4c4c1c1c1c1c1c1c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0d1745d0b45d4140c40d030701c0701c0341400c0300c40f270f270f0b0b0f0f0f2783c3c9e030303030f51701c1c0b1b0b1b030380e030303130303030303031f030b03870303030303030345d1742d17503175030340d03072f0781e0707071b0707070b07070303030303030707030307030303030303030303030303001c0701c0700c0c00c1c00c03048750543c9c3c9c3c2c2c3c0c0c0e030f0380c3c0c0c0c0c3d45c1c1c1e070f078070702c2c2c2c0e0384c4e1384c2c2d1745c8e81c8c1c8c1c1c1cec1cec1c1c1c2c1c2c1c4c0c0c1c01c07121d143e0f81e0f82c2c2c2c0c4c0c4c0c1c0c2d3c8d3e4f93c8c1c1c1c0c0c0c1c1c4c4c0c0c0c0c1c1d1745d0b42d0344d4142c0701c0701c0700c0741401c40f0f0f0f0b0b0b0b0f03030f0f0f0f83c3c3e0f50f01c1c0b0b0b0b0b1f03130313030b038703030b0b0b0b82e0b0b0303030b130b45d1742d0b40d1350b1750b0b07330781e0707070b0707070b07070713030303030707070b070b07070707070b0707070707001c0701c0701c0301c1c01c1c048750543c3c3c3c2c3c2c2c2c2c3c0c0c3c2c2c2e0b0f0b83d43c1c1c1e070f078070700c0c0e0380c7c2c2c2c2c0c0c2c0c0c0c0c0c0c0c0c0c0c0c0c2c0d1745d40c0d40c5d0b42d0340c1cbc1e0781c1c0c0c1c7c0c0c0c0c0c0c0c0c0c0c1c1c1c2c1c1c1c2c1c1c0c0c0c0c0c0c0c0c00701c03070030300701c0300c121d4150f0f0f0f030f0380c0c0e0b0b0b0b030303030f50f07070781c3c1e01c1c1b0b130b0303030ba0b130b0b131323a070b070b0713030307130713070487450b0f0f0f130f0783e038723a1c4c0c6c0c0c0c2c0e80c4c0c0c4c4c8e81c0c0c0c0c6c1c2c1c4c1c4c1c121d140c3c6c9c4c4c1e0f80c0c0c0c0c7c4c4c4c4c0c0c4e1d1745d0340d131344c4c1cbc1e0781c1c0c0c0c0c0c0c0c0c1c4c1c1c1c4c1c1c00701c0300c0701c121d4150f0f0f0f030f030303030f0f130f0f0f0f50f07070781c3c1e01c1c13131b1b80e03131382e0b545d17230723a0781c8c1c8c1c1c1cec1cec1c1c1c6c1c2c1c4c0c0c1c01c1c1c07121d143e0f81e0f82c6c2c6c0c4c0c4c0c2c0c1d3c8d3e4f93c8c0c0c1c1c1c1c1c0c2c2c0c0c0c0c1c1d1745d0b45d0344d4144c0701c0701c0700c0741401c540f270f270f0b0b0f0f0303130f0f2783c3c9e0f51701c1c0b0f0b0f03130313030b03070f0f0f0f030b0b0f0b03030f45d1742d0f40d1343d0f075b0781e0707070f0707070b07070713030303030707070f0707070f0707001c0701c0701c0301c07048750542c6c2c6c6c0c4c0c4c4c0c0c2c2c0c2c0c4c4e1384c4c0c0c0c2c2c2d1745d0b45d0344d44c4c5c5d1351313070781e0707071b0707070b07070713030303030707071307130707070707130707070707001c0701c0701c0301c1c01c1c048750543c9c3c9c3c6c2c2c9c3c3c3c0c0c3c4c3c3c4c4e270f130f1383d45c1c1c1e070f078070701c1c8c6c2c6c2c6c8c4c0c4c0c4c0c2c2c0cbc8c4c8e84e132313231313132f134713131303030b0b17174445d130707440701c0f83e1b270f0f0f13a130f5b81c1c1c8e88c8c2ccc6ccc2c8c6c8e88c8c0cbc4cbc0c8c4cbcccbd85d17175171411745d1745c1c1c81c5007401c0701c0701c4aa230fa270fa2789e2789e175881c45d1745d1745d17070781e0707071b0707070b07070713070307030707001c0701c0701c07048750549c9c9c9c9c9c9c9c9c9c9c9c5d45c1c1c1e070f078070706c6c000a0b00a043a1f43031f1343031f130b0b0b0b5555555555000000000000aa0f0fa0f0fa0b82e0f83e5500 26 67108863 11 2047
def hc_64_10 : Nat → Nat := unpackHintV5 0xc609415ab10aad4e0156a7000b5100559f8122cfc00167e000b2d024556c7fa7e05ad2bb26a8fc8c2443076a0c82a0f821c47760963804759a323a0be726457090627fc7112063f075935434c8c016148a09902f43fc19819d0c208748e823e3f800023e 0xb0b0b0b030303030303030353235394e5323030350340c0c0c0c00c030345d1740d0b40d0350303517170701c0701c0300c070700707007103c3c3c3c2c2c2c2c0c0c0c0c3c3c3e0f0f0f83d43c070702c2c2c2c0c0c0e0380ccc0c0c0c2c0c2c0c0c0c2c0c6c0c0c0c0c0c0c0c0c045d1742d8750b0b503035031740d030b2f0b82e0b0b540c0c2c0c0c0c0c0c0c0c0c0c0c2c2c0c0c2c4c0c0c0c0c0c0c0c0c2c5c2c1c0701c0700c0c1c0c0c00321c1c407070070700f0f0f0f0b0b0b0b030f0380c0c0e030303030f50f0b0b0b82c3c2e01c1c23a230b030348e40c1c0f27231b0b13217407270f0b0b0b0b030303030303030323a2303030b0b030303035045555555555550701c0701c030401c1c141103c3c3c3c2c2c2c2c0c0c0c0c3c3c3e0f0f0f954070715952f0b0b0b0b50b03030380e03335030355555030303030b0303030b0303030340d550303030303015555542d875555550701c41c1401c0700c0c1c0c0c00321d103c3c3c3d0f5560b0b0b0b030f0380c0c0e030303035501c1c1f1f03030380e030303030b0303031b0303030303030303007c7c0d03030340c5c0c0c0c0c1c0701c0700c0c1c0c0c00321c1c070acacacac7cacac7c0c3c0e03030380c0c0c0cacacacac070705c5c0007e87c7c2c7c6c7c2c7c6c0e84d41c1d540c4c0c4c65401415554000000000002a8ac3e8ac3e87e1f84e03954011747e87d51b42d40e84d51340d40c4c0c4d9875555555400000000000321c0023020110010001b002c007040400aa5643d47e1f84e0395400080f0aaaa031303134645d1740d1300501f1b1f0b1f0b1f1b0707aaa1717000000000000000aaaaaa96aaaa00aaaa03130313661d691745d0344d586ea0ba84ea03a85e00000000c87000000202006c00b001c05c170110220020000aaaaaa96aaaa000220a0001f0b1f1b1f0b1f1baa5550707aa031303135000515555000000000000aaaaaaaaaa5500590b5546ea940c0d5544c4ea80c4c0c4d555661d5554407000000000000c87001000440080801b002c007041701100162b5558deaaaaa9540008807e87c0e84c0c4c0c4da611745d0344d40007c6c7c2c7c2c7c6c1c1c0c0c0c0c4c1e80000000000321c000000aa1f87e1380e17589c3e89c3e8007e87c0e84c0c4c0c4d6998745d1740d13545c6c5c2c5c2c5c5c4c4c0c0c0c0c4c4ea00000000c8700000008c0801b002c00701701005c170005c0002a87e1f84e0385d6170fa170fa000203c001f1fa1f1f1f0b1f1b1f0b1f1b0384e13130384c1e81c1c0c4c0c4c8e88c8d3b173b48c5c7c7c7c7c4c0c0c4c0000000000002a88c3e8ac3e87e1f84e038ae2b8007c7c7c7c0c4c0c4c0c4c0c4c7c7c7c7c4c0c0c4c0000000321c0002006c00b001c05c04002b372b371f1f1f1f130303132b372b37000203c06c6ea81c1c1e82c1e0707a070743a1f43031f1343031f130b0b0b0b645d4142c42d0b45d1707201d0500701c0701c0712a83c3e83c3e82e0b83e0f83d620702c6c2e82e1e82c2eaa1f0b030b130b030b0b0b0b0b0b0b645d42c5d42c2d0b42d1745c1c8ea81c1c1c2c1c2c1c1c1c1c1c2c1c1c1c1c1c1c2c1c1c1c2c1c1c1c4c1c0c1c0c1c1c007201c1c01c1c01c0701c0704875056a82c2e82c3e82e0b83e0f83d60707a070fa2072aaaaa86c6c1c1c1c1c1c1ea86c2c2c6c7c0c7c4c7c0c7c4d990b45d41611745e201c07241401c07212aaaaaaaaaa58a282e1eaaa86eaa1b0b0b1ba84e03a6642d17585d691745eaaa81c6c1c1c1c2c1c1eaa81c1e81ea81c4c1c0c1c0c1c1c0880701ca081c01c0704875056aaaaaaaaaa5aaaa8a2a80c0c0c0ea90340d990b42c0c0c0c0c0c0c0c0eaaa81c2c1c1c1c2c1c1c00300c880701c121d415aaaaaa96aaaa28aaaaa0b0b0b0b6642d0b44c4d1313aaaa070b0707070b0707071307070713070702201c0701c0704875056aaaaa83e96aaaa28aaaa0b0b070707070707aa47031f1347031f13aa0b0b0b0b58506642d0b45d175090880701c0701c810aaaaaaaaaa9628aa82eaa82e1e80eaa84ea82c2c2c2d696176642d0b45d17a07aaaaa0707aaaa070b0707070b070707130703070307070281c1c2882201c0701c0704875056aaaaaaaaaa5aaaa8a02e81c2c2ea81c1e81c1c1c1c1e1fa1f1b0b0b1b1f031f131f031f13645d0b45d4145c45d1707201c0701d0500701c07152a83e0b83c3e83c3e83e0f83d620702e81c2e83e82c3c7e87c3c2c3c2c3c6c3c3c3c3d91742d0f43d0f45d170723aa0707070f0707070b0707070f0707070f07070713070307030707001c80701c0701c0701c121d415 25 33554431 11 2047
def hc_64_11 : Nat → Nat := unpackHintV5 0xe049b6db7136d489bacda1bac3c278bae238af8ad6a869c89f424a9751fc90c1a487c2407893cc78401477882e71199c676a6c6129905c1944531a404c61ae426a7e4188383cc13236e1782dfa3a2d582827d1621fba0616ca3c0ee9f80003ba 0xaaaa03030303661d691745d0340d586ea0ba80ea03a85e000000c8700000000202006c00b000c05c040880080002aaaaaa5aaaa80008828000fc2c7c6cfc2c7c6ea80c0d556a80c0c0c0d400145555400000000030000aaaaaaaaaa5500590b5546ea940c0d5540c4ea80c0c0c0d555661d5554000000000321c00004001100202006c00b000c10100162b5558deaaaaa954000880be87c0e80c0c0c0c0d911745d0340d40007c6cbc2cbc2c7c6c0c0c0c0c0c0c0c0e80000000000000002a87e2780e0385d6270fa270fa002fa1f03a03030303035a661d1745d0340d5171b170b170b17170303030303030303a800000321c00000001701c02302006c00b000c05c0401705c00170000aa1f89e0380e17585c3e85c3e800080f00b0b0b0b030303030303030345d175142d0340d4c8d4e5394c8c01400c0c0c0c0c0c0c0c5c5c00000000000000003c3c3c3c2c2c2c2c0c0c0c0c3d43c3c3c3c3c3e0f0f0f27a000b0b0b0b030303030303030345d1742d8750b0b40d030b2f0b82e0b0b540c0c0c0c0c0c0c0c2c5c2c00000321c000000003302002c00b000c05c0400b02c000b00000f0f0f0f0b0b0b0b030303030f50f0b0b0b82c3c2e000203c13c8d3e4f93c8c2c2c2c2c2c2c0000c0c0c0c0c0d5540c0c0c0d55400145540000000000003c3c3c3c3c3c3e0f0f0f82c2c2c2c0c0c0c0d54015952f0b0b0b0b50b03030303503035550313030303035555550b61d54000000000321c000033020100044000b06c00b02c0030404000f0f0f0f43d5582c2c2c2c0c0c0c0d5400080f0008e87c8c2c7c6ccc2c7c6c0c0e80c0c0c0e80c0c0e0303030323a23234fc5cfd23171f33331f030303030000000000000aa230fa2b0fa1f8ae0380e2b8ae001f1f03030303030303031f1f03030303000000c87000000801b002c00301701000acacacac7cacac7c0c0c0c0cacacacac00080f003a0b03a03030303030303aa1b1b0303a0380c0c0c0c00c03032fa2f0b0b0b0b030303032f4bc5cbd2f1707201c0700c0301c1c01c1c01c072a82e0b80e0383c3e83c3e83e0f881c0b1b0ba0b87a0b0ba80c0ea80c8c0c0c0c0c0c2c0c0c0c0c0c0c2c0c2c0c0c0c2c0c2c0c0c0c2c0c6c0e80c0c0c0c0c0c0c0c0c0c0c0c0c0c0c02fa2f0b42c5c2d0b0b0b0b0b0b0340c0c0d03170303030307201c1c01c1c01c0700c0c1c0c0c00321c1c072a82c2e82c3e82e0b80c3e80c0e80e0383e0f881c85d8d85d8c6c2d01eaaaa80c0c0c0eaaa80c0c2c2c0c0c0c0e808aaaa0b0b0b0b0303030358c5d8d17880701c030801c1c2801c072aaaaaaaaaaa8a2aa0baaa0b87a0303aaaaa03aaaa0303030b0303030ba0303aaa0313aa03030303026a617aa0b0b0b0b0340c0c0d03170303030381c282201c0700c0c1c0c0c00321c1c072aaaaaaaaaaaaaaa8a00c0c0c0c7c8ccc7e00c0c8c0c5c5c5c5ccc8d2345c5c5c0e0390303031b0b0b1780c0e545c5c1c1c1c0701c0708e2783e0f80c0d990340d0b46d03603031f23331f8030345c5d48d233355548d23070707101c0710f2b5688e2b88e87c0c0e80c0c0c0c0c0c0c0c0c7c6c8c2ccc2c7c6e800c0388e88c7ccccc7c0c0c0c0c8d1748c5c1c1c81c0701c0300c07070070700701caa1f8ae0380e230fa2b0fa2b8ae2070be87c0e80c0c0c0c0c0c0ea85c5c7c6cbc2cbc2c7c6d4115555555555541c80701c03101c1c14112a87e2b80e038ac3e8ac3e95481c45d2fa1f546d0b50303aa03235550350303550303030b0303031b03a03540d035030303030198755555555550345d541c85041c01c0700c0c1c0c0c00321d12a9590f51f8ae030fa0303a0380e5520700e9030303170780c0c0c0c7c8ccc7e291745d0340d40d45eaaa80ea85e0701c03201c80712881caaaaaa96aa28aaaa03030303a59a1f1b730b730b1f1ba08a69a45d1740d035030351717880701c03201c1c2801c4aaaaaaaaaa9628aaaaaaa030303030b0303031baa03030303019875a45d17503035031740d03561ba82ea03aaa0380eaa03a80ea17a201c0700c0c1c0c0c00321c1c4a081c2aaaaaaaaaa5aaaa8a07c2c6e1e1eaaa80c0c0c0eaaa87c6c2dfc2c7c6d411555661d55555556201c0700c0c100c87070705044aaaaaaaaaa5528590b5546ea940c0d555540eaaa80c0c0c2c0c0c0c6d035540ea80c0c0c0c055559875555555541c142201c0700c0c1c0c0c00321d1162b5558deaaaaaaaaa954a00c0c0c0c7c8c8c7e00c0d1745d0340d45c5d2361c0c5c5c5c5c0c5c0c0c0c0c0e1c0d40c0c0c0d40ea0701c0300c0701c07101c1c170707078707e2780e0388e2385d61785e2070be87c0e80c0c0c0c0c0daa51f1b2f0b2f0b1f1b030300300c0d90345d1740d035039681c80701c0300c07070070700712a87e2780e0389c3e89c3e85d62070be87c0c0e80ea0323030303030b0303031b03a0303030303016998745d1740d40c0d40c0c5c5d0340d5171b170b170b1717030317030303030303030303031717030317130303030303030303a81c80701c0303070303000c8707101c1c170070707070aa1f89e030fa0303a0380e17585c3e85c3e881c 24 16777215 10 1023
def hc_64_12 : Nat → Nat := unpackHintV5 0xe3f950dce9c4d8392cd0e1d6c9a1d0c01264b7e20cb0d1c4a79250a0e9aa96fa7c91297488423a82e9567a6a20724a0864338660a0e45a61905491745168ca4c295042b25e3cb97e32529a2ae9da1ff2be1a317012a9e20ca9800541da000150 0x2aaa86c2c2c6d190b45d1745c01401c1eaa87c4c7c0c7c0c7c4c5c5c000000000000002aaaaaa5aaaa802aaa86c2c2c6d9875a42d1745d17561ba82ea13a80ea17800000b21c00000000808007013000c01705c0440880080002aaaaaa5aaaa800088280015541c1ea87c0c7c4c7c0c7c4ea86c2c2c6d4001455554000000000002aaaaaaaaa95401650b0b5551b1baa40d5513aa1b0b0b1b55559875555101c000000000b21c00004001100202001c04c0030105c04400583d55637aaaaaa550002200ba1b1fa1f1b0b0b1b69842d1745d17500007070b0b0b0b17071f131f031f031f13a000000002c87000000002a83e0b83e0f83d60f0fa0f0fa000ba1b1fa1f1b0b0b1b5a661d0b45d1745d5171b0b0b0b0b17171713170317031713a800000b21c000000002302001c04c003005c0401705c00170000aa0f82e0f83e0f583c3e83c3e800080f0002e1b86c6c2e1b07a07071f1fa1f1f1f031f131f031f131b0b0b1b23a23234fc5cfd23171b0b0b1b1f1f1f1f0000000000000aa0f0fa0f0fa0f82e0f83e0f83e000b1b0b1b1f1f1f1f1b0b0b1b1b0b0b1b1f1f1f1f000002c870000008007013000c017010003cdc3cdc3c2c2c3c3c7c3c7c3cdc3cdc00080f00707071fa1f1f0b1f1b1f0b1f1b0384e13130384ca00313031323a23234ec5ced23171f1f1f1f13030313070720700c0c01c0c01c0701c0301c072a88c3e8ac3e87e1f84e038ae2b881ca1717a07071f0b1f1b1f0b1f1b1fa1f505403a13031303135555555555500303007201c07100c442b0fa2b0faaa1f87e1380e5520711747e87d51b42d40e84d51340d40c4c0c4c1c8ea81c1d5541c1d41d541c6c1c1c1c2c1c1c0661d555555555550721410700701c00c870303003030344aa5643d47e1f84e0381c1e07a07070fa552072aaa5687c6c7c2c7c2c7c6ea80c4c0c4e82a1991745d45c5d41c1d0344e201c072800c0c200c0712aaaaaaaaaa58a2aaa80c4c0c4eaaa81c6c1c1c1c2c1c1c0661d691745d0344d41c5d41c1d586ea0ba84ea03a81e07aa81eaa85e880701c00c8703030030303071282070aaaaaaaaa81ea96aaaa28aaaaaa1f0b1f1b1f0b1f1baa54500313031355555555558803030500701c400c112aa3b83eaaaaaaa954a1642d551baa40d5513aa03130313507555550707aaaa071b0707070b070701555661d5555555541c1c1442201c0700321c0c0c00c0c0d1162b5558deaaaaaaaaa07a954a07e87d6a81d1f1b1f0b1f0b1f1b03a130313031303030030313190745d175a50790344c1c80701c07030030300700c0c0c0712a87e1f89c3e89c3e84e0385d620707e87c0e84c0c4c0c4c1c8ea81c1c1c6c1c1c1c2c1c1c05a661d1745d0344d41c5d41c1d5171b170b170b1717131313130303030317031313070707070707171707071707070707a81c80701c00c870303003030307101c1c01c1c2a87e1f84e0381c1e07a07070fa17585c3e85c3e881caaaa03130313aa1f1f1f1f13030313880701c0700c0701caaaaa8aa2845d0fa0f543d0b503a13544d035030f030f0fa0f543d0f50f0f0f0f2030f661d55555555543c1c85041c01c07100c0700c44aaaa030f030faa0f0f0f0f2a661d690f43d0344d0f43d583ea0ba84ea03a83ea0fa85e880701c803200c071282070aaaa030f030faa0f0f0f0f13a9559555556201c07100c807111642d550faa40d5513aa030f030f50f0f5550faa0f0f0f0f2a555598755555541c142201c07100c8031103e83c0e84c0c3c0c3c3e83c3c3c3c3c80c3d6998743d0f40d1343c3d0f0f543c3c3c2c3c2c3c3c4c4c4c4c0c0c0c0c5c0c4c4c3c3c3c3c3c3c3c3ea07201c0701c0301c0301c407070070700f0f0f0f03130313030f030f0f0f0f0f0f0f0f0f00c0c3c3c3c3c3c4c0c0c4c3c3c3c3c1c0701c0701c0301c0301c0707c7c7c7c0c4c0c4c0c4c0c4c1c1e0781c1c1c6c1c1c1c2c1c1c01f1f1f1f130303130741c5c1d07070701c0701c00c87030300303030701c2b372b371f1f1f1f130303130707070781c1c3c1e2b372b3701c1c1b1b000282c02800e80c0c0c0c0c0c0c0c0c0c0c0c0cbe8bcbd2f172f4bc5c2c2c2c2c0c0c0c0c000000000002a83c3e83c3e82e0b80e0383e0f8002c6c2e82e1e82c2ea03a0303030303030303030303030303032fa2f0b42c5c2d0b0b0b0b0b0b030303030000000000c87000008c0800b02c000b0000b06c00b02c00301701002a82c2e82c3e82e0b80e0383e0f800080f0a0000b0b000a8a030303aaaaaa030303033f4fc5cfd3f17aa0b0b0b0b030303030000000000000aaaaaaaaaaaa00aa82eaa82e1e80c0eaa80c4ea80c0c0c0e6a617aa0b0b0b0b030303030000000000c8700002000880080800b002c00301701002aaaaaaaaaaa80008805c5c000be87cbc2c7c6cbc2c7c6c0e80d540c0d40c0c0c0c5401415554000000000002a8ac3e8ac3e87e2b80e0395401174be87d51b42d40e80d50340d40c0c0c0d98755555554000000000321c000023020110010001b002c003040400aa5643d47e2b80e0395400080f0aaaa030303034645d1740d0300501f1b3f0b3f0b1f1baa0303a1717000000000000000aaaaaa96aaaa00 24 16777215 10 1023
def hc_64_13 : Nat → Nat := unpackHintV5 0xbb212055f8f32ae802955d02ea478ce4d649b250435d14327e89381c42384c9fa42f0eb523a75081437c05899da40cbcf23c5698fc23d8ee8f6a5045a042a2cd805166c000b2c0145720482b900015c8000a9c09044f1fe17216b06bc9a81da3080001da 0xba0b0707aa1313030300300c0c0e80c0c0c0c0e80c0c0e030333a330b0b0b0b334cc5ccd33170303030307201c0301c1c00c0c00c0301c072a82e0b83c3e83c3e80e0383e0f881c0313030707aa07230303030303030703030707030303030ba0b0303030b030b03030280e1e80c0ea03030303030303030307031303030303030b33a330340c5c0d03030741c1c1d07170b0b0b0b0303030307200c0c00c1c01c1c1c1c1c00b21c0c0301c072a80c0e80c3e81c3e81c1e82e0b80e0383e0f881c85ddd85ddd130301eaaaaaa808aaaaa030303030303030303030303aa0b0b0b0b5dc5ddd170303030388070801c1c2800c0301c072aaaaaaaaaaa8a2aa0707aaaaa07aaaaa0b0baaa0b1baa0280eaa80e1c0c0c0c0c0c0c0c0c0c0c0c0e6a617aa0741c1c1d07170b0b0b0b0303030381c282201c1c1c1c1c00b21c0c0301c072aaaaaaaaaaaaaaa8a02e82c1c1ea85c5d4114ce87c2c2c2c2ccc0c7c4ccc0c7c4d555555555541c807101c1c1401c07112a82e0b83c3e83c3e83e0f95481c45d0707aa07235550750707550ba0b542d0b500ce87d51340d41c0c1c1c1c0c1c4c2c2c2c2d987555555550745d55541c85041c01c1c1c1c1c00b21c1c07112a9590f5070fa0707a0b82e0f83e5520702e90707071707a282c2c2c2c8c7cbc7d0b42d41d45d1745ea82eaaa85e07201c80701c0712881caaaaaa96aa28aaa59aa08aaa0b0b0b0b73031f1373031f1369a42d0b507075171745d178807201c1c2801c0701c4aaaaaaaaaa9628aaaaa07aa02a81c0c1c1c1c0c1c4c2c2c2c2d9875a507075071742d0b45d175607aaa0781eaa0ba82ea13a80ea17a201c1c1c1c1c00b21c1c0701c4a081c2aaaaaaaaaa5aaaa8a04c7c0e1e1eaaaaa94116a82c2c2c2c0c7c4dfc0c7c4d55661d55555556201c1c102c8707070500701c44aaaaaaaaaa55285941c1d555541eaaa90b5542ea8040d5513aa07030707070307130b0b0b0b55559875555555541c142201c1c1c1c1c00b21c1c0711160f5558deaaaaaaaaa954a202c2c2c2c2c2c8c7c8c7d0b42d45c5d2361c1d1745c2c5c2c2c2c2c2e1c2d41c1c1c1d41c5c5c5c5ea0701c0701c0701c07101c1c170707078702e0b83e0f83e0f83d60f83e20702e82c1daa50b0b00b02c2cce87c2c2c2c2ccc0c7c4ccc0c7c4d90742d0b5079691745c1c80701c07070070700701c0712a82e0b83c3e83c3e83e0f83d620701c1e81ea0723070ba0b00ce87c1c0c1c1c1c0c1c4c2c2c2c2d6998741d41c1d41c1c5c5d0b42d1745d50707170707070707070707070717170b0b171b0b0b0b0b0b0b0b0b1713170317031713a81c80707070707002c870701c07101c1c170070707070aa070fa0707a0b82e0f83e0f583c3e83c3e881c0b0b0b0b4b234b92e4b23030300300c0c0c0c0c0c0c0c0c0d40c0c0d030345d1742d0b507075131340d030701c0700c07070030300300c07103c3c3c3c2c2c2c2c3c3c3e0f0f0f80c0c0c0c3d43c070701c1c1e0781cbc2c2c2c2c0030303030303030303030303030703130303030345d17507075071742d0b40d875030303330380e0303030703030303030307030703030303030b031b0303030b030b0303540c4c0c1c0701c1c1c1c1c00b21c0c0301c403030030700f0f0f0f070f0781c1c1e0b0b0b0b030303030f50f03030380c3c0e01c1c23a230b40c1c8e41c1c0f27231b04c0e17407270f0b0b0b0b030303030303030323a2350450303030303030303555555555550701c070400c0301c1c141103c3c3c3c2c2c2c2c0c0c0c0c3c3c3e0f0f0f954070701c1c1e0781cbc2c2c2c2c05654cd550741d5507550b542c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0d40d5555555555540d870701c0707070707002c8741c1400c031103c3c3c3c1c3c1e07070782c2c2c2d0f556030303035501c1c07070781e070b0b0b0b007c7c1c0c1c1c1c0c1c4c2c2c2c2c1d07070741c5c2c2c2c2c7c7c1c0701c1c1c1c1c00b21c1c0701c0703c3c3c3c1c3c1e07070782c2c2c2c3c3c3c3c3c3c3c3c070705c5c0002e86d41c1d547e87c7c0c7c4c7c0c7c4c6c2c2c6c65401415554000000000002a83c3e83c3e83e0b83e0f954011742e86d51b42d47e87d51340d46c2c2c6d98755555554000000000b21c0000230201100100007013000c040400aa5643d43e0b83e0f95400080f0 25 33554431 11 2047
def hc_64_14 : Nat → Nat := unpackHintV5 0xe51a20dcfa08cee386cb50e4c51190bf4174bc18cab6d950ad625ea7697e9d029a9599da8aa2be84e1707d59e27759806ff1da6ab15063d9b65f01365819ba5131ba4752783e7238331ad62bf9c822d24a1ae1fc1451a40e1190090144000240 0x1642d551baa507555550707aaaa01035544ea86c2c2c6c1c0c1c4c1c0c1c1d555661d5555555541c1c1442200b21c1c1c01c1c1c1c0711160f5558deaaaaaaa07aaa954a16a81d0ba1b0b0b00b0b1707e87c7c0c7c4c7c0c7c4c6c2c2c6d9075a50790b45d1745c1c807070070700702c1c1c0701c0712a83c3e83c3e83e0b83e0f83d620702e86c1c8ea81c1c01fa1f1b0b0b1b07030713070307075a661d0b45d41c5d41c1d1745d5171b171b0b0b0b0b170b17170707070707071717070717070707071713170317031713a81c802c87070700707070701c07101c1c01c1c2a83e0b81c1e07a07070fa0f83e0f583c3e83c3e881caaaa1b0b0b1baa1b0b0b1b1f1f1f1f880701c0701c0701caaa8aaaa2845d0ba0f543d0b50fa0f543d0f520b0f1fa1f544d0350f0b0b0f0f0f0f0f661d555555543d541c85041c101c0701c0701c44aaaa2aaa0f0b0b0f0f0f0f0f661d690b43d0f43d1745d583ea0ba83ea0fa84ea03a85e88807201c0701c071282070aaaa0faaa83c2c2c3c7c7c7c7d5595555562101c80701c07111642d550faa50f0f5550faa2a40d5513aa0f0b0b0f0f0f0f0f555598755555541c1422101c80701c071102e83c3e83c82c3c7e87c3c2c2c3c3c3c3c3d6998742d0f43c3d0f0f45d17543c3c5c6c2c2c2c2c3c2c3c3c3c3c3c3c3c3c3c3c5c4c5c0c5c0c5c4ea07201c0701c0701c0701c407070070700b0f0b0f0f0f0f0f02c2c3c7c7c7c7c3c2c2c3c3c3c3c3c3c2c2c3c3c3c3c3c7c7c7c7c1c0701c0701c0701c0701c0702c6c2c6c1c1e0781c1c01f1f1f1f1b0b0b1b07030713070307071b0b0b1b0741c5c1d07071f1f1f1f0701c02c87070700707070701c0701c0f370f370f0b0b0f0707070781c1c3c1e0f1f0f1f0f370f3701c1c13130000ba0b0303030307070303280c02800c0c0c0cce8cccd3317334cc5c2c2c2c2c0c0c0c0c000000000002a83c3e83c3e82e0b80e0383e0f8000c4c0c2e82c0c0c0c2c0c2c0c0e80e1e80c0ea03030303030b33a330340c5c0d03030b0b0b0b0303030300000002c8700000008c0800300c00030000700304c00300c01701002a80c0e80c3e82e0b80e0383e0f800080f0a000070707aaaaaa0303000a8a030303033f4fc5cfd3f17aa0b0b0b0b030303030000000000000aaaaaaaaaaaa00aa82c2eaa82c6eaa80eaa80e1c0c0c0c0e6a617aa0b0b0b0b0303030300000002c8700000020008800808007003000c01701002aaaaaaaaaaa80008805c5c0002e82d541c1d4ce87ccc0c7c4ccc0c7c4c2c2c2c2c5401415554000000000002a83c3e83c3e82e0b83e0f954011742e82d50b42d4ce87d51340d42c2c2c2d987555555540000000b21c000000230201100100007013000c040400aa5643d42e0b83e0f95400080f0aaaa0b0b0b0b4642d0b45d170050aa0707a1f133f033f031f131717000000000000000aaaaaa96aaaa00aaaa0b0b0b0b661d690b42d1745d582ea0ba84ea03a85e0002c870000000000202001c04c003005c040880080002aaaaaa5aaaa800088280001c1d556a8fc0c7c4cfc0c7c4ea82c2c2c2d40014555540000000b000000aaaaaaaaaa55005942c2d5542c6ea9035544ea82c2c2c2d555661d55540000000b21c0000004001100202001c04c003010100160f5558deaaaaa9540008802e82cce87c2c2c2c2d910b42d1745d40002c2c2c1c1c1c2c2c7c4ccc0ccc0c7c4e80000000000000002a82e0b83e0f83d60f0fa0f0fa000ba0b33a1f0b0b0b0b5a661d0b42d1745d50b0b0b0b0b0b0b0b1713170317031713a8000b21c0000000001701c02302001c04c003005c0401705c00170000aa0b82e0f83e0f583c3e83c3e800080f00b0b0b0b030303030303030345d1742d0b5140d2c8d2e4b92c8c0c0c0c0c1c1c0c0c01404c4c00000000000000003c3c3c3c2c2c2c2c0c0c0c0c3d43c3c3c3c3c3e0f0f0f27a000b0b0b0b030303030303030345d1742d0b40d875030303330380e0303030b0303030b0303540c4c0c000b21c00000000002f02001c00c003005c0400300c000300000f0f0f0f0b0b0b0b030303030f50f03030380c3c0e000203c02c2c2c2d3c8d3e4f93c8d41c1d540c0c0c0c0c0c0c0c0c0c00155554001440000000000003c3c3c3c2c2c2c2c3c3c3e0f0f0f80c0c0c0d54002c2c2c2d59533542d0b542d1b0303030303030303503555555550361c000b21c00000000002f02001c100044000304c00300c0404000f0f0f0f0b0b0b0b43d5580c0c0c0d5400080f0002c2e82c2c1c1e82c1c2e23a1f23031f132f031f130b0b0b0b23a23234fc5cfd23170b0b0b0b1f2f2f1f0000000000000aa0f0fa0f0fa0b82e0f83e0f83e000b0b0b0b1f1f0b0b0b0b0b0b0b0b1f1f0002c87000000008007013000c017010003c3c3c3c2c2c2c2c3c3c3c3c3c3c3c3c00080f00b0b070780b0b231f2f1f23071717172348d171717172f0781e41c1c1e0b0b9513030313171707070701c0701c0f83e0f83e0b0b6641d0742d81c1e02c2d171703513231f2f1f52348d5548d232f41c1c1c40701c43c3d5a0f83e0b0ba0b0b070707a00b02e23a1f0b0b0b0b23031f132f031f1323a230b0b0b0b2345d23171f2f2f1f070720701c0701c1c01c1c01c0701c072a82e0b83c3e83c3e83e0f83e0f881c 24 16777215 10 1023
def hc_64_15 : Nat → Nat := unpackHintV5 0xe5d21edee9bad342eacc69b6c3aa30bd818ab78180afb1f4a8f9ae9f1a7899d15293d1808b92108469ca7ac26a74998a6e998066c9f46011ae56327850e9524ae98042aa103b81ca31da6a2de8fc24aa501e01aa14127c0e4174055a3a000156 0x2cbe86c6c0cce84c4c0c0c2c2c0c2c0c0707aa130703030000b0b0002fa2f1b0b0b1b1303031345d1700221c0000000000aa0f1b82cae0f0f80c3e0f0fa0f0fa0f83e000ba0f03a13030b0303e83c0e0b0f0b80c3cbe8bc3c2c2c3c4c0c0c4c3c3c3c3c00887000003c00000700f002c013000c00f003c017010002cbe86c6c0cce84c4c0c0c2c2c0c2c0c4c8ea84c4c0c0c0c2c2c2cbe8bc6c2c2c6c4c0c0c4c4d13171344c4c00887000000000001c06c00b004c003004c130004c0005c0400aa0f1b82cae0f0f80c3e0f0f84e83c4c3e83e0f800080f066a951b42d6a951340d4bcbcbcbd9875555555400887000101c000000081100101c001b002c013000c0417011002a95996aaa954000882aa23aa88cbcbcbcbd69991745d1745d5171b170b170b17171713170317031713a800880000000001701c0806c00b004c003005c17011001c0700110002aaaaaa5aaaa80008802e86c1c1d5545c5c0007e87c6c2c2c6c7c0c7c4c7c0c7c4d5442d5005055000000000000aa0f82e0f0fa0f0fa0f83e55000ba0f0fa0f0f82c3c7e87c3c2c2c3c3c3c3c3d54555554008870003c0000000700f06c00b02c00f003c013000c0404000ba1b48d5951747e87c6c2c2c6d51340d5550b61d5555500221c00000000000701b06c00b02c0440040004c0030101002a83e0b956943d43e0f95400080f00ba0b33a1f0b0b0b0b645d450b45d170707aa0b0700501f13330333031f131717000000000000000aa0b82e0f83e0f583c3e83c3e8002e82cce87c2c2c2c2d91742d8750b0b45d170b23aa0b0b542c4c2c0c2c0c2c2c2c5c2c00887000000000001c02c00b004c003005c17011002c0b0002c0002a82e0b83e0f83d60b0ba0b0fa000203c20b0b0b0b0b0b0b231f231f515555000008c8700000000b21c001100000487000b82e0f83e0f83e55000055507070ba0b0b0b00033a1f33031f1333031f130b0b0b0b5550005155000000000000aa0f0fa0f0fa0b82e0f83e5500566548d0ba0b50b33a1f40d55130b0b0b0b5555550b61d5400887101c0000000000070400110002c1b002c0b004c0030105c04400aa43d5582e0b83e0f95400080f00ba1b1fa1f1b0b0b1b645d42c2d0b61c45d170707aa170750001f131f031f031f130b0b0000080000000000aa0f82e0f83e0f583c3e83c3e8002e86c7e87c6c2c2c6d91750b0b42d8745d171723aa1717545c4c5c0c5c0c5c4c2c2c2c00887000000000001c06c00b004c003005c0401705c00170000aa0f82e0f83e0f583c3e83c3e800080f01fa1f03a130313031307075551f1b1f0b1f0b1f1b13130005555103540140000000000002a87e1f84e038ac3e8ac3e954003e83c0e84c0c3c0c3c3e83c3c3c3c3c3e030f5555155500221c00000f000001c03c00b004c13000c03003c00f01010007e87c0e84c0c4c0c4d2356546d50b544d555540d87555400887000000000001c06c00b004c13000c0301100100040400aa1f87e1380e55a50f555000203c0be87c0e80c0c0c0c0d91745d175140c1c1ea80c0c7c6cbc2cbc2c7c6c01404c4c000000000000002a87e2780e0385d6270fa270fa002fa1f03a0303030303645d1745d0361d40c0c0c8ea80c0c0c6c0c0c0c2c0c0d503130300221c00000000000701b002c003000c01705c04400300c00030000aa1f89e0380e17580c0e80c3e800080f0030303031f23231f80c0c0d5545540000002321c00000000c870004400121c007e2b80e0388e239540000be87d5541c1c7c6cbc2cbc2c7c6c0e80c0c0c0c0c0c0c0015555400144000000000002a87e2b8ac3e8ac3e80e0395400be87d599523550b546c0e80c0c0c0c0d40d555555540d8700221c004070000000001c06c00b0100044000304c00300c0417011002a87e2b90f5560380e55000203c07e87c0e84c0c4c0c4d91745d175030340d8701c1ea84c1c7c6c7c2c7c2c7c6d40000c0c0000200000000002a87e1f84e0385d6270fa270fa001fa1f03a1303130313645d1745d40c0d0361c4c8ea84c4c4c6c4c2c4c2c4c4d503030300221c00000000000701b002c013000c01701004c130004c0002a87e1f84e0385d6130fa130fa000203c2aa80088700000001c06c00b004c003005c0400aa378de378de378de000203c01c1c1c2e1b86c6c2e1b2807e87c7c0c7c4c7c0c7c4c6c2c2c6c8e88c8d43174348c5c6c2c2c6c7c7c7c7c1c1c81c07070070700701c0701c0701caa0f0fa0f0fa0f82e0f83e0f83e207285c5e81c1d41502e86c7c0c7c4c7c0c7c4c7e87c6c2c2c6d5555555555401c1c01c840701c071103c3e83c3eaa83e0b83e0f95481c45d0ba1b546d0b50723aa0707555070750755007e87d51340d46c2c2c6c1c0c1c4c1c0c1c1d9875555555555541c85041c00b21c1c1c01c1c1c1c07112a9590f50f82e070781e81c1c3e83e0f95481ca95aaaa0a8aa1f031f131f031f131b0b0b1b66517175070742d1745d1788a00707080701c0701c4aaaaaaaaaa9628aaaaaa02a86c2c2c6c1c0c1c4c1c0c1c1d9875a42d17507175070745d17561ba82ea0781eaa07aaa13a80ea17a200b21c1c1c01c1c1c1c0701c4a081c2aaaaaaa07aaaa5aaaa8a2aaaaa95142a87c0c7c4c7c0c7c4c6c2c2c6d5555555556201c1c14100700701c44aa90e0faaaaaaaa5528 24 16777215 10 1023
def hc_64_16 : Nat → Nat := unpackHintV5 0x9a61b89381b88ce1a88908f684d10e7dc1c47ab0c47699066d126266b1985cd278534a624ce998430a783b11fe2fc2d427c9fe1c7ad4115ac80a39c805f91005b81005701205301004f01004a81203b03e027050019038015010011010000044 0xaaaaaa031303aaa030b038703030303030303aa1b0b0b1b0340c5c0d030303030303880701c03030030700300c0701c8aaaaaaaaaaaa28aaaaa030b038703030b0baaaa0303030b130baa0b0b0b0b130303130b42c5c2d0b0b880701c0700c07070070700701c8aaaaaaaaaaaa28aaaaaa03030baa03030303030303030b03aa0340c0c0d03170b0b0b0b030303038803070030300701c0300c0701c8aaaaaaaaaaa28aaaaa03031387aa0303030313131313880300c0701c0701c8aaaaaa13aa8a2aaa80c2c0eaa03a82eaaa1b0b0b1b1303031327272727880701c0700c0701c0701caaaaaa03030b0b030b03aaaa0303030b0b0baa1b0b0b1b130303131344c5c4d1313880701c0700c07070070700701c8aaaaaaaaaa84eaaa28aaaaaa2727272727272727880701c0701c0701c8aaaaaaa28020baa86eaa03aa84eaa6a617aaa07a0221c1c0701c0701c072aaaaaaaaaaaa8a282ea87a82eaaa0b030b130b030b0b0b0b0b0b0b2faa0b42c5c2d0b0b0b0b0b0b1f2f2f1f00221c0000b01c0000000801c070002c070002c1b002c0b004c003005c0400aaaaaaaaaaaa000220a8aaaaaa0f0b0f0b0f1b0f0f0f0faa0f0b0b0f0f0f0f0f1f1f1f1f00221c00000000803c1b002c0b003c00f004c003005c040082eaa87a0baaa86c2c7c2c6c6c6c0c6c4c6c0c6c4eaa231b0b0b1b1b46c5c6d1b171f1f1f1f00221c000001b01c00000806c1b002c0b001c070002c070004c003005c0400aaaaaaa86eaaaaa000220a03aa0303031b030b0303aa1ea03a80c0c0c0c0ccea80d03170340c0c7ccccc7c0c0c0c0c0088700000c070000000200300c000301c001b002c00304c00300c01701002aaaaaaaaaaa8000882aaa00c3c3c0c3c3ea83c3c3c3eaaa83c3c3c3c4c0c0c4c3c3c3c3c0088700000000200f002c01304c00300c00f003c01701002aa03aaa1c0c7c4c0c4c4e80c4c6c4c2c4c2c4c4eaaa88c7c7c7c7c4c0c0c4c4d13171344c4c00887000000004c07000201b002c01304c00300c00701c000300c001701002aaaaaaaaa13aaa80008802e86c1c1ea80c0c4c4c0000c0e80c7c030b03030300030302fa2f1b0b0b1b2f4bc5cbd2f1703030303000000000000aa0f82e0f0fa0f0fa030f80c0e0f83e000ba1b0323aa03030313030303a031f030b0387030303030303032fa2f1b0b0b1b0340c5c0d03030303030300221c00000000000701b06c00b02c00300c000300003000c01701002a83e0b80c0e80c3e80c3e030383e0f800080f00b0ba0b1f03a13030300c0c2c1c1ea82c1c000c0c04c4c000be8bc2c2c2c2c4c0c0c4ccd3317334cc5c000000000002a82c3e0b0b83e0383c3e83c3e83e0f8002c2e82c7c0e84c0c2c0e1c0c0c2c2c2c8ea82c2c0c0c0c2c4c2cbe8bc2c2c2c2c4c0c0c4c2d0b170b42c2c00887000000000001c02c00b004c13000c03002c0b0002c0005c0400aa0b0f82c2e0f80e0b0ba0b0fa0f83e000203c00c0ea80c7c2e82c0c0c2c0e80c0c0c0c0c0c0c0c0c2c0cbe8bc0d03030340c5c2c2c2c2c0c0c0c0c00887000000000001c00c1f0000c030002c1b002c0b000c13000c03005c0400aa030fa0303a0b82e0380e0f83e000203c00c0e80c7c4e84c0c0c4e1cbe8bc0c0c0c0c4c4c4c4c0088700000001c00c003004c13004c005c0400aa030f80c0e0f84c3c3e0f83e000203c00c0e80c7c1e84c0c0c00be8bc0c0c0c0c008870000002a80c3e030383e0f83e0f8021e1c5d87878787871761e07031f87870703e81c2c0c0c2c5d870703e872f87c8701e0f87878787172f86c1318701e0f 24 16777215 10 1023
def hc_64_17 : Nat → Nat := unpackHintV5 0xc5f1a2bbda86b2326aab79aea4e1a69ee97e9aa1129411a488e2cc8341687fe8d67a616272e9de6cd98463825662e0285d296e5601ca503174463a7e4099683d40d637b9623041de2a318420da562038281a816e1359ca0d897403927e0000e4 0x2822aa80c0eaaaaaaa84c4c0c2e030b0baa3b4ec5ced3b170b0b0b0b130303138807070070700701c0700c0701caaaaaaaaaaaa280282c2eaa82c6eaaa03aa84ea80c2c0e1c0c0c2c2e82eaaaa82c2eaaa80c0c0c2c4c2e6a617aa0b0b0b0b130303130b42c5c2d0b0ba07a0221c1c0701c0301c1c01c1c01c072a0faaaaaaaaaaaaaaaa8a00a0303aaaaa031faaaa82eaa0baa03030b80eaa03aa03030303030303030b039a985ea80d03030340c5c2c2c2c2c0c0c0c0e81e8088703070030300701c0300c0701ca83eaaaaaaaaaaaaaaa280280c0eaa80c7eaaa13aa84e13aa030313879a985ea80c0c0c0c4c4c4c4e81e808870300c0704c1c1c0701ca83eaaaaaaaaaa0faa8a2822aaaaa80c0eaaaa82c2c0c2c0eaa3b4ec5ced3b171b0b0b1b130303138807070070700701c0700c0701caa8ee0faaaaaaaaaa28a3baa86ea03aa84ea0b030b03a6988cecec8c6c2c2c6c4c0c0c4e81c1c1c01c2321c1c0701c0301c072aaaaaaaaaa8a2aaa80c2c0e8a0fa84eaaa0f0b0b0f1303031357575757a220701c0700c0701c0701c020baa83eaa03aa84ea80c2c0ea0f0faaa0faa03a82ea9a985ea83c2c2c3c4c0c0c4c3c3c3c3e81e808870701c0700c0701c0701c0282c2eaa86c6eaaa80c0eaa84c4eaa80c0c2c2c0c2c0e84eaaaa84c4e84eaaa80c0c0c2c2c2e6a617aa1b0b0b1b130303131344c5c4d1313a07a0221c1c0701c0301c1c1300707070700701ca83eaaaaaaaaaaaaaa84eaaa285045aaaaa1717aa1f031f131f031f131b0b0b1b555555555558407070500701c0701c44aa90e0faaaaaaaa5528aa8a0faaa83c2c2c3c7c7c7c7d555555568481c0701c0701c07110082eaa0faaa0f0faaa0faa0faa03aa84ea83c2c2c3c3c3c3c3d55555555555681e808870701c0701c0701c44020baa86ea99556655656545d80eaa13aa1b0b0b1b544d0355555645d550b61d55555a07a0221c1c071410700701c44a83eaaa27aaaa55a596a954a2822aa96a6aa91c0c7c4d1c0c7c4c2c2c2c2d996945c5d0b90b0b45d178807070070700701c0701c0712aaaaaaaaaa58a00a0b0baaa0b1baa80eaa13aa0b0b0b0b5a585d990b61d42c2d1745e82eaaaa82c2eaaa950b130b030b030b0b0b170ba07a0221c1c0701c0701c40707007070a83eaaa27aaaaaa96aaaa28131f038787aa5045a0b0baaaa0b0b0b0b031f1383031f13555550b61d55555681221c1c0701c1c1401c07112aaaaaaaaa954a0055665565595a0baa82ea942e03aa84ea9035544c2c2c2c2d55555555542d8755a07a0221d070500701c0701c44a83eaaa27aa6556aaaa5528a08aaaa9a5aa1f031f131f031f131b0b0b1b665a50b0b42d91745e201c1c01c1c01c0701c0701c4aaaaaaaaaa96280282c2eaa86c6eaa03aa84ea86c2c2c6d969685c5d9942c2d0b61d1745e85eaaaa85c5eaaa9517131703170317130b0b0ba07a0221c1c0701c0701c4070705c01c1c1c1c2a0faaa89eaaaaaa5aaaa8a14116a87c2c7c6c7c2c7c6eaaaa84c4c0c4c0c4d55555555556101c1c1401c0701c03112aa3b83eaaaaaaa954a2aaa80c3c0c3e283c3c3c3c4ea55555555a120701c0700c0701c44020baa83eaa03aa84ea80c3c0c3e83c3eaa83ea83c3c3c3c3ea555555555555a07a0221c1c0701c0301c07110082eaa1baa80eaa13aa031303136555995595951b542d51355555917555540d87555681e808870701c0700c5041c112a2baaa89eaaaaa9569655528a08aaa470b1f1b470b1f1baa5a9a03030303665a5131345d1740e40c0e201c1c00c0c01c0700c0301c4aaaaaaaaaa9628020baa86eaa80c0eaa80c4ea80c0c0c0d696176645d1740d8750303a03aaaaa0303aaaa031b0303030b0303540c4c0e81e808870701c0300c07100c0c00c1c2a2baaa89eaaaaaa5aaaa8a07c2c6e1e1eaaa80c0c0c0d41147c6c2e0c2c7c6e80c0ea955555540d875555a048870701c0300c070705044aaaaaaaaaa5528020baa86ea955995595656542d51b80eaa03aa030303035035555555555550361e81e808870701c41c1400c03112a2baaa89eaaa9955aa954a2822aa87c2c7c6c7c2c7c6eaaa6940c4c0c4d996940c0d1745d0368807070070700701c0700c0712aaaaaaaaaa58a0082eaa1baaa0303aaa1313aa0313031365a5a17176645d175030340d87a13aaaaa1313aaaa131b130b130b1313540c0c0e81e808870701c0700c07101c1c130070707070a8aeaaa27aaaaaa96aaaa282aaaaaaaaa0f0f0f0faaaa0f0f0f0f2b2b2b2b88880701c0701c0701c 24 16777215 10 1023
def hc_64_18 : Nat → Nat := unpackHintV5 0xb11166a832389fc21c9a216894b95a8f316285826c80d12c7c212c75c19870c93e6901f268981a64f0ea60313059d19854d93e4cc20648112c43612c3d019838093e3041f22fd81a2c30ea2771302111981c193e14020610a0d80a19a2000286 0x2aaa80c2c030b0baaaa00030301313000aa0b0b0b0b130303133b4ec5ced3b17000000000000aaaaaaaaaaaa00aaaaa030b038703030b0baaaa0303030b130baa0b0b0b0b130303130b42c5c2d0b0b221c000000000000802c1b002c0b004c003002c0b0002c0005c0400aaaaaaaaaaaaa000220aaaaaa03030baa03030303030303030b03aa0340c0c0d03170b0b0b0b03030303221c000000000000800c1f0000c030002c00b000c003005c0400aaaaaaaaaaaa000220aaaaa03031387aa0303030313131313221c0000004c00200307c00300c013004c01701002aaaaaa83eaa000220aaaa030b032aaa80c0c0002c2c002a86c2c2c6c4c0c0c4ced3b173b4ec5c0000000000002aaaaaaaaaaa802aaa80c2c0caa03a82eaaa0f0b0b0f130303130f0f0f0f221c0000000000803c00b004c003003c00f005c0400aaaaaa03030b0b030b03aaaa0303030b0b0baa1b0b0b1b130303131344c5c4d1313221c0000000001301c000806c1b002c0b004c13000c03004c130004c0005c0400aaaaaaaaaaa84eaaa000220aa55a51717000aa1b0b0b1b1f031f131f031f135515005055000000000000aaaaaaaaaa5500aaaa0faaa83c2c2c3c3c3c3c3d545555548870000000000200f002c00f003c013000c040400aa656545daa1b0b0b1b544d0355542d87555554887000000000000201b002c0440040004c0030101002aaa956965aa55000220aaaa0b0b0b0b66442d1745eaaa801407c4d1c0d1c0c7c4c5c5c000000000000002aaaaaa5aaaa802aaa82c2c2c2d990b61d42c2d1745eaaa950b130b030b030b0b0b170b221c000000000000802c00b004c003005c0400b02c000b0000aaaaaa96aaaa0002200b814020ba0b0b0b0b231f2f1f515555000000000000b00000100aaaaaa5500005a55aa0b0b000aa4f031f134f031f130b0b0b0b55500051552000000000000aaaaaaaaaa5500566566a942ea9035544c2c2c2c2d5555542d8755221c0000000000008100044000b002c013000c040400aa6556aaaa55000220aaaa1b0b0b1b6642d11745eaaa940007c4c7c0c7c0c7c4c2c2c000000000000002aaaaaa5aaaa802aaa86c2c2c6d9942c2d0b61d1745eaaa9517131703170317130b0b0b221c000000000001701c0806c00b004c003005c0401705c00170000aaaaaa96aaaa000220aaaa0313031355a51f1b1f0b1f0b1f1b13130005555150050000000000000aaaaaaaaaa5500aaaa030f030faa0f0f0f0f0fa9555455548870000000000200f002c013000c00f003c040400aaaa03130313656546d50b544d555540d875554887000000000000201b002c013000c04400400101002aaaaa95696555000220aaaa030303036645d17440eaaa87c6d1c2d1c2c7c6c01404c4c000000000000002aaaaaa5aaaa802aaa80c0c0c0d991745d0361d40c0eaaa80c6c0c0c0c2c0c0d5031303221c000000000000806c00b000c003005c0400300c00030000aaaaaa96aaaa00022003814000c0c0c0c7c8ccc7e03a555155000000000000003000100aaaaaa550000aa5a551f1b4f0b4f0b1f1baa03030303030300055555000512000000000000aaaaaaaaaa5500aa56656550b546ea80c0c0c0d40d555555540d87221c000000000000806c00b01000440003000c040400aaaa6556aa55000220aaaa031303136645d1740d2aaa87c6c7c2c7c2c7c6d40000c0c000000000000002aaaaaa5aaaa802aaa80c4c0c4d991745d40c0d0361eaaa84c6c4c2c4c2c4c4d5030303221c000000000001301c0806c00b004c003005c0401304c00130000aaaaaa96aaaa000220aaaaaa221c00000000806c00b004c003005c0400aaaaaaaa000220a08aaaaaa1313aa0303aaa80c0c0c0c0ea90d43174350c5c6c2c2c6c0c0c0c0e201c1c00c0c01c0700c0301c072aaaaaaaaaaa8a0082eaa1baaa03aaaaa0303aaaa031303a0303aaa0313aaa030b0387030303030303039a985ea86c2c2c6c0d03170340c0c0c0c0c0e81e808870701c03030030700300c0701ca83eaaaaaaaaaaaaaaaa28 24 16777215 10 1023
def hc_64_19 : Nat → Nat := unpackHintV5 0x9611de48b894227e77905839c7df1343cac931d244c8df3a7a67adfc31aa8b17675b8b461b65638fe28b29a935d3f08d9b544358dd1f3a9c8e9f3f867ab543068db16387f09e74d44759f81d05aa0cc86e852b4e42169fc0a0daa039e5a011c2cc000238 0x2e86c1c1c1c6c1c2c1c1c0c8ea80c0c0c1c0c1c0c0c0c0c0c1c0c0c0c0c0c0c4c0c0c0e80c7c0c0c0c0c0c0c0c0c0c2c0e1c0c0c0c0c0c0c0cbe8bc1d07170741c1c6c2c2c6c0d03170340c0c0c0c0c0c887a0a81c0700c0c00c1c00c0301c072a81c1e81c3e83e0b80c0e80c3e80c3e030383e0f881ca0a0b01c0c1c1c0c0c1c1c2c2e82c7c0c0c4c4c0c0c1c1c0e84c0c1c0c2ccd3317334cc5cbe8bc2c2c2c2c4c0c0c4c1e0a007201c0701c0301c0703c3e83c3eaa82e0b83e0383e0f881c002c2e82c7c1c1c1c2c1c2c1c1c0e84c0c0c1c4c0c0c1c1c0c2c0e1c0c0c2c2c2c8ea82c2c1c1c1c1c1c1c2c2c1c1c2c1c1c1c1c0c0c0c2c4c2cbe8bc1d07170741c1c2c2c2c2c4c0c0c4c2d0b170b42c2c887a0a81c0701c0301c1c01c1c01c072a81c1e81c3e82c3e0b0b83e0382c2e82c3e83e0f881c000c0ea80c7c0c0c0c0c0c1c0c7c0c0c0c0c0c1c0c1c2e82c1c1c1c2c1c2c1c1c0c0c2c0e80c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c2c0cbe8bc1d07170741c1c0d03030340c5c2c2c2c2c0c0c0c0c887a0a80c1c00c0c01c0700c0301c072a81c1e81c3e80c3e80c0e82e0b80e0383e0f881c000c0e80c7c0c0c0c0c0c0c0c0c4c4e84c4c1c1c1c4c1c4c1c1c0c0c4e1cbe8bc1d07170741c1c0c0c0c0c4c4c4c4c887a0a80c0301c0701c072a81c1e81c3e80c3e030383e130f0f83e0f881c070700704c0707071b0707070b1b80c0c1c4c0c1c1c0c4e0b030b03070741c1d07232323231b0b0b1b13030313a81c2321c1c1c01c0701c0301c0701e0783e0f83e0b83e0383e0f881ca0a1301c1c0c0c1c1c1c0c2cbe86c6c0c0c2c2c0c0c1c1c0cce84c4c0c2c0c1cfd3f173f4fc5cbe8bc6c2c2c6c4c0c0c4c1e0a0072a01c0701c0301c0703c3e83c3eaa83e0b83e0383e0f881c002e83c1c1c1c3c1c2c1c1c0e84c0c0c1c4c0c0c1c1c0c2c0c1c3e83c1c1c1c3c1c3c1c1c0e0b0f0b80c3cbe8bc1d07170741c1c3c2c2c3c4c0c0c4c3c3c3c3c887a0a81c0701c0301c1c0703c1c07000b2fa1b1b0707071b070b07070333a1313030307130303070703030b0b030b03132313aa1384c4c1c1c1c1c1c1c4c4c1c1c4c1c1c1c1c0c0c0c2c2c2cbe8bc1d07170741c1c6c2c2c6c4c0c0c4c4d13171344c4c887a0a81c0701c0301c1c01c1c01c072a81c1e81c3e83c6e0b2b83c3e030f83c3e13a0f130fa0f83e20700650741c011156a81c1c1c6c1c2c1c1d51b42d6a81c0c1c4c1c0c1c1d51340d4bcbcbcbd98755541d17555555554887a0a944141c1c01c0701c07112aaaaaa95996aaa954a00aa0707071b070b0707aa07030713070307072f2f2f2f5a661d41c1c5c5d075070745d1745d175554001c407070707171b170b170b17171713170317031713a8887a0a81c0701c0701c4070705c01c1c1c1c2aaaaaaaaaa5aaaa8a141501c1c5c5c1c1c1c1c2e86c7c0c7c4c7c0c7c4c7e87c6c2c2c6d55555555554281201c0701c071103c3e83c3eaa83e0b83e0f95481c002e83c1c1c1c3c1c2c1c1c3e83c1c1c1c3c1c3c1c1c3e0b0f1fa1f07030713070307070f0b0b0f0f0f0f0f555555555555221e82a0701c070701c0f0701c44002e86c1c1c1c6c1c2c1c1d2356541d075541d5545d1fa1f07030713070307071b0b0b1b544d03555555542d87555554887a0a81c071410700701c44aa0707a070fa0f82e55a50f50f83e5520728282c0741c1d41c1c2e82ccc0c7c4ccc0c7c4cce87c2c2c2c2d45c5d41c1d91741d0b45d170782801c80701c0701c07103c3e83c3eaa82e0b83e0f83d6207000ba0b0707070b070b070733a1f07030713070307070b0b0b0b645d41c5d41c1d0b61d42c2d1745c2c8ea82c2c1c1c1c1c1c1c2c2c1c1c2c1c1c1c1d50b130b030b030b0b0b170b221e82a0701c0701c07101c1c01c1c2a81c1e81c3e82e0b83e0f83d60b0ba0b0fa20702e82d15401c1c2c2c1c1c1c1cce87c2c2c2c2ccc0c7c4ccc0c7c4d55555555550801c07281401c07112a82e0b83c3e83c3e83e0f95481c01595235541d5541d070ba0b0707070b070b070750b33a1f070307130703070740d55130b0b0b0b55555555550b61d54887a0a941c1c14401c0701c07112a81c1e81c3e90f5560b82e0f83e5520728285c0707507070742e86c7c0c7c4c7c0c7c4c7e87c6c2c2c6d42c2d41c1d91742d0745d170782801ca80701c0701c07103c3e83c3eaa83e0b83e0f83d6207000ba1b0707071b070b07071fa1f07030713070307071b0b0b1b645d41c5d41c1d42c2d0b61d1745c5c8ea85c5c1c1c1c1c1c1c5c5c1c1c5c1c1c1c1d517131703170317130b0b0b221e82a0701c0701c07101c1c01c1c2a81c1e81c3e83e0b83e0f83d60f0fa0f0fa207141507c2c7c6c7c2c7c6c7e87c0c0c4c4c0c0c1c1c0e84c0c4c0c4d55555555554281201c0701c03110ac3e8ac3eaa87e1f84e0395481c003e83c1c1c1c3c1c2c1c1c0e84c0c0c1c4c0c0c1c1c0c3c0c3c3e83c1c1c1c3c1c3c1c1c3c3c3c3c3e030f555555555555221e82a0701c0700c070701c0f44007e87c1c1c1c6c1c2c1c1c0e84c0c0c1c4c0c0c1c1c0c4c0c4d2356541d075541d5546d50b544d5555555540d875554887a0a81c0701c0314107044aa0707a070fa1f87e1380e55a50f55520728280c2f0b1f1b2f0b1f1b2fa1f0340c0d40c0c0e80c0c0c0c0d44c4d41c1d91745d1740d030382800c80701c0300c07109c3e89c3eaa87e2780e0385d6207002fa1f0707071b070b070703a03030303030303030303030303645d41c5d41c1d1745d0361d40c0c0c8ea80c0c0c1c0c1c0c0c0c0c0c1c0c0c0c0c0c0c6c0c0c0c2c0c0d5031303221e82a0701c0300c07100c0c00c1c2a81c1e81c3e87e2780e0385d60303a030fa2070be87c0e80c0c0c0c0d15407c6cbc2cbc2c7c6c0c0c0c0c0c0c0c0d55555555550801c0700c032814112a87e2b80e038ac3e8ac3e95481c00be87c1c1c1c6c1c2c1c1d595235541d5541d07542d51b03a030303030303030303030303035035555555555550361c887a0a81c07141c1c14400c03112a81c1e81c3e87e2b90f5560380e5520728284c1f0b1f1b1f0b1f1b1fa1f0303503030740e84c0c4c0c4d40c0d41c0d91745d1740d070782801ca80701c0700c07109c3e89c3eaa87e1f84e0385d6207001fa1f0707071b070b070703a13030307130303070703130313645d41c5d41c1d1745d40c0d0361c4c8ea84c4c1c1c1c1c1c1c4c4c1c1c4c1c1c1c1c4c6c4c2c4c2c4c4d5030303221e82a0701c0700c07101c1c01c1c2a81c1e81c3e87e1f84e0385d6130fa130fa20700a0707071b070b0707a0703071307030707a0741c5c1d0707221e82a0701c0701c0701caa0707a070faaaa2072aaaaa84c4c002a803030303030003030aa1b0b0b1b4350c5d0d431703030303000000000000aaaaaaaaaaaa00aaaaaa031303aaa030b038703030303030303aa1b0b0b1b0340c5c0d030303030303221c000000000000806c00b000c030000c0000c13000c03005c0400aaaaaaaaaaaaa000220 25 33554431 10 1023
def hc_64_20 : Nat → Nat := unpackHintV5 0x80c0d23e00981dbb514e5e9fc7174603772521ad5390cdaa405f3de62df26b15c34d8a4da504d993524f276911a57c88801443e4172092580f583c476c10038b4ab1a6e7b0c6534859aa6027c145109cd1072f47c2c63460fa9a205968f812868c000250 0x56542c2c2c2d42c7c7d035544c2c2c2c2d5555542d875541d1502c2c2c2c7c7d543c3c3c3d0f5560b0b0b0b0f0f0f0f550f0f0f0f1717170b86e1b1b0b86da51f1fa1f1f1f031f131f031f131b0b0b1b61745c5d45c2d42c2d0b45d1745c8e88c8c1d0c43072306c2c2c6c7c7c7c7c5d45ea83c3e83c3e83e0b83e0f83d60f83e0b1b0b1b1f1f1f1f1b0b0b1b45d1750b0b42d8745d17171785e1717545c4c5c0c5c0c5c4c2c2c2c6c2c2c6c7c7c7c7c5d45c5c1c5c17071703c9c3c9c3c2c2c3c3c7c3c7c3d45c3c3c5e0f0f1783c9c3c9d51fa1f1f0b1f1b1f0b1f1b0384e13130384c4e84c4c0c4c0c4d555555555548e88c8c1cec3b072307c7c7c7c4c0c0c4d56a88c3e8ac3e87e1f84e03954ae2baaaa80c4c0c4d555556a87c7c7c7c4c0c0c4d56aaaaa956a83c3c3c3c0c4c0c4c0c3c0c3c3c3c3c3c3c3c3c3c3c0c0c3d555555543c3c3c3c4c0c0c4c3c3c3c3d547c7c7c7c0c4c0c4c0c4c0c4d56546d50b544d555540d8755547c7c7c7c4c0c0c4d51074552b272b271f1f1f1f1303031355943d554ac9cac9c6c6ea80c0c0e82c0e0303a030303a030340c0d40c0c0c0c0c0d9175131350b0b42d0b40d032fa2f2f072f0bc1cbc0b0b0b0b0303030317517aa0f0fa0f0fa0b82e0380e0f583e0f82c6c2e82e1e82c2ea03a030303030303030303030303030303645d42c5d42c2d0b42d0361d40c0c0c8ea80c0c0c2c0c2c0c0c0c0c0c2c0c0c0c0c0c0c2c0c6c0c0c0c2c0c2c0c0d50313032fa2f0b070b02c1c2c0b0b0b0b030303031751703030300c1c0caa0b0ba0b0fa0b82e0380e0f580c0e80c3e83e0faaaa82c2c0c0c0c0c0c0eaa95a9aaaa030303035a513136642d0b5940d1c1d1c4707472a82c2c2c2c0c0c0c0c5d45eaaaaaaaaaa5aaaaa0baaa0b87a0303aaa0313aa030303035a585d990b42d0361d40c0e80eaaaa80c0eaaa80c2c0c0c0c2c0c0d503130381e2a2a82c2c2c2c0c0c0c0c5d45c0c0c0c0307032aaaaaaaaaa5aaaaaa80c0c0c8e87c8c2c7c6ccc2c7c6c0c0e80c0d680d0380c0c0c0d85d1717517135131345d1740d0323a2323074711c1c8c1f33331f0303030317517aa230fa270fa1f89e0380e17589e2787c7c0c0c0c0c0c0c0c0d1745d1745d0361d40c0c0c0e0380c0c0c6c0c0c0c2c0c0d50313031f1f030303031751703030300c1c0c272727271f27271f030303031751703030380c3c0e27272727682c0e80c0c0c0c0d5546c6d69540c0c0c0c0c0c0c0d5555555554be8bc2c2c2c2c0c0c0c0cbc1cbc2f072f156a82e0b80e0383c3e83c3e9543e0f82c6c2e82e1e82c2ea56548d550b5550b42d50b42d50b46c0e80c0c0c0c0c0c0c0c0c0c0c0c0c0c0d40d5555555555540d872fa2f0b070b02c1c2c0b0b0b0b41d1500c0c0c0d56a82c2e82c3e82e0b90f5560380e550f83e87b0787b1b0b07176a6aa80c0c0c0d695542c2d5680c0c0eaa955555555556a82c2c2c2c0c0c0c0c1dec7b07156aaaaaaaaa956aaaa0baaa0b8755665565595950b542e80c0eaa80c4ea80c0c0c0d40d5555555555540d8781e2a2a82c2c2c2d074540303030355aaaaaaaa6556aa55aa030351f23331f80c0c0d5548c00332308c0102006c0b200c0701d1008e2b883c03034055070b071b80c0e51f23331f80c0c0c0555550708c233307070707070708c23070f2b81c1e88e2b88e87c0c0e80c0c0c0c0c0d51f1b230b330b1f1ba03030303039555555555548e88c7ccccc7c0c0c0c0c8c1c0723156a87e2b80e0388c3e8ac3e954ae2b87c7d595542d51b0303030303030303503555555550361c7c7d0745403030303552b272b271f272b1f43d5580c0c0c0d54ac9cac9c4c4c4c7c7e87c7c7c2c7c6c7c2c7c6c0e1384c4c0e136940c4c0c4d85d1717517035030345d1740d1323a2323073b0ec1c8c1f1f1f1f1303031317517aa230fa270fa1f87e1380e17589e2787c7c7c7c0c4c0c4c0c4c0c4d1745d1745d40c0d0361c4c4e1384c4c4c6c4c2c4c2c4c4d50303031f1f1f1f130303131751713071304c1c4c272727271f1f1f1f1303031317517130f1384c3c4e272727270282c1c1c1c1c001c0b01c1c1c1ea87a82c1c1c1c1c2c6c1c1c2c2c1c1ea88ea81c0c1c4c1c0c1c1c2c0c2c4c2c0c2c2c2c2c2c2c2cbea81d07170741c1c2d0b170b42c2c2c2c2c2c7cbcbc7c887a0a81c1c0b00707070700701c0701c0701caaaaaaaaaaaaaaaa2802a81c1c1c3c1c2c1c1ea81c1c1c3c1c3c1c1eaaa81c0c1c4c1c0c1c1c3c2c3c2c3c6c3c3c3c3ea81d07170741c1c3c2c2c3c3c3c3c3c7c7c7c7c887a0a81c0701c0701c0701c070082eaa87070707071b1b07070b0b0707a0b07070707000702c07070707aaa81c0c1c4c1c0c1c1c6c2c7c2c6c6c6c0c6c4c6c0c6c4ea81d07170741c1c6c2c2c6c6d1b171b46c5c7c7c7c7c887a0a81c0701c1c1b00707070700701c0701caaaaaaaaaaa86eaaaaa280280c0c1c0c1c000c0300c0c0c0e23aa0707071b070b07070303031b030b0303aa1ea03030303070313030303030303a80c0c0c0c0ccea81d07170741c1c0d03170340c0c7ccccc7c0c0c0c0c887a0a80c0c0300303070700701c0300c0701caaaaaaaaaaaaaaaa2802a81c1c1c3c1c2c1c1ea80c0c1c4c0c0c1c1c0c3c3c0c3c3ea80c0c1c3c1c3c1c1c3c3c3c3eaaa81d07170741c1c3c3c3c3c4c0c0c4c3c3c3c3c887a0a81c0701c0301c0701c0700aa0707071b070b070780eaa87030307071313030703030707031f13031313a0303030303000700c07070707131b130b130b1313aaa81d07170741c1c7c7c7c7c4c0c0c4c4d13171344c4c887a0a81c0701c0301c1c1300707070700701caaaaaaaaaaaaa84eaaa28a0a0301c1c4c4c1c1c1c1c2e86c0c0c0c0c0c0c0c0c0c0e80c7c0c0c0c0cbd2f172f4bc5cbe8bc6c2c2c6c0c0c0c0c0e0a003201c0700c0301c0703c3e83c3eaa83e0b80e0383e0f881c 25 33554431 10 1023
def hc_64_21 : Nat → Nat := unpackHintV5 0xb35810b31810b2d012b20832b0f844b0003eafc010af8010ae4050a402909a1a7a8a83e68421987c31fc7930c07411486cf1c863f24054c3cc4e11ac44626c3b2250317a6a2d79002821562071ec1909da0e12be0dc0140d082e0789600001e2 0x21e1e1e1e1c079031f876870fa42c0c0c2c876070fa1e1cbe1f031760f87878787870be1b0b1303071760f0b2fa1b1b0333a131303030b0b030b03135aa1340c0c2c2c2c2c5c0c2c2c0c0c0c0c4c2d699871342d1740d135a5138be8bc6c2c2c6c4c0c0c4c1c0705d45ea83c6e0b2783c3e030f83c3e83c3e83d60f83e0ba0f03a13030b030f0fa0f0382c3c2e030f5a661d0b43d0344d0f0f43c3d50f0f0b0b0b0b0f0f13130303030313130f0f0f0f0f0f0f0fa8be8bc3c2c2c3c4c0c0c4c3c3c3c3c5d45c5c1c5c17071702cbe86c6c0cce84c4c0c0c2c2c0c2c0c4c8ea84c4c0c0c0c2c2c2d6998742d1740d135131751313545c6c2c2c2c2c5c5c4c4c0c0c0c0c4c4c4c4c4c4c4c4c5c5c4c4c5c4c4c4c4ea2fa2f1b0b0b1b1303031313071304c1c4c1751717071705c1c5caa0f1b82c9e0f0f80c3e0f0f84e83c4c3e83d60f0fa0f0fa0f83eaa5a661d1745d1745d5171b170b170b17171713170317031713aa85d45c5c1c5c1707172a89e2789e2785d6170fa170fa2789e542e1b86c6c2e1b17a17171fa1f1f031f131f031f131b0b0b1b5555555555523a2323074310c1c8c1b0b0b1b1f1f1f1f55aa0f0fa0f0fa0f82e0f83e550f83eaaaa1b0b0b1b555555aa1b0b0b1b1f1f1f1f55aaaaaa55aa0b0f0b0f0f0f0f0f0f0b0b0f1f1f1f1f0f0b0b0f0f0f0f0f555555550f0b0b0f0f0f0f0f1f1f1f1f550b1b0b1b55951747c7c7c7c6c2c2c6d51340d5550b61d555551b0b0b1b5441d07c7c7c7d543c9c3c9c3c2c2c3d5650f50f1f0f1f550f270f271313aa0b0b0ba0b0340c0d40c0c0e80c0e0303a030303030303645d45c5d40c0d0342d0340cce8cccc1ccc33073302c2c2c2c0c0c0c0c5d45ea83c3e83c3e82e0b80e0383d60f83e0313030ba0b0303030b030b0303a0387a0303a80c0c0c0c0c2d917503175030342d8750b0b40d030b23aa0b0b0303030303030b0b03030b03030303540c0c2c4c0c0c0c0c0c0c0c0c2c5c2cce8cc0c0c0c03070302c2c2c2c0c0c0c0c5d45c2c1c2c0b070b2a80c0e80c3e82e0b80e0383d60b0ba0b0fa0f83eaaaa56a6aaa80c0c0c0c0c0c0c0eaa80c0c0c0d6945c5d99650b40d0347074711c1d1caa0b0b0b0b0303030317517aaaaaaaaaa96aaaa82c2eaa82c6eaa80eaa80e1c0c0c0c0d696176642d8750b0b40d03a0baaaaa0b0baaaa540c0c0c0c0c0c0c0c2c5c2e078a8aa0b0b0b0b03030303175170b070b02c1c2caaaaaaaaaa96aaaaaa0b0b0b0b0ba0b0b5a0b42e23a1f23031f132f031f130b0b0b0b61745c5d45c5d45c5d0b42d1745c8e88c8c1d1c47072302c2c2c2c7cbcbc7c5d45ea83c3e83c3e82e0b83e0f83d60f83e0b0b0b0b1f1f0b0b0b0b45d1742d8750b0b45d170b0b82e0b0b542c4c2c0c2c0c2c2c2c5c2c2c2c2c2c7c7c5d45c2c1c2c0b070b03c3c3c3c2c2c2c2c3c3c3c3c3d43c2c2c2e0b0f0b83c3c3c3c2c2d60b0b0b231f2f1f55523002308c002f408080b01c071300c4400f83e20f02c2d01560b07960b0b0b000c1c0c4c8c7cbc7d555541c2308c1c1c1c1c1c2308cbc1c1c3c3e0707a0f83e0b0ba0b0b5682c2c2c2c2e23a1f0b0b0b0b23031f132f031f135555555555523a230b0b0b0b230701c8c1f2f2f1f55aa0b82e0f0fa0f0fa0f83e550f83e0ba0b555131303030b0b03030303680c0c0c0c0e95555555555554ce8cc2c2c2c2ccc1ccc33073300c0c0c0d56a82e0b83c3e83c3e80e039543e0f80c4c0d595235540d5540d030ba0b0303030b030b030350ba0387a0303a940c0d5540c4c0c0c0c0c0c2d55555555542d875533a3303030300c1c0c41d1502c2c2c2c0c0c0c0d56a80c0e80c3e90f5560b82e0380e550f83e85f0785f071303176a9695682c2c2eaaaa680c0c0c0c0c0d55555555555556a82c2c2c2c1d7c5f0700c0c0c0d56aaaaaaaaa956aaa55665565595a82c2eaa82c6ea942e80eaa80e1d035540c0c0c0c0d55555555542d875581e2a2a9074540b0b0b0b0303030355aaaaaa6556aaaa55aa 24 16777215 10 1023
def hc_64_22 : Nat → Nat := unpackHintV5 0xec9a44e3fa28de017ed8596ad33948cfb0e2c9f96ebfea84bce8c0b6f97cb1097cab596ca810d2a498de9e79889bf8a09888dc8ba33a822a5e74eb5068033a5e8a5e514b50478a70381bdc2e5a701eebdc0f7bdc05ba7000894c004810000012 0x1650b0b5550b1baaa40d5513aa030b038703030b0b50b555550b0baaaa0303030b130b55559875555555541d152a82c2c2c2c4c0c0c4c2c1c2c0b070b15560f555aaaaaaaaaaa956a965030355555031faaaa42d550baa03030b40d5503aa03030303030303030b0355559875555555541d152a80c1c0c03030302c2c2c2c0c0c0c0d5560f555aaaaaaaaaa956a9650303555031faaa44d551384ea80c0c4e1d555661d5544d541d152a80c0c0c0c4c4c4c4d5560f555aaaaaaa83e55aaaaaaaa5550303aa5550b0b030b0355555555556a8ec1cec3b073b06c2c2c6c4c0c0c4d56aa3b83eaaaaaaa956a94ed551ba80d5513a82c0c2c0d555548d87555541d548cecec8c6c2c2c6c4c0c0c4d55556aaaaa956aaaaa80c2c0daa0fa84ea556555555aa0f0b0b0f130303135757575755590b5543ea9035544ea80c2c0d50f0f5550faa03a82ea555598755555541d152a83c2c2c3c4c0c0c4c3c3c3c3d55650b0b5551b1baaa503035551313aaa03030b0b030b03513555551313a13aaaa0303030b0b0b55559875555544d1755541d152a86c2c2c6c4c0c0c4c4c1c4c13071315560f555aaaaaaaaaaaa13a956aaaaaaaaaaa83c3c3c3d55555556aaa83c3c3c3cacacacad56aaaaa80c4c0eaa80c2c0e1c0c0c0c0c0c0c0d5555555556a86c2c2c6c0c0c0c03070300c0c0c0d56aaaaaaaaaa956aaaaaa80c2c0e1c0c0c2c2eaaa80c0c0c2c4c2d5555555556a82c2c2c2c4c0c0c4c2c1c2c0b070b156aaaaaaaaaa956aaaaaaa80c0c2ea80c0c0c0c0c0c0c0c2c0d5555555556a80c1c0c03030302c2c2c2c0c0c0c0d56aaaaaaaaa956aaaaaa80c0c4e1d555556a80c0c0c0c4c4c4c4d56aaaaaa84e55aaaaaa030b036a80ea0ba955555556a86c2c2c6c4c0c0c4cdcdcdcdd56aaaaa80c0c2c2c0c2c0eaaa80c0c0c2c2c2d5555555556a86c2c2c6c4c0c0c4c4c1c4c130713156aaaaaaaaaaa13a956aaaaa9555556a8dcdcdcdcdcdcdcdd56aaaaa956a9642d551baa40d5513aa5555987555541d152a9556555aaaaaa956aa82ea87a82eaaa0b030b130b030b0b0b0b0b0b0b2f5a661d42c2c5c5d0b50b0b42d0b45d1755542c2c5c5c2c2d42c2c2c2c2c2c5c6c2c2c2c2c2c2c2c2c5c4c5c0c5c0c5c4eaaa0b070b02c1c2c0b0b0b0b1f2f2f1f1751717071705c1c5caaaaaaaaaa96aaaaaaaaaaaaaa0f0b0f0b0f1b0f0f0f0f5a661d0b43d0f43d1745d50f0f171b0b0b0b0b0f0b0f0f0f0f0b0b0f0f0f0f1713170317031713aaa83c2c2c3c3c3c3c3c7c7c7c7c5d45c5c1c5c17071720baaa1e82eaaa1b0b1f0b1b1b1b031b131b031b135a661d0b45d45c5c5c5d1b5171745d17545c6c5c6c2c2c2c2c5c2c5c5d542c2c2c2c5c2d45c5c5c5c5c4c5c0c5c0c5c4eaaa88c6c2c2c6c6c1c6c1b071b07c7c7c7c5d45c5c1c5c1707172aaaaaaa1baaaa5aaaaaaa80ea80c0c0c6c0c2c0c0ea87a80ea0303030303335a661d40c0c5c5d035030345d1740d0355540c0c4c4c0c0d40c0c0c0c5c6c5c2c5c2c5c5c0c0c5c4c0c0c0c0c0c0c0c0eaaa03030300c1c0c1f33331f030303031751717071705c1c5caaaaaaaaaa96aaaaaaaaaa030f0f030f0faa0f0f0f0faa5a661d0f43d0344d0f43d50f0f0f0b0f0b0f0f1313131303030303170313130f0f03030f0f0f0faaa83c3c3c3c4c0c0c4c3c3c3c3c5d45c5c1c5c1707172aa03aaa1c0c7c4c0c4c4e80c4c6c4c2c4c2c4c4ea5a661d1745d0344d44c4c5c5d1351313545c6c5c2c5c2c5c5c4c4c4c4c0c0c0c0c5c0c4c4d540c0c0c0c4c0d44c4c4c4eaaa88c7c7c7c7c4c0c0c4c4c1c4c13071305d45c5c1c5c1707172aaaaaaaaa13aa5aaaaaa82e86d6a80d13130b0b0b0b17130303a031f03030b0303030303030303030303640d0b45d6940e40d032fa2f1b0b0b1b2f072f0bc1cbc0303030317517aa0f82e0f0fa0f0fa030f80c0e0f583e0f82e86c0c8ea80c0c0c4c0c0c0e80c7c0c2c0e1c0c0c0c0c0c0c0d6998742d17503175030340d03545c6c5c6c2c2c2c2c5c2c5c5c0c0c0c0c0c0c5c5c0c0c5c0c0c0c0c0c0c0c0c0c0c0c0ea2fa2f1b0b0b1b03030300c1c0c030303031751717071705c1c5caa0f82e0303a030fa030f80c0e0f583c3e83c3e83e0f82c2e82c7c0e84c0c0c2c0c0c2d6a82d0b0b0b0303030b0b1313030303031313642d0b42d0344d6942e2fa2f0b0b0b0b130303133307330cc1ccc17517aa0b0f82c2e0f80e0f0fa0f0fa0f583e0f82c2e82c7c0e84c0c2c0e1c0c0c2c2c2c8ea82c2c0c0c0c2c4c2d6998742d0b40d1350b1750b0b542c2c2c2c2c2c2c2c4c4c4c4c0c0c0c0c5c0c4c4c2c2c2c2c2c2c5c5c2c2c5c2c2c2c2ea2fa2f0b0b0b0b130303130b070b02c1c2c1751717071705c1c5caa0b0f82c2e0f80e0b0ba0b0fa0f583c3e83c3e83e0f80c0ea80c7c2e82c0c0c2c0e80c0c0c0c0c0c0c0c0c2c0d69987503035031742d0b40d03540c0c5c7c0c0c0c0c0c0c0c0c0c0c5c5c2c2c5c6c2c2c2c2c2c2c2c2c0c0c5c4c0c0c0c0c0c0c0c0ea2fa2f03070300c0c0c0b0b0b0b030303031751717071705c1c5caa030fa0303a0b82e0380e0f583c3e83c3e83e0f80c0e80c7c4e84c0c0c4e1d6998740d0344d13540c0c0c0c0c0c0c0c4c4c4c4c4c4c4c4c5c4c4ea2fa2f03030303131313131751717071705c1c5caa030f80c0e0f84c3c3e0f583c3e83c3e83e0f80c0e80c7da130303030303035a661c0d0340d9132fa2f0303030317517aa030f80c0e0f83e0f583e0fa1e1c8707 24 16777215 10 1023
def hc_64_23 : Nat → Nat := unpackHintV5 0xf8e180ee62a0e4b26cdea184d4ea6ecb3a6cc52984bb726eb3f9dea8fac0a181de9682c08c02a084d1cc7e599e7691f26fa9ba63bafc6088cc5a01a2501a7a4991a23faa7a36325e2fd198297996231998184ab41441020ea966059a44000166 0xb0f0b0f03130313030b030f0f0f0f0f030b0b0f0b03030f0f0b0b0f130303130f0f0f0f0f0b0b0f130303130f0f0f0f0b1b0b1b1b031303131303030b0b030b03131384e13130303030b0b0b1b0b0b1b130303131344c5c4d13131b0b0b1b1303031313071304c1c4c0f0f0f1b0b0b2b0f0f0f03030f130f0f131383c4c3c4e0f0f0f0f6682d5542c2d42c5d56a87a82d542c6d42c2d6a88ea951340d42c0c2c4c2c0c2c2c2c2c2c2c2cbd987555550b45d5555556a9510740b070b02c1c2c0b0b0b0b1f2f2f1f55aa5665aaaaaaaa55aa66a550f42d6a950f43d6aaa951340d43c2c3c2c3c6c3c3c3c3d9875555555556a9510740f0b0b0f0f0f0f0f1f1f1f1f55660baaa1d546c6d42c2d682d5545c5d42c2d56aaa544d0351b0b1f0b1b1b1b031b131b031b13661d55555546d1755555aa5441d06c2c2c6c6c1c6c1b071b07c7c7c7d56a95996aaaaa1baaa956a99a035550303503135588ea951b42d40c0c0c6c0c2c0c0ea87a80d540c4d40c0d6a030303030333661d555540d175555555aa5441d00c0c0c03070307ccccc7c0c0c0c0d56a95996aaaaaaa956a99aa543d0b5a9544d035030f0f030f0faa543d0f50f0f0f0faa661d555555555aa5441d03c3c3c3c4c0c0c4c3c3c3c3d559aa546d0b580eaa87551313503035031f13031313a0355513135030355131b130b130b1313a99875555555551345d556a9510741f1f1f1f1303031313071304c1c4c55aa5665aaaaaaa84ea55aaa1717a030351313550ba1b55030350303a031f40c0c0d5555555554bc1cbc2f072f0be8bc6c2c2c6c0c0c0c0d543c3e83c3eaa83e0b80e039543e0f91742e86d51b42d40c8ea80c0d5540c0d40d540c4c0c0c0e80c7d50340d40c2c0e1c0c0c0c0c0c0c0d987555555555554be8bd510741b0b0b1b03030300c1c0c0303030355aa5643d43e0b80c0e80c3e80c3e03039543e0fa85c5e82c2d540c0d42c2e82c7d44c4d540e84c0d030b55555555553307330cc1ccc2fa2f0b0b0b0b13030313550f0fa0f0faaa0b82e0f80e550f83e45d0b0ba0b1f542d0b503a13544d035030b038703030b0b0b23aa0b0b5550b0b50b550303030b130b661d555555555552fa2f5441d02c2c2c2c4c0c0c4c2c1c2c0b070b156a9590f50b0f82c2e0f80e0b0ba0b0fa550f83e45d0303aa031f555031f50303550ba0b542d0b503030b03a03540d03503030303030303030b03661d555555555552fa2f5441d00c1c0c03030302c2c2c2c0c0c0c0d56a9590f5030fa0303a0b82e0380e550f83e45d0303a031f540d0351313a1313544d13503031387661d55555552fa2f5441d00c0c0c0c4c4c4c4d56a9590f5030f80c0e0f84c3c3e550f83e5551313546d50b1b80d44d5031382c0c2c0d5548d87555555550748c8c8c8c6c2c2c6c4c0c0c4d55543e0f83e0b83e039543e0fa85c5e84c4d40c0d542cbe86c6d42c2d540cce84c4c0c2c0d5555595555547074711c1d1c2fa2f1b0b0b1b13030313550f0fa0f0faaa0f82e0f80e550f83e45d0ba0f543d0b503a13544d035030b0343e83d50f43d40e0b0f0b80c3d98755555555550f2fa2f5441d03c2c2c3c4c0c0c4c3c3c3c3d551742cbe86c6d51b42d40cce84c4d51340d40c0c2c2c0c2c0c4c8c4ea84e13135551313513550303030b0b0b661d555555555552fa2f5441d06c2c2c6c4c0c0c4c4c1c4c130713156a9590f50f1b82cae0f0f80c3e0f0f84e83c4c3e9543e0f9176951b42d6951340d59875555555695107455aa5643d6a956aaaa5684c4eaaaaa0303030303aa0303a6642d17517175030340d03aa1b0b0b1b43074310c1d0c0303030317517aaaaaaaaaa96aaaaaaaa031303aaa030b038703030303030303661d690b45d40c5d40c0d0340d586ea0ba80e03aa80eaa80e13a80e03a85eaa1b0b0b1b03030300c1c0c0303030317517a881e2aaaaaaaaaaa5aaaaaaaaaa80c2e030b0ba95aaa0303a1313aaa6642d0b40d135171750b0baa0b0b0b0b130303133b073b0ec1cec17517aaaaaaaaaa96aaaaaaa030b038703030b0baaaa0303030b130b661d690b42d0344d42c5d42c2d582e1ba82e0ba84ea03a82e0baa82eaa85eaa0b0b0b0b130303130b070b02c1c2c17517a881e2aaaaaaaaaaa5aaaaaaaaaaaa80c0c2ea80c0c0c0c0c0c0c0c2c0d9875a503035031742d0b40d03560387eaa0380eaa0ba82ea03a80ea17aa80c1c0c03030302c2c2c2c0c0c0c0c5d45ea2078aaaaaaaaaa96aaaaaaaaaaa03031387661d690340d131344c4d580e1fa80e03a84ea13a85eaa030303031313131317517a881e2aaaaaa83e96aaaaaaaaaa030b03aa5680c0eaa82c2eaa96590b45d0344d45c5d44c4ea86c2c2c6c4c0c0c4cec1cec3b073b05d45eaaaaaaaaaa5aaaaaa80c2c0eaa03a82ea661d690b43d0344d0f43d583ea0ba84ea03a83ea0fa85eaa0f0b0b0f130303130f0f0f0f17517a881e2aaaaa80c0c2c2c0c2c0eaaa80c0c0c2c2c2d9875a42d1740d1351313171744d44c4d586e1ba82e0ba84e13a80e03a84e13aa84eaa85eaa1b0b0b1b1303031313071304c1c4c17517a881e2aaaaaaaaaaa13aa5aaaaaaaaaa99875a45d1745d17561ba82ea13a80ea17aa85d45ea2078aaaaaa96aaaaaaaaaaaa5551313aa030355540c0c0c0c0d5555555556a90c1d0c43074306c2c2c6c0c0c0c0d56aaaaaaaaa956a9642d551baa503555550303aaaa031303503035550313aaa030b03870303030303030355559875555555541d152a86c2c2c6c0c0c0c03070300c0c0c0d5560f555aaaaaaaaaaa956aaaaaaa80c0d556a95544c4c0c2d030b0b5555555555aa3b073b0ec1cec0b0b0b0b1303031355aaaaaaaaaa55aa 24 16777215 10 1023
def hc_64_24 : Nat → Nat := unpackHintV5 0xc2f20abd5966b9b8e8b5e0f6b0b94aac9908a6f9689dd24a8f7398874a0a81b1667e10e87a38f675114a70f1086b5168622a4a583a7c4d5ab8436a7c388ab82e2a98250a481dd1ce14b2480df1b004426c000110 0x2c6c2e82e1e82c2eaa1f0b030b130b030b0b0b0b0b0b0ba0b42c5c2d0b0b0b0b0b0b1f1fa0b070b02c1c2c0b0b0b0b1f1faa0b0ba0b0fa0b82e0f83e0f83e0f83ea0b87aaaa1baa86c2c2c6ea1380eaa86c2c2c6e6179a1f1f1f1faa1b0b0b1ba881e07c7c7c7eaaaaaaaaaaaaaaa80c0c0c0ea80c0c0c0ea82c2c2c2c0c0c0c0ea82c2c2c2eaaaaaaaaaaaaaa82c2c2c2ea82c2c2c2c4c4c4c4ea82c2c2c2c4c4c4c4eaaaaa83eaaaaaa82eaa82e1e80eaa84ea82c2c2c2e6a617aa0b0b0b0b1f1f81e2a2a82c2c2c2c7c7eaaaaaaaaaaaaaaaaa86c2c2c6ea86c2c2c6c7c7c7c7ea86c2c2c6c7c7c7c7c9c9c9c9eaaaaaaaaa82e83c2e83e82c3c7e87c3c2c3c2c3c6c3c3c3c3e83c2c2c3c3c3c3c3c7c7c7c7e83c2c2c3c3c3c3c3c7c7c7c7c2c2ea82e1c2c2c2ea1fa1f1b0b1f0b1b1b1b031b131b031b13a1b0b0b1b1b46c5c6d1b171f1f1f1fa1b0b0b1b1b071b06c1c6c1f1f1f1faa0f82e0f0f86e0f1b0fa0f83e0f83e0f83ea03a0b0303030303030b0b03030b1303030303aa1ea0b030303030b1b03030b0b0303aaa87a80ea0303030b03130303030303030303030303030b0388ea80d03170340c0c2d0b170b42c2c2c2c2c2c0c0c0c0e23aa03030300c1c0c0b070b02c1c2c0b0b0b0b03030303aaaaaaaaaaaaaaaaaa031303a1f0303031b030b0303a0387a0303a80c0c0c0c0e80d03170340c0c7c7c0c0c0c0e80c0c0c03070307c7c0c0c0c0ea80c0e80c3e87e2b80e038ae2b8ae2baaa80e1ea80c4c0c4ea86ea0ba84eaa1f1f1f1f13030313985e6aa87c7c7c7c4c0c0c4ea2078aaaaaaaaaaaaaaaaaa03030303aa0b0b0b0b03030303aa0b0b0b0b03030303aaaaaaaaaaaaaaa03030303aa1b1b1b1b03030303aa1b1b1b1b03030303aaaa1baaaaaaaaa0baaa1baaa03aaa0387030303039a985ea87c7c0c0c0c0e078a8aa1f1f03030303aaaaaaaaaaaaaaaaaa03130313aa1f1f1f1f13030313aa1f1f1f1f1303031327272727aaaaaaaaaa0fa0f03a13030f0f030f0f03a0f0f0f0f0fa030fa0f0f0f0f130303130f0f0f0fa0f0f0f0f130303130f0f0f0f1fa1f0303aa0387031f13031313030303131b130b130b1313aa87c7c7c7c4c0c0c4c4d13171344c4e87c7c7c7c4c0c0c4c4c1c4c1307132a87e1f84e0384c3e1384c4c3e8ae2b8ae2b80c0c0c2e1b86c6c2e1b13a13130303a03030303a03030380c0c0c0c0c0c8e88c8d43174348c5c6c2c2c6c0c0c0c0c8e88c8c1d0c43072306c2c2c6c0c0c0c0ea83c3e83c3e83e0b80e0383e0f83e0f82c6c2c6c0c0e0380c0c0c4c0c0c0c0c0c0c7c0c2c0e1c0c0c0c0c0c0c0c6c2c2c6c0d03170340c0c0c0c0c0c6c2c2c6c0c0c0c03070300c0c0c0c3cac3cac3c2c2c3c0c0c0e030f0380c3c0c0c0c0c3cac3cac3cac3cac2c2c2c2c2e82c2c0c0e82c0c2e0384e13130384c4e84c4c0c2c2c0c2c2c8e88c8d3b173b48c5c2c2c2c2c4c0c0c4c8e88c8c1cec3b072302c2c2c2c4c0c0c4ea83c3e83c3e82e0b83e0383e0f83e0f82c2c2c2c2c7c0c4c0c4c0c2c0e1c0c0c2c2c2c2e0b82c2c0c0c0c2c4c2c2c2c2c2c4c0c0c4c2d0b170b42c2c2c2c2c2c4c0c0c4c2c1c2c0b070b03c3c3c3c2c3c2c2c2c2c3c0c0c3c2c2c2e0b0f0b83c3c3c3c3c3c3c3c0c0c0e0380c7c2c2c2c2c0c0c2c0c0c0c0c0c0c0c0c0c0c0c0c2c0c0d03030340c5c2c2c2c2c0c0c0c0c0c1c0c03030302c2c2c2c0c0c0c0c3c3c3c3c0c3c0e03030382c2c2c2c0c0c0c0c3c3c3c3c3c3c3c3c2c6c2c0e84c4c0c2c0c0c2c0c0c2c2c4ea84c2c2c4c2c2c2cbe8bc2c2c2c2c4c0c0c4c4c4c4c4cbe8bc2c2c2c2c4c0c0c4c4c4c4c4ea82c2e0b0f83c3e030f83e130f0f83e0f83e0fa80e82c0c0c0c2e03030303aa87a84c0c0c4c2c2c4e23aa030303030b0b0b0b1313131388ea80c0c0c0c2c2c2c2c4c4c4c4eaaaaaaaaa83eaaaa0313030ba1b1b0303030303030b030313aa1303031303030333a33030303031b0b0b1b1313131333a33030303031b0b0b1b13131313aa030380c3e0f1b82cae0f84c3c4e0f83e0f83e03030303031f1313131303031387030303031313131303030303131313130f0f0f0f030f030303030f0f130f0f0f0f0f0f0f0f0f0f0f1313130b86e1b1b0b86c0e80c0c0e1384c4c0e130ba0b0b030b031323a23234ec5ced23171b0b0b1b1303031323a2323073b0ec1c8c1b0b0b1b13030313aa0f0fa0f0fa0f82e0f80e0f83e0f83eaaaa030b0313aa1b0b0b1b13030313aa1b0b0b1b1303031327272727aaaaaaaaaaaa 24 16777215 10 1023
def nh_64 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_64_24 (Nat.sub p 768)) (hc_64_23 (Nat.sub p 736)) (Nat.blt p 768)) (Bool.rec (hc_64_22 (Nat.sub p 704)) (hc_64_21 (Nat.sub p 672)) (Nat.blt p 704)) (Nat.blt p 736)) (Bool.rec (Bool.rec (hc_64_20 (Nat.sub p 640)) (hc_64_19 (Nat.sub p 608)) (Nat.blt p 640)) (hc_64_18 (Nat.sub p 576)) (Nat.blt p 608)) (Nat.blt p 672)) (Bool.rec (Bool.rec (Bool.rec (hc_64_17 (Nat.sub p 544)) (hc_64_16 (Nat.sub p 512)) (Nat.blt p 544)) (hc_64_15 (Nat.sub p 480)) (Nat.blt p 512)) (Bool.rec (Bool.rec (hc_64_14 (Nat.sub p 448)) (hc_64_13 (Nat.sub p 416)) (Nat.blt p 448)) (hc_64_12 (Nat.sub p 384)) (Nat.blt p 416)) (Nat.blt p 480)) (Nat.blt p 576)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_64_11 (Nat.sub p 352)) (hc_64_10 (Nat.sub p 320)) (Nat.blt p 352)) (hc_64_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (Bool.rec (hc_64_8 (Nat.sub p 256)) (hc_64_7 (Nat.sub p 224)) (Nat.blt p 256)) (hc_64_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (hc_64_5 (Nat.sub p 160)) (hc_64_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_64_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_64_2 (Nat.sub p 64)) (hc_64_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_64_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)) (Nat.blt p 384)
def f_64 : Nat → Nat × Nat := unpackForestF 0x317c018b78bb6cc5db000315f140918a04400629e251bc016be00b5bc3a3661d180016af85838c2c1a002d4f098dc00b4fc1db7002d2c0168f7f56ec0e375fd1bafe8a97f36ebf81c5fc0d00168776c6fbec225db18eed6df7c034bb5b1ded192ed69f7a364bb5a5ddad1eee8a97737cbb9b25dc0d2ed68600a5fbad2a5c717ee948971c5bb8e2bdc9592e448972044b8e2980296ee18f967b4fb7dbe59ed2ecf68f6c454b61be5b0db2d94c16c034b3da1d9e1b2d069f6834bb41a3da3152d106968343b3c3000295eb3adf66054aceb1d671bec908959c63b1d2a56717ec548959c5bace2bd69592b68a960564ad89fd7b592bd4995b13baeeb256c4deb7ac95c13cadd2256c4ceb44895a044ace2980294eaf8dd57848abc2200293ead4c954c6faad3e55319ea94dc00a4ba98a5d4c51e9fac552568a7db7d4253ea128750570a7db380291e9d4dc00a43a65b75320e29906800a3fa5d325275be954f949d67a4d370028ee918d144d6fa389fd1c4ce8d8e144d67a289dd144de898c400a37a1d370028ce628df4204498a31cc4dbe81069313639fe324c4d3e7d6c93134b989a3cef152776f93bb649dc1a4c4d0e624df312639ca324e41126249f3826498925cdd5a26248f3626498921cd2d92690693123f99d324c48ee658d13123798d324c48cc012bf3015490a2fcbc512428b721457966b24b25125908921453958aa4ac152426bf2a134909adca455a50ce12816c909abc9c4d2426a72594492c22484d3e492692134b91ca348b5c2452b92134790c9a484d0c012b72047c861a7c7cdf2186970c3478de2a46edf2376d91c2608dc1a430d0e338f91a3608cc2243093e314f90c24b8bda7c5d5c21848f1627c86121c50df2294c1140348611fc4c9f2184771235b88e384308de214f90c23386036432d3e196970cb4786a2a4340d2196870c060004abbcd5be150a8f356379a37c24111e68c70815479a2fc1c511e68b6f34577f6b23ff15209ac8ffa3f81ab240cd31ff477025647fd1bc0159201479003447fd19bfa511fd088f3453799b7bccd8df82a8fc054799afbec4d1e66b6f9e707ccb63ccd5df1268f33537b8a23dc111e669ef6134799a5bd35c1e92b8f334779c9a3ccd0c012a6eac6e78e323aa9bde14a8eaa6b77e3e3aa99ddd4a8eaa63754243ac57dd62b6ec360758abbac54dd50880094f74cb23871bdd12f8e1c6773cb2386dbdcd268e1b6b72cbe386d9dc9268e1b6371c9a386d2dc52b8e1b4770cb700252dc0496e024768ab137d5a1a26dedda4f6ed21b755c1a26cedc56868937b6c959b4ce0da26c68935b64d3db1ae0d12676bb3835c9b1a24c6d626c6891db48dbda98f8d236b691b3b4cdb1a58e8d236368e303448dc0128ed0164661b7b3c4d1986d6ce17c661b3b344d1986c6cc16e004a1b0edb9956c8c3a6f64d2230e9ad916f8c3a6763d2230e98d87070c415f620adb14981882aec415361c1a0024fd852c8bad6f60cbe2eb59d812c8bab6f5fc9a2eadad7d2f8bab675ec9a2ead8d79268bab5b5dcb62ead5d752dc0093b5ce342a95bd7047eb82335be382a959d6c476b6237552312d51a1544deb424659ab82cc971544d6b235b58e382a899d60ae0b025c55131abc971544b6ab36f56e3e2acdad566ceac36c55e3a2acd8d558c0aa2570049baa45914a6dea8134529b5a9c5f14a6cea6134529b1a945b801266a4264486b7a8c95121ad6a147c50a382849f121ace9fa544fc2a24358d3cafe9e26448637a74911218d69b57c4dab826c9f1218ce99a444cc2224318d30afc982544862fa5b1f92d48890c5b4862ba499f929afc9257e492b22491f9244889204448629a44d0d214dc0092f47cb21f15bd1d2a87c56b4663e2331c1192f87c567458aa22c150f8ac689d7f44cb21f11bd112887c46b436be21b5c10d2f87c467428a2214110f88c683d7e41caa1f117d048fc821443e22d9f115cfbcfc8057e3eebf1f7590fb8fc7d9443ec221f114cf96867c16e004959ecda0baade7a3582eab59df1f0ef8e07824b3bdb817559ceb6b0762403ac2a17558ce8afe743682ea379ccd20ba8d670d7c386b81c496ce16e05d467375a41bc8c0dd0885d46336abf1b4d60ba8be6bc7e35da417516cba8ae6567e34ebf1955f8caac86547e336b719d1b8cd8dc6534832d18194110ba8a661d6930eb09871a4c38c26224430e29974d88ba0785db4f2eda5976d1cbc8a85e0342eda19740c00124e5c164186b796c55061ad65947c2ca381645f061ace579542bc2a0c358cacafe5616418637954510618d65357c29ab814c5f0618ce5194428c220c318ca0afc501541862f93b1f89d28830c5b1862b91b9f899afc46d7e236b211b1f88f6de4a47c23db591ed9c916d84847423db191a5108d08830c531922f8c916c866d84336021d1d90c980648ae4194420c220c914c818de3235f191ad8f71b07b8c03e24b1ed300c8d5c782683c034191a98ed1b86469e3a36e191a58c8d1c65adc3846e196370cb150656dc33a5f19d2d8d4580674ae3412819d298ca4d065068323431851a0c4d0c612dc0092317c9380217c5d0882e4530042d8b4dc05924e0085715c220ad14c010a626c6e14e3209a9bc518c82696f13abf09cd604d24e0084f12826094110010962324711d2288c51c3bac4225680ed378855a03b2de1fb5a0fdac07b9c83d6c01d9270ec3500211c0108618b6e0ddb20629bc356c81896f0ca3f064d203124e0083f0b82e05c15001076152370ad1a8544dc1f8c41446807d3784d1a01f2de11b4a08da40435c8216a00f92707c350020dc010660d26e06d320345bc0105e0c04405e298020ac152de0082704c2202114c102ac081460041181c5900c6de0616e0040f814110098a60081b01db780205c0508801453008ab004518010260003f 10 11
def ch_64 : Nat → Bool := dagCheckNodeV5 fullMask g_64 ep_64 6 63 bds_64 795 (dagTraceF fullMask rootStock 11 f_64) cur_64 nh_64
set_option maxHeartbeats 0 in
theorem rc_64 : dagCheckRootsV5 fullMask g_64 ep_64 6 63 795 bds_64 (dagTraceF fullMask rootStock 11 f_64) (cur_64 0) (nh_64 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_0 : treeBlockF 0 32 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_1 : treeBlockF 32 64 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_2 : treeBlockF 64 96 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_3 : treeBlockF 96 128 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_4 : treeBlockF 128 160 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_5 : treeBlockF 160 192 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_6 : treeBlockF 192 224 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_7 : treeBlockF 224 256 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_8 : treeBlockF 256 288 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_9 : treeBlockF 288 320 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_10 : treeBlockF 320 352 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_11 : treeBlockF 352 384 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_12 : treeBlockF 384 416 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_13 : treeBlockF 416 448 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_14 : treeBlockF 448 480 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_15 : treeBlockF 480 512 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_16 : treeBlockF 512 544 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_17 : treeBlockF 544 576 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_18 : treeBlockF 576 608 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_19 : treeBlockF 608 640 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_20 : treeBlockF 640 672 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_21 : treeBlockF 672 704 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_22 : treeBlockF 704 736 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_23 : treeBlockF 736 768 ch_64 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_64_24 : treeBlockF 768 795 ch_64 = true := by decide +kernel
theorem nj_64_1 : ∀ i, 0 ≤ i → i < 64 → ch_64 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_64_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_64_1 h1 h2)
theorem nj_64_2 : ∀ i, 0 ≤ i → i < 96 → ch_64 i = true := block_join nj_64_1 (fun _ h1 h2 => treeBlockF_at nb_64_2 h1 h2)
theorem nj_64_3 : ∀ i, 0 ≤ i → i < 128 → ch_64 i = true := block_join nj_64_2 (fun _ h1 h2 => treeBlockF_at nb_64_3 h1 h2)
theorem nj_64_4 : ∀ i, 0 ≤ i → i < 160 → ch_64 i = true := block_join nj_64_3 (fun _ h1 h2 => treeBlockF_at nb_64_4 h1 h2)
theorem nj_64_5 : ∀ i, 0 ≤ i → i < 192 → ch_64 i = true := block_join nj_64_4 (fun _ h1 h2 => treeBlockF_at nb_64_5 h1 h2)
theorem nj_64_6 : ∀ i, 0 ≤ i → i < 224 → ch_64 i = true := block_join nj_64_5 (fun _ h1 h2 => treeBlockF_at nb_64_6 h1 h2)
theorem nj_64_7 : ∀ i, 0 ≤ i → i < 256 → ch_64 i = true := block_join nj_64_6 (fun _ h1 h2 => treeBlockF_at nb_64_7 h1 h2)
theorem nj_64_8 : ∀ i, 0 ≤ i → i < 288 → ch_64 i = true := block_join nj_64_7 (fun _ h1 h2 => treeBlockF_at nb_64_8 h1 h2)
theorem nj_64_9 : ∀ i, 0 ≤ i → i < 320 → ch_64 i = true := block_join nj_64_8 (fun _ h1 h2 => treeBlockF_at nb_64_9 h1 h2)
theorem nj_64_10 : ∀ i, 0 ≤ i → i < 352 → ch_64 i = true := block_join nj_64_9 (fun _ h1 h2 => treeBlockF_at nb_64_10 h1 h2)
theorem nj_64_11 : ∀ i, 0 ≤ i → i < 384 → ch_64 i = true := block_join nj_64_10 (fun _ h1 h2 => treeBlockF_at nb_64_11 h1 h2)
theorem nj_64_12 : ∀ i, 0 ≤ i → i < 416 → ch_64 i = true := block_join nj_64_11 (fun _ h1 h2 => treeBlockF_at nb_64_12 h1 h2)
theorem nj_64_13 : ∀ i, 0 ≤ i → i < 448 → ch_64 i = true := block_join nj_64_12 (fun _ h1 h2 => treeBlockF_at nb_64_13 h1 h2)
theorem nj_64_14 : ∀ i, 0 ≤ i → i < 480 → ch_64 i = true := block_join nj_64_13 (fun _ h1 h2 => treeBlockF_at nb_64_14 h1 h2)
theorem nj_64_15 : ∀ i, 0 ≤ i → i < 512 → ch_64 i = true := block_join nj_64_14 (fun _ h1 h2 => treeBlockF_at nb_64_15 h1 h2)
theorem nj_64_16 : ∀ i, 0 ≤ i → i < 544 → ch_64 i = true := block_join nj_64_15 (fun _ h1 h2 => treeBlockF_at nb_64_16 h1 h2)
theorem nj_64_17 : ∀ i, 0 ≤ i → i < 576 → ch_64 i = true := block_join nj_64_16 (fun _ h1 h2 => treeBlockF_at nb_64_17 h1 h2)
theorem nj_64_18 : ∀ i, 0 ≤ i → i < 608 → ch_64 i = true := block_join nj_64_17 (fun _ h1 h2 => treeBlockF_at nb_64_18 h1 h2)
theorem nj_64_19 : ∀ i, 0 ≤ i → i < 640 → ch_64 i = true := block_join nj_64_18 (fun _ h1 h2 => treeBlockF_at nb_64_19 h1 h2)
theorem nj_64_20 : ∀ i, 0 ≤ i → i < 672 → ch_64 i = true := block_join nj_64_19 (fun _ h1 h2 => treeBlockF_at nb_64_20 h1 h2)
theorem nj_64_21 : ∀ i, 0 ≤ i → i < 704 → ch_64 i = true := block_join nj_64_20 (fun _ h1 h2 => treeBlockF_at nb_64_21 h1 h2)
theorem nj_64_22 : ∀ i, 0 ≤ i → i < 736 → ch_64 i = true := block_join nj_64_21 (fun _ h1 h2 => treeBlockF_at nb_64_22 h1 h2)
theorem nj_64_23 : ∀ i, 0 ≤ i → i < 768 → ch_64 i = true := block_join nj_64_22 (fun _ h1 h2 => treeBlockF_at nb_64_23 h1 h2)
theorem nj_64_24 : ∀ i, 0 ≤ i → i < 795 → ch_64 i = true := block_join nj_64_23 (fun _ h1 h2 => treeBlockF_at nb_64_24 h1 h2)
theorem nc_64 : ∀ i, 0 ≤ i → i < 795 → ch_64 i = true := nj_64_24
theorem lb_64 : LowerBin fullMask rootStock g_64 12 :=
  lowerDagV5 (kn_cons lb_62 (kn_cons lb_60 (kn_cons lb_29 (kn_cons lb_61 (kn_cons lb_63 (kn_cons lb_58 (kn_cons lb_38 (kn_cons lb_57 (kn_cons lb_56 (kn_cons lb_59 (kn_cons lb_33 (kn_cons lb_54 (kn_cons lb_23 (kn_cons lb_40 (kn_cons lb_49 (kn_cons lb_48 (kn_cons lb_24 (kn_cons lb_28 (kn_cons lb_34 (kn_cons lb_45 (kn_cons lb_35 (kn_cons lb_43 (kn_cons lb_42 (kn_cons lb_39 (kn_cons lb_26 (kn_cons lb_41 (kn_cons lb_51 (kn_cons lb_30 (kn_cons lb_52 (kn_cons lb_32 (kn_cons lb_27 (kn_cons lb_36 (kn_cons lb_50 (kn_cons lb_31 (kn_cons lb_53 (kn_cons lb_44 (kn_nil))))))))))))))))))))))))))))))))))))) rc_64 nc_64 (by decide +kernel)

def wg : List Gate := [⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [2, 8]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [0, 11]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.or, [5, 12]⟩, ⟨GateOp.and, [7, 14]⟩, ⟨GateOp.or, [8, 15]⟩, ⟨GateOp.or, [10, 13]⟩, ⟨GateOp.and, [16, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 4272465920) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276676776 * 2 ^ 32 + 4272465920)) (13 - 1) := by
  rw [show canon fullMask (4276676776 * 2 ^ 32 + 4272465920) = g_64 by decide]
  exact lb_64

end PEqualNP.Outside.L_meta_47937

theorem PEqualNP.Outside.L_meta_47937 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676776 * 2 ^ 32 + 4272465920) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 4272465920) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_47937.table2_from_lowerBin (4276676776 * 2 ^ 32 + 4272465920) 13 PEqualNP.Outside.L_meta_47937.root_lb PEqualNP.Outside.L_meta_47937.wg 18 rfl PEqualNP.Outside.L_meta_47937.wfits PEqualNP.Outside.L_meta_47937.weval
